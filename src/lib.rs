//! Client-side Groth16 prover for the Paraloom wallet.
//!
//! Proofs are assembled entirely in the browser — spend keys never leave the
//! wallet — and each entry point returns the body the wallet POSTs to the
//! validator network. `prove_transact` is the current settlement path (circuit
//! v3); the v2 withdraw and transfer provers remain for the pre-v3 flows.
//!
//! The circuits are not reimplemented here. `privacy` includes paraloom-core's
//! own sources by path, so the browser proves against the same constraint
//! system the validators verify.

pub mod privacy;

use ark_bn254::{Bn254, Fr};
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::ProvingKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use wasm_bindgen::prelude::*;

use serde::Deserialize;

use privacy::circuits::{Groth16ProofSystem, TransferCircuitV2, WithdrawCircuitV2};
use privacy::poseidon::{
    poseidon_commit, poseidon_commit_spend, poseidon_merkle_pair, poseidon_nullifier_spend,
    poseidon_pubkey, poseidon_signature,
};
use privacy::poseidon_circom::v3_merkle_pair;
use sha2::{Digest, Sha256};

fn fr_to_le_bytes_32(fr: Fr) -> [u8; 32] {
    let mut v = fr.into_bigint().to_bytes_le();
    v.resize(32, 0);
    let mut o = [0u8; 32];
    o.copy_from_slice(&v[..32]);
    o
}

fn hex32(s: &str) -> Result<[u8; 32], JsValue> {
    let b = hex::decode(s.trim()).map_err(|e| JsValue::from_str(&format!("bad hex: {e}")))?;
    if b.len() != 32 {
        return Err(JsValue::from_str("expected 32-byte hex"));
    }
    let mut o = [0u8; 32];
    o.copy_from_slice(&b);
    Ok(o)
}

/// Poseidon commitment for a note `(amount, randomness, recipient)`, hex. The
/// wallet needs this to look up the note's Merkle path from the path server.
#[wasm_bindgen]
pub fn note_commitment(
    amount: u64,
    randomness_hex: &str,
    recipient_hex: &str,
) -> Result<String, JsValue> {
    let randomness = hex32(randomness_hex)?;
    let recipient = hex32(recipient_hex)?;
    let c = poseidon_commit(
        Fr::from(amount),
        Fr::from_le_bytes_mod_order(&randomness),
        Fr::from_le_bytes_mod_order(&recipient),
        Fr::from(0u64), // native-SOL asset id (#235)
    );
    Ok(hex::encode(fr_to_le_bytes_32(c)))
}

/// Derive the v2 spend public key.
///
/// `pubkey = Poseidon(privkey)`, the value bound into a v2 note's commitment.
/// The wallet derives its spend keypair from the account seed and publishes
/// this pubkey as part of its shielded address, so a sender can bind an output
/// note to it; only the holder of `privkey` can later spend that note.
///
/// This is the v2 hash family (domain-tagged). The v3 equivalent is
/// [`v3_note_pubkey`], which uses circom Poseidon and is not interchangeable.
#[wasm_bindgen]
pub fn spend_pubkey(privkey_hex: &str) -> Result<String, JsValue> {
    let sk = Fr::from_le_bytes_mod_order(&hex32(privkey_hex)?);
    Ok(hex::encode(fr_to_le_bytes_32(poseidon_pubkey(sk))))
}

/// The v2 note commitment,
/// `Poseidon(amount, Poseidon(privkey), blinding, asset_id)`.
///
/// Unlike the v1 [`note_commitment`], the note binds the owner's spend *public
/// key* rather than a recipient address, and an `asset_id` (the mint's 32
/// bytes; all-zero for native SOL). The wallet stores `(privkey, blinding,
/// asset_id)` and recomputes this to look up the note's Merkle path.
///
/// Drives the v2 withdraw and transfer flows, so it lives exactly as long as
/// [`prove_withdrawal_v2`] and [`prove_transfer_v2`] do.
#[wasm_bindgen]
pub fn note_commitment_v2(
    amount: u64,
    privkey_hex: &str,
    blinding_hex: &str,
    asset_id_hex: &str,
) -> Result<String, JsValue> {
    let sk = Fr::from_le_bytes_mod_order(&hex32(privkey_hex)?);
    let c = poseidon_commit_spend(
        Fr::from(amount),
        poseidon_pubkey(sk),
        Fr::from_le_bytes_mod_order(&hex32(blinding_hex)?),
        Fr::from_le_bytes_mod_order(&hex32(asset_id_hex)?),
    );
    Ok(hex::encode(fr_to_le_bytes_32(c)))
}

fn rng_from_entropy() -> StdRng {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).expect("browser entropy");
    StdRng::from_seed(seed)
}

/// Build a `(sibling, is_left)` Merkle path from parallel hex/bool arrays.
fn merkle_path_from(
    path_hex: &[String],
    indices: &[bool],
) -> Result<Vec<([u8; 32], bool)>, JsValue> {
    if path_hex.len() != indices.len() {
        return Err(JsValue::from_str("path and indices length mismatch"));
    }
    let mut path = Vec::with_capacity(path_hex.len());
    for (h, dir) in path_hex.iter().zip(indices) {
        path.push((hex32(h)?, *dir));
    }
    Ok(path)
}

/// Leaf index from a path's direction bits: a level adds `2^level` when the
/// current node is the right child (`is_left == false`), matching the spend-key
/// circuits' in-circuit derivation. The spend-key nullifier binds this index, so
/// the prover must compute it the same way.
fn leaf_index_from(indices: &[bool]) -> u64 {
    let mut idx = 0u64;
    for (level, is_left) in indices.iter().enumerate() {
        if !is_left {
            idx += 1u64 << level;
        }
    }
    idx
}

/// Prove a spend-key withdrawal (circuit v2, #293).
///
/// Spend authority is the note's private key rather than a free secret: the commitment binds `Poseidon(privkey)` and the
/// nullifier folds in a signature over `(commitment, leaf_index)`, so only the
/// key-holder can spend and a note at a tree position yields exactly one
/// nullifier. The proof also commits to the withdrawal's `asset_id` (finding A)
/// and `ext_data_hash` (finding D), the latter derived here exactly as the
/// on-chain program does: `sha256(dest_recipient || amount.to_le_bytes())`. The
/// program recomputes both from the vault mint and the recipient it pays, so a
/// proof cannot be replayed against another asset or redirected.
///
/// - `proving_key`: the v2 ceremony proving key bytes (withdraw_v2_proving.key)
/// - `privkey_hex`, `blinding_hex`, `asset_id_hex`: the note's spend key,
///   blinding and asset id (32-byte hex; asset id all-zero for native SOL)
/// - `dest_recipient_hex`: the on-chain Solana destination the funds are paid to
/// - `path_hex_json` / `indices_json`: the root-less Merkle path and its
///   direction bits
///
/// Returns `{ nullifier, proof }` (hex).
#[wasm_bindgen]
#[allow(clippy::too_many_arguments)]
pub fn prove_withdrawal_v2(
    proving_key: &[u8],
    root_hex: &str,
    amount: u64,
    blinding_hex: &str,
    privkey_hex: &str,
    asset_id_hex: &str,
    dest_recipient_hex: &str,
    path_hex_json: &str,
    indices_json: &str,
) -> Result<String, JsValue> {
    let root = hex32(root_hex)?;
    let blinding = hex32(blinding_hex)?;
    let privkey = hex32(privkey_hex)?;
    let asset_id = hex32(asset_id_hex)?;
    let dest_recipient = hex32(dest_recipient_hex)?;

    let path_hex: Vec<String> = serde_json::from_str(path_hex_json)
        .map_err(|e| JsValue::from_str(&format!("bad path json: {e}")))?;
    let indices: Vec<bool> = serde_json::from_str(indices_json)
        .map_err(|e| JsValue::from_str(&format!("bad indices json: {e}")))?;
    let merkle_path = merkle_path_from(&path_hex, &indices)?;

    let leaf_index = leaf_index_from(&indices);

    let sk = Fr::from_le_bytes_mod_order(&privkey);
    let commitment_fr = poseidon_commit_spend(
        Fr::from(amount),
        poseidon_pubkey(sk),
        Fr::from_le_bytes_mod_order(&blinding),
        Fr::from_le_bytes_mod_order(&asset_id),
    );
    let signature = poseidon_signature(sk, commitment_fr, Fr::from(leaf_index));
    let nullifier_fr = poseidon_nullifier_spend(commitment_fr, Fr::from(leaf_index), signature);
    let nullifier = fr_to_le_bytes_32(nullifier_fr);

    // ext_data_hash = sha256(recipient || amount_le), identical to the program's
    // `withdraw_ext_data_hash`.
    let mut hasher = Sha256::new();
    hasher.update(dest_recipient);
    hasher.update(amount.to_le_bytes());
    let ext_data_hash: [u8; 32] = hasher.finalize().into();

    let circuit = WithdrawCircuitV2 {
        merkle_root: Some(root),
        nullifier: Some(nullifier),
        withdraw_amount: Some(amount),
        ext_data_hash: Some(ext_data_hash),
        input_value: Some(amount),
        blinding: Some(blinding),
        privkey: Some(privkey),
        asset_id: Some(asset_id),
        input_path: Some(merkle_path),
    };

    let pk = ProvingKey::<Bn254>::deserialize_compressed(proving_key)
        .map_err(|e| JsValue::from_str(&format!("bad proving key: {e}")))?;
    let proof =
        Groth16ProofSystem::prove::<WithdrawCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| JsValue::from_str(&format!("serialize failed: {e}")))?;

    Ok(format!(
        "{{\"nullifier\":\"{}\",\"proof\":\"{}\"}}",
        hex::encode(nullifier),
        hex::encode(proof_bytes)
    ))
}

/// An input note being spent in a transfer. `path_hex`/`indices` are the
/// root-less Merkle path proving the note's commitment is in the tree, pulled
/// from the path server.
#[derive(Deserialize, Clone)]
pub struct TransferInputV2 {
    pub amount: u64,
    /// The note's spend key. Authority is knowledge of this, not of a free
    /// secret: it is folded into the nullifier through a signature over
    /// `(commitment, leaf_index)`.
    pub privkey_hex: String,
    pub blinding_hex: String,
    /// Root-less Merkle path, sibling per level.
    pub path_hex: Vec<String>,
    /// Direction bit per level; also gives the leaf index.
    pub indices: Vec<bool>,
}

/// An output note being created. A value-0 note is a valid "empty" output.
#[derive(Deserialize, Clone)]
pub struct TransferOutputV2 {
    pub amount: u64,
    /// The recipient's spend *public* key, `Poseidon(privkey)`.
    pub pubkey_hex: String,
    pub blinding_hex: String,
}

pub fn validate_v2_two_input_merkle_lca(
    c0: Fr,
    c1: Fr,
    i0: u64,
    i1: u64,
    path0: &[[u8; 32]],
    path1: &[[u8; 32]],
    context: &str,
) -> Result<(), String> {
    if path0.len() != path1.len() {
        return Err(format!("{context}: cross-input path length mismatch"));
    }
    let depth = path0.len();
    if depth == 0 {
        return Err(format!("{context}: cross-input path cannot be empty"));
    }
    if i0 == i1 {
        return Err(format!(
            "{context}: cross-input active notes must have distinct leaf indices"
        ));
    }
    let diff = i0 ^ i1;
    let d_lca = (63 - diff.leading_zeros()) as usize;
    if d_lca >= depth {
        return Err(format!(
            "{context}: cross-input LCA depth {d_lca} exceeds tree depth {depth}"
        ));
    }

    let mut node0 = c0;
    for (d, sib_bytes) in path0.iter().enumerate().take(d_lca) {
        let sib_fr = Fr::from_le_bytes_mod_order(sib_bytes);
        node0 = if ((i0 >> d) & 1) == 0 {
            poseidon_merkle_pair(node0, sib_fr)
        } else {
            poseidon_merkle_pair(sib_fr, node0)
        };
    }

    let mut node1 = c1;
    for (d, sib_bytes) in path1.iter().enumerate().take(d_lca) {
        let sib_fr = Fr::from_le_bytes_mod_order(sib_bytes);
        node1 = if ((i1 >> d) & 1) == 0 {
            poseidon_merkle_pair(node1, sib_fr)
        } else {
            poseidon_merkle_pair(sib_fr, node1)
        };
    }

    if path0[d_lca] != fr_to_le_bytes_32(node1) {
        return Err(format!(
            "{context}: cross-input LCA sibling mismatch at level {d_lca}: path_0[{d_lca}] != node_1"
        ));
    }
    if path1[d_lca] != fr_to_le_bytes_32(node0) {
        return Err(format!(
            "{context}: cross-input LCA sibling mismatch at level {d_lca}: path_1[{d_lca}] != node_0"
        ));
    }

    for d in (d_lca + 1)..depth {
        if path0[d] != path1[d] {
            return Err(format!(
                "{context}: cross-input ancestor sibling mismatch at level {d}: path_0[{d}] != path_1[{d}]"
            ));
        }
    }

    Ok(())
}

pub fn validate_v3_two_input_merkle_lca(
    c0: Fr,
    c1: Fr,
    i0: u64,
    i1: u64,
    path0: &[[u8; 32]],
    path1: &[[u8; 32]],
    context: &str,
) -> Result<(), String> {
    if path0.len() != path1.len() {
        return Err(format!("{context}: cross-input path length mismatch"));
    }
    let depth = path0.len();
    if depth == 0 {
        return Err(format!("{context}: cross-input path cannot be empty"));
    }
    if i0 == i1 {
        return Err(format!(
            "{context}: cross-input active notes must have distinct leaf indices"
        ));
    }
    let diff = i0 ^ i1;
    let d_lca = (63 - diff.leading_zeros()) as usize;
    if d_lca >= depth {
        return Err(format!(
            "{context}: cross-input LCA depth {d_lca} exceeds tree depth {depth}"
        ));
    }

    let mut node0 = c0;
    for (d, sib_bytes) in path0.iter().enumerate().take(d_lca) {
        let sib_fr = Fr::from_le_bytes_mod_order(sib_bytes);
        node0 = if ((i0 >> d) & 1) == 0 {
            v3_merkle_pair(node0, sib_fr)
        } else {
            v3_merkle_pair(sib_fr, node0)
        };
    }

    let mut node1 = c1;
    for (d, sib_bytes) in path1.iter().enumerate().take(d_lca) {
        let sib_fr = Fr::from_le_bytes_mod_order(sib_bytes);
        node1 = if ((i1 >> d) & 1) == 0 {
            v3_merkle_pair(node1, sib_fr)
        } else {
            v3_merkle_pair(sib_fr, node1)
        };
    }

    if path0[d_lca] != fr_to_le_bytes_32(node1) {
        return Err(format!(
            "{context}: cross-input LCA sibling mismatch at level {d_lca}: path_0[{d_lca}] != node_1"
        ));
    }
    if path1[d_lca] != fr_to_le_bytes_32(node0) {
        return Err(format!(
            "{context}: cross-input LCA sibling mismatch at level {d_lca}: path_1[{d_lca}] != node_0"
        ));
    }

    for d in (d_lca + 1)..depth {
        if path0[d] != path1[d] {
            return Err(format!(
                "{context}: cross-input ancestor sibling mismatch at level {d}: path_0[{d}] != path_1[{d}]"
            ));
        }
    }

    Ok(())
}

pub fn validate_transfer_v2_slots(
    inputs: &[TransferInputV2],
    outputs: &[TransferOutputV2],
    context: &str,
) -> Result<(), String> {
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(format!(
            "{context}: transfer requires exactly 2 inputs and 2 outputs"
        ));
    }
    if inputs[0].amount == 0 || inputs[1].amount == 0 {
        return Err(format!(
            "{context}: transfer requires both inputs to have amount > 0"
        ));
    }
    if inputs[0].path_hex.is_empty() || inputs[0].path_hex.len() != inputs[1].path_hex.len() {
        return Err(format!(
            "{context}: transfer requires non-empty input paths of equal depth"
        ));
    }
    if outputs[0].amount == 0 {
        return Err(format!(
            "{context}: transfer requires outputs[0].amount > 0"
        ));
    }
    Ok(())
}

pub fn validate_transact_slots(
    inputs: &[TransactInputNote],
    outputs: &[TransactOutputNote],
    ext_amount: i64,
    context: &str,
) -> Result<(), String> {
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(format!("{context}: transact is fixed 2-in/2-out"));
    }
    if inputs[0].amount == 0 {
        return Err(format!(
            "{context}: transact requires inputs[0].amount > 0 (dummy inputs are placed in inputs[1])"
        ));
    }
    if (ext_amount == 0 || outputs[1].amount > 0) && outputs[0].amount == 0 {
        return Err(format!(
            "{context}: transact requires outputs[0].amount > 0 when ext_amount == 0 or outputs[1].amount > 0"
        ));
    }
    Ok(())
}

/// Build a shielded → shielded transfer proof with the spend-key construction
/// (circuit v2, #293), entirely in the browser.
///
/// Fixed 2-in/2-out. Each input is spent by
/// proving knowledge of its private key (folded into the nullifier through a
/// signature over `(commitment, leaf_index)`), and each output binds the
/// recipient's spend public key. All notes share one `asset_id` (all-zero for
/// native SOL); the circuit enforces value conservation and input-nullifier
/// distinctness.
///
/// - `proving_key`: the v2 transfer ceremony proving key bytes
/// - `root_hex`: the inputs' membership root, 32-byte hex
/// - `asset_id_hex`: the shared asset id, 32-byte hex (all-zero = native SOL)
/// - `inputs_json`: JSON array of 2 input notes
/// - `outputs_json`: JSON array of 2 output notes
///
/// Returns `{ nullifiers, output_commitments, proof }` (hex).
#[wasm_bindgen]
pub fn prove_transfer_v2(
    proving_key: &[u8],
    root_hex: &str,
    asset_id_hex: &str,
    inputs_json: &str,
    outputs_json: &str,
) -> Result<String, JsValue> {
    let root = hex32(root_hex)?;
    let asset_id = hex32(asset_id_hex)?;
    let asset_fr = Fr::from_le_bytes_mod_order(&asset_id);

    let inputs: Vec<TransferInputV2> = serde_json::from_str(inputs_json)
        .map_err(|e| JsValue::from_str(&format!("bad inputs json: {e}")))?;
    let outputs: Vec<TransferOutputV2> = serde_json::from_str(outputs_json)
        .map_err(|e| JsValue::from_str(&format!("bad outputs json: {e}")))?;
    validate_transfer_v2_slots(&inputs, &outputs, "prove_transfer_v2")
        .map_err(|e| JsValue::from_str(&e))?;

    let mut nullifiers = Vec::with_capacity(2);
    let mut input_commitments = Vec::with_capacity(2);
    let mut input_values = Vec::with_capacity(2);
    let mut input_blindings = Vec::with_capacity(2);
    let mut input_privkeys = Vec::with_capacity(2);
    let mut input_paths = Vec::with_capacity(2);
    for inp in &inputs {
        let blinding = hex32(&inp.blinding_hex)?;
        let privkey = hex32(&inp.privkey_hex)?;
        let sk = Fr::from_le_bytes_mod_order(&privkey);
        let commitment_fr = poseidon_commit_spend(
            Fr::from(inp.amount),
            poseidon_pubkey(sk),
            Fr::from_le_bytes_mod_order(&blinding),
            asset_fr,
        );
        input_commitments.push(commitment_fr);
        let leaf_index = leaf_index_from(&inp.indices);
        let signature = poseidon_signature(sk, commitment_fr, Fr::from(leaf_index));
        let nullifier_fr = poseidon_nullifier_spend(commitment_fr, Fr::from(leaf_index), signature);
        nullifiers.push(fr_to_le_bytes_32(nullifier_fr));
        input_values.push(inp.amount);
        input_blindings.push(blinding);
        input_privkeys.push(privkey);
        input_paths.push(merkle_path_from(&inp.path_hex, &inp.indices)?);
    }

    let i0 = leaf_index_from(&inputs[0].indices);
    let i1 = leaf_index_from(&inputs[1].indices);
    let mut p0 = Vec::with_capacity(inputs[0].path_hex.len());
    for s in &inputs[0].path_hex {
        p0.push(hex32(s)?);
    }
    let mut p1 = Vec::with_capacity(inputs[1].path_hex.len());
    for s in &inputs[1].path_hex {
        p1.push(hex32(s)?);
    }
    validate_v2_two_input_merkle_lca(
        input_commitments[0],
        input_commitments[1],
        i0,
        i1,
        &p0,
        &p1,
        "prove_transfer_v2",
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let mut output_commitments = Vec::with_capacity(2);
    let mut output_values = Vec::with_capacity(2);
    let mut output_blindings = Vec::with_capacity(2);
    let mut output_pubkeys = Vec::with_capacity(2);
    for out in &outputs {
        let blinding = hex32(&out.blinding_hex)?;
        let pubkey = hex32(&out.pubkey_hex)?;
        let commitment_fr = poseidon_commit_spend(
            Fr::from(out.amount),
            Fr::from_le_bytes_mod_order(&pubkey),
            Fr::from_le_bytes_mod_order(&blinding),
            asset_fr,
        );
        output_commitments.push(fr_to_le_bytes_32(commitment_fr));
        output_values.push(out.amount);
        output_blindings.push(blinding);
        output_pubkeys.push(pubkey);
    }

    let circuit = TransferCircuitV2::with_witness(
        root,
        nullifiers.clone(),
        output_commitments.clone(),
        input_values,
        input_blindings,
        input_privkeys,
        input_paths,
        output_values,
        output_blindings,
        output_pubkeys,
        asset_id,
    );

    let pk = ProvingKey::<Bn254>::deserialize_compressed(proving_key)
        .map_err(|e| JsValue::from_str(&format!("bad proving key: {e}")))?;
    let proof =
        Groth16ProofSystem::prove::<TransferCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| JsValue::from_str(&format!("serialize failed: {e}")))?;

    let nulls: Vec<String> = nullifiers.iter().map(hex::encode).collect();
    let commits: Vec<String> = output_commitments.iter().map(hex::encode).collect();
    Ok(format!(
        "{{\"nullifiers\":[\"{}\",\"{}\"],\"output_commitments\":[\"{}\",\"{}\"],\"proof\":\"{}\"}}",
        nulls[0],
        nulls[1],
        commits[0],
        commits[1],
        hex::encode(proof_bytes)
    ))
}

// ===== circuit v3 (#350): unified transact =====

use privacy::circuits::{TransactCircuitV3, TX_LEVELS};
use privacy::poseidon_circom::{v3_commit, v3_nullifier, v3_pubkey, v3_signature};

/// Derive the shielded-asset field element for an SPL `mint` (#779):
/// `Poseidon(2)` over the mint's two 16-byte little-endian halves. Matches the
/// on-chain `merkle_tree::mint_to_asset` exactly, so a wallet-built SPL note or
/// transact proof carries the same `asset_id` the program derives from the mint
/// account. Native SOL keeps the all-zero asset and never calls this.
///
/// `mint_hex` is the 32-byte mint pubkey, hex. Returns the 32-byte asset id, hex.
#[wasm_bindgen]
pub fn mint_to_asset(mint_hex: &str) -> Result<String, JsValue> {
    let mint = hex32(mint_hex)?;
    let lo = Fr::from_le_bytes_mod_order(&mint[..16]);
    let hi = Fr::from_le_bytes_mod_order(&mint[16..]);
    Ok(hex::encode(fr_to_le_bytes_32(v3_merkle_pair(lo, hi))))
}

/// Derive the v3 spend public key `Poseidon1(privkey)` (circom Poseidon).
#[wasm_bindgen]
pub fn v3_note_pubkey(privkey_hex: &str) -> Result<String, JsValue> {
    let sk = Fr::from_le_bytes_mod_order(&hex32(privkey_hex)?);
    Ok(hex::encode(fr_to_le_bytes_32(v3_pubkey(sk))))
}

/// Derive a v3 note commitment `Poseidon4(amount, pubkey, blinding, asset)`
/// for the native asset — the exact leaf `deposit_note` appends on-chain.
#[wasm_bindgen]
pub fn v3_note_commitment(
    amount: u64,
    pubkey_hex: &str,
    blinding_hex: &str,
) -> Result<String, JsValue> {
    let c = v3_commit(
        Fr::from(amount),
        Fr::from_le_bytes_mod_order(&hex32(pubkey_hex)?),
        Fr::from_le_bytes_mod_order(&hex32(blinding_hex)?),
        Fr::from(0u64), // NATIVE_SOL
    );
    Ok(hex::encode(fr_to_le_bytes_32(c)))
}

/// The v3 note commitment for an arbitrary asset (#779): identical to
/// [`v3_note_commitment`] but takes the note's `asset_id` (all-zero for native
/// SOL, or `mint_to_asset(mint)` for a shielded SPL note) instead of assuming
/// native. Used to locate a shielded SPL note's leaf in the on-chain tree.
#[wasm_bindgen]
pub fn v3_note_commitment_asset(
    amount: u64,
    pubkey_hex: &str,
    blinding_hex: &str,
    asset_id_hex: &str,
) -> Result<String, JsValue> {
    let c = v3_commit(
        Fr::from(amount),
        Fr::from_le_bytes_mod_order(&hex32(pubkey_hex)?),
        Fr::from_le_bytes_mod_order(&hex32(blinding_hex)?),
        Fr::from_le_bytes_mod_order(&hex32(asset_id_hex)?),
    );
    Ok(hex::encode(fr_to_le_bytes_32(c)))
}

/// An input note being spent by `prove_transact`. `path_hex` is the 32-entry
/// sibling list from the tree (level 0 first); the left/right direction at
/// each level comes from the bits of `leaf_index`, so no direction flags are
/// needed. A padding input has `amount: 0` (membership is skipped in-circuit
/// for zero-value notes) with any well-formed path, e.g. all-zero siblings.
#[derive(Deserialize, Clone)]
pub struct TransactInputNote {
    pub amount: u64,
    pub privkey_hex: String,
    pub blinding_hex: String,
    pub leaf_index: u64,
    pub path_hex: Vec<String>,
}

/// An output note being created. A value-0 note is a valid "empty" output.
#[derive(Deserialize, Clone)]
pub struct TransactOutputNote {
    pub amount: u64,
    pub pubkey_hex: String,
    pub blinding_hex: String,
}

/// Build a v3 unified transact proof entirely in the browser.
///
/// Fixed 2-in/2-out against the program's **on-chain** incremental tree:
/// `root_hex` must be a root from the program's root history (the wallet reads
/// it from the tree account or an event), and `ext_amount` is the signed
/// external flow — `< 0` withdraws `|ext_amount|` lamports to `recipient`,
/// `== 0` is a pure shielded transfer (`> 0` is rejected: deposits go through
/// `deposit_note`, no proof needed). The circuit enforces
/// `sum(inputs) + ext_amount == sum(outputs)`; `ext_data_hash` is derived here
/// exactly as the program derives it (SHA-256 over `recipient ‖ ext_amount`),
/// so the proof binds the payout destination. Spend keys never leave the
/// browser.
///
/// Returns `{ nullifiers: [hex, hex], output_commitments: [hex, hex], proof }`
/// — with `root`/`ext_amount`/`recipient`, exactly the transact-ingress body.
#[wasm_bindgen]
pub fn prove_transact(
    proving_key: &[u8],
    root_hex: &str,
    ext_amount: i64,
    recipient_hex: &str,
    asset_id_hex: &str,
    inputs_json: &str,
    outputs_json: &str,
) -> Result<String, JsValue> {
    if ext_amount > 0 {
        return Err(JsValue::from_str(
            "positive ext_amount: deposits go through deposit_note, not transact",
        ));
    }
    let root = hex32(root_hex)?;
    let recipient = hex32(recipient_hex)?;

    let inputs: Vec<TransactInputNote> = serde_json::from_str(inputs_json)
        .map_err(|e| JsValue::from_str(&format!("bad inputs json: {e}")))?;
    let outputs: Vec<TransactOutputNote> = serde_json::from_str(outputs_json)
        .map_err(|e| JsValue::from_str(&format!("bad outputs json: {e}")))?;
    validate_transact_slots(&inputs, &outputs, ext_amount, "prove_transact")
        .map_err(|e| JsValue::from_str(&e))?;

    // The shielded asset: all-zero for native SOL, or `mint_to_asset(mint)` for
    // a shielded SPL note (#779). All notes in one transact share one asset.
    let asset = Fr::from_le_bytes_mod_order(&hex32(asset_id_hex)?);

    let mut in_amounts = Vec::new();
    let mut in_privkeys = Vec::new();
    let mut in_blindings = Vec::new();
    let mut in_leaf_indices = Vec::new();
    let mut in_paths = Vec::new();
    let mut nullifiers = Vec::new();
    let mut input_commitments = Vec::with_capacity(2);
    for inp in &inputs {
        let privkey = hex32(&inp.privkey_hex)?;
        let blinding = hex32(&inp.blinding_hex)?;
        if inp.path_hex.len() != TX_LEVELS {
            return Err(JsValue::from_str(&format!(
                "input path must have {TX_LEVELS} siblings, got {}",
                inp.path_hex.len()
            )));
        }
        let mut path = Vec::with_capacity(TX_LEVELS);
        for sib in &inp.path_hex {
            path.push(hex32(sib)?);
        }

        let sk = Fr::from_le_bytes_mod_order(&privkey);
        let c = v3_commit(
            Fr::from(inp.amount),
            v3_pubkey(sk),
            Fr::from_le_bytes_mod_order(&blinding),
            asset,
        );
        input_commitments.push(c);
        let sig = v3_signature(sk, c, Fr::from(inp.leaf_index));
        let nf = v3_nullifier(c, Fr::from(inp.leaf_index), sig);
        nullifiers.push(fr_to_le_bytes_32(nf));

        in_amounts.push(Some(inp.amount));
        in_privkeys.push(Some(privkey));
        in_blindings.push(Some(blinding));
        in_leaf_indices.push(Some(inp.leaf_index));
        in_paths.push(Some(path));
    }

    if inputs[0].amount > 0 && inputs[1].amount > 0 {
        if let (Some(p0), Some(p1)) = (&in_paths[0], &in_paths[1]) {
            validate_v3_two_input_merkle_lca(
                input_commitments[0],
                input_commitments[1],
                inputs[0].leaf_index,
                inputs[1].leaf_index,
                p0,
                p1,
                "prove_transact",
            )
            .map_err(|e| JsValue::from_str(&e))?;
        }
    }

    let mut out_amounts = Vec::new();
    let mut out_pubkeys = Vec::new();
    let mut out_blindings = Vec::new();
    let mut output_commitments = Vec::new();
    for outp in &outputs {
        let pubkey = hex32(&outp.pubkey_hex)?;
        let blinding = hex32(&outp.blinding_hex)?;
        let oc = v3_commit(
            Fr::from(outp.amount),
            Fr::from_le_bytes_mod_order(&pubkey),
            Fr::from_le_bytes_mod_order(&blinding),
            asset,
        );
        output_commitments.push(fr_to_le_bytes_32(oc));
        out_amounts.push(Some(outp.amount));
        out_pubkeys.push(Some(pubkey));
        out_blindings.push(Some(blinding));
    }

    // public_amount = the field encoding of the signed ext_amount (negative =
    // p − |ext_amount|), exactly as the program derives it on-chain.
    let magnitude = Fr::from(ext_amount.unsigned_abs());
    let public_amount = if ext_amount < 0 {
        -magnitude
    } else {
        magnitude
    };

    // ext_data_hash = sha256(recipient || ext_amount_le), identical to the
    // program's `transact_ext_data_hash`.
    let mut hasher = Sha256::new();
    hasher.update(recipient);
    hasher.update(ext_amount.to_le_bytes());
    let ext_data_hash: [u8; 32] = hasher.finalize().into();

    let circuit = TransactCircuitV3 {
        root: Some(root),
        public_amount: Some(fr_to_le_bytes_32(public_amount)),
        ext_data_hash: Some(ext_data_hash),
        asset_id: Some(fr_to_le_bytes_32(asset)),
        input_nullifiers: nullifiers.iter().map(|n| Some(*n)).collect(),
        output_commitments: output_commitments.iter().map(|c| Some(*c)).collect(),
        in_amounts,
        in_privkeys,
        in_blindings,
        in_leaf_indices,
        in_paths,
        out_amounts,
        out_pubkeys,
        out_blindings,
    };

    let pk = ProvingKey::<Bn254>::deserialize_compressed(proving_key)
        .map_err(|e| JsValue::from_str(&format!("bad proving key: {e}")))?;
    let proof =
        Groth16ProofSystem::prove::<TransactCircuitV3, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| JsValue::from_str(&format!("serialize failed: {e}")))?;

    // The L2 carries `tag(1) || body`. Nodes split the envelope and reject an
    // unknown suite rather than assuming the one they happen to embed, so an
    // untagged blob does not settle.
    let wire = privacy::proof_codec::tag_proof(
        privacy::proof_codec::ProofSuite::Groth16Bn254TransactV3,
        &proof_bytes,
    );

    Ok(format!(
        "{{\"nullifiers\":[\"{}\",\"{}\"],\"output_commitments\":[\"{}\",\"{}\"],\"proof\":\"{}\"}}",
        hex::encode(nullifiers[0]),
        hex::encode(nullifiers[1]),
        hex::encode(output_commitments[0]),
        hex::encode(output_commitments[1]),
        hex::encode(wire)
    ))
}

/// Rebuild the v3 on-chain tree from its ordered leaf list and return the
/// membership path for `leaf_index` plus the current root.
///
/// The wallet reconstructs the tree client-side from the program's public
/// `DepositNoteEvent`/`TransactEvent` logs instead of asking a validator for
/// its path — asking would leak which leaf is the wallet's. Hashing here (the
/// same circom Poseidon as the circuit and the on-chain syscall) keeps the
/// rebuild fast and bit-identical.
///
/// `leaves_json`: JSON array of 32-byte hex leaf commitments in append order.
/// Returns `{ "path": [hex; 32], "root": hex }`.
#[wasm_bindgen]
#[allow(clippy::needless_range_loop, clippy::manual_is_multiple_of)]
pub fn v3_merkle_path(leaves_json: &str, leaf_index: u32) -> Result<String, JsValue> {
    use privacy::poseidon_circom::v3_merkle_pair;

    let leaves_hex: Vec<String> = serde_json::from_str(leaves_json)
        .map_err(|e| JsValue::from_str(&format!("bad leaves json: {e}")))?;
    if (leaf_index as usize) >= leaves_hex.len() {
        return Err(JsValue::from_str("leaf_index out of range"));
    }
    let mut level: Vec<Fr> = Vec::with_capacity(leaves_hex.len());
    for l in &leaves_hex {
        level.push(Fr::from_le_bytes_mod_order(&hex32(l)?));
    }

    // Zero-subtree hashes, as the on-chain tree pads with.
    let mut zeros = vec![Fr::from(0u64)];
    for k in 0..TX_LEVELS {
        zeros.push(v3_merkle_pair(zeros[k], zeros[k]));
    }

    let mut path = Vec::with_capacity(TX_LEVELS);
    let mut idx = leaf_index as usize;
    for depth in 0..TX_LEVELS {
        let sibling = if idx % 2 == 0 {
            *level.get(idx + 1).unwrap_or(&zeros[depth])
        } else {
            level[idx - 1]
        };
        path.push(hex::encode(fr_to_le_bytes_32(sibling)));

        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        for pair in level.chunks(2) {
            let l = pair[0];
            let r = *pair.get(1).unwrap_or(&zeros[depth]);
            next.push(v3_merkle_pair(l, r));
        }
        level = next;
        idx /= 2;
    }

    let root = *level.first().unwrap_or(&zeros[TX_LEVELS]);
    Ok(format!(
        "{{\"path\":{},\"root\":\"{}\"}}",
        serde_json::to_string(&path).unwrap(),
        hex::encode(fr_to_le_bytes_32(root))
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slot_ordering_validation() {
        // Transfer slot ordering
        let valid_transfer_inputs = vec![
            TransferInputV2 {
                amount: 100,
                privkey_hex: "01".repeat(32),
                blinding_hex: "02".repeat(32),
                path_hex: vec!["00".repeat(32); 4],
                indices: vec![false; 4],
            },
            TransferInputV2 {
                amount: 200,
                privkey_hex: "03".repeat(32),
                blinding_hex: "04".repeat(32),
                path_hex: vec!["00".repeat(32); 4],
                indices: vec![true; 4],
            },
        ];
        let valid_transfer_outputs = vec![
            TransferOutputV2 {
                amount: 250,
                pubkey_hex: "05".repeat(32),
                blinding_hex: "06".repeat(32),
            },
            TransferOutputV2 {
                amount: 50,
                pubkey_hex: "07".repeat(32),
                blinding_hex: "08".repeat(32),
            },
        ];

        // Valid transfer slots pass
        assert!(validate_transfer_v2_slots(
            &valid_transfer_inputs,
            &valid_transfer_outputs,
            "test"
        )
        .is_ok());

        // Zero-amount input 0 rejected
        let mut zero_inp0 = valid_transfer_inputs.clone();
        zero_inp0[0].amount = 0;
        assert!(validate_transfer_v2_slots(&zero_inp0, &valid_transfer_outputs, "test").is_err());

        // Zero-amount input 1 rejected
        let mut zero_inp1 = valid_transfer_inputs.clone();
        zero_inp1[1].amount = 0;
        assert!(validate_transfer_v2_slots(&zero_inp1, &valid_transfer_outputs, "test").is_err());

        // Zero-amount output 0 rejected
        let mut zero_out0 = valid_transfer_outputs.clone();
        zero_out0[0].amount = 0;
        assert!(validate_transfer_v2_slots(&valid_transfer_inputs, &zero_out0, "test").is_err());

        // Transact slot ordering
        let valid_transact_inputs = vec![
            TransactInputNote {
                amount: 1000,
                privkey_hex: "01".repeat(32),
                blinding_hex: "02".repeat(32),
                leaf_index: 0,
                path_hex: vec!["00".repeat(32); 32],
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: "03".repeat(32),
                blinding_hex: "04".repeat(32),
                leaf_index: 0,
                path_hex: vec!["00".repeat(32); 32],
            },
        ];
        let valid_transact_outputs = vec![
            TransactOutputNote {
                amount: 400,
                pubkey_hex: "05".repeat(32),
                blinding_hex: "06".repeat(32),
            },
            TransactOutputNote {
                amount: 100,
                pubkey_hex: "07".repeat(32),
                blinding_hex: "08".repeat(32),
            },
        ];

        // Valid transact slots pass
        assert!(validate_transact_slots(
            &valid_transact_inputs,
            &valid_transact_outputs,
            -500,
            "test"
        )
        .is_ok());

        // Inverted dummy input [dummy, active] rejected
        let mut inverted_inputs = valid_transact_inputs.clone();
        inverted_inputs[0].amount = 0;
        inverted_inputs[1].amount = 1000;
        assert!(
            validate_transact_slots(&inverted_inputs, &valid_transact_outputs, -500, "test")
                .is_err()
        );

        // Inverted [zero, active] outputs in pure transfer (ext_amount == 0) rejected
        let mut inverted_outputs = valid_transact_outputs.clone();
        inverted_outputs[0].amount = 0;
        inverted_outputs[1].amount = 500;
        assert!(
            validate_transact_slots(&valid_transact_inputs, &inverted_outputs, 0, "test").is_err()
        );

        // Inverted [zero, active] outputs in withdrawal rejected when outputs[1].amount > 0
        assert!(
            validate_transact_slots(&valid_transact_inputs, &inverted_outputs, -500, "test")
                .is_err()
        );

        // Full withdrawal with 0 change ([0, 0] outputs) allowed
        let mut zero_change_outputs = valid_transact_outputs.clone();
        zero_change_outputs[0].amount = 0;
        zero_change_outputs[1].amount = 0;
        assert!(validate_transact_slots(
            &valid_transact_inputs,
            &zero_change_outputs,
            -1000,
            "test"
        )
        .is_ok());
    }

    #[test]
    fn test_v3_two_input_merkle_lca_validation() {
        // Construct a consistent 4-level v3 Merkle tree
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let c2 = Fr::from(300u64);
        let c3 = Fr::from(400u64);

        // Level 1:
        let n01 = v3_merkle_pair(c0, c1);
        let n23 = v3_merkle_pair(c2, c3);
        // Level 2:
        let n0123 = v3_merkle_pair(n01, n23);
        // Level 3 (root):
        let dummy_right = Fr::from(999u64);
        let _root = v3_merkle_pair(n0123, dummy_right);

        // Case A: Adjacent leaves i0 = 0, i1 = 1 (LCA depth = 0)
        let path0_a = [
            fr_to_le_bytes_32(c1),
            fr_to_le_bytes_32(n23),
            fr_to_le_bytes_32(dummy_right),
        ];
        let path1_a = [
            fr_to_le_bytes_32(c0),
            fr_to_le_bytes_32(n23),
            fr_to_le_bytes_32(dummy_right),
        ];
        assert!(validate_v3_two_input_merkle_lca(c0, c1, 0, 1, &path0_a, &path1_a, "test").is_ok());

        // Same leaf index rejected
        assert!(
            validate_v3_two_input_merkle_lca(c0, c1, 0, 0, &path0_a, &path1_a, "test").is_err()
        );

        // LCA sibling mismatch at d_lca = 0 rejected
        let mut bad_lca_path = path0_a;
        bad_lca_path[0] = fr_to_le_bytes_32(Fr::from(777u64));
        assert!(
            validate_v3_two_input_merkle_lca(c0, c1, 0, 1, &bad_lca_path, &path1_a, "test")
                .is_err()
        );

        // Above-LCA sibling mismatch at d = 1 rejected
        let mut bad_ancestor_path = path0_a;
        bad_ancestor_path[1] = fr_to_le_bytes_32(Fr::from(888u64));
        assert!(validate_v3_two_input_merkle_lca(
            c0,
            c1,
            0,
            1,
            &bad_ancestor_path,
            &path1_a,
            "test"
        )
        .is_err());

        // Case B: Leaves i0 = 0, i1 = 2 (LCA depth = 1)
        // For leaf 0: path sibling at d=0 is c1, at d=1 is n23
        // For leaf 2: path sibling at d=0 is c3, at d=1 is n01
        let path0_b = [
            fr_to_le_bytes_32(c1),
            fr_to_le_bytes_32(n23),
            fr_to_le_bytes_32(dummy_right),
        ];
        let path2_b = [
            fr_to_le_bytes_32(c3),
            fr_to_le_bytes_32(n01),
            fr_to_le_bytes_32(dummy_right),
        ];
        assert!(validate_v3_two_input_merkle_lca(c0, c2, 0, 2, &path0_b, &path2_b, "test").is_ok());

        // Tampered folded node at LCA depth 1 rejected
        let mut bad_lca1_path = path0_b;
        bad_lca1_path[1] = fr_to_le_bytes_32(Fr::from(555u64));
        assert!(
            validate_v3_two_input_merkle_lca(c0, c2, 0, 2, &bad_lca1_path, &path2_b, "test")
                .is_err()
        );
    }

    #[test]
    fn test_v2_two_input_merkle_lca_validation() {
        // Construct a consistent 4-level v2 Merkle tree
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let c2 = Fr::from(300u64);
        let c3 = Fr::from(400u64);

        let n01 = poseidon_merkle_pair(c0, c1);
        let n23 = poseidon_merkle_pair(c2, c3);
        let n0123 = poseidon_merkle_pair(n01, n23);
        let dummy_right = Fr::from(999u64);
        let _root = poseidon_merkle_pair(n0123, dummy_right);

        let path0 = [
            fr_to_le_bytes_32(c1),
            fr_to_le_bytes_32(n23),
            fr_to_le_bytes_32(dummy_right),
        ];
        let path1 = [
            fr_to_le_bytes_32(c0),
            fr_to_le_bytes_32(n23),
            fr_to_le_bytes_32(dummy_right),
        ];
        assert!(validate_v2_two_input_merkle_lca(c0, c1, 0, 1, &path0, &path1, "test").is_ok());

        // Same leaf index rejected
        assert!(validate_v2_two_input_merkle_lca(c0, c1, 0, 0, &path0, &path1, "test").is_err());

        // LCA mismatch rejected
        let mut bad_lca = path0;
        bad_lca[0] = fr_to_le_bytes_32(Fr::from(111u64));
        assert!(validate_v2_two_input_merkle_lca(c0, c1, 0, 1, &bad_lca, &path1, "test").is_err());

        // Above-LCA mismatch rejected
        let mut bad_ancestor = path0;
        bad_ancestor[1] = fr_to_le_bytes_32(Fr::from(222u64));
        assert!(
            validate_v2_two_input_merkle_lca(c0, c1, 0, 1, &bad_ancestor, &path1, "test").is_err()
        );
    }
}
