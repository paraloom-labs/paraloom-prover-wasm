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

use serde::{Deserialize, Serialize};

use privacy::circuits::{Groth16ProofSystem, TransferCircuitV2, WithdrawCircuitV2};
use privacy::poseidon::{
    poseidon_commit, poseidon_commit_spend, poseidon_merkle_pair, poseidon_nullifier_spend,
    poseidon_pubkey, poseidon_signature,
};
use sha2::{Digest, Sha256};

fn fr_to_le_bytes_32(fr: Fr) -> [u8; 32] {
    let mut v = fr.into_bigint().to_bytes_le();
    v.resize(32, 0);
    let mut o = [0u8; 32];
    o.copy_from_slice(&v[..32]);
    o
}

pub fn hex32_inner(s: &str) -> Result<[u8; 32], String> {
    let b = hex::decode(s.trim()).map_err(|e| format!("bad hex: {e}"))?;
    if b.len() != 32 {
        return Err("expected 32-byte hex".to_string());
    }
    let mut o = [0u8; 32];
    o.copy_from_slice(&b);
    Ok(o)
}

fn hex32(s: &str) -> Result<[u8; 32], JsValue> {
    hex32_inner(s).map_err(|e| JsValue::from_str(&e))
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

fn merkle_path_from_inner(
    path_hex: &[String],
    indices: &[bool],
) -> Result<Vec<([u8; 32], bool)>, String> {
    if path_hex.len() != indices.len() {
        return Err("path and indices length mismatch".to_string());
    }
    let mut path = Vec::with_capacity(path_hex.len());
    for (h, dir) in path_hex.iter().zip(indices) {
        path.push((hex32_inner(h)?, *dir));
    }
    Ok(path)
}

/// Build a `(sibling, is_left)` Merkle path from parallel hex/bool arrays.
#[allow(dead_code)]
fn merkle_path_from(
    path_hex: &[String],
    indices: &[bool],
) -> Result<Vec<([u8; 32], bool)>, JsValue> {
    merkle_path_from_inner(path_hex, indices).map_err(|e| JsValue::from_str(&e))
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

/// Validate cross-input Merkle LCA sibling reciprocity and above-LCA sibling identity
/// for two active inputs in circuit v2 (#47).
pub fn validate_v2_two_input_merkle_lca(
    c0: Fr,
    path_0: &[([u8; 32], bool)],
    c1: Fr,
    path_1: &[([u8; 32], bool)],
) -> Result<(), String> {
    if path_0.is_empty() || path_0.len() != path_1.len() {
        return Err("input paths must have equal non-zero depth".to_string());
    }
    let depth = path_0.len();

    let mut i0 = 0u64;
    for (level, (_, is_left)) in path_0.iter().enumerate() {
        if !is_left {
            i0 += 1u64 << level;
        }
    }

    let mut i1 = 0u64;
    for (level, (_, is_left)) in path_1.iter().enumerate() {
        if !is_left {
            i1 += 1u64 << level;
        }
    }

    if i0 == i1 {
        return Err("inputs must have distinct leaf indices".to_string());
    }

    let diff = i0 ^ i1;
    let d_lca = (63 - diff.leading_zeros()) as usize;
    if d_lca >= depth {
        return Err("leaf index difference exceeds tree depth".to_string());
    }

    let mut node_0 = c0;
    for (sib_bytes, is_left) in path_0.iter().take(d_lca) {
        let sib = Fr::from_le_bytes_mod_order(sib_bytes);
        node_0 = if *is_left {
            poseidon_merkle_pair(node_0, sib)
        } else {
            poseidon_merkle_pair(sib, node_0)
        };
    }

    let mut node_1 = c1;
    for (sib_bytes, is_left) in path_1.iter().take(d_lca) {
        let sib = Fr::from_le_bytes_mod_order(sib_bytes);
        node_1 = if *is_left {
            poseidon_merkle_pair(node_1, sib)
        } else {
            poseidon_merkle_pair(sib, node_1)
        };
    }

    let n0_bytes = fr_to_le_bytes_32(node_0);
    let n1_bytes = fr_to_le_bytes_32(node_1);

    if path_0[d_lca].0 != n1_bytes {
        return Err(format!(
            "cross-input Merkle LCA sibling mismatch at depth {d_lca}: path_0 expected node_1"
        ));
    }
    if path_1[d_lca].0 != n0_bytes {
        return Err(format!(
            "cross-input Merkle LCA sibling mismatch at depth {d_lca}: path_1 expected node_0"
        ));
    }

    for d in (d_lca + 1)..depth {
        if path_0[d].0 != path_1[d].0 {
            return Err(format!(
                "cross-input Merkle above-LCA sibling mismatch at depth {d}: path_0 != path_1"
            ));
        }
        if path_0[d].1 != path_1[d].1 {
            return Err(format!(
                "cross-input Merkle above-LCA direction mismatch at depth {d}: path_0 != path_1"
            ));
        }
    }

    Ok(())
}

/// An input note being spent in a transfer. `path_hex`/`indices` are the
/// root-less Merkle path proving the note's commitment is in the tree, pulled
/// from the path server.
#[derive(Serialize, Deserialize)]
struct TransferInputV2 {
    amount: u64,
    /// The note's spend key. Authority is knowledge of this, not of a free
    /// secret: it is folded into the nullifier through a signature over
    /// `(commitment, leaf_index)`.
    privkey_hex: String,
    blinding_hex: String,
    /// Root-less Merkle path, sibling per level.
    path_hex: Vec<String>,
    /// Direction bit per level; also gives the leaf index.
    indices: Vec<bool>,
}

/// An output note being created. A value-0 note is a valid "empty" output.
#[derive(Serialize, Deserialize)]
struct TransferOutputV2 {
    amount: u64,
    /// The recipient's spend *public* key, `Poseidon(privkey)`.
    pubkey_hex: String,
    blinding_hex: String,
}

pub fn prove_transfer_v2_inner(
    proving_key: &[u8],
    root_hex: &str,
    asset_id_hex: &str,
    inputs_json: &str,
    outputs_json: &str,
) -> Result<String, String> {
    let root = hex32_inner(root_hex)?;
    let asset_id = hex32_inner(asset_id_hex)?;
    let asset_fr = Fr::from_le_bytes_mod_order(&asset_id);

    let inputs: Vec<TransferInputV2> =
        serde_json::from_str(inputs_json).map_err(|e| format!("bad inputs json: {e}"))?;
    let outputs: Vec<TransferOutputV2> =
        serde_json::from_str(outputs_json).map_err(|e| format!("bad outputs json: {e}"))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err("transfer requires exactly 2 inputs and 2 outputs".to_string());
    }

    if inputs[0].amount == 0 || inputs[1].amount == 0 {
        return Err("transfer requires positive amounts on both inputs".to_string());
    }

    if outputs[0].amount == 0 {
        return Err("transfer requires positive amount on primary output (outputs[0])".to_string());
    }

    if inputs[0].path_hex.is_empty() || inputs[0].path_hex.len() != inputs[1].path_hex.len() {
        return Err("transfer input paths must be non-empty and of equal depth".to_string());
    }
    if inputs[0].indices.len() != inputs[0].path_hex.len()
        || inputs[1].indices.len() != inputs[1].path_hex.len()
    {
        return Err("path and indices length mismatch".to_string());
    }

    let mut nullifiers = Vec::with_capacity(2);
    let mut input_values = Vec::with_capacity(2);
    let mut input_blindings = Vec::with_capacity(2);
    let mut input_privkeys = Vec::with_capacity(2);
    let mut input_paths = Vec::with_capacity(2);
    let mut input_commitments = Vec::with_capacity(2);
    for inp in &inputs {
        let blinding = hex32_inner(&inp.blinding_hex)?;
        let privkey = hex32_inner(&inp.privkey_hex)?;
        let sk = Fr::from_le_bytes_mod_order(&privkey);
        let commitment_fr = poseidon_commit_spend(
            Fr::from(inp.amount),
            poseidon_pubkey(sk),
            Fr::from_le_bytes_mod_order(&blinding),
            asset_fr,
        );
        let leaf_index = leaf_index_from(&inp.indices);
        let signature = poseidon_signature(sk, commitment_fr, Fr::from(leaf_index));
        let nullifier_fr = poseidon_nullifier_spend(commitment_fr, Fr::from(leaf_index), signature);
        nullifiers.push(fr_to_le_bytes_32(nullifier_fr));
        input_values.push(inp.amount);
        input_blindings.push(blinding);
        input_privkeys.push(privkey);
        input_paths.push(merkle_path_from_inner(&inp.path_hex, &inp.indices)?);
        input_commitments.push(commitment_fr);
    }

    validate_v2_two_input_merkle_lca(
        input_commitments[0],
        &input_paths[0],
        input_commitments[1],
        &input_paths[1],
    )?;

    let mut output_commitments = Vec::with_capacity(2);
    let mut output_values = Vec::with_capacity(2);
    let mut output_blindings = Vec::with_capacity(2);
    let mut output_pubkeys = Vec::with_capacity(2);
    for out in &outputs {
        let blinding = hex32_inner(&out.blinding_hex)?;
        let pubkey = hex32_inner(&out.pubkey_hex)?;
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
        .map_err(|e| format!("bad proving key: {e}"))?;
    let proof =
        Groth16ProofSystem::prove::<TransferCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| format!("prove failed: {e}"))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| format!("serialize failed: {e}"))?;

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
    prove_transfer_v2_inner(
        proving_key,
        root_hex,
        asset_id_hex,
        inputs_json,
        outputs_json,
    )
    .map_err(|e| JsValue::from_str(&e))
}

// ===== circuit v3 (#350): unified transact =====

use privacy::circuits::{TransactCircuitV3, TX_LEVELS};
use privacy::poseidon_circom::{v3_commit, v3_merkle_pair, v3_nullifier, v3_pubkey, v3_signature};

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

/// Validate cross-input Merkle LCA sibling reciprocity and above-LCA sibling identity
/// for two active inputs in circuit v3 (#47).
pub fn validate_v3_two_input_merkle_lca(
    c0: Fr,
    leaf_index_0: u64,
    path_0: &[[u8; 32]],
    c1: Fr,
    leaf_index_1: u64,
    path_1: &[[u8; 32]],
) -> Result<(), String> {
    if leaf_index_0 == leaf_index_1 {
        return Err("inputs must have distinct leaf indices".to_string());
    }
    if path_0.len() != TX_LEVELS || path_1.len() != TX_LEVELS {
        return Err(format!("input paths must have {TX_LEVELS} siblings"));
    }

    let diff = leaf_index_0 ^ leaf_index_1;
    let d_lca = (63 - diff.leading_zeros()) as usize;
    if d_lca >= TX_LEVELS {
        return Err("leaf index difference exceeds tree depth".to_string());
    }

    let mut node_0 = c0;
    for (k, sib_bytes) in path_0.iter().take(d_lca).enumerate() {
        let sib = Fr::from_le_bytes_mod_order(sib_bytes);
        let bit = (leaf_index_0 >> k) & 1;
        node_0 = if bit == 0 {
            v3_merkle_pair(node_0, sib)
        } else {
            v3_merkle_pair(sib, node_0)
        };
    }

    let mut node_1 = c1;
    for (k, sib_bytes) in path_1.iter().take(d_lca).enumerate() {
        let sib = Fr::from_le_bytes_mod_order(sib_bytes);
        let bit = (leaf_index_1 >> k) & 1;
        node_1 = if bit == 0 {
            v3_merkle_pair(node_1, sib)
        } else {
            v3_merkle_pair(sib, node_1)
        };
    }

    let n0_bytes = fr_to_le_bytes_32(node_0);
    let n1_bytes = fr_to_le_bytes_32(node_1);

    if path_0[d_lca] != n1_bytes {
        return Err(format!(
            "cross-input Merkle LCA sibling mismatch at depth {d_lca}: path_0 expected node_1"
        ));
    }
    if path_1[d_lca] != n0_bytes {
        return Err(format!(
            "cross-input Merkle LCA sibling mismatch at depth {d_lca}: path_1 expected node_0"
        ));
    }

    for d in (d_lca + 1)..TX_LEVELS {
        if path_0[d] != path_1[d] {
            return Err(format!(
                "cross-input Merkle above-LCA sibling mismatch at depth {d}: path_0 != path_1"
            ));
        }
    }

    Ok(())
}

/// An input note being spent by `prove_transact`. `path_hex` is the 32-entry
/// sibling list from the tree (level 0 first); the left/right direction at
/// each level comes from the bits of `leaf_index`, so no direction flags are
/// needed. A padding input has `amount: 0` (membership is skipped in-circuit
/// for zero-value notes) with any well-formed path, e.g. all-zero siblings.
#[derive(Serialize, Deserialize)]
struct TransactInputNote {
    amount: u64,
    privkey_hex: String,
    blinding_hex: String,
    leaf_index: u64,
    path_hex: Vec<String>,
}

/// An output note being created. A value-0 note is a valid "empty" output.
#[derive(Serialize, Deserialize)]
struct TransactOutputNote {
    amount: u64,
    pubkey_hex: String,
    blinding_hex: String,
}

pub fn prove_transact_inner(
    proving_key: &[u8],
    root_hex: &str,
    ext_amount: i64,
    recipient_hex: &str,
    asset_id_hex: &str,
    inputs_json: &str,
    outputs_json: &str,
) -> Result<String, String> {
    if ext_amount > 0 {
        return Err(
            "positive ext_amount: deposits go through deposit_note, not transact".to_string(),
        );
    }
    let root = hex32_inner(root_hex)?;
    let recipient = hex32_inner(recipient_hex)?;

    let inputs: Vec<TransactInputNote> =
        serde_json::from_str(inputs_json).map_err(|e| format!("bad inputs json: {e}"))?;
    let outputs: Vec<TransactOutputNote> =
        serde_json::from_str(outputs_json).map_err(|e| format!("bad outputs json: {e}"))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err("transact is fixed 2-in/2-out".to_string());
    }

    if inputs[0].amount == 0 {
        return Err("transact requires positive amount on primary input (inputs[0])".to_string());
    }

    if (ext_amount == 0 || outputs[1].amount > 0) && outputs[0].amount == 0 {
        return Err("transact requires positive amount on primary output (outputs[0])".to_string());
    }

    // The shielded asset: all-zero for native SOL, or `mint_to_asset(mint)` for
    // a shielded SPL note (#779). All notes in one transact share one asset.
    let asset = Fr::from_le_bytes_mod_order(&hex32_inner(asset_id_hex)?);

    let mut in_amounts = Vec::new();
    let mut in_privkeys = Vec::new();
    let mut in_blindings = Vec::new();
    let mut in_leaf_indices = Vec::new();
    let mut in_paths = Vec::new();
    let mut parsed_paths = Vec::new();
    let mut in_commitments = Vec::new();
    let mut nullifiers = Vec::new();
    for inp in &inputs {
        let privkey = hex32_inner(&inp.privkey_hex)?;
        let blinding = hex32_inner(&inp.blinding_hex)?;
        if inp.path_hex.len() != TX_LEVELS {
            return Err(format!(
                "input path must have {TX_LEVELS} siblings, got {}",
                inp.path_hex.len()
            ));
        }
        let mut path = Vec::with_capacity(TX_LEVELS);
        for sib in &inp.path_hex {
            path.push(hex32_inner(sib)?);
        }

        let sk = Fr::from_le_bytes_mod_order(&privkey);
        let c = v3_commit(
            Fr::from(inp.amount),
            v3_pubkey(sk),
            Fr::from_le_bytes_mod_order(&blinding),
            asset,
        );
        let sig = v3_signature(sk, c, Fr::from(inp.leaf_index));
        let nf = v3_nullifier(c, Fr::from(inp.leaf_index), sig);
        nullifiers.push(fr_to_le_bytes_32(nf));

        in_amounts.push(Some(inp.amount));
        in_privkeys.push(Some(privkey));
        in_blindings.push(Some(blinding));
        in_leaf_indices.push(Some(inp.leaf_index));
        in_paths.push(Some(path.clone()));
        parsed_paths.push(path);
        in_commitments.push(c);
    }

    if inputs[0].amount > 0 && inputs[1].amount > 0 {
        validate_v3_two_input_merkle_lca(
            in_commitments[0],
            inputs[0].leaf_index,
            &parsed_paths[0],
            in_commitments[1],
            inputs[1].leaf_index,
            &parsed_paths[1],
        )?;
    }

    let mut out_amounts = Vec::new();
    let mut out_pubkeys = Vec::new();
    let mut out_blindings = Vec::new();
    let mut output_commitments = Vec::new();
    for outp in &outputs {
        let pubkey = hex32_inner(&outp.pubkey_hex)?;
        let blinding = hex32_inner(&outp.blinding_hex)?;
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
        .map_err(|e| format!("bad proving key: {e}"))?;
    let proof =
        Groth16ProofSystem::prove::<TransactCircuitV3, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| format!("prove failed: {e}"))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| format!("serialize failed: {e}"))?;

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
    prove_transact_inner(
        proving_key,
        root_hex,
        ext_amount,
        recipient_hex,
        asset_id_hex,
        inputs_json,
        outputs_json,
    )
    .map_err(|e| JsValue::from_str(&e))
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
    use privacy::poseidon_circom::v3_merkle_pair;

    #[test]
    fn test_validate_v2_two_input_merkle_lca_valid_adjacent() {
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let s1 = Fr::from(11u64);
        let s2 = Fr::from(22u64);
        let s3 = Fr::from(33u64);

        // i0 = 0 (all left), i1 = 1 (bit 0 is right, others left)
        // d_lca = 0
        let path_0 = vec![
            (fr_to_le_bytes_32(c1), true),
            (fr_to_le_bytes_32(s1), true),
            (fr_to_le_bytes_32(s2), true),
            (fr_to_le_bytes_32(s3), true),
        ];
        let path_1 = vec![
            (fr_to_le_bytes_32(c0), false),
            (fr_to_le_bytes_32(s1), true),
            (fr_to_le_bytes_32(s2), true),
            (fr_to_le_bytes_32(s3), true),
        ];

        let res = validate_v2_two_input_merkle_lca(c0, &path_0, c1, &path_1);
        assert!(res.is_ok(), "expected Ok, got {res:?}");
    }

    #[test]
    fn test_validate_v2_two_input_merkle_lca_valid_deeper() {
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let s0_0 = Fr::from(101u64);
        let s1_0 = Fr::from(201u64);
        let s2 = Fr::from(22u64);
        let s3 = Fr::from(33u64);

        // i0 = 0 (0b00: left, left)
        // i1 = 2 (0b10: left, right)
        // d_lca = 1
        let node_0_1 = poseidon_merkle_pair(c0, s0_0);
        let node_1_1 = poseidon_merkle_pair(c1, s1_0);

        let path_0 = vec![
            (fr_to_le_bytes_32(s0_0), true),
            (fr_to_le_bytes_32(node_1_1), true),
            (fr_to_le_bytes_32(s2), true),
            (fr_to_le_bytes_32(s3), true),
        ];
        let path_1 = vec![
            (fr_to_le_bytes_32(s1_0), true),
            (fr_to_le_bytes_32(node_0_1), false),
            (fr_to_le_bytes_32(s2), true),
            (fr_to_le_bytes_32(s3), true),
        ];

        let res = validate_v2_two_input_merkle_lca(c0, &path_0, c1, &path_1);
        assert!(res.is_ok(), "expected Ok, got {res:?}");
    }

    #[test]
    fn test_validate_v2_two_input_merkle_lca_failures() {
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let s1 = Fr::from(11u64);

        // Same leaf index
        let path_same = vec![(fr_to_le_bytes_32(s1), true)];
        let res = validate_v2_two_input_merkle_lca(c0, &path_same, c1, &path_same);
        assert!(
            res.unwrap_err().contains("distinct leaf indices"),
            "should reject identical leaf indices"
        );

        // Empty paths
        let empty_path: Vec<([u8; 32], bool)> = vec![];
        let res = validate_v2_two_input_merkle_lca(c0, &empty_path, c1, &empty_path);
        assert!(
            res.unwrap_err().contains("equal non-zero depth"),
            "should reject empty paths"
        );

        // Mismatched depth
        let path_short = vec![(fr_to_le_bytes_32(s1), true)];
        let path_long = vec![(fr_to_le_bytes_32(s1), true), (fr_to_le_bytes_32(s1), true)];
        let res = validate_v2_two_input_merkle_lca(c0, &path_short, c1, &path_long);
        assert!(
            res.unwrap_err().contains("equal non-zero depth"),
            "should reject mismatched depths"
        );

        // LCA sibling mismatch
        let path_0 = vec![(fr_to_le_bytes_32(c1), true), (fr_to_le_bytes_32(s1), true)];
        let bad_path_1 = vec![
            (fr_to_le_bytes_32(Fr::from(999u64)), false), // bad sibling
            (fr_to_le_bytes_32(s1), true),
        ];
        let res = validate_v2_two_input_merkle_lca(c0, &path_0, c1, &bad_path_1);
        assert!(
            res.unwrap_err().contains("LCA sibling mismatch"),
            "should reject wrong LCA sibling"
        );

        // Divergence above LCA
        let path_0 = vec![(fr_to_le_bytes_32(c1), true), (fr_to_le_bytes_32(s1), true)];
        let bad_path_above = vec![
            (fr_to_le_bytes_32(c0), false),
            (fr_to_le_bytes_32(Fr::from(999u64)), true), // bad sibling above LCA
        ];
        let res = validate_v2_two_input_merkle_lca(c0, &path_0, c1, &bad_path_above);
        assert!(
            res.unwrap_err().contains("above-LCA sibling mismatch"),
            "should reject differing sibling above LCA"
        );
    }

    #[test]
    fn test_validate_v3_two_input_merkle_lca_valid_adjacent() {
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let mut path_0 = Vec::with_capacity(TX_LEVELS);
        let mut path_1 = Vec::with_capacity(TX_LEVELS);

        // d_lca = 0: i0 = 0, i1 = 1
        path_0.push(fr_to_le_bytes_32(c1));
        path_1.push(fr_to_le_bytes_32(c0));

        for d in 1..TX_LEVELS {
            let sib = fr_to_le_bytes_32(Fr::from(d as u64 + 10));
            path_0.push(sib);
            path_1.push(sib);
        }

        let res = validate_v3_two_input_merkle_lca(c0, 0, &path_0, c1, 1, &path_1);
        assert!(res.is_ok(), "expected Ok, got {res:?}");
    }

    #[test]
    fn test_validate_v3_two_input_merkle_lca_valid_deeper() {
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let s0_0 = Fr::from(101u64);
        let s1_0 = Fr::from(201u64);

        // i0 = 0, i1 = 2 -> d_lca = 1
        let node_0_1 = v3_merkle_pair(c0, s0_0);
        let node_1_1 = v3_merkle_pair(c1, s1_0);

        let mut path_0 = Vec::with_capacity(TX_LEVELS);
        let mut path_1 = Vec::with_capacity(TX_LEVELS);

        path_0.push(fr_to_le_bytes_32(s0_0));
        path_1.push(fr_to_le_bytes_32(s1_0));

        path_0.push(fr_to_le_bytes_32(node_1_1));
        path_1.push(fr_to_le_bytes_32(node_0_1));

        for d in 2..TX_LEVELS {
            let sib = fr_to_le_bytes_32(Fr::from(d as u64 + 10));
            path_0.push(sib);
            path_1.push(sib);
        }

        let res = validate_v3_two_input_merkle_lca(c0, 0, &path_0, c1, 2, &path_1);
        assert!(res.is_ok(), "expected Ok, got {res:?}");
    }

    #[test]
    fn test_validate_v3_two_input_merkle_lca_failures() {
        let c0 = Fr::from(100u64);
        let c1 = Fr::from(200u64);
        let dummy_path = vec![[0u8; 32]; TX_LEVELS];

        // Same index
        let res = validate_v3_two_input_merkle_lca(c0, 5, &dummy_path, c1, 5, &dummy_path);
        assert!(
            res.unwrap_err().contains("distinct leaf indices"),
            "should reject same leaf index"
        );

        // Wrong depth
        let short_path = vec![[0u8; 32]; 10];
        let res = validate_v3_two_input_merkle_lca(c0, 0, &short_path, c1, 1, &dummy_path);
        assert!(
            res.unwrap_err().contains("siblings"),
            "should reject path length != 32"
        );

        // Bad LCA sibling
        let mut path_0 = vec![[0u8; 32]; TX_LEVELS];
        let mut path_1 = vec![[0u8; 32]; TX_LEVELS];
        path_0[0] = fr_to_le_bytes_32(c1);
        path_1[0] = [99u8; 32]; // bad
        let res = validate_v3_two_input_merkle_lca(c0, 0, &path_0, c1, 1, &path_1);
        assert!(
            res.unwrap_err().contains("LCA sibling mismatch"),
            "should reject bad LCA sibling"
        );

        // Divergence above LCA
        path_1[0] = fr_to_le_bytes_32(c0);
        path_0[1] = [1u8; 32];
        path_1[1] = [2u8; 32]; // mismatch
        let res = validate_v3_two_input_merkle_lca(c0, 0, &path_0, c1, 1, &path_1);
        assert!(
            res.unwrap_err().contains("above-LCA sibling mismatch"),
            "should reject divergence above LCA"
        );
    }

    #[test]
    fn test_prove_transfer_v2_slot_ordering_and_input_validation() {
        let dummy_pk = vec![0u8; 32];
        let root = hex::encode([1u8; 32]);
        let asset = hex::encode([0u8; 32]);

        let valid_path = vec![hex::encode([2u8; 32])];
        let valid_indices = vec![true];

        // Test inputs[0].amount == 0 is rejected
        let inputs_zero_0 = serde_json::to_string(&vec![
            TransferInputV2 {
                amount: 0,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                path_hex: valid_path.clone(),
                indices: valid_indices.clone(),
            },
            TransferInputV2 {
                amount: 100,
                privkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
                path_hex: valid_path.clone(),
                indices: valid_indices.clone(),
            },
        ])
        .unwrap();

        let outputs_valid = serde_json::to_string(&vec![
            TransferOutputV2 {
                amount: 100,
                pubkey_hex: hex::encode([7u8; 32]),
                blinding_hex: hex::encode([8u8; 32]),
            },
            TransferOutputV2 {
                amount: 0,
                pubkey_hex: hex::encode([9u8; 32]),
                blinding_hex: hex::encode([10u8; 32]),
            },
        ])
        .unwrap();

        let res = prove_transfer_v2_inner(&dummy_pk, &root, &asset, &inputs_zero_0, &outputs_valid);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("positive amounts on both inputs"));

        // Test inputs[1].amount == 0 is rejected
        let inputs_zero_1 = serde_json::to_string(&vec![
            TransferInputV2 {
                amount: 100,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                path_hex: valid_path.clone(),
                indices: valid_indices.clone(),
            },
            TransferInputV2 {
                amount: 0,
                privkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
                path_hex: valid_path.clone(),
                indices: valid_indices.clone(),
            },
        ])
        .unwrap();

        let res = prove_transfer_v2_inner(&dummy_pk, &root, &asset, &inputs_zero_1, &outputs_valid);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("positive amounts on both inputs"));

        // Test outputs[0].amount == 0 is rejected
        let inputs_valid = serde_json::to_string(&vec![
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                path_hex: valid_path.clone(),
                indices: valid_indices.clone(),
            },
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
                path_hex: valid_path.clone(),
                indices: valid_indices.clone(),
            },
        ])
        .unwrap();

        let outputs_zero_0 = serde_json::to_string(&vec![
            TransferOutputV2 {
                amount: 0,
                pubkey_hex: hex::encode([7u8; 32]),
                blinding_hex: hex::encode([8u8; 32]),
            },
            TransferOutputV2 {
                amount: 100,
                pubkey_hex: hex::encode([9u8; 32]),
                blinding_hex: hex::encode([10u8; 32]),
            },
        ])
        .unwrap();

        let res = prove_transfer_v2_inner(&dummy_pk, &root, &asset, &inputs_valid, &outputs_zero_0);
        assert!(res.is_err());
        assert!(res
            .unwrap_err()
            .contains("positive amount on primary output (outputs[0])"));

        // Test empty path rejection
        let inputs_empty_path = serde_json::to_string(&vec![
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                path_hex: vec![],
                indices: vec![],
            },
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
                path_hex: vec![],
                indices: vec![],
            },
        ])
        .unwrap();
        let res =
            prove_transfer_v2_inner(&dummy_pk, &root, &asset, &inputs_empty_path, &outputs_valid);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("non-empty and of equal depth"));
    }

    #[test]
    fn test_prove_transact_slot_ordering_validation() {
        let dummy_pk = vec![0u8; 32];
        let root = hex::encode([1u8; 32]);
        let recipient = hex::encode([2u8; 32]);
        let asset = hex::encode([0u8; 32]);
        let path = vec![hex::encode([3u8; 32]); TX_LEVELS];

        // 1. Inverted inputs: inputs[0].amount == 0 && inputs[1].amount > 0
        let inputs_inverted = serde_json::to_string(&vec![
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([4u8; 32]),
                blinding_hex: hex::encode([5u8; 32]),
                leaf_index: 0,
                path_hex: path.clone(),
            },
            TransactInputNote {
                amount: 500,
                privkey_hex: hex::encode([6u8; 32]),
                blinding_hex: hex::encode([7u8; 32]),
                leaf_index: 1,
                path_hex: path.clone(),
            },
        ])
        .unwrap();

        let outputs_valid = serde_json::to_string(&vec![
            TransactOutputNote {
                amount: 500,
                pubkey_hex: hex::encode([8u8; 32]),
                blinding_hex: hex::encode([9u8; 32]),
            },
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
            },
        ])
        .unwrap();

        let res = prove_transact_inner(
            &dummy_pk,
            &root,
            0,
            &recipient,
            &asset,
            &inputs_inverted,
            &outputs_valid,
        );
        assert!(res.is_err());
        assert!(res
            .unwrap_err()
            .contains("positive amount on primary input (inputs[0])"));

        // 2. Shielded transfer (ext_amount == 0) with outputs[0].amount == 0
        let inputs_valid_1note = serde_json::to_string(&vec![
            TransactInputNote {
                amount: 500,
                privkey_hex: hex::encode([4u8; 32]),
                blinding_hex: hex::encode([5u8; 32]),
                leaf_index: 0,
                path_hex: path.clone(),
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([6u8; 32]),
                blinding_hex: hex::encode([7u8; 32]),
                leaf_index: 0,
                path_hex: path.clone(),
            },
        ])
        .unwrap();

        let outputs_zero_0 = serde_json::to_string(&vec![
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([8u8; 32]),
                blinding_hex: hex::encode([9u8; 32]),
            },
            TransactOutputNote {
                amount: 500,
                pubkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
            },
        ])
        .unwrap();

        let res = prove_transact_inner(
            &dummy_pk,
            &root,
            0,
            &recipient,
            &asset,
            &inputs_valid_1note,
            &outputs_zero_0,
        );
        assert!(res.is_err());
        assert!(res
            .unwrap_err()
            .contains("positive amount on primary output (outputs[0])"));

        // 3. Withdrawal with change in outputs[1] but outputs[0] is 0
        let res = prove_transact_inner(
            &dummy_pk,
            &root,
            -300,
            &recipient,
            &asset,
            &inputs_valid_1note,
            &outputs_zero_0,
        );
        assert!(res.is_err());
        assert!(res
            .unwrap_err()
            .contains("positive amount on primary output (outputs[0])"));
    }
}
