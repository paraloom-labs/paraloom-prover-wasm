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
    poseidon_commit, poseidon_commit_spend, poseidon_nullifier_spend, poseidon_pubkey,
    poseidon_signature,
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

pub fn note_commitment_inner(
    amount: u64,
    randomness_hex: &str,
    recipient_hex: &str,
) -> Result<String, String> {
    if amount == 0 {
        return Err("amount must be greater than zero".to_string());
    }
    let randomness = hex32_inner(randomness_hex)?;
    if randomness == [0u8; 32] {
        return Err("randomness must not be all-zero".to_string());
    }
    let recipient = hex32_inner(recipient_hex)?;
    if recipient == [0u8; 32] {
        return Err("recipient must not be all-zero".to_string());
    }
    let c = poseidon_commit(
        Fr::from(amount),
        Fr::from_le_bytes_mod_order(&randomness),
        Fr::from_le_bytes_mod_order(&recipient),
        Fr::from(0u64), // native-SOL asset id (#235)
    );
    Ok(hex::encode(fr_to_le_bytes_32(c)))
}

/// Poseidon commitment for a note `(amount, randomness, recipient)`, hex. The
/// wallet needs this to look up the note's Merkle path from the path server.
#[wasm_bindgen]
pub fn note_commitment(
    amount: u64,
    randomness_hex: &str,
    recipient_hex: &str,
) -> Result<String, JsValue> {
    note_commitment_inner(amount, randomness_hex, recipient_hex).map_err(|e| JsValue::from_str(&e))
}

pub fn spend_pubkey_inner(privkey_hex: &str) -> Result<String, String> {
    let sk = Fr::from_le_bytes_mod_order(&hex32_inner(privkey_hex)?);
    Ok(hex::encode(fr_to_le_bytes_32(poseidon_pubkey(sk))))
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
    spend_pubkey_inner(privkey_hex).map_err(|e| JsValue::from_str(&e))
}

pub fn note_commitment_v2_inner(
    amount: u64,
    privkey_hex: &str,
    blinding_hex: &str,
    asset_id_hex: &str,
) -> Result<String, String> {
    if amount == 0 {
        return Err("amount must be greater than zero".to_string());
    }
    let privkey = hex32_inner(privkey_hex)?;
    if privkey == [0u8; 32] {
        return Err("privkey must not be all-zero".to_string());
    }
    let blinding = hex32_inner(blinding_hex)?;
    if blinding == [0u8; 32] {
        return Err("blinding must not be all-zero".to_string());
    }
    let asset_id = hex32_inner(asset_id_hex)?;
    let sk = Fr::from_le_bytes_mod_order(&privkey);
    let c = poseidon_commit_spend(
        Fr::from(amount),
        poseidon_pubkey(sk),
        Fr::from_le_bytes_mod_order(&blinding),
        Fr::from_le_bytes_mod_order(&asset_id),
    );
    Ok(hex::encode(fr_to_le_bytes_32(c)))
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
    note_commitment_v2_inner(amount, privkey_hex, blinding_hex, asset_id_hex)
        .map_err(|e| JsValue::from_str(&e))
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
#[allow(clippy::too_many_arguments)]
pub fn prove_withdrawal_v2_inner(
    proving_key: &[u8],
    root_hex: &str,
    amount: u64,
    blinding_hex: &str,
    privkey_hex: &str,
    asset_id_hex: &str,
    dest_recipient_hex: &str,
    path_hex_json: &str,
    indices_json: &str,
) -> Result<String, String> {
    if amount == 0 {
        return Err("amount must be greater than zero".to_string());
    }
    let root = hex32_inner(root_hex)?;
    let blinding = hex32_inner(blinding_hex)?;
    if blinding == [0u8; 32] {
        return Err("blinding must not be all-zero".to_string());
    }
    let privkey = hex32_inner(privkey_hex)?;
    if privkey == [0u8; 32] {
        return Err("privkey must not be all-zero".to_string());
    }
    let asset_id = hex32_inner(asset_id_hex)?;
    let dest_recipient = hex32_inner(dest_recipient_hex)?;
    if dest_recipient == [0u8; 32] {
        return Err("dest_recipient must not be all-zero".to_string());
    }

    let path_hex: Vec<String> =
        serde_json::from_str(path_hex_json).map_err(|e| format!("bad path json: {e}"))?;
    let indices: Vec<bool> =
        serde_json::from_str(indices_json).map_err(|e| format!("bad indices json: {e}"))?;
    if path_hex.len() != indices.len() {
        return Err("path and indices length mismatch".to_string());
    }
    if path_hex.is_empty() || path_hex.len() > 63 {
        return Err("path depth must be between 1 and 63".to_string());
    }
    let merkle_path = merkle_path_from_inner(&path_hex, &indices)?;

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
        .map_err(|e| format!("bad proving key: {e}"))?;
    let proof =
        Groth16ProofSystem::prove::<WithdrawCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| format!("prove failed: {e}"))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| format!("serialize failed: {e}"))?;

    Ok(format!(
        "{{\"nullifier\":\"{}\",\"proof\":\"{}\"}}",
        hex::encode(nullifier),
        hex::encode(proof_bytes)
    ))
}

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
    prove_withdrawal_v2_inner(
        proving_key,
        root_hex,
        amount,
        blinding_hex,
        privkey_hex,
        asset_id_hex,
        dest_recipient_hex,
        path_hex_json,
        indices_json,
    )
    .map_err(|e| JsValue::from_str(&e))
}

/// An input note being spent in a transfer. `path_hex`/`indices` are the
/// root-less Merkle path proving the note's commitment is in the tree, pulled
/// from the path server.
#[derive(Deserialize)]
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
#[derive(Deserialize)]
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

    if inputs[0].path_hex.len() != inputs[1].path_hex.len() {
        return Err("input path depths must match".to_string());
    }

    for inp in &inputs {
        if inp.path_hex.len() != inp.indices.len() {
            return Err("path and indices length mismatch".to_string());
        }
        if inp.path_hex.is_empty() || inp.path_hex.len() > 63 {
            return Err("path depth must be between 1 and 63".to_string());
        }
    }

    let mut nullifiers = Vec::with_capacity(2);
    let mut input_values = Vec::with_capacity(2);
    let mut input_blindings = Vec::with_capacity(2);
    let mut input_privkeys = Vec::with_capacity(2);
    let mut input_paths = Vec::with_capacity(2);
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
    }

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

/// An input note being spent by `prove_transact`. `path_hex` is the 32-entry
/// sibling list from the tree (level 0 first); the left/right direction at
/// each level comes from the bits of `leaf_index`, so no direction flags are
/// needed. A padding input has `amount: 0` (membership is skipped in-circuit
/// for zero-value notes) with any well-formed path, e.g. all-zero siblings.
#[derive(Deserialize)]
struct TransactInputNote {
    amount: u64,
    privkey_hex: String,
    blinding_hex: String,
    leaf_index: u64,
    path_hex: Vec<String>,
}

/// An output note being created. A value-0 note is a valid "empty" output.
#[derive(Deserialize)]
struct TransactOutputNote {
    amount: u64,
    pubkey_hex: String,
    blinding_hex: String,
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
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(JsValue::from_str("transact is fixed 2-in/2-out"));
    }

    // The shielded asset: all-zero for native SOL, or `mint_to_asset(mint)` for
    // a shielded SPL note (#779). All notes in one transact share one asset.
    let asset = Fr::from_le_bytes_mod_order(&hex32(asset_id_hex)?);

    let mut in_amounts = Vec::new();
    let mut in_privkeys = Vec::new();
    let mut in_blindings = Vec::new();
    let mut in_leaf_indices = Vec::new();
    let mut in_paths = Vec::new();
    let mut nullifiers = Vec::new();
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
        let sig = v3_signature(sk, c, Fr::from(inp.leaf_index));
        let nf = v3_nullifier(c, Fr::from(inp.leaf_index), sig);
        nullifiers.push(fr_to_le_bytes_32(nf));

        in_amounts.push(Some(inp.amount));
        in_privkeys.push(Some(privkey));
        in_blindings.push(Some(blinding));
        in_leaf_indices.push(Some(inp.leaf_index));
        in_paths.push(Some(path));
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

    fn hx(b: &[u8; 32]) -> String {
        hex::encode(b)
    }

    #[test]
    fn test_note_commitment_rejects_zero_amount_and_all_zero_keys() {
        let valid_randomness = hx(&[1u8; 32]);
        let valid_recipient = hx(&[2u8; 32]);
        let zero_32 = hx(&[0u8; 32]);

        // amount == 0
        let err = note_commitment_inner(0, &valid_randomness, &valid_recipient).unwrap_err();
        assert!(err.contains("amount must be greater than zero"));

        // randomness == 0
        let err = note_commitment_inner(100, &zero_32, &valid_recipient).unwrap_err();
        assert!(err.contains("randomness must not be all-zero"));

        // recipient == 0
        let err = note_commitment_inner(100, &valid_randomness, &zero_32).unwrap_err();
        assert!(err.contains("recipient must not be all-zero"));

        // valid note commitment succeeds
        assert!(note_commitment_inner(100, &valid_randomness, &valid_recipient).is_ok());
    }

    #[test]
    fn test_note_commitment_v2_rejects_zero_amount_and_all_zero_keys() {
        let valid_privkey = hx(&[1u8; 32]);
        let valid_blinding = hx(&[2u8; 32]);
        let asset = hx(&[0u8; 32]);
        let zero_32 = hx(&[0u8; 32]);

        // amount == 0
        let err = note_commitment_v2_inner(0, &valid_privkey, &valid_blinding, &asset).unwrap_err();
        assert!(err.contains("amount must be greater than zero"));

        // privkey == 0
        let err = note_commitment_v2_inner(100, &zero_32, &valid_blinding, &asset).unwrap_err();
        assert!(err.contains("privkey must not be all-zero"));

        // blinding == 0
        let err = note_commitment_v2_inner(100, &valid_privkey, &zero_32, &asset).unwrap_err();
        assert!(err.contains("blinding must not be all-zero"));

        // valid note commitment v2 succeeds
        assert!(note_commitment_v2_inner(100, &valid_privkey, &valid_blinding, &asset).is_ok());
    }

    #[test]
    fn test_prove_withdrawal_v2_rejects_zero_amount_zero_keys_and_invalid_path() {
        let dummy_pk = vec![0u8; 32];
        let root = hx(&[1u8; 32]);
        let valid_privkey = hx(&[2u8; 32]);
        let valid_blinding = hx(&[3u8; 32]);
        let valid_recipient = hx(&[4u8; 32]);
        let asset = hx(&[0u8; 32]);
        let zero_32 = hx(&[0u8; 32]);

        let path_1 = serde_json::to_string(&vec![hx(&[5u8; 32])]).unwrap();
        let indices_1 = serde_json::to_string(&vec![false]).unwrap();

        // amount == 0
        let err = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            0,
            &valid_blinding,
            &valid_privkey,
            &asset,
            &valid_recipient,
            &path_1,
            &indices_1,
        )
        .unwrap_err();
        assert!(err.contains("amount must be greater than zero"));

        // blinding == 0
        let err = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            100,
            &zero_32,
            &valid_privkey,
            &asset,
            &valid_recipient,
            &path_1,
            &indices_1,
        )
        .unwrap_err();
        assert!(err.contains("blinding must not be all-zero"));

        // privkey == 0
        let err = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            100,
            &valid_blinding,
            &zero_32,
            &asset,
            &valid_recipient,
            &path_1,
            &indices_1,
        )
        .unwrap_err();
        assert!(err.contains("privkey must not be all-zero"));

        // dest_recipient == 0
        let err = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            100,
            &valid_blinding,
            &valid_privkey,
            &asset,
            &zero_32,
            &path_1,
            &indices_1,
        )
        .unwrap_err();
        assert!(err.contains("dest_recipient must not be all-zero"));

        // empty path (depth 0)
        let empty_path = serde_json::to_string(&Vec::<String>::new()).unwrap();
        let empty_indices = serde_json::to_string(&Vec::<bool>::new()).unwrap();
        let err = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            100,
            &valid_blinding,
            &valid_privkey,
            &asset,
            &valid_recipient,
            &empty_path,
            &empty_indices,
        )
        .unwrap_err();
        assert!(err.contains("path depth must be between 1 and 63"));

        // depth > 63
        let path_64 = serde_json::to_string(&vec![hx(&[5u8; 32]); 64]).unwrap();
        let indices_64 = serde_json::to_string(&vec![false; 64]).unwrap();
        let err = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            100,
            &valid_blinding,
            &valid_privkey,
            &asset,
            &valid_recipient,
            &path_64,
            &indices_64,
        )
        .unwrap_err();
        assert!(err.contains("path depth must be between 1 and 63"));

        // length mismatch
        let err = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            100,
            &valid_blinding,
            &valid_privkey,
            &asset,
            &valid_recipient,
            &path_1,
            &empty_indices,
        )
        .unwrap_err();
        assert!(err.contains("path and indices length mismatch"));
    }

    #[test]
    fn test_prove_transfer_v2_rejects_mismatched_and_invalid_path_depths() {
        let dummy_pk = vec![0u8; 32];
        let root = hx(&[1u8; 32]);
        let asset = hx(&[0u8; 32]);

        let in0_sk = hx(&[2u8; 32]);
        let in0_bl = hx(&[3u8; 32]);
        let in1_sk = hx(&[4u8; 32]);
        let in1_bl = hx(&[5u8; 32]);

        let out0_pk = hx(&[6u8; 32]);
        let out0_bl = hx(&[7u8; 32]);
        let out1_pk = hx(&[8u8; 32]);
        let out1_bl = hx(&[9u8; 32]);

        let path_1 = vec![hx(&[10u8; 32]); 1];
        let indices_1 = vec![false; 1];

        let path_2 = vec![hx(&[10u8; 32]); 2];
        let indices_2 = vec![false; 2];

        let valid_outputs = format!(
            r#"[
                {{"amount":50,"pubkey_hex":"{out0_pk}","blinding_hex":"{out0_bl}"}},
                {{"amount":50,"pubkey_hex":"{out1_pk}","blinding_hex":"{out1_bl}"}}
            ]"#
        );

        // Mismatched depths (input 0 has depth 1, input 1 has depth 2)
        let mismatched_inputs = format!(
            r#"[
                {{"amount":50,"privkey_hex":"{in0_sk}","blinding_hex":"{in0_bl}","path_hex":{},"indices":{}}},
                {{"amount":50,"privkey_hex":"{in1_sk}","blinding_hex":"{in1_bl}","path_hex":{},"indices":{}}}
            ]"#,
            serde_json::to_string(&path_1).unwrap(),
            serde_json::to_string(&indices_1).unwrap(),
            serde_json::to_string(&path_2).unwrap(),
            serde_json::to_string(&indices_2).unwrap()
        );
        let err =
            prove_transfer_v2_inner(&dummy_pk, &root, &asset, &mismatched_inputs, &valid_outputs)
                .unwrap_err();
        assert!(err.contains("input path depths must match"));

        // Empty depth (depth 0)
        let empty_inputs = format!(
            r#"[
                {{"amount":50,"privkey_hex":"{in0_sk}","blinding_hex":"{in0_bl}","path_hex":[],"indices":[]}},
                {{"amount":50,"privkey_hex":"{in1_sk}","blinding_hex":"{in1_bl}","path_hex":[],"indices":[]}}
            ]"#
        );
        let err = prove_transfer_v2_inner(&dummy_pk, &root, &asset, &empty_inputs, &valid_outputs)
            .unwrap_err();
        assert!(err.contains("path depth must be between 1 and 63"));

        // Depth > 63
        let path_64 = vec![hx(&[10u8; 32]); 64];
        let indices_64 = vec![false; 64];
        let depth64_inputs = format!(
            r#"[
                {{"amount":50,"privkey_hex":"{in0_sk}","blinding_hex":"{in0_bl}","path_hex":{},"indices":{}}},
                {{"amount":50,"privkey_hex":"{in1_sk}","blinding_hex":"{in1_bl}","path_hex":{},"indices":{}}}
            ]"#,
            serde_json::to_string(&path_64).unwrap(),
            serde_json::to_string(&indices_64).unwrap(),
            serde_json::to_string(&path_64).unwrap(),
            serde_json::to_string(&indices_64).unwrap()
        );
        let err =
            prove_transfer_v2_inner(&dummy_pk, &root, &asset, &depth64_inputs, &valid_outputs)
                .unwrap_err();
        assert!(err.contains("path depth must be between 1 and 63"));
    }
}
