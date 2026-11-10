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
use ark_ec::AffineRepr;
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

const VK_GAMMA_ABC_LEN_OFFSET: usize = 32 + 64 + 64 + 64; // alpha_g1(32) + beta_g2(64) + gamma_g2(64) + delta_g2(64)
const MAX_GAMMA_ABC_LEN: u64 = 64;

fn deserialize_proving_key_bounded(
    proving_key: &[u8],
    context: &str,
) -> Result<ProvingKey<Bn254>, String> {
    if proving_key.len() < VK_GAMMA_ABC_LEN_OFFSET + 8 {
        return Err(format!(
            "{context}: proving key buffer too short ({} bytes)",
            proving_key.len()
        ));
    }
    let mut len_bytes = [0u8; 8];
    len_bytes.copy_from_slice(&proving_key[VK_GAMMA_ABC_LEN_OFFSET..VK_GAMMA_ABC_LEN_OFFSET + 8]);
    let gamma_abc_len = u64::from_le_bytes(len_bytes);
    if gamma_abc_len == 0 || gamma_abc_len > MAX_GAMMA_ABC_LEN {
        return Err(format!(
            "{context}: invalid proving key gamma_abc_g1 length prefix ({gamma_abc_len})"
        ));
    }
    let pk = ProvingKey::<Bn254>::deserialize_compressed(proving_key)
        .map_err(|e| format!("bad proving key: {e}"))?;
    if pk.b_g1_query.len() != pk.b_g2_query.len() {
        return Err(format!(
            "{context}: b_g1_query length ({}) != b_g2_query length ({})",
            pk.b_g1_query.len(),
            pk.b_g2_query.len()
        ));
    }
    if pk.a_query.len() < pk.vk.gamma_abc_g1.len() {
        return Err(format!(
            "{context}: a_query length ({}) < gamma_abc_g1 length ({})",
            pk.a_query.len(),
            pk.vk.gamma_abc_g1.len()
        ));
    }
    if pk.l_query.is_empty() || pk.l_query.iter().all(|p| p.is_zero()) {
        return Err(format!(
            "{context}: proving key l_query is empty or all-zero"
        ));
    }
    if pk.h_query.is_empty() || pk.h_query.iter().all(|p| p.is_zero()) {
        return Err(format!(
            "{context}: proving key h_query is empty or all-zero"
        ));
    }
    Ok(pk)
}

fn validate_output_against_input_artifacts(
    pubkey: &[u8; 32],
    blinding: &[u8; 32],
    input_commitments: &[[u8; 32]],
    nullifiers: &[[u8; 32]],
    input_signatures: &[[u8; 32]],
    context: &str,
) -> Result<(), String> {
    if input_commitments.contains(pubkey)
        || nullifiers.contains(pubkey)
        || input_signatures.contains(pubkey)
        || input_commitments.contains(blinding)
        || nullifiers.contains(blinding)
        || input_signatures.contains(blinding)
    {
        return Err(format!(
            "{context}: output pubkey or blinding collides with input commitment, nullifier, or spend signature"
        ));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_withdrawal_recipient_distinct(
    recipient: &[u8; 32],
    in_privkeys: &[[u8; 32]],
    in_blindings: &[[u8; 32]],
    out_blindings: &[[u8; 32]],
    in_pubkeys: &[[u8; 32]],
    out_pubkeys: &[[u8; 32]],
    in_commitments: &[[u8; 32]],
    out_commitments: &[[u8; 32]],
    nullifiers: &[[u8; 32]],
    signatures: &[[u8; 32]],
    context: &str,
) -> Result<(), String> {
    if in_privkeys.contains(recipient)
        || in_blindings.contains(recipient)
        || out_blindings.contains(recipient)
        || in_pubkeys.contains(recipient)
        || out_pubkeys.contains(recipient)
        || in_commitments.contains(recipient)
        || out_commitments.contains(recipient)
        || nullifiers.contains(recipient)
        || signatures.contains(recipient)
    {
        return Err(format!(
            "{context}: withdrawal recipient collides with shielded pubkey, commitment, nullifier, signature, or secret witness"
        ));
    }
    Ok(())
}

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
    let pubkey_fr = poseidon_pubkey(sk);
    let pubkey_bytes = fr_to_le_bytes_32(pubkey_fr);
    let commitment_fr = poseidon_commit_spend(
        Fr::from(amount),
        pubkey_fr,
        Fr::from_le_bytes_mod_order(&blinding),
        Fr::from_le_bytes_mod_order(&asset_id),
    );
    let commitment_bytes = fr_to_le_bytes_32(commitment_fr);
    let signature = poseidon_signature(sk, commitment_fr, Fr::from(leaf_index));
    let signature_bytes = fr_to_le_bytes_32(signature);
    let nullifier_fr = poseidon_nullifier_spend(commitment_fr, Fr::from(leaf_index), signature);
    let nullifier = fr_to_le_bytes_32(nullifier_fr);

    validate_withdrawal_recipient_distinct(
        &dest_recipient,
        &[privkey],
        &[blinding],
        &[],
        &[pubkey_bytes],
        &[],
        &[commitment_bytes],
        &[],
        &[nullifier],
        &[signature_bytes],
        "prove_withdrawal_v2",
    )
    .map_err(|e| JsValue::from_str(&e))?;

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

    let pk = deserialize_proving_key_bounded(proving_key, "prove_withdrawal_v2")
        .map_err(|e| JsValue::from_str(&e))?;
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
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(JsValue::from_str(
            "transfer requires exactly 2 inputs and 2 outputs",
        ));
    }

    let mut nullifiers = Vec::with_capacity(2);
    let mut input_commitments = Vec::with_capacity(2);
    let mut input_signatures = Vec::with_capacity(2);
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
        let leaf_index = leaf_index_from(&inp.indices);
        let signature = poseidon_signature(sk, commitment_fr, Fr::from(leaf_index));
        let nullifier_fr = poseidon_nullifier_spend(commitment_fr, Fr::from(leaf_index), signature);
        input_commitments.push(fr_to_le_bytes_32(commitment_fr));
        input_signatures.push(fr_to_le_bytes_32(signature));
        nullifiers.push(fr_to_le_bytes_32(nullifier_fr));
        input_values.push(inp.amount);
        input_blindings.push(blinding);
        input_privkeys.push(privkey);
        input_paths.push(merkle_path_from(&inp.path_hex, &inp.indices)?);
    }

    let mut output_commitments = Vec::with_capacity(2);
    let mut output_values = Vec::with_capacity(2);
    let mut output_blindings = Vec::with_capacity(2);
    let mut output_pubkeys = Vec::with_capacity(2);
    for out in &outputs {
        let blinding = hex32(&out.blinding_hex)?;
        let pubkey = hex32(&out.pubkey_hex)?;
        validate_output_against_input_artifacts(
            &pubkey,
            &blinding,
            &input_commitments,
            &nullifiers,
            &input_signatures,
            "prove_transfer_v2",
        )
        .map_err(|e| JsValue::from_str(&e))?;
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

    let pk = deserialize_proving_key_bounded(proving_key, "prove_transfer_v2")
        .map_err(|e| JsValue::from_str(&e))?;
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
    let mut in_derived_pubkeys = Vec::new();
    let mut in_commitments = Vec::new();
    let mut in_signatures = Vec::new();
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
        let pk_fr = v3_pubkey(sk);
        let c = v3_commit(
            Fr::from(inp.amount),
            pk_fr,
            Fr::from_le_bytes_mod_order(&blinding),
            asset,
        );
        let sig = v3_signature(sk, c, Fr::from(inp.leaf_index));
        let nf = v3_nullifier(c, Fr::from(inp.leaf_index), sig);
        in_derived_pubkeys.push(fr_to_le_bytes_32(pk_fr));
        in_commitments.push(fr_to_le_bytes_32(c));
        in_signatures.push(fr_to_le_bytes_32(sig));
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
    let mut out_pubkey_raw = Vec::new();
    let mut out_blinding_raw = Vec::new();
    let mut output_commitments = Vec::new();
    for outp in &outputs {
        let pubkey = hex32(&outp.pubkey_hex)?;
        let blinding = hex32(&outp.blinding_hex)?;
        validate_output_against_input_artifacts(
            &pubkey,
            &blinding,
            &in_commitments,
            &nullifiers,
            &in_signatures,
            "prove_transact",
        )
        .map_err(|e| JsValue::from_str(&e))?;
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
        out_pubkey_raw.push(pubkey);
        out_blinding_raw.push(blinding);
    }

    if ext_amount < 0 {
        let raw_in_privkeys: Vec<[u8; 32]> = in_privkeys.iter().flatten().copied().collect();
        let raw_in_blindings: Vec<[u8; 32]> = in_blindings.iter().flatten().copied().collect();
        validate_withdrawal_recipient_distinct(
            &recipient,
            &raw_in_privkeys,
            &raw_in_blindings,
            &out_blinding_raw,
            &in_derived_pubkeys,
            &out_pubkey_raw,
            &in_commitments,
            &output_commitments,
            &nullifiers,
            &in_signatures,
            "prove_transact",
        )
        .map_err(|e| JsValue::from_str(&e))?;
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

    let pk = deserialize_proving_key_bounded(proving_key, "prove_transact")
        .map_err(|e| JsValue::from_str(&e))?;
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
mod issue_57_tests {
    use super::*;
    use ark_bn254::{G1Affine, G2Affine};
    use ark_ec::CurveGroup;

    #[test]
    fn deserialize_proving_key_bounded_rejects_corrupted_length_prefix_and_zero_queries() {
        // Short buffer rejected without panic.
        assert!(deserialize_proving_key_bounded(&[0u8; 64], "test").is_err());

        // Corrupted huge gamma_abc_g1 u64 length prefix at offset 224..232 is rejected before Vec::with_capacity OOM.
        let mut bad_header = vec![0u8; 240];
        bad_header[VK_GAMMA_ABC_LEN_OFFSET..VK_GAMMA_ABC_LEN_OFFSET + 8]
            .copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(deserialize_proving_key_bounded(&bad_header, "test").is_err());

        // Zero gamma_abc_g1 count rejected.
        let mut zero_header = vec![0u8; 240];
        zero_header[VK_GAMMA_ABC_LEN_OFFSET..VK_GAMMA_ABC_LEN_OFFSET + 8]
            .copy_from_slice(&0u64.to_le_bytes());
        assert!(deserialize_proving_key_bounded(&zero_header, "test").is_err());

        let g1_a = G1Affine::generator();
        let g1_b = (g1_a + g1_a).into_affine();
        let g2_a = G2Affine::generator();
        let vk = ark_groth16::VerifyingKey::<Bn254> {
            alpha_g1: g1_a,
            beta_g2: g2_a,
            gamma_g2: g2_a,
            delta_g2: g2_a,
            gamma_abc_g1: vec![g1_a, g1_b],
        };
        let pk = ProvingKey::<Bn254> {
            vk,
            beta_g1: g1_a,
            delta_g1: g1_b,
            a_query: vec![g1_a, g1_b],
            b_g1_query: vec![g1_a, g1_b],
            b_g2_query: vec![g2_a, g2_a],
            h_query: vec![g1_a],
            l_query: vec![g1_a],
        };
        let mut valid_bytes = Vec::new();
        pk.serialize_compressed(&mut valid_bytes).unwrap();
        assert!(deserialize_proving_key_bounded(&valid_bytes, "test").is_ok());

        // Mismatched b_g1_query vs b_g2_query lengths rejected.
        let mut mismatch_pk = pk.clone();
        mismatch_pk.b_g2_query = vec![g2_a];
        let mut mismatch_bytes = Vec::new();
        mismatch_pk
            .serialize_compressed(&mut mismatch_bytes)
            .unwrap();
        assert!(deserialize_proving_key_bounded(&mismatch_bytes, "test").is_err());

        // a_query shorter than gamma_abc_g1 rejected.
        let mut short_a_pk = pk.clone();
        short_a_pk.a_query = vec![g1_a];
        let mut short_a_bytes = Vec::new();
        short_a_pk.serialize_compressed(&mut short_a_bytes).unwrap();
        assert!(deserialize_proving_key_bounded(&short_a_bytes, "test").is_err());

        // All-zero l_query rejected.
        let mut zero_l_pk = pk.clone();
        zero_l_pk.l_query = vec![G1Affine::zero()];
        let mut zero_l_bytes = Vec::new();
        zero_l_pk.serialize_compressed(&mut zero_l_bytes).unwrap();
        assert!(deserialize_proving_key_bounded(&zero_l_bytes, "test").is_err());

        // All-zero h_query rejected.
        let mut zero_h_pk = pk;
        zero_h_pk.h_query = vec![G1Affine::zero()];
        let mut zero_h_bytes = Vec::new();
        zero_h_pk.serialize_compressed(&mut zero_h_bytes).unwrap();
        assert!(deserialize_proving_key_bounded(&zero_h_bytes, "test").is_err());
    }

    #[test]
    fn recipient_and_output_collision_guards_reject_shielded_and_secret_reuse() {
        let sk = [11u8; 32];
        let bl = [22u8; 32];
        let out_bl = [33u8; 32];
        let in_pk = fr_to_le_bytes_32(v3_pubkey(Fr::from_le_bytes_mod_order(&sk)));
        let out_pk = fr_to_le_bytes_32(v3_pubkey(Fr::from(44u64)));
        let c0 = fr_to_le_bytes_32(v3_commit(
            Fr::from(1000u64),
            Fr::from_le_bytes_mod_order(&in_pk),
            Fr::from_le_bytes_mod_order(&bl),
            Fr::from(0u64),
        ));
        let sig0 = fr_to_le_bytes_32(v3_signature(
            Fr::from_le_bytes_mod_order(&sk),
            Fr::from_le_bytes_mod_order(&c0),
            Fr::from(0u64),
        ));
        let nf0 = fr_to_le_bytes_32(v3_nullifier(
            Fr::from_le_bytes_mod_order(&c0),
            Fr::from(0u64),
            Fr::from_le_bytes_mod_order(&sig0),
        ));
        let oc0 = fr_to_le_bytes_32(v3_commit(
            Fr::from(500u64),
            Fr::from_le_bytes_mod_order(&out_pk),
            Fr::from_le_bytes_mod_order(&out_bl),
            Fr::from(0u64),
        ));

        // Distinct L1 recipient and output artifacts succeed.
        assert!(validate_output_against_input_artifacts(
            &out_pk,
            &out_bl,
            &[c0],
            &[nf0],
            &[sig0],
            "test"
        )
        .is_ok());
        assert!(validate_withdrawal_recipient_distinct(
            &[99u8; 32],
            &[sk],
            &[bl],
            &[out_bl],
            &[in_pk],
            &[out_pk],
            &[c0],
            &[oc0],
            &[nf0],
            &[sig0],
            "test"
        )
        .is_ok());

        // Output pubkey or blinding colliding with input commitment, nullifier, or signature fails.
        for bad in [c0, nf0, sig0] {
            assert!(validate_output_against_input_artifacts(
                &bad,
                &out_bl,
                &[c0],
                &[nf0],
                &[sig0],
                "test"
            )
            .is_err());
            assert!(validate_output_against_input_artifacts(
                &out_pk,
                &bad,
                &[c0],
                &[nf0],
                &[sig0],
                "test"
            )
            .is_err());
        }

        // Withdrawal recipient colliding with shielded pubkey, commitment, nullifier, signature, or secret witness fails.
        for bad_rec in [sk, bl, out_bl, in_pk, out_pk, c0, oc0, nf0, sig0] {
            assert!(validate_withdrawal_recipient_distinct(
                &bad_rec,
                &[sk],
                &[bl],
                &[out_bl],
                &[in_pk],
                &[out_pk],
                &[c0],
                &[oc0],
                &[nf0],
                &[sig0],
                "test"
            )
            .is_err());
        }
    }
}
