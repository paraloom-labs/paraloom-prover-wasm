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
pub mod transact_vk_data;

use ark_bn254::{Bn254, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{Proof, ProvingKey, VerifyingKey};
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

fn hex32_inner(s: &str) -> Result<[u8; 32], String> {
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

/// Reverse a 32-byte coordinate in place (little-endian <-> big-endian).
fn rev32(src: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, b) in src.iter().take(32).rev().enumerate() {
        out[i] = *b;
    }
    out
}

/// G1 point -> 64-byte big-endian `[x || y]`.
pub fn g1_to_wire(p: &G1Affine) -> [u8; 64] {
    let mut le = Vec::with_capacity(64);
    p.serialize_uncompressed(&mut le)
        .expect("G1 serialize_uncompressed is infallible");
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(&rev32(&le[..32]));
    out[32..].copy_from_slice(&rev32(&le[32..64]));
    out
}

/// G2 point -> 128-byte big-endian `[x.c1 || x.c0 || y.c1 || y.c0]`.
pub fn g2_to_wire(p: &G2Affine) -> [u8; 128] {
    let mut le = Vec::with_capacity(128);
    p.serialize_uncompressed(&mut le)
        .expect("G2 serialize_uncompressed is infallible");
    let mut out = [0u8; 128];
    out[..32].copy_from_slice(&rev32(&le[32..64]));
    out[32..64].copy_from_slice(&rev32(&le[..32]));
    out[64..96].copy_from_slice(&rev32(&le[96..128]));
    out[96..].copy_from_slice(&rev32(&le[64..96]));
    out
}

/// 64-byte big-endian wire format -> G1 point.
pub fn wire_to_g1(wire: &[u8; 64]) -> Result<G1Affine, ark_serialize::SerializationError> {
    let mut le = [0u8; 64];
    le[..32].copy_from_slice(&rev32(&wire[..32]));
    le[32..64].copy_from_slice(&rev32(&wire[32..64]));
    G1Affine::deserialize_uncompressed(&le[..])
}

/// 128-byte big-endian wire format -> G2 point.
pub fn wire_to_g2(wire: &[u8; 128]) -> Result<G2Affine, ark_serialize::SerializationError> {
    let mut le = [0u8; 128];
    le[..32].copy_from_slice(&rev32(&wire[32..64]));
    le[32..64].copy_from_slice(&rev32(&wire[..32]));
    le[64..96].copy_from_slice(&rev32(&wire[96..128]));
    le[96..128].copy_from_slice(&rev32(&wire[64..96]));
    G2Affine::deserialize_uncompressed(&le[..])
}

/// Deserialize the canonical ceremony verifying key for TransactCircuitV3.
pub fn canonical_transact_verifying_key() -> Result<VerifyingKey<Bn254>, ark_serialize::SerializationError> {
    let alpha_g1 = wire_to_g1(&transact_vk_data::VK_ALPHA_G1)?;
    let beta_g2 = wire_to_g2(&transact_vk_data::VK_BETA_G2)?;
    let gamma_g2 = wire_to_g2(&transact_vk_data::VK_GAMMA_G2)?;
    let delta_g2 = wire_to_g2(&transact_vk_data::VK_DELTA_G2)?;
    let mut gamma_abc_g1 = Vec::with_capacity(transact_vk_data::VK_IC.len());
    for ic in &transact_vk_data::VK_IC {
        gamma_abc_g1.push(wire_to_g1(ic)?);
    }
    Ok(VerifyingKey {
        alpha_g1,
        beta_g2,
        gamma_g2,
        delta_g2,
        gamma_abc_g1,
    })
}

/// SHA-256 fingerprint for canonical ceremony verifying key over wire elements.
pub fn ceremony_transact_vk_fingerprint() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(&transact_vk_data::VK_ALPHA_G1);
    hasher.update(&transact_vk_data::VK_BETA_G2);
    hasher.update(&transact_vk_data::VK_GAMMA_G2);
    hasher.update(&transact_vk_data::VK_DELTA_G2);
    for ic in &transact_vk_data::VK_IC {
        hasher.update(ic);
    }
    hasher.finalize().into()
}

/// SHA-256 fingerprint for a transact VerifyingKey over its wire representation.
pub fn vk_to_transact_fingerprint(vk: &VerifyingKey<Bn254>) -> Result<[u8; 32], &'static str> {
    if vk.gamma_abc_g1.len() != 9 {
        return Err("transact verifying key must have exactly 9 IC points");
    }
    let mut hasher = Sha256::new();
    hasher.update(&g1_to_wire(&vk.alpha_g1));
    hasher.update(&g2_to_wire(&vk.beta_g2));
    hasher.update(&g2_to_wire(&vk.gamma_g2));
    hasher.update(&g2_to_wire(&vk.delta_g2));
    for ic in &vk.gamma_abc_g1 {
        hasher.update(&g1_to_wire(ic));
    }
    Ok(hasher.finalize().into())
}

/// Verify that a transact VerifyingKey matches the canonical on-chain ceremony constants.
pub fn verify_transact_ceremony_vk(vk: &VerifyingKey<Bn254>) -> Result<(), &'static str> {
    if vk.gamma_abc_g1.len() != 9 {
        return Err("transact verifying key must have exactly 9 IC points");
    }
    if g1_to_wire(&vk.alpha_g1) != transact_vk_data::VK_ALPHA_G1 {
        return Err("verifying key alpha_g1 does not match canonical ceremony VK");
    }
    if g2_to_wire(&vk.beta_g2) != transact_vk_data::VK_BETA_G2 {
        return Err("verifying key beta_g2 does not match canonical ceremony VK");
    }
    if g2_to_wire(&vk.gamma_g2) != transact_vk_data::VK_GAMMA_G2 {
        return Err("verifying key gamma_g2 does not match canonical ceremony VK");
    }
    if g2_to_wire(&vk.delta_g2) != transact_vk_data::VK_DELTA_G2 {
        return Err("verifying key delta_g2 does not match canonical ceremony VK");
    }
    for (i, ic) in vk.gamma_abc_g1.iter().enumerate() {
        if g1_to_wire(ic) != transact_vk_data::VK_IC[i] {
            return Err("verifying key IC point does not match canonical ceremony VK");
        }
    }
    let fp = vk_to_transact_fingerprint(vk)?;
    if fp != ceremony_transact_vk_fingerprint() {
        return Err("verifying key fingerprint does not match canonical ceremony VK fingerprint");
    }
    Ok(())
}

/// Validate proving key toxic-waste elements and ensure no degenerate collisions.
pub fn validate_proving_key(pk: &ProvingKey<Bn254>) -> Result<(), &'static str> {
    if pk.beta_g1.is_zero() {
        return Err("proving key beta_g1 is point at infinity");
    }
    if pk.delta_g1.is_zero() {
        return Err("proving key delta_g1 is point at infinity");
    }
    if !pk.beta_g1.is_on_curve() || !pk.beta_g1.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proving key beta_g1 not on curve or in subgroup");
    }
    if !pk.delta_g1.is_on_curve() || !pk.delta_g1.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proving key delta_g1 not on curve or in subgroup");
    }

    if pk.vk.alpha_g1.is_zero() || !pk.vk.alpha_g1.is_on_curve() || !pk.vk.alpha_g1.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key alpha_g1 is zero or invalid");
    }
    if pk.vk.beta_g2.is_zero() || !pk.vk.beta_g2.is_on_curve() || !pk.vk.beta_g2.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key beta_g2 is zero or invalid");
    }
    if pk.vk.gamma_g2.is_zero() || !pk.vk.gamma_g2.is_on_curve() || !pk.vk.gamma_g2.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key gamma_g2 is zero or invalid");
    }
    if pk.vk.delta_g2.is_zero() || !pk.vk.delta_g2.is_on_curve() || !pk.vk.delta_g2.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key delta_g2 is zero or invalid");
    }

    // Enforce pairwise distinctness of (alpha_g1, beta_g1, delta_g1)
    if pk.vk.alpha_g1 == pk.beta_g1 {
        return Err("toxic waste collision: alpha_g1 == beta_g1");
    }
    if pk.vk.alpha_g1 == pk.delta_g1 {
        return Err("toxic waste collision: alpha_g1 == delta_g1");
    }
    if pk.beta_g1 == pk.delta_g1 {
        return Err("toxic waste collision: beta_g1 == delta_g1");
    }

    // Enforce pairwise distinctness of (beta_g2, gamma_g2, delta_g2)
    if pk.vk.beta_g2 == pk.vk.gamma_g2 {
        return Err("toxic waste collision: beta_g2 == gamma_g2");
    }
    if pk.vk.beta_g2 == pk.vk.delta_g2 {
        return Err("toxic waste collision: beta_g2 == delta_g2");
    }
    if pk.vk.gamma_g2 == pk.vk.delta_g2 {
        return Err("toxic waste collision: gamma_g2 == delta_g2");
    }

    // Enforce IC points validation
    if pk.vk.gamma_abc_g1.is_empty() {
        return Err("verifying key gamma_abc_g1 is empty");
    }
    for (i, ic) in pk.vk.gamma_abc_g1.iter().enumerate() {
        if ic.is_zero() {
            return Err("verifying key gamma_abc_g1 contains zero point");
        }
        if !ic.is_on_curve() || !ic.is_in_correct_subgroup_assuming_on_curve() {
            return Err("verifying key gamma_abc_g1 point not on curve or in subgroup");
        }
        for other in pk.vk.gamma_abc_g1.iter().skip(i + 1) {
            if ic == other {
                return Err("toxic waste collision: duplicate IC points in gamma_abc_g1");
            }
        }
    }

    Ok(())
}

/// Validate Groth16 proof curve elements.
pub fn validate_proof(proof: &Proof<Bn254>) -> Result<(), &'static str> {
    if proof.a.is_zero() {
        return Err("proof element A is zero");
    }
    if proof.b.is_zero() {
        return Err("proof element B is zero");
    }
    if proof.c.is_zero() {
        return Err("proof element C is zero");
    }
    if !proof.a.is_on_curve() || !proof.a.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proof element A not on curve or in subgroup");
    }
    if !proof.b.is_on_curve() || !proof.b.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proof element B not on curve or in subgroup");
    }
    if !proof.c.is_on_curve() || !proof.c.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proof element C not on curve or in subgroup");
    }
    if proof.a == proof.c {
        return Err("degenerate proof: proof.a == proof.c");
    }
    Ok(())
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
    validate_proving_key(&pk)
        .map_err(|e| JsValue::from_str(&format!("invalid proving key: {e}")))?;
    let proof =
        Groth16ProofSystem::prove::<WithdrawCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;
    validate_proof(&proof)
        .map_err(|e| JsValue::from_str(&format!("invalid proof: {e}")))?;

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
    validate_proving_key(&pk)
        .map_err(|e| JsValue::from_str(&format!("invalid proving key: {e}")))?;
    let proof =
        Groth16ProofSystem::prove::<TransferCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;
    validate_proof(&proof)
        .map_err(|e| JsValue::from_str(&format!("invalid proof: {e}")))?;

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

    let inputs: Vec<TransactInputNote> = serde_json::from_str(inputs_json)
        .map_err(|e| format!("bad inputs json: {e}"))?;
    let outputs: Vec<TransactOutputNote> = serde_json::from_str(outputs_json)
        .map_err(|e| format!("bad outputs json: {e}"))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err("transact is fixed 2-in/2-out".to_string());
    }

    // The shielded asset: all-zero for native SOL, or `mint_to_asset(mint)` for
    // a shielded SPL note (#779). All notes in one transact share one asset.
    let asset = Fr::from_le_bytes_mod_order(&hex32_inner(asset_id_hex)?);

    let mut in_amounts = Vec::new();
    let mut in_privkeys = Vec::new();
    let mut in_blindings = Vec::new();
    let mut in_leaf_indices = Vec::new();
    let mut in_paths = Vec::new();
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
        in_paths.push(Some(path));
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
    if !pk.h_query.len().is_power_of_two() {
        return Err("proving key h_query must be a power of two (circom convention)".to_string());
    }
    validate_proving_key(&pk)
        .map_err(|e| format!("invalid proving key: {e}"))?;
    verify_transact_ceremony_vk(&pk.vk)
        .map_err(|e| format!("verifying key does not match canonical ceremony: {e}"))?;

    let proof =
        Groth16ProofSystem::prove::<TransactCircuitV3, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| format!("prove failed: {e}"))?;
    validate_proof(&proof)
        .map_err(|e| format!("invalid proof: {e}"))?;

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
pub fn v3_merkle_path_inner(leaves_json: &str, leaf_index: u32) -> Result<String, String> {
    use privacy::poseidon_circom::v3_merkle_pair;

    let leaves_hex: Vec<String> = serde_json::from_str(leaves_json)
        .map_err(|e| format!("bad leaves json: {e}"))?;
    if (leaf_index as usize) >= leaves_hex.len() {
        return Err("leaf_index out of range".to_string());
    }
    let target_leaf = Fr::from_le_bytes_mod_order(&hex32_inner(&leaves_hex[leaf_index as usize])?);
    let mut level: Vec<Fr> = Vec::with_capacity(leaves_hex.len());
    for l in &leaves_hex {
        level.push(Fr::from_le_bytes_mod_order(&hex32_inner(l)?));
    }

    // Zero-subtree hashes, as the on-chain tree pads with.
    let mut zeros = vec![Fr::from(0u64)];
    for k in 0..TX_LEVELS {
        zeros.push(v3_merkle_pair(zeros[k], zeros[k]));
    }

    let mut path = Vec::with_capacity(TX_LEVELS);
    let mut path_fr = Vec::with_capacity(TX_LEVELS);
    let mut idx = leaf_index as usize;
    for depth in 0..TX_LEVELS {
        let sibling = if idx % 2 == 0 {
            *level.get(idx + 1).unwrap_or(&zeros[depth])
        } else {
            level[idx - 1]
        };
        path_fr.push(sibling);
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

    // Bit-fold self-verification and path-sibling non-collision check
    if target_leaf == root {
        return Err("merkle target leaf collides with tree root".to_string());
    }
    let mut current = target_leaf;
    for depth in 0..TX_LEVELS {
        let sibling = path_fr[depth];
        if sibling == target_leaf {
            return Err("merkle path sibling collides with target leaf commitment".to_string());
        }
        if sibling == root {
            return Err("merkle path sibling collides with tree root".to_string());
        }
        let bit = ((leaf_index >> depth) & 1) == 1;
        current = if bit {
            v3_merkle_pair(sibling, current)
        } else {
            v3_merkle_pair(current, sibling)
        };
    }
    if current != root {
        return Err("merkle path bit-fold self-verification failed to reproduce root".to_string());
    }
    Ok(format!(
        "{{\"path\":{},\"root\":\"{}\"}}",
        serde_json::to_string(&path).unwrap(),
        hex::encode(fr_to_le_bytes_32(root))
    ))
}

#[wasm_bindgen]
pub fn v3_merkle_path(leaves_json: &str, leaf_index: u32) -> Result<String, JsValue> {
    v3_merkle_path_inner(leaves_json, leaf_index).map_err(|e| JsValue::from_str(&e))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_canonical_transact_verifying_key_matches_and_roundtrips() {
        let vk = canonical_transact_verifying_key().expect("canonical vk must deserialize");
        assert_eq!(g1_to_wire(&vk.alpha_g1), transact_vk_data::VK_ALPHA_G1);
        assert_eq!(g2_to_wire(&vk.beta_g2), transact_vk_data::VK_BETA_G2);
        assert_eq!(g2_to_wire(&vk.gamma_g2), transact_vk_data::VK_GAMMA_G2);
        assert_eq!(g2_to_wire(&vk.delta_g2), transact_vk_data::VK_DELTA_G2);
        assert_eq!(vk.gamma_abc_g1.len(), 9);
        for (i, ic) in vk.gamma_abc_g1.iter().enumerate() {
            assert_eq!(g1_to_wire(ic), transact_vk_data::VK_IC[i]);
        }

        // Verify fingerprint
        let fp = vk_to_transact_fingerprint(&vk).expect("fingerprint");
        assert_eq!(fp, ceremony_transact_vk_fingerprint());

        // Verify ceremony check passes
        assert!(verify_transact_ceremony_vk(&vk).is_ok());
    }

    #[test]
    fn test_verify_transact_ceremony_vk_rejects_tampered_elements() {
        let canonical = canonical_transact_verifying_key().expect("canonical vk");

        // Tamper alpha_g1
        let mut tampered = canonical.clone();
        tampered.alpha_g1 = tampered.gamma_abc_g1[0];
        assert!(verify_transact_ceremony_vk(&tampered).is_err());

        // Tamper beta_g2
        let mut tampered = canonical.clone();
        tampered.beta_g2 = tampered.gamma_g2;
        assert!(verify_transact_ceremony_vk(&tampered).is_err());

        // Tamper gamma_g2
        let mut tampered = canonical.clone();
        tampered.gamma_g2 = tampered.delta_g2;
        assert!(verify_transact_ceremony_vk(&tampered).is_err());

        // Tamper delta_g2
        let mut tampered = canonical.clone();
        tampered.delta_g2 = tampered.beta_g2;
        assert!(verify_transact_ceremony_vk(&tampered).is_err());

        // Tamper IC points
        for i in 0..9 {
            let mut tampered = canonical.clone();
            tampered.gamma_abc_g1[i] = canonical.alpha_g1;
            assert!(verify_transact_ceremony_vk(&tampered).is_err());
        }

        // Tamper IC length
        let mut tampered = canonical.clone();
        tampered.gamma_abc_g1.pop();
        assert!(verify_transact_ceremony_vk(&tampered).is_err());
    }

    #[test]
    fn test_prove_transact_rejects_tampered_proving_key() {
        let vk = canonical_transact_verifying_key().expect("canonical vk");
        let beta_g1 = wire_to_g1(&transact_vk_data::VK_IC_1).unwrap();
        let delta_g1 = wire_to_g1(&transact_vk_data::VK_IC_2).unwrap();

        // Proving key with tampered VK
        let mut tampered_vk = vk;
        tampered_vk.alpha_g1 = beta_g1;

        let pk = ProvingKey {
            vk: tampered_vk,
            beta_g1,
            delta_g1,
            a_query: Vec::new(),
            b_g1_query: Vec::new(),
            b_g2_query: Vec::new(),
            h_query: vec![beta_g1, delta_g1],
            l_query: Vec::new(),
        };

        let mut pk_bytes = Vec::new();
        pk.serialize_compressed(&mut pk_bytes).unwrap();

        let zero32 = hex::encode([0u8; 32]);
        let path32 = vec![zero32.clone(); 32];
        let path_json = serde_json::to_string(&path32).unwrap();

        let inputs = format!(
            r#"[
              {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{}}},
              {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{}}}
            ]"#,
            hex::encode([1u8; 32]), hex::encode([2u8; 32]), path_json,
            hex::encode([3u8; 32]), hex::encode([4u8; 32]), path_json
        );

        let outputs = format!(
            r#"[
              {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}},
              {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
            ]"#,
            hex::encode([5u8; 32]), hex::encode([6u8; 32]),
            hex::encode([7u8; 32]), hex::encode([8u8; 32])
        );

        let res = prove_transact_inner(
            &pk_bytes,
            &zero32,
            0,
            &zero32,
            &zero32,
            &inputs,
            &outputs,
        );
        assert!(res.is_err());
    }

    #[test]
    fn test_validate_proving_key_toxic_waste_invariants() {
        let vk = canonical_transact_verifying_key().expect("canonical vk");
        let beta_g1 = wire_to_g1(&transact_vk_data::VK_IC_1).unwrap();
        let delta_g1 = wire_to_g1(&transact_vk_data::VK_IC_2).unwrap();

        let make_pk = |vk: VerifyingKey<Bn254>, b1: G1Affine, d1: G1Affine| ProvingKey {
            vk,
            beta_g1: b1,
            delta_g1: d1,
            a_query: Vec::new(),
            b_g1_query: Vec::new(),
            b_g2_query: Vec::new(),
            h_query: vec![b1, d1],
            l_query: Vec::new(),
        };

        // Valid PK passes
        let pk = make_pk(vk.clone(), beta_g1, delta_g1);
        assert!(validate_proving_key(&pk).is_ok());

        // beta_g1 is zero
        let pk_zero_beta = make_pk(vk.clone(), G1Affine::zero(), delta_g1);
        assert_eq!(validate_proving_key(&pk_zero_beta), Err("proving key beta_g1 is point at infinity"));

        // delta_g1 is zero
        let pk_zero_delta = make_pk(vk.clone(), beta_g1, G1Affine::zero());
        assert_eq!(validate_proving_key(&pk_zero_delta), Err("proving key delta_g1 is point at infinity"));

        // alpha_g1 == beta_g1 collision
        let pk_alpha_beta = make_pk(vk.clone(), vk.alpha_g1, delta_g1);
        assert_eq!(validate_proving_key(&pk_alpha_beta), Err("toxic waste collision: alpha_g1 == beta_g1"));

        // alpha_g1 == delta_g1 collision
        let pk_alpha_delta = make_pk(vk.clone(), beta_g1, vk.alpha_g1);
        assert_eq!(validate_proving_key(&pk_alpha_delta), Err("toxic waste collision: alpha_g1 == delta_g1"));

        // beta_g1 == delta_g1 collision
        let pk_beta_delta = make_pk(vk.clone(), beta_g1, beta_g1);
        assert_eq!(validate_proving_key(&pk_beta_delta), Err("toxic waste collision: beta_g1 == delta_g1"));

        // beta_g2 == gamma_g2 collision
        let mut vk_b_g = vk.clone();
        vk_b_g.beta_g2 = vk.gamma_g2;
        let pk_bg = make_pk(vk_b_g, beta_g1, delta_g1);
        assert_eq!(validate_proving_key(&pk_bg), Err("toxic waste collision: beta_g2 == gamma_g2"));

        // beta_g2 == delta_g2 collision
        let mut vk_b_d = vk.clone();
        vk_b_d.beta_g2 = vk.delta_g2;
        let pk_bd = make_pk(vk_b_d, beta_g1, delta_g1);
        assert_eq!(validate_proving_key(&pk_bd), Err("toxic waste collision: beta_g2 == delta_g2"));

        // gamma_g2 == delta_g2 collision
        let mut vk_g_d = vk.clone();
        vk_g_d.gamma_g2 = vk.delta_g2;
        let pk_gd = make_pk(vk_g_d, beta_g1, delta_g1);
        assert_eq!(validate_proving_key(&pk_gd), Err("toxic waste collision: gamma_g2 == delta_g2"));

        // Duplicate IC points
        let mut vk_dup_ic = vk.clone();
        vk_dup_ic.gamma_abc_g1[1] = vk_dup_ic.gamma_abc_g1[0];
        let pk_dup = make_pk(vk_dup_ic, beta_g1, delta_g1);
        assert_eq!(validate_proving_key(&pk_dup), Err("toxic waste collision: duplicate IC points in gamma_abc_g1"));

        // Zero IC point
        let mut vk_zero_ic = vk.clone();
        vk_zero_ic.gamma_abc_g1[0] = G1Affine::zero();
        let pk_zic = make_pk(vk_zero_ic, beta_g1, delta_g1);
        assert_eq!(validate_proving_key(&pk_zic), Err("verifying key gamma_abc_g1 contains zero point"));
    }

    #[test]
    fn test_validate_proof_invariants() {
        let p_a = wire_to_g1(&transact_vk_data::VK_IC_1).unwrap();
        let p_b = wire_to_g2(&transact_vk_data::VK_BETA_G2).unwrap();
        let p_c = wire_to_g1(&transact_vk_data::VK_IC_2).unwrap();

        let valid_proof = Proof {
            a: p_a,
            b: p_b,
            c: p_c,
        };
        assert!(validate_proof(&valid_proof).is_ok());

        let mut zero_a = valid_proof.clone();
        zero_a.a = G1Affine::zero();
        assert_eq!(validate_proof(&zero_a), Err("proof element A is zero"));

        let mut zero_b = valid_proof.clone();
        zero_b.b = G2Affine::zero();
        assert_eq!(validate_proof(&zero_b), Err("proof element B is zero"));

        let mut zero_c = valid_proof.clone();
        zero_c.c = G1Affine::zero();
        assert_eq!(validate_proof(&zero_c), Err("proof element C is zero"));

        let mut a_eq_c = valid_proof.clone();
        a_eq_c.c = a_eq_c.a;
        assert_eq!(validate_proof(&a_eq_c), Err("degenerate proof: proof.a == proof.c"));
    }

    #[test]
    fn test_v3_merkle_path_bit_fold_and_non_collision() {
        use privacy::poseidon_circom::{v3_commit, v3_pubkey};

        let leaf0 = v3_commit(Fr::from(500u64), v3_pubkey(Fr::from(11u64)), Fr::from(1u64), Fr::from(0u64));
        let leaf1 = v3_commit(Fr::from(300u64), v3_pubkey(Fr::from(22u64)), Fr::from(2u64), Fr::from(0u64));
        let leaf2 = v3_commit(Fr::from(200u64), v3_pubkey(Fr::from(33u64)), Fr::from(3u64), Fr::from(0u64));

        let leaves = serde_json::to_string(&[
            hex::encode(fr_to_le_bytes_32(leaf0)),
            hex::encode(fr_to_le_bytes_32(leaf1)),
            hex::encode(fr_to_le_bytes_32(leaf2)),
        ]).unwrap();

        // Valid path for leaf 0, 1, 2
        for i in 0..3 {
            let res = v3_merkle_path_inner(&leaves, i);
            assert!(res.is_ok(), "v3_merkle_path for leaf {i} must succeed: {:?}", res.err());
            let val: serde_json::Value = serde_json::from_str(&res.unwrap()).unwrap();
            let path_arr = val["path"].as_array().unwrap();
            assert_eq!(path_arr.len(), 32);
            assert!(val["root"].as_str().is_some());
        }

        // Out of range index
        assert!(v3_merkle_path_inner(&leaves, 3).is_err());
        assert!(v3_merkle_path_inner(&leaves, 100).is_err());

        // Collision check: if leaf equals zeros[0] (i.e. zero leaf) with only 1 leaf in tree,
        // then sibling at depth 0 is zeros[0] == target_leaf.
        let zero_leaf_json = serde_json::to_string(&[hex::encode([0u8; 32])]).unwrap();
        let res_collision = v3_merkle_path_inner(&zero_leaf_json, 0);
        assert!(res_collision.is_err());
    }
}
