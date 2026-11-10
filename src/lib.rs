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

use ark_bn254::{Bn254, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField, Zero};
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

fn rev32(src: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, b) in src.iter().take(32).rev().enumerate() {
        out[i] = *b;
    }
    out
}

pub fn g1_to_wire(p: &G1Affine) -> [u8; 64] {
    let mut le = Vec::with_capacity(64);
    p.serialize_uncompressed(&mut le).unwrap_or_default();
    let mut out = [0u8; 64];
    if le.len() >= 64 {
        out[..32].copy_from_slice(&rev32(&le[..32]));
        out[32..].copy_from_slice(&rev32(&le[32..64]));
    }
    out
}

pub fn g2_to_wire(p: &G2Affine) -> [u8; 128] {
    let mut le = Vec::with_capacity(128);
    p.serialize_uncompressed(&mut le).unwrap_or_default();
    let mut out = [0u8; 128];
    if le.len() >= 128 {
        out[..32].copy_from_slice(&rev32(&le[32..64]));
        out[32..64].copy_from_slice(&rev32(&le[..32]));
        out[64..96].copy_from_slice(&rev32(&le[96..128]));
        out[96..].copy_from_slice(&rev32(&le[64..96]));
    }
    out
}

pub const TRANSACT_CEREMONY_VK_FINGERPRINT: [u8; 32] = [
    0x26, 0x3b, 0xc9, 0xa0, 0xc9, 0x45, 0x21, 0xd4, 0x91, 0xc6, 0xb0, 0x71, 0x42, 0x9d, 0xdb,
    0xd7, 0x7d, 0xd9, 0x13, 0x13, 0xcd, 0x7a, 0xaa, 0xa6, 0x71, 0x65, 0x03, 0x10, 0xd7, 0x24,
    0x9b, 0x36,
];

pub fn compute_transact_ceremony_vk_fingerprint() -> [u8; 32] {
    use privacy::transact_vk_data as vk;
    let mut hasher = Sha256::new();
    hasher.update(&vk::VK_ALPHA_G1);
    hasher.update(&vk::VK_BETA_G2);
    hasher.update(&vk::VK_GAMMA_G2);
    hasher.update(&vk::VK_DELTA_G2);
    hasher.update(&vk::VK_IC_0);
    hasher.update(&vk::VK_IC_1);
    hasher.update(&vk::VK_IC_2);
    hasher.update(&vk::VK_IC_3);
    hasher.update(&vk::VK_IC_4);
    hasher.update(&vk::VK_IC_5);
    hasher.update(&vk::VK_IC_6);
    hasher.update(&vk::VK_IC_7);
    hasher.update(&vk::VK_IC_8);
    hasher.finalize().into()
}

pub fn compute_vk_fingerprint(vk: &VerifyingKey<Bn254>) -> Result<[u8; 32], String> {
    if vk.gamma_abc_g1.len() != 9 {
        return Err(format!(
            "invalid IC points count for transact v3: expected 9, got {}",
            vk.gamma_abc_g1.len()
        ));
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

pub fn validate_transact_ceremony_vk(vk: &VerifyingKey<Bn254>) -> Result<(), String> {
    let fp = compute_vk_fingerprint(vk)?;
    if fp != TRANSACT_CEREMONY_VK_FINGERPRINT {
        return Err(
            "proving key verifying key does not match canonical ceremony verifying key".to_string(),
        );
    }
    Ok(())
}

pub fn validate_proving_key(pk: &ProvingKey<Bn254>, expected_ic_len: usize) -> Result<(), String> {
    if pk.beta_g1.is_zero() {
        return Err("proving key beta_g1 must not be zero".to_string());
    }
    if pk.delta_g1.is_zero() {
        return Err("proving key delta_g1 must not be zero".to_string());
    }
    if pk.vk.alpha_g1.is_zero() {
        return Err("verifying key alpha_g1 must not be zero".to_string());
    }
    if pk.vk.beta_g2.is_zero() {
        return Err("verifying key beta_g2 must not be zero".to_string());
    }
    if pk.vk.gamma_g2.is_zero() {
        return Err("verifying key gamma_g2 must not be zero".to_string());
    }
    if pk.vk.delta_g2.is_zero() {
        return Err("verifying key delta_g2 must not be zero".to_string());
    }

    if !pk.beta_g1.is_on_curve() || !pk.beta_g1.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proving key beta_g1 is not on curve or in correct subgroup".to_string());
    }
    if !pk.delta_g1.is_on_curve() || !pk.delta_g1.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proving key delta_g1 is not on curve or in correct subgroup".to_string());
    }
    if !pk.vk.alpha_g1.is_on_curve() || !pk.vk.alpha_g1.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key alpha_g1 is not on curve or in correct subgroup".to_string());
    }
    if !pk.vk.beta_g2.is_on_curve() || !pk.vk.beta_g2.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key beta_g2 is not on curve or in correct subgroup".to_string());
    }
    if !pk.vk.gamma_g2.is_on_curve() || !pk.vk.gamma_g2.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key gamma_g2 is not on curve or in correct subgroup".to_string());
    }
    if !pk.vk.delta_g2.is_on_curve() || !pk.vk.delta_g2.is_in_correct_subgroup_assuming_on_curve() {
        return Err("verifying key delta_g2 is not on curve or in correct subgroup".to_string());
    }

    if pk.beta_g1 == pk.delta_g1 {
        return Err("proving key beta_g1 and delta_g1 must not collide".to_string());
    }
    if pk.vk.alpha_g1 == pk.beta_g1 {
        return Err("verifying key alpha_g1 and proving key beta_g1 must not collide".to_string());
    }
    if pk.vk.alpha_g1 == pk.delta_g1 {
        return Err("verifying key alpha_g1 and proving key delta_g1 must not collide".to_string());
    }

    if pk.vk.gamma_g2 == pk.vk.delta_g2 {
        return Err("verifying key gamma_g2 and delta_g2 must not collide".to_string());
    }
    if pk.vk.beta_g2 == pk.vk.delta_g2 {
        return Err("verifying key beta_g2 and delta_g2 must not collide".to_string());
    }
    if pk.vk.beta_g2 == pk.vk.gamma_g2 {
        return Err("verifying key beta_g2 and gamma_g2 must not collide".to_string());
    }

    if pk.vk.gamma_abc_g1.len() != expected_ic_len {
        return Err(format!(
            "invalid IC points count: expected {}, got {}",
            expected_ic_len,
            pk.vk.gamma_abc_g1.len()
        ));
    }
    for (i, ic) in pk.vk.gamma_abc_g1.iter().enumerate() {
        if ic.is_zero() {
            return Err(format!("IC point {i} must not be zero"));
        }
        if !ic.is_on_curve() || !ic.is_in_correct_subgroup_assuming_on_curve() {
            return Err(format!("IC point {i} is not on curve or in correct subgroup"));
        }
    }
    for i in 0..pk.vk.gamma_abc_g1.len() {
        for j in (i + 1)..pk.vk.gamma_abc_g1.len() {
            if pk.vk.gamma_abc_g1[i] == pk.vk.gamma_abc_g1[j] {
                return Err(format!("IC points {i} and {j} must not collide"));
            }
        }
    }

    if !pk.h_query.is_empty() && !pk.h_query.len().is_power_of_two() {
        return Err("h_query length must be a power of two".to_string());
    }

    Ok(())
}

pub fn validate_proof(proof: &Proof<Bn254>) -> Result<(), String> {
    if proof.a == proof.c {
        return Err("proof elements A and C must not collide".to_string());
    }
    if proof.a.is_zero() || proof.b.is_zero() || proof.c.is_zero() {
        return Err("proof elements must not be zero".to_string());
    }
    if !proof.a.is_on_curve() || !proof.a.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proof element A is not on curve or in correct subgroup".to_string());
    }
    if !proof.b.is_on_curve() || !proof.b.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proof element B is not on curve or in correct subgroup".to_string());
    }
    if !proof.c.is_on_curve() || !proof.c.is_in_correct_subgroup_assuming_on_curve() {
        return Err("proof element C is not on curve or in correct subgroup".to_string());
    }
    Ok(())
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
    validate_proving_key(&pk, 6)
        .map_err(|e| JsValue::from_str(&format!("bad proving key: {e}")))?;
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
    validate_proving_key(&pk, 7)
        .map_err(|e| JsValue::from_str(&format!("bad proving key: {e}")))?;
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
    validate_proving_key(&pk, 9)
        .map_err(|e| JsValue::from_str(&format!("bad proving key: {e}")))?;
    validate_transact_ceremony_vk(&pk.vk)
        .map_err(|e| JsValue::from_str(&format!("bad ceremony verifying key: {e}")))?;
    let proof =
        Groth16ProofSystem::prove::<TransactCircuitV3, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;
    validate_proof(&proof)
        .map_err(|e| JsValue::from_str(&format!("invalid proof: {e}")))?;

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

pub fn v3_merkle_path_inner(leaves_json: &str, leaf_index: u32) -> Result<String, String> {
    use privacy::poseidon_circom::v3_merkle_pair;

    let leaves_hex: Vec<String> = serde_json::from_str(leaves_json)
        .map_err(|e| format!("bad leaves json: {e}"))?;
    if (leaf_index as usize) >= leaves_hex.len() {
        return Err("leaf_index out of range".to_string());
    }
    let mut level: Vec<Fr> = Vec::with_capacity(leaves_hex.len());
    for l in &leaves_hex {
        level.push(Fr::from_le_bytes_mod_order(&hex32_inner(l)?));
    }

    let target_leaf = level[leaf_index as usize];
    if target_leaf.is_zero() {
        return Err("target leaf must not be zero".to_string());
    }

    // Zero-subtree hashes, as the on-chain tree pads with.
    let mut zeros = vec![Fr::from(0u64)];
    for k in 0..TX_LEVELS {
        zeros.push(v3_merkle_pair(zeros[k], zeros[k]));
    }
    if zeros.contains(&target_leaf) {
        return Err("target leaf collides with reserved ZERO_HASHES subtree node".to_string());
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
        path.push(hex::encode(fr_to_le_bytes_32(sibling)));
        path_fr.push(sibling);

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

    if target_leaf == root {
        return Err("target leaf collides with tree root".to_string());
    }

    // Bit-fold verification and path-sibling distinctness against target leaf and root
    let mut cur = target_leaf;
    for depth in 0..TX_LEVELS {
        let sibling = path_fr[depth];
        if sibling == target_leaf {
            return Err("path sibling collides with target leaf".to_string());
        }
        if sibling == root {
            return Err("path sibling collides with tree root".to_string());
        }
        let bit = (leaf_index >> depth) & 1;
        if bit == 0 {
            cur = v3_merkle_pair(cur, sibling);
        } else {
            cur = v3_merkle_pair(sibling, cur);
        }
    }
    if cur != root {
        return Err("merkle path fold does not reproduce tree root".to_string());
    }

    Ok(format!(
        "{{\"path\":{},\"root\":\"{}\"}}",
        serde_json::to_string(&path).unwrap(),
        hex::encode(fr_to_le_bytes_32(root))
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
pub fn v3_merkle_path(leaves_json: &str, leaf_index: u32) -> Result<String, JsValue> {
    v3_merkle_path_inner(leaves_json, leaf_index).map_err(|e| JsValue::from_str(&e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::G1Affine;
    use privacy::circuits::{Groth16ProofSystem, TransactCircuitV3, WithdrawCircuitV2};
    use privacy::poseidon_circom::{v3_commit, v3_merkle_pair, v3_pubkey};

    #[test]
    fn test_ceremony_vk_fingerprint_matches_constant() {
        let computed = compute_transact_ceremony_vk_fingerprint();
        assert_eq!(computed, TRANSACT_CEREMONY_VK_FINGERPRINT);
    }

    #[test]
    fn test_validate_proving_key_rejects_zero_curve_elements() {
        let mut rng = StdRng::seed_from_u64(42);
        let circuit = WithdrawCircuitV2::new();
        let (clean_pk, _) = Groth16ProofSystem::setup(circuit, &mut rng).expect("setup");

        assert!(validate_proving_key(&clean_pk, 6).is_ok());

        let mut pk = clean_pk.clone();
        pk.beta_g1 = G1Affine::zero();
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("proving key beta_g1 must not be zero"));

        let mut pk = clean_pk.clone();
        pk.delta_g1 = G1Affine::zero();
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("proving key delta_g1 must not be zero"));

        let mut pk = clean_pk.clone();
        pk.vk.alpha_g1 = G1Affine::zero();
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key alpha_g1 must not be zero"));

        let mut pk = clean_pk.clone();
        pk.vk.beta_g2 = G2Affine::zero();
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key beta_g2 must not be zero"));

        let mut pk = clean_pk.clone();
        pk.vk.gamma_g2 = G2Affine::zero();
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key gamma_g2 must not be zero"));

        let mut pk = clean_pk.clone();
        pk.vk.delta_g2 = G2Affine::zero();
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key delta_g2 must not be zero"));
    }

    #[test]
    fn test_validate_proving_key_rejects_toxic_waste_collisions() {
        let mut rng = StdRng::seed_from_u64(42);
        let circuit = WithdrawCircuitV2::new();
        let (clean_pk, _) = Groth16ProofSystem::setup(circuit, &mut rng).expect("setup");

        let mut pk = clean_pk.clone();
        pk.beta_g1 = pk.delta_g1;
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("proving key beta_g1 and delta_g1 must not collide"));

        let mut pk = clean_pk.clone();
        pk.vk.alpha_g1 = pk.beta_g1;
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key alpha_g1 and proving key beta_g1 must not collide"));

        let mut pk = clean_pk.clone();
        pk.vk.gamma_g2 = pk.vk.delta_g2;
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key gamma_g2 and delta_g2 must not collide"));

        let mut pk = clean_pk.clone();
        pk.vk.beta_g2 = pk.vk.delta_g2;
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key beta_g2 and delta_g2 must not collide"));

        let mut pk = clean_pk.clone();
        pk.vk.beta_g2 = pk.vk.gamma_g2;
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("verifying key beta_g2 and gamma_g2 must not collide"));

        let mut pk = clean_pk.clone();
        pk.vk.gamma_abc_g1[1] = pk.vk.gamma_abc_g1[0];
        let err = validate_proving_key(&pk, 6).unwrap_err();
        assert!(err.contains("IC points 0 and 1 must not collide"));
    }

    #[test]
    fn test_validate_proving_key_rejects_invalid_ic_count() {
        let mut rng = StdRng::seed_from_u64(42);
        let circuit = WithdrawCircuitV2::new();
        let (pk, _) = Groth16ProofSystem::setup(circuit, &mut rng).expect("setup");

        let err = validate_proving_key(&pk, 9).unwrap_err();
        assert!(err.contains("invalid IC points count: expected 9, got 6"));
    }

    #[test]
    fn test_validate_proof_checks() {
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, _) = Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");
        let valid_proof = Proof {
            a: pk.beta_g1,
            b: pk.vk.beta_g2,
            c: pk.delta_g1,
        };

        assert!(validate_proof(&valid_proof).is_ok());

        let mut p = valid_proof.clone();
        p.a = p.c;
        let err = validate_proof(&p).unwrap_err();
        assert!(err.contains("proof elements A and C must not collide"));

        let mut p = valid_proof.clone();
        p.a = G1Affine::zero();
        let err = validate_proof(&p).unwrap_err();
        assert!(err.contains("proof elements must not be zero"));

        let mut p = valid_proof.clone();
        p.b = G2Affine::zero();
        let err = validate_proof(&p).unwrap_err();
        assert!(err.contains("proof elements must not be zero"));

        let mut p = valid_proof.clone();
        p.c = G1Affine::zero();
        let err = validate_proof(&p).unwrap_err();
        assert!(err.contains("proof elements must not be zero"));
    }

    #[test]
    fn test_validate_transact_ceremony_vk_rejects_mismatch() {
        let mut rng = StdRng::seed_from_u64(42);
        let (_, vk) = Groth16ProofSystem::setup(TransactCircuitV3::blank(), &mut rng).expect("setup");
        let err = validate_transact_ceremony_vk(&vk).unwrap_err();
        assert!(err.contains("proving key verifying key does not match canonical ceremony verifying key"));
    }

    #[test]
    fn test_v3_merkle_path_inner_success_and_bit_fold() {
        let leaf0 = hex::encode(fr_to_le_bytes_32(v3_commit(
            Fr::from(100u64),
            v3_pubkey(Fr::from(1u64)),
            Fr::from(2u64),
            Fr::from(0u64),
        )));
        let leaf1 = hex::encode(fr_to_le_bytes_32(v3_commit(
            Fr::from(200u64),
            v3_pubkey(Fr::from(3u64)),
            Fr::from(4u64),
            Fr::from(0u64),
        )));
        let leaves_json = serde_json::to_string(&vec![leaf0, leaf1]).unwrap();

        let out_json = v3_merkle_path_inner(&leaves_json, 0).expect("v3_merkle_path");
        let v: serde_json::Value = serde_json::from_str(&out_json).unwrap();
        let path = v["path"].as_array().unwrap();
        assert_eq!(path.len(), TX_LEVELS);
        assert!(v["root"].as_str().is_some());
    }

    #[test]
    fn test_v3_merkle_path_inner_rejections() {
        let leaf0 = hex::encode(fr_to_le_bytes_32(v3_commit(
            Fr::from(100u64),
            v3_pubkey(Fr::from(1u64)),
            Fr::from(2u64),
            Fr::from(0u64),
        )));
        let leaves_json = serde_json::to_string(&vec![leaf0.clone()]).unwrap();

        // Out of range index
        let err = v3_merkle_path_inner(&leaves_json, 1).unwrap_err();
        assert!(err.contains("leaf_index out of range"));

        // Zero leaf
        let zero_leaf = hex::encode([0u8; 32]);
        let zero_json = serde_json::to_string(&vec![zero_leaf]).unwrap();
        let err = v3_merkle_path_inner(&zero_json, 0).unwrap_err();
        assert!(err.contains("target leaf must not be zero"));

        // Subtree zero-node collision
        let z1 = v3_merkle_pair(Fr::from(0u64), Fr::from(0u64));
        let z1_hex = hex::encode(fr_to_le_bytes_32(z1));
        let z1_json = serde_json::to_string(&vec![z1_hex]).unwrap();
        let err = v3_merkle_path_inner(&z1_json, 0).unwrap_err();
        assert!(err.contains("target leaf collides with reserved ZERO_HASHES subtree node"));

        // Sibling collides with target leaf
        let dup_json = serde_json::to_string(&vec![leaf0.clone(), leaf0]).unwrap();
        let err = v3_merkle_path_inner(&dup_json, 0).unwrap_err();
        assert!(err.contains("path sibling collides with target leaf"));
    }
}
