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
use privacy::poseidon_circom::{v3_commit, v3_merkle_pair, v3_nullifier, v3_pubkey, v3_signature};
use sha2::{Digest, Sha256};


#[cfg(target_arch = "wasm32")]
fn err_msg(s: &str) -> JsValue {
    JsValue::from_str(s)
}

#[cfg(not(target_arch = "wasm32"))]
fn err_msg(_s: &str) -> JsValue {
    JsValue::NULL
}

fn fr_to_le_bytes_32(fr: Fr) -> [u8; 32] {
    let mut v = fr.into_bigint().to_bytes_le();
    v.resize(32, 0);
    let mut o = [0u8; 32];
    o.copy_from_slice(&v[..32]);
    o
}

fn hex32(s: &str) -> Result<[u8; 32], JsValue> {
    let b = hex::decode(s.trim()).map_err(|e| err_msg(&format!("bad hex: {e}")))?;
    if b.len() != 32 {
        return Err(err_msg("expected 32-byte hex"));
    }
    let mut o = [0u8; 32];
    o.copy_from_slice(&b);
    Ok(o)
}

pub const GROTH16_BN254_COMPRESSED_LEN: usize = 128;

#[rustfmt::skip]
pub const ZERO_HASHES: [[u8; 32]; 33] = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [100, 72, 182, 70, 132, 238, 57, 168, 35, 213, 254, 95, 213, 36, 49, 220, 129, 228, 129, 123, 242, 195, 234, 60, 171, 158, 35, 158, 251, 245, 152, 32],
    [225, 241, 177, 96, 68, 119, 164, 103, 240, 141, 198, 157, 203, 68, 26, 38, 236, 167, 132, 245, 111, 26, 48, 223, 99, 34, 177, 205, 61, 103, 105, 16],
    [56, 210, 86, 184, 178, 126, 213, 40, 213, 29, 55, 80, 234, 110, 124, 70, 6, 33, 247, 80, 141, 117, 61, 46, 175, 226, 126, 83, 49, 51, 244, 24],
    [42, 149, 188, 157, 85, 151, 172, 202, 101, 130, 86, 26, 87, 40, 183, 241, 69, 35, 165, 59, 233, 255, 32, 99, 211, 176, 23, 203, 55, 216, 249, 7],
    [85, 63, 24, 57, 22, 236, 92, 123, 77, 173, 178, 148, 140, 197, 153, 166, 7, 41, 243, 93, 76, 31, 99, 201, 245, 179, 70, 135, 94, 207, 148, 43],
    [120, 157, 160, 46, 163, 221, 17, 29, 97, 83, 185, 81, 105, 30, 215, 254, 188, 225, 169, 204, 34, 125, 234, 70, 150, 69, 102, 166, 197, 147, 238, 45],
    [157, 52, 135, 60, 190, 170, 164, 168, 127, 172, 181, 140, 168, 21, 5, 139, 123, 89, 57, 182, 30, 96, 207, 130, 233, 132, 43, 162, 229, 149, 130, 7],
    [97, 204, 243, 153, 58, 190, 76, 68, 26, 33, 65, 74, 39, 46, 107, 97, 42, 71, 100, 69, 134, 236, 27, 80, 166, 39, 96, 143, 241, 229, 165, 47],
    [71, 215, 252, 20, 166, 86, 33, 62, 171, 40, 226, 227, 204, 122, 94, 228, 102, 31, 148, 158, 56, 128, 183, 236, 33, 253, 216, 208, 118, 67, 136, 14],
    [242, 10, 25, 218, 229, 117, 97, 222, 51, 53, 113, 87, 249, 146, 88, 249, 105, 180, 46, 165, 209, 122, 113, 40, 30, 79, 73, 114, 218, 1, 114, 27],
    [54, 118, 125, 206, 250, 107, 188, 190, 181, 8, 8, 101, 228, 225, 230, 166, 25, 152, 36, 1, 178, 192, 0, 82, 56, 54, 94, 114, 34, 136, 141, 31],
    [90, 248, 181, 113, 4, 154, 135, 208, 168, 136, 207, 42, 161, 176, 98, 97, 251, 252, 140, 186, 137, 21, 112, 185, 175, 75, 145, 108, 246, 130, 93, 44],
    [208, 191, 191, 224, 112, 242, 88, 100, 100, 244, 19, 161, 170, 196, 245, 78, 19, 161, 63, 223, 90, 127, 149, 32, 184, 11, 148, 160, 72, 65, 197, 20],
    [12, 232, 235, 244, 75, 142, 17, 22, 212, 137, 173, 140, 88, 37, 190, 17, 175, 185, 216, 68, 238, 192, 16, 30, 150, 111, 152, 47, 177, 51, 13, 25],
    [146, 108, 224, 37, 147, 100, 179, 165, 10, 81, 175, 150, 101, 174, 103, 17, 237, 115, 173, 20, 73, 53, 23, 172, 82, 65, 112, 206, 169, 138, 249, 34],
    [35, 115, 186, 139, 211, 83, 183, 248, 238, 204, 110, 198, 41, 111, 82, 90, 87, 106, 191, 114, 141, 34, 111, 159, 11, 136, 229, 108, 155, 124, 124, 42],
    [146, 185, 54, 63, 100, 221, 117, 77, 149, 139, 152, 194, 201, 67, 0, 71, 252, 63, 70, 77, 193, 249, 122, 198, 193, 142, 105, 88, 229, 134, 129, 46],
    [15, 241, 31, 28, 157, 36, 70, 53, 39, 146, 115, 100, 173, 110, 239, 138, 148, 174, 13, 5, 207, 200, 226, 73, 171, 78, 154, 30, 87, 197, 87, 15],
    [202, 44, 247, 52, 97, 227, 156, 60, 228, 70, 125, 105, 16, 227, 120, 254, 28, 14, 128, 136, 67, 61, 246, 213, 74, 85, 251, 181, 103, 238, 48, 24],
    [62, 31, 25, 34, 223, 182, 113, 211, 249, 18, 247, 234, 70, 30, 10, 136, 238, 132, 143, 221, 225, 43, 108, 24, 171, 26, 210, 197, 106, 231, 52, 33],
    [177, 165, 145, 219, 243, 141, 143, 143, 168, 58, 238, 88, 201, 216, 81, 192, 176, 89, 56, 243, 102, 216, 235, 254, 79, 188, 78, 132, 236, 144, 223, 25],
    [43, 229, 239, 34, 247, 5, 140, 100, 180, 18, 73, 239, 147, 14, 175, 116, 45, 133, 132, 253, 174, 105, 30, 152, 135, 7, 92, 107, 166, 162, 204, 24],
    [141, 83, 210, 73, 69, 100, 5, 223, 250, 131, 173, 239, 242, 56, 131, 98, 58, 71, 79, 213, 210, 4, 19, 77, 27, 13, 35, 21, 148, 144, 136, 35],
    [64, 213, 158, 82, 228, 115, 230, 150, 29, 11, 141, 156, 44, 175, 162, 102, 232, 77, 41, 181, 67, 245, 232, 233, 192, 108, 123, 169, 180, 31, 23, 39],
    [33, 174, 230, 221, 150, 150, 213, 248, 229, 131, 37, 57, 185, 48, 178, 220, 40, 13, 252, 116, 188, 160, 17, 87, 253, 41, 246, 64, 5, 101, 246, 47],
    [24, 21, 97, 206, 48, 38, 147, 105, 86, 215, 173, 246, 104, 81, 173, 224, 162, 120, 119, 39, 245, 247, 2, 89, 233, 145, 212, 67, 241, 88, 12, 18],
    [149, 55, 72, 121, 210, 101, 214, 162, 29, 162, 101, 165, 160, 149, 196, 30, 7, 3, 219, 229, 213, 83, 248, 123, 176, 33, 63, 13, 183, 254, 33, 31],
    [210, 114, 138, 225, 221, 161, 177, 139, 150, 158, 138, 6, 104, 231, 38, 168, 35, 134, 106, 246, 192, 140, 99, 76, 225, 53, 19, 167, 95, 144, 190, 36],
    [109, 194, 218, 83, 229, 116, 76, 116, 40, 195, 101, 29, 130, 243, 126, 89, 205, 212, 87, 173, 222, 234, 12, 197, 145, 116, 209, 46, 182, 102, 134, 15],
    [239, 89, 25, 14, 35, 42, 26, 61, 180, 140, 224, 106, 63, 122, 122, 78, 89, 65, 28, 26, 74, 63, 65, 52, 176, 152, 45, 245, 107, 212, 24, 9],
    [242, 95, 92, 55, 173, 19, 133, 18, 101, 90, 252, 10, 13, 249, 38, 46, 250, 77, 64, 94, 100, 23, 105, 231, 205, 158, 71, 76, 27, 176, 190, 27],
    [217, 234, 52, 151, 76, 24, 142, 172, 213, 25, 177, 42, 146, 185, 96, 213, 30, 85, 245, 223, 97, 108, 122, 161, 66, 126, 37, 142, 197, 161, 104, 47],
];

fn is_reserved_zero_hash(b: &[u8; 32]) -> bool {
    ZERO_HASHES.iter().any(|zh| zh == b)
}

fn is_degenerate_pubkey(b: &[u8; 32]) -> bool {
    if b == &[0u8; 32] {
        return true;
    }
    let zero_fr = Fr::from(0u64);
    let v2_zero_pk = fr_to_le_bytes_32(poseidon_pubkey(zero_fr));
    let v3_zero_pk = fr_to_le_bytes_32(v3_pubkey(zero_fr));
    b == &v2_zero_pk || b == &v3_zero_pk
}

fn validate_canonical_scalar(bytes: &[u8; 32]) -> Result<Fr, JsValue> {
    if bytes == &[0u8; 32] {
        return Err(err_msg("zero scalar rejected"));
    }
    if is_reserved_zero_hash(bytes) {
        return Err(err_msg("reserved zero hash rejected"));
    }
    let fr = Fr::from_le_bytes_mod_order(bytes);
    if fr == Fr::from(0u64) {
        return Err(err_msg("zero scalar rejected"));
    }
    if &fr_to_le_bytes_32(fr) != bytes {
        return Err(err_msg("non-canonical scalar rejected"));
    }
    Ok(fr)
}

fn validate_pubkey_or_blinding(bytes: &[u8; 32], label: &str) -> Result<Fr, JsValue> {
    if bytes == &[0u8; 32] {
        return Err(err_msg(&format!("{label} cannot be all-zero")));
    }
    if is_degenerate_pubkey(bytes) {
        return Err(err_msg(&format!("{label} is degenerate zero-key public key")));
    }
    if is_reserved_zero_hash(bytes) {
        return Err(err_msg(&format!("{label} is reserved zero hash")));
    }
    let fr = Fr::from_le_bytes_mod_order(bytes);
    if &fr_to_le_bytes_32(fr) != bytes {
        return Err(err_msg(&format!("{label} is non-canonical field element")));
    }
    Ok(fr)
}

fn validate_proving_key(pk: &ProvingKey<Bn254>) -> Result<(), JsValue> {
    if pk.vk.alpha_g1.is_zero()
        || pk.vk.beta_g2.is_zero()
        || pk.vk.gamma_g2.is_zero()
        || pk.vk.delta_g2.is_zero()
        || pk.vk.gamma_abc_g1.is_empty()
        || pk.vk.gamma_abc_g1.iter().any(|p| p.is_zero())
    {
        return Err(err_msg("proving key vk contains point at infinity"));
    }
    Ok(())
}

fn validate_proof(proof: &ark_groth16::Proof<Bn254>) -> Result<(), JsValue> {
    if proof.a.is_zero() || proof.b.is_zero() || proof.c.is_zero() {
        return Err(err_msg("proof contains point at infinity"));
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
    let rand_fr = validate_pubkey_or_blinding(&randomness, "randomness")?;
    let recipient = hex32(recipient_hex)?;
    let recip_fr = validate_pubkey_or_blinding(&recipient, "recipient")?;
    let c = poseidon_commit(
        Fr::from(amount),
        rand_fr,
        recip_fr,
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
    let raw = hex32(privkey_hex)?;
    let sk = validate_canonical_scalar(&raw)?;
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
    let raw_priv = hex32(privkey_hex)?;
    let sk = validate_canonical_scalar(&raw_priv)?;
    let raw_blinding = hex32(blinding_hex)?;
    let blinding_fr = validate_pubkey_or_blinding(&raw_blinding, "blinding")?;
    let raw_asset = hex32(asset_id_hex)?;
    let c = poseidon_commit_spend(
        Fr::from(amount),
        poseidon_pubkey(sk),
        blinding_fr,
        Fr::from_le_bytes_mod_order(&raw_asset),
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
        return Err(err_msg("path and indices length mismatch"));
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
    let blinding_fr = validate_pubkey_or_blinding(&blinding, "blinding")?;
    let privkey = hex32(privkey_hex)?;
    let sk = validate_canonical_scalar(&privkey)?;
    let asset_id = hex32(asset_id_hex)?;
    let dest_recipient = hex32(dest_recipient_hex)?;

    let path_hex: Vec<String> = serde_json::from_str(path_hex_json)
        .map_err(|e| err_msg(&format!("bad path json: {e}")))?;
    let indices: Vec<bool> = serde_json::from_str(indices_json)
        .map_err(|e| err_msg(&format!("bad indices json: {e}")))?;
    let merkle_path = merkle_path_from(&path_hex, &indices)?;

    let leaf_index = leaf_index_from(&indices);

    let commitment_fr = poseidon_commit_spend(
        Fr::from(amount),
        poseidon_pubkey(sk),
        blinding_fr,
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
        .map_err(|e| err_msg(&format!("bad proving key: {e}")))?;
    validate_proving_key(&pk)?;

    let proof =
        Groth16ProofSystem::prove::<WithdrawCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| err_msg(&format!("prove failed: {e}")))?;
    validate_proof(&proof)?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| err_msg(&format!("serialize failed: {e}")))?;
    if proof_bytes.len() != GROTH16_BN254_COMPRESSED_LEN {
        return Err(err_msg("invalid compressed proof length"));
    }

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
        .map_err(|e| err_msg(&format!("bad inputs json: {e}")))?;
    let outputs: Vec<TransferOutputV2> = serde_json::from_str(outputs_json)
        .map_err(|e| err_msg(&format!("bad outputs json: {e}")))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(err_msg(
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
        let blinding_fr = validate_pubkey_or_blinding(&blinding, "input blinding")?;
        let privkey = hex32(&inp.privkey_hex)?;
        let sk = validate_canonical_scalar(&privkey)?;
        let commitment_fr = poseidon_commit_spend(
            Fr::from(inp.amount),
            poseidon_pubkey(sk),
            blinding_fr,
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
        let blinding_fr = validate_pubkey_or_blinding(&blinding, "output blinding")?;
        let pubkey = hex32(&out.pubkey_hex)?;
        let pubkey_fr = validate_pubkey_or_blinding(&pubkey, "output pubkey")?;
        let commitment_fr = poseidon_commit_spend(
            Fr::from(out.amount),
            pubkey_fr,
            blinding_fr,
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
        .map_err(|e| err_msg(&format!("bad proving key: {e}")))?;
    validate_proving_key(&pk)?;

    let proof =
        Groth16ProofSystem::prove::<TransferCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| err_msg(&format!("prove failed: {e}")))?;
    validate_proof(&proof)?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| err_msg(&format!("serialize failed: {e}")))?;
    if proof_bytes.len() != GROTH16_BN254_COMPRESSED_LEN {
        return Err(err_msg("invalid compressed proof length"));
    }

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
    let raw = hex32(privkey_hex)?;
    let sk = validate_canonical_scalar(&raw)?;
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
    let raw_pk = hex32(pubkey_hex)?;
    let pubkey_fr = validate_pubkey_or_blinding(&raw_pk, "pubkey")?;
    let raw_bl = hex32(blinding_hex)?;
    let blinding_fr = validate_pubkey_or_blinding(&raw_bl, "blinding")?;
    let c = v3_commit(
        Fr::from(amount),
        pubkey_fr,
        blinding_fr,
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
    let raw_pk = hex32(pubkey_hex)?;
    let pubkey_fr = validate_pubkey_or_blinding(&raw_pk, "pubkey")?;
    let raw_bl = hex32(blinding_hex)?;
    let blinding_fr = validate_pubkey_or_blinding(&raw_bl, "blinding")?;
    let raw_asset = hex32(asset_id_hex)?;
    let c = v3_commit(
        Fr::from(amount),
        pubkey_fr,
        blinding_fr,
        Fr::from_le_bytes_mod_order(&raw_asset),
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
        return Err(err_msg(
            "positive ext_amount: deposits go through deposit_note, not transact",
        ));
    }
    let root = hex32(root_hex)?;
    let recipient = hex32(recipient_hex)?;

    let inputs: Vec<TransactInputNote> = serde_json::from_str(inputs_json)
        .map_err(|e| err_msg(&format!("bad inputs json: {e}")))?;
    let outputs: Vec<TransactOutputNote> = serde_json::from_str(outputs_json)
        .map_err(|e| err_msg(&format!("bad outputs json: {e}")))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(err_msg("transact is fixed 2-in/2-out"));
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
        let sk = validate_canonical_scalar(&privkey)?;
        let blinding = hex32(&inp.blinding_hex)?;
        let blinding_fr = validate_pubkey_or_blinding(&blinding, "input blinding")?;
        if inp.path_hex.len() != TX_LEVELS {
            return Err(err_msg(&format!(
                "input path must have {TX_LEVELS} siblings, got {}",
                inp.path_hex.len()
            )));
        }
        let mut path = Vec::with_capacity(TX_LEVELS);
        for sib in &inp.path_hex {
            path.push(hex32(sib)?);
        }

        let c = v3_commit(
            Fr::from(inp.amount),
            v3_pubkey(sk),
            blinding_fr,
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
        let pubkey_fr = validate_pubkey_or_blinding(&pubkey, "output pubkey")?;
        let blinding = hex32(&outp.blinding_hex)?;
        let blinding_fr = validate_pubkey_or_blinding(&blinding, "output blinding")?;
        let oc = v3_commit(
            Fr::from(outp.amount),
            pubkey_fr,
            blinding_fr,
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
        .map_err(|e| err_msg(&format!("bad proving key: {e}")))?;
    validate_proving_key(&pk)?;

    let proof =
        Groth16ProofSystem::prove::<TransactCircuitV3, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| err_msg(&format!("prove failed: {e}")))?;
    validate_proof(&proof)?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| err_msg(&format!("serialize failed: {e}")))?;
    if proof_bytes.len() != GROTH16_BN254_COMPRESSED_LEN {
        return Err(err_msg("invalid compressed proof length"));
    }

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
pub fn v3_merkle_path(leaves_json: &str, leaf_index: u32) -> Result<String, JsValue> {
    use privacy::poseidon_circom::v3_merkle_pair;

    let leaves_hex: Vec<String> = serde_json::from_str(leaves_json)
        .map_err(|e| err_msg(&format!("bad leaves json: {e}")))?;
    if (leaf_index as usize) >= leaves_hex.len() {
        return Err(err_msg("leaf_index out of range"));
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
