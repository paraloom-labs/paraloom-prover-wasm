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

pub const DISALLOWED_WITHDRAWAL_RECIPIENTS: &[[u8; 32]] = &[
    // System program / null address
    [0u8; 32],
    // Protocol PDAs
    [
        197, 155, 251, 42, 196, 183, 226, 109, 235, 249, 136, 182, 177, 79, 174, 12, 10, 122, 228,
        36, 246, 159, 142, 8, 110, 3, 200, 9, 109, 114, 252, 160,
    ], // bridge_vault
    [
        209, 64, 216, 14, 115, 15, 95, 129, 35, 107, 43, 135, 195, 180, 53, 49, 45, 158, 236, 38,
        11, 206, 184, 100, 198, 254, 176, 51, 213, 102, 249, 145,
    ], // slashed_funds_vault
    [
        141, 44, 180, 73, 23, 185, 229, 16, 75, 80, 98, 188, 138, 232, 230, 3, 31, 40, 65, 134, 6,
        123, 221, 160, 146, 143, 93, 106, 109, 137, 78, 147,
    ], // stake_vault_authority
    [
        87, 54, 40, 230, 215, 224, 170, 146, 61, 8, 146, 52, 185, 11, 81, 74, 93, 50, 71, 174, 38,
        101, 161, 141, 53, 56, 162, 253, 177, 191, 124, 228,
    ], // asset_vault_authority
    [
        119, 136, 95, 13, 92, 182, 101, 201, 170, 160, 62, 219, 170, 89, 84, 16, 34, 180, 200, 77,
        69, 71, 105, 30, 233, 116, 190, 2, 178, 210, 203, 21,
    ], // bridge_state
    [
        183, 131, 247, 59, 176, 21, 32, 214, 150, 92, 235, 37, 51, 91, 210, 66, 160, 217, 65, 40,
        77, 59, 128, 40, 98, 228, 160, 83, 210, 56, 8, 146,
    ], // merkle_tree
    [
        114, 21, 92, 212, 16, 163, 61, 159, 175, 145, 79, 253, 140, 146, 114, 188, 143, 70, 104,
        174, 53, 113, 45, 142, 67, 176, 112, 237, 22, 141, 105, 106,
    ], // validator_registry
    [
        238, 134, 82, 123, 157, 89, 165, 0, 134, 4, 89, 247, 86, 109, 9, 55, 26, 105, 56, 115, 172,
        124, 144, 57, 78, 147, 14, 58, 233, 152, 194, 189,
    ], // stake_token_vault
    // Reserved programs, sysvars, and mint
    [
        114, 25, 81, 135, 203, 105, 61, 30, 20, 238, 159, 213, 206, 216, 186, 93, 44, 129, 255,
        169, 217, 199, 244, 242, 76, 132, 55, 227, 218, 88, 6, 196,
    ], // PARALOOM_PROGRAM_ID
    [
        6, 221, 246, 225, 215, 101, 161, 147, 217, 203, 225, 70, 206, 235, 121, 172, 28, 180, 133,
        237, 95, 91, 55, 145, 58, 140, 245, 133, 126, 255, 0, 169,
    ], // SPL_TOKEN_PROGRAM_ID
    [
        6, 221, 246, 225, 238, 117, 143, 222, 24, 66, 93, 188, 228, 108, 205, 218, 182, 26, 252,
        77, 131, 185, 13, 39, 254, 189, 249, 40, 216, 161, 139, 252,
    ], // SPL_TOKEN_2022_PROGRAM_ID
    [
        140, 151, 37, 143, 78, 36, 137, 241, 187, 61, 16, 41, 20, 142, 13, 131, 11, 90, 19, 153,
        218, 255, 16, 132, 4, 142, 123, 216, 219, 233, 248, 89,
    ], // ASSOCIATED_TOKEN_PROGRAM_ID
    [
        2, 168, 246, 145, 78, 136, 161, 176, 226, 16, 21, 62, 247, 99, 174, 43, 0, 194, 185, 61,
        22, 193, 36, 210, 192, 83, 122, 16, 4, 128, 0, 0,
    ], // BPF_LOADER_UPGRADEABLE_ID
    [
        6, 167, 213, 23, 25, 44, 92, 81, 33, 140, 201, 76, 61, 74, 241, 127, 88, 218, 238, 8, 155,
        161, 253, 68, 227, 219, 217, 138, 0, 0, 0, 0,
    ], // RENT_SYSVAR_ID
    [
        6, 167, 213, 23, 24, 199, 116, 201, 40, 86, 99, 152, 105, 29, 94, 182, 139, 94, 184, 163,
        155, 75, 109, 92, 115, 85, 91, 33, 0, 0, 0, 0,
    ], // CLOCK_SYSVAR_ID
    [
        6, 155, 136, 87, 254, 171, 129, 132, 251, 104, 127, 99, 70, 24, 192, 53, 218, 196, 57, 220,
        26, 235, 59, 85, 152, 160, 240, 0, 0, 0, 0, 1,
    ], // WSOL_NATIVE_MINT
];

pub fn is_disallowed_withdrawal_recipient(addr: &[u8; 32]) -> bool {
    DISALLOWED_WITHDRAWAL_RECIPIENTS.contains(addr)
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

pub fn validate_merkle_path(
    path_siblings: &[[u8; 32]],
    nullifiers: &[[u8; 32]],
    output_commitments: &[[u8; 32]],
    asset_id: &[u8; 32],
    withdrawal_recipient: Option<&[u8; 32]>,
) -> Result<(), String> {
    for (d1, s1) in path_siblings.iter().enumerate() {
        for (d2, s2) in path_siblings.iter().enumerate().skip(d1 + 1) {
            if s1 == s2 {
                return Err(format!(
                    "duplicate sibling hash in Merkle path across levels {d1} and {d2}"
                ));
            }
        }
    }

    for sib in path_siblings {
        for nf in nullifiers {
            if sib == nf {
                return Err("Merkle path sibling collides with nullifier".to_string());
            }
        }
        for oc in output_commitments {
            if sib == oc {
                return Err("Merkle path sibling collides with output commitment".to_string());
            }
        }
        if asset_id != &[0u8; 32] && sib == asset_id {
            return Err("Merkle path sibling collides with asset_id".to_string());
        }
        if let Some(recipient) = withdrawal_recipient {
            if sib == recipient {
                return Err("Merkle path sibling collides with withdrawal recipient".to_string());
            }
        }
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
    let root = hex32_inner(root_hex)?;
    let blinding = hex32_inner(blinding_hex)?;
    let privkey = hex32_inner(privkey_hex)?;
    let asset_id = hex32_inner(asset_id_hex)?;
    let dest_recipient = hex32_inner(dest_recipient_hex)?;

    if is_disallowed_withdrawal_recipient(&dest_recipient) {
        return Err(
            "disallowed withdrawal recipient: cannot withdraw to protocol PDA, program, sysvar, or mint".to_string(),
        );
    }

    let path_hex: Vec<String> =
        serde_json::from_str(path_hex_json).map_err(|e| format!("bad path json: {e}"))?;
    let indices: Vec<bool> =
        serde_json::from_str(indices_json).map_err(|e| format!("bad indices json: {e}"))?;
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

    let path_siblings: Vec<[u8; 32]> = merkle_path.iter().map(|(sib, _)| *sib).collect();
    validate_merkle_path(
        &path_siblings,
        &[nullifier],
        &[],
        &asset_id,
        Some(&dest_recipient),
    )?;

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

    for input_path in &input_paths {
        let siblings: Vec<[u8; 32]> = input_path.iter().map(|(sib, _)| *sib).collect();
        validate_merkle_path(&siblings, &nullifiers, &output_commitments, &asset_id, None)?;
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

    if ext_amount < 0 && is_disallowed_withdrawal_recipient(&recipient) {
        return Err(
            "disallowed withdrawal recipient: cannot withdraw to protocol PDA, program, sysvar, or mint".to_string(),
        );
    }

    let inputs: Vec<TransactInputNote> =
        serde_json::from_str(inputs_json).map_err(|e| format!("bad inputs json: {e}"))?;
    let outputs: Vec<TransactOutputNote> =
        serde_json::from_str(outputs_json).map_err(|e| format!("bad outputs json: {e}"))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err("transact is fixed 2-in/2-out".to_string());
    }

    if ext_amount < 0 && outputs[1].amount == 0 {
        let pk0 = hex32_inner(&outputs[0].pubkey_hex)?;
        let pk1 = hex32_inner(&outputs[1].pubkey_hex)?;
        if pk0 != pk1 {
            return Err(
                "withdrawal change output must share pubkey with primary output".to_string(),
            );
        }
    }

    // The shielded asset: all-zero for native SOL, or `mint_to_asset(mint)` for
    // a shielded SPL note (#779). All notes in one transact share one asset.
    let asset_id_bytes = hex32_inner(asset_id_hex)?;
    let asset = Fr::from_le_bytes_mod_order(&asset_id_bytes);

    let mut in_amounts = Vec::new();
    let mut in_privkeys = Vec::new();
    let mut in_blindings = Vec::new();
    let mut in_leaf_indices = Vec::new();
    let mut in_paths = Vec::new();
    let mut parsed_paths = Vec::new();
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

        if inp.amount == 0 && inp.leaf_index != 0 {
            return Err("dummy input note with zero amount must have leaf_index 0".to_string());
        }

        let mut path = Vec::with_capacity(TX_LEVELS);
        for (lvl, sib_str) in inp.path_hex.iter().enumerate() {
            let sib = hex32_inner(sib_str)?;
            if inp.amount == 0 && lvl >= 1 && sib == [0u8; 32] {
                return Err(
                    "dummy input note cannot have zero hash sibling at level > 0".to_string(),
                );
            }
            path.push(sib);
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

    let withdrawal_recipient = if ext_amount < 0 {
        Some(&recipient)
    } else {
        None
    };

    for path in &parsed_paths {
        validate_merkle_path(
            path,
            &nullifiers,
            &output_commitments,
            &asset_id_bytes,
            withdrawal_recipient,
        )?;
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

    fn dummy_path(depth: usize) -> Vec<String> {
        (0..depth)
            .map(|i| {
                let mut b = [0u8; 32];
                b[0] = (i + 1) as u8;
                hex::encode(b)
            })
            .collect()
    }

    #[test]
    fn test_is_disallowed_withdrawal_recipient_all_17() {
        assert_eq!(DISALLOWED_WITHDRAWAL_RECIPIENTS.len(), 17);
        for addr in DISALLOWED_WITHDRAWAL_RECIPIENTS {
            assert!(
                is_disallowed_withdrawal_recipient(addr),
                "Address {:?} should be disallowed",
                addr
            );
        }

        let user_addr = [3u8; 32];
        assert!(!is_disallowed_withdrawal_recipient(&user_addr));
    }

    #[test]
    fn test_prove_withdrawal_v2_rejects_disallowed_recipients() {
        let path = dummy_path(32);
        let indices = vec![false; 32];
        let path_json = serde_json::to_string(&path).unwrap();
        let indices_json = serde_json::to_string(&indices).unwrap();

        for disallowed in DISALLOWED_WITHDRAWAL_RECIPIENTS {
            let res = prove_withdrawal_v2_inner(
                &[],
                &hex::encode([1u8; 32]),
                100,
                &hex::encode([2u8; 32]),
                &hex::encode([3u8; 32]),
                &hex::encode([0u8; 32]),
                &hex::encode(disallowed),
                &path_json,
                &indices_json,
            );
            assert!(res.is_err());
            assert!(
                res.unwrap_err().contains("disallowed withdrawal recipient"),
                "Expected disallowed recipient error for {:?}",
                disallowed
            );
        }
    }

    #[test]
    fn test_prove_withdrawal_v2_rejects_duplicate_and_colliding_siblings() {
        let indices = vec![false; 32];
        let indices_json = serde_json::to_string(&indices).unwrap();

        // 1. Duplicate sibling across levels
        let mut dup_path = dummy_path(32);
        dup_path[5] = dup_path[2].clone();
        let res_dup = prove_withdrawal_v2_inner(
            &[],
            &hex::encode([1u8; 32]),
            100,
            &hex::encode([2u8; 32]),
            &hex::encode([3u8; 32]),
            &hex::encode([0u8; 32]),
            &hex::encode([99u8; 32]),
            &serde_json::to_string(&dup_path).unwrap(),
            &indices_json,
        );
        assert!(res_dup.is_err());
        assert!(res_dup.unwrap_err().contains("duplicate sibling hash"));

        // 2. Collision with withdrawal recipient
        let mut rec_path = dummy_path(32);
        rec_path[3] = hex::encode([99u8; 32]);
        let res_rec = prove_withdrawal_v2_inner(
            &[],
            &hex::encode([1u8; 32]),
            100,
            &hex::encode([2u8; 32]),
            &hex::encode([3u8; 32]),
            &hex::encode([0u8; 32]),
            &hex::encode([99u8; 32]),
            &serde_json::to_string(&rec_path).unwrap(),
            &indices_json,
        );
        assert!(res_rec.is_err());
        assert!(res_rec
            .unwrap_err()
            .contains("Merkle path sibling collides with withdrawal recipient"));

        // 3. Collision with non-zero asset_id
        let asset_id = [77u8; 32];
        let mut asset_path = dummy_path(32);
        asset_path[4] = hex::encode(asset_id);
        let res_asset = prove_withdrawal_v2_inner(
            &[],
            &hex::encode([1u8; 32]),
            100,
            &hex::encode([2u8; 32]),
            &hex::encode([3u8; 32]),
            &hex::encode(asset_id),
            &hex::encode([99u8; 32]),
            &serde_json::to_string(&asset_path).unwrap(),
            &indices_json,
        );
        assert!(res_asset.is_err());
        assert!(res_asset
            .unwrap_err()
            .contains("Merkle path sibling collides with asset_id"));
    }

    #[test]
    fn test_prove_transfer_v2_rejects_duplicate_and_colliding_siblings() {
        let indices = vec![false; 32];

        // 1. Duplicate sibling
        let mut dup_path = dummy_path(32);
        dup_path[4] = dup_path[1].clone();
        let inps_dup = vec![
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                path_hex: dup_path,
                indices: indices.clone(),
            },
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                path_hex: dummy_path(32),
                indices: indices.clone(),
            },
        ];
        let outs = vec![
            TransferOutputV2 {
                amount: 50,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([31u8; 32]),
            },
            TransferOutputV2 {
                amount: 50,
                pubkey_hex: hex::encode([40u8; 32]),
                blinding_hex: hex::encode([41u8; 32]),
            },
        ];
        let res_dup = prove_transfer_v2_inner(
            &[],
            &hex::encode([1u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps_dup).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        assert!(res_dup.is_err());
        assert!(res_dup.unwrap_err().contains("duplicate sibling hash"));

        // 2. Collision with asset_id
        let asset_id = [88u8; 32];
        let mut asset_path = dummy_path(32);
        asset_path[6] = hex::encode(asset_id);
        let inps_asset = vec![
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                path_hex: asset_path,
                indices: indices.clone(),
            },
            TransferInputV2 {
                amount: 50,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                path_hex: dummy_path(32),
                indices,
            },
        ];
        let res_asset = prove_transfer_v2_inner(
            &[],
            &hex::encode([1u8; 32]),
            &hex::encode(asset_id),
            &serde_json::to_string(&inps_asset).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        assert!(res_asset.is_err());
        assert!(res_asset
            .unwrap_err()
            .contains("Merkle path sibling collides with asset_id"));
    }

    #[test]
    fn test_prove_transact_rejects_disallowed_recipient_on_withdrawal() {
        let inps = vec![
            TransactInputNote {
                amount: 100,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
        ];
        let outs = vec![
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([31u8; 32]),
            },
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([41u8; 32]),
            },
        ];
        let inps_json = serde_json::to_string(&inps).unwrap();
        let outs_json = serde_json::to_string(&outs).unwrap();

        for disallowed in DISALLOWED_WITHDRAWAL_RECIPIENTS {
            let res = prove_transact_inner(
                &[],
                &hex::encode([1u8; 32]),
                -50,
                &hex::encode(disallowed),
                &hex::encode([0u8; 32]),
                &inps_json,
                &outs_json,
            );
            assert!(res.is_err());
            assert!(
                res.unwrap_err().contains("disallowed withdrawal recipient"),
                "Expected disallowed recipient error for {:?}",
                disallowed
            );
        }

        // When ext_amount == 0, disallowed recipient check is not performed
        let res_zero = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            0,
            &hex::encode([0u8; 32]),
            &hex::encode([0u8; 32]),
            &inps_json,
            &outs_json,
        );
        // Fails at proving key deserialization, NOT at recipient check
        assert!(res_zero.is_err());
        assert!(!res_zero
            .unwrap_err()
            .contains("disallowed withdrawal recipient"));
    }

    #[test]
    fn test_prove_transact_dummy_inputs_validation() {
        // 1. Dummy input with leaf_index != 0 rejected
        let inps_nonzero_leaf = vec![
            TransactInputNote {
                amount: 100,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 5, // Invalid: must be 0
                path_hex: dummy_path(TX_LEVELS),
            },
        ];
        let outs = vec![
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([31u8; 32]),
            },
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([40u8; 32]),
                blinding_hex: hex::encode([41u8; 32]),
            },
        ];
        let res = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            0,
            &hex::encode([0u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps_nonzero_leaf).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        assert!(res.is_err());
        assert!(res
            .unwrap_err()
            .contains("dummy input note with zero amount must have leaf_index 0"));

        // 2. Dummy input with raw zero sibling at level >= 1 rejected
        let mut zero_sib_path = dummy_path(TX_LEVELS);
        zero_sib_path[2] = hex::encode([0u8; 32]); // level 2 is zero
        let inps_zero_sib = vec![
            TransactInputNote {
                amount: 100,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 0,
                path_hex: zero_sib_path,
            },
        ];
        let res2 = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            0,
            &hex::encode([0u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps_zero_sib).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        assert!(res2.is_err());
        assert!(res2
            .unwrap_err()
            .contains("dummy input note cannot have zero hash sibling at level > 0"));

        // 3. Dummy input with raw zero sibling at level 0 is allowed
        let mut zero_level0_path = dummy_path(TX_LEVELS);
        zero_level0_path[0] = hex::encode([0u8; 32]); // level 0 can be zero
        let inps_level0_zero = vec![
            TransactInputNote {
                amount: 100,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 0,
                path_hex: zero_level0_path,
            },
        ];
        let res3 = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            0,
            &hex::encode([0u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps_level0_zero).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        assert!(res3.is_err());
        assert!(!res3
            .unwrap_err()
            .contains("dummy input note cannot have zero hash sibling"));
    }

    #[test]
    fn test_prove_transact_withdrawal_filler_output_pubkey_validation() {
        let inps = vec![
            TransactInputNote {
                amount: 100,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
        ];

        // Mismatched pubkey on outputs[1] when amount == 0 and ext_amount < 0
        let outs_mismatch = vec![
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([31u8; 32]),
            },
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([40u8; 32]), // Mismatch!
                blinding_hex: hex::encode([41u8; 32]),
            },
        ];
        let res = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            -50,
            &hex::encode([99u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps).unwrap(),
            &serde_json::to_string(&outs_mismatch).unwrap(),
        );
        assert!(res.is_err());
        assert!(res
            .unwrap_err()
            .contains("withdrawal change output must share pubkey with primary output"));

        // Matching pubkey on outputs[1] when amount == 0 and ext_amount < 0
        let outs_matching = vec![
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([31u8; 32]),
            },
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([30u8; 32]), // Matching!
                blinding_hex: hex::encode([41u8; 32]),
            },
        ];
        let res2 = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            -50,
            &hex::encode([99u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps).unwrap(),
            &serde_json::to_string(&outs_matching).unwrap(),
        );
        assert!(res2.is_err());
        assert!(!res2
            .unwrap_err()
            .contains("withdrawal change output must share pubkey with primary output"));

        // When ext_amount == 0, mismatched pubkeys are allowed
        let res3 = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            0,
            &hex::encode([0u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps).unwrap(),
            &serde_json::to_string(&outs_mismatch).unwrap(),
        );
        assert!(res3.is_err());
        assert!(!res3
            .unwrap_err()
            .contains("withdrawal change output must share pubkey with primary output"));
    }

    #[test]
    fn test_prove_transact_merkle_path_duplicate_and_colliding_siblings() {
        let outs = vec![
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([31u8; 32]),
            },
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([40u8; 32]),
                blinding_hex: hex::encode([41u8; 32]),
            },
        ];

        // 1. Duplicate sibling across levels
        let mut dup_path = dummy_path(TX_LEVELS);
        dup_path[7] = dup_path[3].clone();
        let inps_dup = vec![
            TransactInputNote {
                amount: 50,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: dup_path,
            },
            TransactInputNote {
                amount: 50,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
        ];
        let res_dup = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            0,
            &hex::encode([0u8; 32]),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps_dup).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        assert!(res_dup.is_err());
        assert!(res_dup.unwrap_err().contains("duplicate sibling hash"));

        // 2. Collision with withdrawal recipient
        let rec = [99u8; 32];
        let mut rec_path = dummy_path(TX_LEVELS);
        rec_path[5] = hex::encode(rec);
        let inps_rec = vec![
            TransactInputNote {
                amount: 100,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: rec_path,
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
        ];
        let outs_withdraw = vec![
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([31u8; 32]),
            },
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([30u8; 32]),
                blinding_hex: hex::encode([41u8; 32]),
            },
        ];
        let res_rec = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            -50,
            &hex::encode(rec),
            &hex::encode([0u8; 32]),
            &serde_json::to_string(&inps_rec).unwrap(),
            &serde_json::to_string(&outs_withdraw).unwrap(),
        );
        assert!(res_rec.is_err());
        assert!(res_rec
            .unwrap_err()
            .contains("Merkle path sibling collides with withdrawal recipient"));

        // 3. Collision with non-zero asset_id
        let asset_id = [77u8; 32];
        let mut asset_path = dummy_path(TX_LEVELS);
        asset_path[8] = hex::encode(asset_id);
        let inps_asset = vec![
            TransactInputNote {
                amount: 50,
                privkey_hex: hex::encode([10u8; 32]),
                blinding_hex: hex::encode([11u8; 32]),
                leaf_index: 0,
                path_hex: asset_path,
            },
            TransactInputNote {
                amount: 50,
                privkey_hex: hex::encode([20u8; 32]),
                blinding_hex: hex::encode([21u8; 32]),
                leaf_index: 0,
                path_hex: dummy_path(TX_LEVELS),
            },
        ];
        let res_asset = prove_transact_inner(
            &[],
            &hex::encode([1u8; 32]),
            0,
            &hex::encode([0u8; 32]),
            &hex::encode(asset_id),
            &serde_json::to_string(&inps_asset).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        assert!(res_asset.is_err());
        assert!(res_asset
            .unwrap_err()
            .contains("Merkle path sibling collides with asset_id"));
    }
}
