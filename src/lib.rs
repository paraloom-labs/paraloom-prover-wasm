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
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{Proof, ProvingKey};
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

const CEREMONY_V3_VK_ALPHA_G1: [u8; 64] = [
    45, 77, 154, 167, 227, 2, 217, 223, 65, 116, 157, 85, 7, 148, 157, 5, 219, 234, 51, 251, 177,
    108, 100, 59, 34, 245, 153, 162, 190, 109, 242, 226, 20, 190, 221, 80, 60, 55, 206, 176, 97,
    216, 236, 96, 32, 159, 227, 69, 206, 137, 131, 10, 25, 35, 3, 1, 240, 118, 202, 255, 0, 77, 25,
    38,
];
const CEREMONY_V3_VK_DELTA_G2: [u8; 128] = [
    28, 77, 218, 77, 113, 171, 170, 231, 170, 35, 190, 159, 219, 195, 241, 204, 226, 198, 69, 179,
    105, 200, 83, 252, 27, 176, 154, 192, 134, 74, 50, 149, 41, 69, 31, 236, 16, 115, 179, 197,
    253, 104, 49, 85, 253, 230, 228, 66, 212, 250, 254, 93, 155, 75, 28, 193, 14, 79, 11, 134, 122,
    70, 162, 26, 163, 202, 225, 169, 55, 109, 202, 98, 131, 32, 39, 134, 214, 171, 247, 134, 26,
    137, 167, 111, 140, 59, 8, 136, 191, 253, 168, 231, 188, 161, 109, 0, 34, 37, 220, 177, 24,
    118, 227, 155, 12, 77, 38, 121, 1, 216, 82, 146, 217, 205, 153, 213, 50, 81, 174, 18, 16, 133,
    190, 212, 204, 5, 1, 109,
];

fn rev32(src: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, b) in src.iter().take(32).rev().enumerate() {
        out[i] = *b;
    }
    out
}

fn g1_to_wire(p: &G1Affine) -> [u8; 64] {
    let mut le = Vec::with_capacity(64);
    p.serialize_uncompressed(&mut le)
        .expect("G1 serialize_uncompressed");
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(&rev32(&le[..32]));
    out[32..].copy_from_slice(&rev32(&le[32..64]));
    out
}

fn g2_to_wire(p: &G2Affine) -> [u8; 128] {
    let mut le = Vec::with_capacity(128);
    p.serialize_uncompressed(&mut le)
        .expect("G2 serialize_uncompressed");
    let mut out = [0u8; 128];
    out[..32].copy_from_slice(&rev32(&le[32..64]));
    out[32..64].copy_from_slice(&rev32(&le[..32]));
    out[64..96].copy_from_slice(&rev32(&le[96..128]));
    out[96..].copy_from_slice(&rev32(&le[64..96]));
    out
}

pub fn is_ceremony_transact_v3_vk(vk: &ark_groth16::VerifyingKey<Bn254>) -> bool {
    vk.gamma_abc_g1.len() == 9
        && g1_to_wire(&vk.alpha_g1) == CEREMONY_V3_VK_ALPHA_G1
        && g2_to_wire(&vk.delta_g2) == CEREMONY_V3_VK_DELTA_G2
}

fn validate_pk_and_proof_integrity(
    pk: &ProvingKey<Bn254>,
    proof: &Proof<Bn254>,
    context: &str,
) -> Result<(), String> {
    if pk.beta_g1.is_zero()
        || pk.delta_g1.is_zero()
        || pk.vk.alpha_g1.is_zero()
        || pk.vk.beta_g2.is_zero()
        || pk.vk.gamma_g2.is_zero()
        || pk.vk.delta_g2.is_zero()
        || pk.vk.gamma_abc_g1.iter().any(|p| p.is_zero())
    {
        return Err(format!(
            "{context}: proving/verifying key contains point at infinity"
        ));
    }
    if pk.vk.alpha_g1 == pk.beta_g1 || pk.vk.alpha_g1 == pk.delta_g1 || pk.beta_g1 == pk.delta_g1 {
        return Err(format!(
            "{context}: degenerate proving key G1 toxic-waste collision (alpha/beta/delta)"
        ));
    }
    if pk.vk.beta_g2 == pk.vk.gamma_g2
        || pk.vk.beta_g2 == pk.vk.delta_g2
        || pk.vk.gamma_g2 == pk.vk.delta_g2
    {
        return Err(format!(
            "{context}: degenerate verifying key G2 toxic-waste collision (beta/gamma/delta)"
        ));
    }
    for i in 0..pk.vk.gamma_abc_g1.len() {
        for j in (i + 1)..pk.vk.gamma_abc_g1.len() {
            if pk.vk.gamma_abc_g1[i] == pk.vk.gamma_abc_g1[j] {
                return Err(format!(
                    "{context}: duplicate IC point in gamma_abc_g1[{i}] and gamma_abc_g1[{j}]"
                ));
            }
        }
    }
    if proof.a.is_zero() || proof.b.is_zero() || proof.c.is_zero() {
        return Err(format!("{context}: proof contains point at infinity"));
    }
    if proof.a == proof.c {
        return Err(format!(
            "{context}: degenerate proof with proof.a == proof.c"
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

const MIN_WITHDRAWAL_AMOUNT: u64 = 400; // WITHDRAWAL_FEE_BPS = 25 => floor(gross * 25 / 10_000) >= 1

const BRIDGE_VAULT_PDA_BYTES: [u8; 32] = [
    187, 239, 66, 195, 191, 212, 36, 250, 79, 167, 57, 104, 226, 39, 222, 60, 154, 190, 102, 184,
    247, 79, 10, 56, 154, 69, 136, 219, 232, 155, 167, 186,
];
const SLASHED_FUNDS_VAULT_PDA_BYTES: [u8; 32] = [
    200, 183, 18, 29, 248, 90, 54, 22, 235, 105, 37, 197, 146, 3, 186, 71, 220, 32, 154, 106, 245,
    28, 66, 227, 54, 104, 2, 68, 94, 75, 178, 44,
];
const BRIDGE_STATE_PDA_BYTES: [u8; 32] = [
    106, 218, 6, 89, 198, 49, 196, 218, 157, 176, 160, 134, 247, 27, 132, 156, 117, 54, 50, 62,
    139, 246, 196, 143, 42, 124, 44, 154, 210, 83, 9, 121,
];
const MERKLE_TREE_PDA_BYTES: [u8; 32] = [
    32, 4, 144, 180, 75, 152, 95, 161, 59, 73, 212, 248, 161, 197, 18, 88, 89, 102, 6, 82, 184,
    158, 34, 28, 116, 212, 12, 191, 145, 133, 255, 185,
];
const VALIDATOR_REGISTRY_PDA_BYTES: [u8; 32] = [
    189, 165, 110, 216, 141, 165, 3, 141, 141, 50, 35, 14, 147, 243, 201, 40, 30, 11, 173, 49, 139,
    135, 63, 124, 55, 27, 22, 232, 156, 232, 154, 16,
];
const STAKE_VAULT_AUTHORITY_PDA_BYTES: [u8; 32] = [
    234, 239, 77, 65, 195, 120, 143, 39, 127, 30, 47, 11, 159, 3, 49, 7, 162, 102, 165, 8, 180, 60,
    186, 144, 218, 111, 198, 117, 255, 244, 2, 234,
];
const ASSET_VAULT_AUTHORITY_PDA_BYTES: [u8; 32] = [
    49, 128, 138, 182, 14, 179, 209, 42, 7, 98, 123, 16, 57, 54, 76, 5, 88, 188, 112, 58, 210, 235,
    92, 112, 248, 231, 240, 8, 21, 43, 211, 235,
];
const STAKE_TOKEN_VAULT_PDA_BYTES: [u8; 32] = [
    169, 23, 231, 115, 157, 146, 101, 135, 95, 15, 103, 157, 101, 36, 165, 209, 163, 247, 190, 11,
    127, 99, 88, 225, 132, 160, 42, 171, 164, 21, 200, 206,
];
const PARALOOM_PROGRAM_ID_BYTES: [u8; 32] = [
    113, 204, 241, 171, 254, 227, 205, 215, 143, 8, 236, 254, 147, 131, 162, 191, 88, 72, 78, 91,
    168, 25, 5, 102, 241, 226, 154, 249, 82, 134, 235, 145,
];
const SPL_TOKEN_PROGRAM_BYTES: [u8; 32] = [
    6, 221, 246, 225, 215, 101, 161, 147, 217, 203, 225, 70, 206, 235, 121, 172, 28, 180, 133, 237,
    95, 91, 55, 145, 58, 140, 245, 133, 126, 255, 0, 169,
];
const SPL_TOKEN_2022_PROGRAM_BYTES: [u8; 32] = [
    6, 221, 246, 225, 238, 117, 143, 222, 24, 66, 93, 188, 228, 108, 205, 218, 182, 26, 252, 77,
    131, 185, 13, 39, 254, 189, 249, 40, 216, 161, 139, 252,
];
const ASSOCIATED_TOKEN_PROGRAM_BYTES: [u8; 32] = [
    140, 151, 37, 143, 78, 36, 137, 241, 187, 61, 16, 41, 20, 142, 13, 131, 11, 90, 19, 153, 218,
    255, 16, 132, 4, 142, 123, 216, 219, 233, 248, 89,
];
const BPF_LOADER_UPGRADEABLE_BYTES: [u8; 32] = [
    2, 168, 246, 145, 78, 136, 161, 176, 226, 16, 21, 62, 247, 99, 174, 43, 0, 194, 185, 61, 22,
    193, 36, 210, 192, 83, 122, 16, 4, 128, 0, 0,
];
const RENT_SYSVAR_BYTES: [u8; 32] = [
    6, 167, 213, 23, 25, 44, 92, 81, 33, 140, 201, 76, 61, 74, 241, 127, 88, 218, 238, 8, 155, 161,
    253, 68, 227, 219, 217, 138, 0, 0, 0, 0,
];
const CLOCK_SYSVAR_BYTES: [u8; 32] = [
    6, 167, 213, 23, 24, 199, 116, 201, 40, 86, 99, 152, 105, 29, 94, 182, 139, 94, 184, 163, 155,
    75, 109, 92, 115, 85, 91, 33, 0, 0, 0, 0,
];
const WSOL_NATIVE_MINT_BYTES: [u8; 32] = [
    6, 155, 136, 87, 254, 171, 129, 132, 251, 104, 127, 99, 70, 24, 192, 53, 218, 196, 57, 220, 26,
    235, 59, 85, 152, 160, 240, 0, 0, 0, 0, 1,
];

fn validate_withdrawal_fee_floor(gross: u64, context: &str) -> Result<(), String> {
    if gross < MIN_WITHDRAWAL_AMOUNT {
        return Err(format!(
            "{context}: withdrawal amount {gross} is below MIN_WITHDRAWAL_AMOUNT ({MIN_WITHDRAWAL_AMOUNT}) and truncates 25 bps validator fee to 0"
        ));
    }
    Ok(())
}

fn validate_asset_id_bytes(
    asset_id: &[u8; 32],
    root: Option<&[u8; 32]>,
    recipient: Option<&[u8; 32]>,
    context: &str,
) -> Result<(), String> {
    if asset_id == &[0u8; 32] {
        return Ok(());
    }
    if asset_id == &WSOL_NATIVE_MINT_BYTES
        || asset_id == &SPL_TOKEN_PROGRAM_BYTES
        || asset_id == &SPL_TOKEN_2022_PROGRAM_BYTES
        || asset_id == &ASSOCIATED_TOKEN_PROGRAM_BYTES
        || asset_id == &PARALOOM_PROGRAM_ID_BYTES
    {
        return Err(format!(
            "{context}: asset_id cannot be a raw WSOL mint or Solana program ID"
        ));
    }
    let wsol_lo = Fr::from_le_bytes_mod_order(&WSOL_NATIVE_MINT_BYTES[..16]);
    let wsol_hi = Fr::from_le_bytes_mod_order(&WSOL_NATIVE_MINT_BYTES[16..]);
    let wsol_hashed_asset = fr_to_le_bytes_32(v3_merkle_pair(wsol_lo, wsol_hi));
    if asset_id == &wsol_hashed_asset {
        return Err(format!(
            "{context}: WSOL uses all-zero NATIVE_SOL_ASSET, not mint_to_asset(WSOL_MINT)"
        ));
    }
    let mut z = Fr::from(0u64);
    for depth in 1..=TX_LEVELS {
        z = v3_merkle_pair(z, z);
        if asset_id == &fr_to_le_bytes_32(z) {
            return Err(format!(
                "{context}: asset_id equals reserved ZERO_HASHES[{depth}] (or mint_to_asset([0; 32]))"
            ));
        }
    }
    if let Some(r) = root {
        if asset_id == r {
            return Err(format!(
                "{context}: non-zero asset_id collides with Merkle root"
            ));
        }
    }
    if let Some(rec) = recipient {
        if asset_id == rec {
            return Err(format!(
                "{context}: non-zero asset_id collides with withdrawal recipient"
            ));
        }
    }
    Ok(())
}

fn validate_commitment_helper_params(
    secret_or_pub: &[u8; 32],
    blinding_or_recipient: &[u8; 32],
    derived_pub: Option<&[u8; 32]>,
    context: &str,
) -> Result<(), String> {
    if secret_or_pub != &[0u8; 32] && secret_or_pub == blinding_or_recipient {
        return Err(format!(
            "{context}: secret/public key and blinding/recipient parameters must not be identical"
        ));
    }
    if let Some(pk) = derived_pub {
        if pk == blinding_or_recipient {
            return Err(format!(
                "{context}: derived spend pubkey must not equal blinding"
            ));
        }
    }
    Ok(())
}

fn validate_blinding_not_derived_pubkey(
    privkey: &[u8; 32],
    blinding: &[u8; 32],
    context: &str,
) -> Result<(), String> {
    let sk = Fr::from_le_bytes_mod_order(privkey);
    let v2_pk = fr_to_le_bytes_32(poseidon_pubkey(sk));
    let v3_pk = fr_to_le_bytes_32(v3_pubkey(sk));
    if blinding == &v2_pk || blinding == &v3_pk {
        return Err(format!(
            "{context}: blinding cannot equal the derived v2 or v3 spend public key"
        ));
    }
    Ok(())
}

fn validate_cross_version_pubkeys_and_output_blindings(
    in_privkeys: &[[u8; 32]],
    in_blindings: &[[u8; 32]],
    same_version_in_pubkeys: &[[u8; 32]],
    wrong_version_in_pubkeys: &[[u8; 32]],
    out_pubkeys: &[[u8; 32]],
    out_blindings: &[[u8; 32]],
    context: &str,
) -> Result<(), String> {
    for i in 0..in_privkeys.len() {
        if in_blindings[i] == same_version_in_pubkeys[i]
            || in_blindings[i] == wrong_version_in_pubkeys[i]
        {
            return Err(format!(
                "{context}: input[{i}] blinding collides with derived spend public key"
            ));
        }
    }
    for j in 0..out_pubkeys.len() {
        if wrong_version_in_pubkeys.contains(&out_pubkeys[j]) {
            return Err(format!(
                "{context}: output[{j}] pubkey uses wrong-version Poseidon pubkey derivation for an input spend key"
            ));
        }
        if in_privkeys.contains(&out_blindings[j]) {
            return Err(format!(
                "{context}: output[{j}] blinding collides with an input spend private key (would leak spend key in encrypted note)"
            ));
        }
        if in_blindings.contains(&out_blindings[j]) {
            return Err(format!(
                "{context}: output[{j}] blinding reuses an input note blinding"
            ));
        }
        if same_version_in_pubkeys.contains(&out_blindings[j])
            || wrong_version_in_pubkeys.contains(&out_blindings[j])
        {
            return Err(format!(
                "{context}: output[{j}] blinding collides with an input spend public key"
            ));
        }
    }
    Ok(())
}

fn validate_withdrawal_recipient_address(
    recipient: &[u8; 32],
    context: &str,
) -> Result<(), String> {
    if recipient == &[0u8; 32] {
        return Err(format!(
            "{context}: withdrawal recipient cannot be all-zero (System Program)"
        ));
    }
    if recipient == &BRIDGE_VAULT_PDA_BYTES
        || recipient == &SLASHED_FUNDS_VAULT_PDA_BYTES
        || recipient == &BRIDGE_STATE_PDA_BYTES
        || recipient == &MERKLE_TREE_PDA_BYTES
        || recipient == &VALIDATOR_REGISTRY_PDA_BYTES
        || recipient == &STAKE_VAULT_AUTHORITY_PDA_BYTES
        || recipient == &ASSET_VAULT_AUTHORITY_PDA_BYTES
        || recipient == &STAKE_TOKEN_VAULT_PDA_BYTES
    {
        return Err(format!(
            "{context}: withdrawal recipient cannot be a protocol vault, authority, or state PDA"
        ));
    }
    if recipient == &PARALOOM_PROGRAM_ID_BYTES
        || recipient == &SPL_TOKEN_PROGRAM_BYTES
        || recipient == &SPL_TOKEN_2022_PROGRAM_BYTES
        || recipient == &ASSOCIATED_TOKEN_PROGRAM_BYTES
        || recipient == &BPF_LOADER_UPGRADEABLE_BYTES
        || recipient == &RENT_SYSVAR_BYTES
        || recipient == &CLOCK_SYSVAR_BYTES
        || recipient == &WSOL_NATIVE_MINT_BYTES
    {
        return Err(format!(
            "{context}: withdrawal recipient cannot be an executable program, sysvar, or mint account"
        ));
    }
    Ok(())
}

fn validate_merkle_path_sibling_uniqueness_and_isolation(
    path: &[[u8; 32]],
    nullifiers: &[[u8; 32]],
    output_commitments: &[[u8; 32]],
    asset_id: &[u8; 32],
    recipient: Option<&[u8; 32]>,
    context: &str,
) -> Result<(), String> {
    for (d1, sib1) in path.iter().enumerate() {
        for (d2, sib2) in path.iter().enumerate().skip(d1 + 1) {
            if sib1 == sib2 {
                return Err(format!(
                    "{context}: duplicate Merkle path sibling across levels {d1} and {d2}"
                ));
            }
        }
        if nullifiers.contains(sib1) {
            return Err(format!(
                "{context}: Merkle path sibling at depth {d1} collides with transaction nullifier"
            ));
        }
        if output_commitments.contains(sib1) {
            return Err(format!(
                "{context}: Merkle path sibling at depth {d1} collides with output commitment"
            ));
        }
        if asset_id != &[0u8; 32] && sib1 == asset_id {
            return Err(format!(
                "{context}: Merkle path sibling at depth {d1} collides with non-zero asset_id"
            ));
        }
        if let Some(rec) = recipient {
            if rec != &[0u8; 32] && sib1 == rec {
                return Err(format!(
                    "{context}: Merkle path sibling at depth {d1} collides with withdrawal recipient"
                ));
            }
        }
    }
    Ok(())
}

fn validate_v3_dummy_and_filler_invariants(
    inputs: &[TransactInputNote],
    in_paths: &[Option<Vec<[u8; 32]>>],
    out_amounts: &[Option<u64>],
    out_pubkeys: &[Option<[u8; 32]>],
    ext_amount: i64,
) -> Result<(), String> {
    for (idx, inp) in inputs.iter().enumerate() {
        if inp.amount == 0 {
            if inp.leaf_index != 0 {
                return Err(format!(
                    "prove_transact: zero-value dummy input[{idx}] must have leaf_index == 0, got {}",
                    inp.leaf_index
                ));
            }
            if let Some(path) = &in_paths[idx] {
                for (depth, sib) in path.iter().enumerate().skip(1) {
                    if sib == &[0u8; 32] {
                        return Err(format!(
                            "prove_transact: zero-value dummy input[{idx}] has raw all-zero sibling at depth {depth}"
                        ));
                    }
                }
            }
        }
    }
    if ext_amount < 0
        && out_amounts.get(1) == Some(&Some(0))
        && out_pubkeys.first() != out_pubkeys.get(1)
    {
        return Err(
            "prove_transact: withdrawal zero-value filler output (outputs[1]) must share outputs[0] pubkey"
                .to_string(),
        );
    }
    Ok(())
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

fn ensure_nonzero_root(root: &[u8; 32]) -> Result<(), String> {
    if root == &[0u8; 32] {
        return Err("merkle root cannot be all-zero".to_string());
    }
    Ok(())
}

fn ensure_nonzero_bytes32(bytes: &[u8; 32], label: &str) -> Result<(), String> {
    if bytes == &[0u8; 32] {
        return Err(format!("{label} cannot be all-zero"));
    }
    Ok(())
}

fn validate_two_note_balance_and_blindings(
    in_amounts: [u64; 2],
    in_privkeys: [[u8; 32]; 2],
    in_blindings: [[u8; 32]; 2],
    out_amounts: [u64; 2],
    out_blindings: [[u8; 32]; 2],
    ext_amount: i64,
) -> Result<(), String> {
    if ext_amount > 0 {
        return Err(
            "positive ext_amount: deposits go through deposit_note, not transact".to_string(),
        );
    }
    if ext_amount == i64::MIN {
        return Err("ext_amount cannot be i64::MIN".to_string());
    }
    let in_sum = in_amounts[0]
        .checked_add(in_amounts[1])
        .ok_or_else(|| "input note amounts overflow u64".to_string())?;
    let out_sum = out_amounts[0]
        .checked_add(out_amounts[1])
        .ok_or_else(|| "output note amounts overflow u64".to_string())?;
    let expected_out = if ext_amount < 0 {
        in_sum
            .checked_sub(ext_amount.unsigned_abs())
            .ok_or_else(|| "withdrawal amount exceeds input note sum".to_string())?
    } else {
        in_sum
    };
    if expected_out != out_sum {
        return Err(
            "unbalanced note amounts: sum(inputs) + ext_amount != sum(outputs)".to_string(),
        );
    }

    ensure_nonzero_bytes32(&in_privkeys[0], "input[0] privkey")?;
    ensure_nonzero_bytes32(&in_privkeys[1], "input[1] privkey")?;
    ensure_nonzero_bytes32(&in_blindings[0], "input[0] blinding")?;
    ensure_nonzero_bytes32(&in_blindings[1], "input[1] blinding")?;
    ensure_nonzero_bytes32(&out_blindings[0], "output[0] blinding")?;
    ensure_nonzero_bytes32(&out_blindings[1], "output[1] blinding")?;

    if in_blindings[0] == in_blindings[1] {
        return Err("input notes cannot share the same blinding".to_string());
    }
    if out_blindings[0] == out_blindings[1] {
        return Err("output notes cannot share the same blinding".to_string());
    }
    for (i, ib) in in_blindings.iter().enumerate() {
        for (j, ob) in out_blindings.iter().enumerate() {
            if ib == ob {
                return Err(format!(
                    "input[{i}] and output[{j}] cannot share the same blinding"
                ));
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
    validate_commitment_helper_params(&randomness, &recipient, None, "note_commitment")
        .map_err(|e| JsValue::from_str(&e))?;
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
    let privkey = hex32(privkey_hex)?;
    let blinding = hex32(blinding_hex)?;
    let asset_id = hex32(asset_id_hex)?;
    validate_blinding_not_derived_pubkey(&privkey, &blinding, "note_commitment_v2")
        .map_err(|e| JsValue::from_str(&e))?;
    let sk = Fr::from_le_bytes_mod_order(&privkey);
    let pk_bytes = fr_to_le_bytes_32(poseidon_pubkey(sk));
    validate_commitment_helper_params(&privkey, &blinding, Some(&pk_bytes), "note_commitment_v2")
        .map_err(|e| JsValue::from_str(&e))?;
    validate_asset_id_bytes(&asset_id, None, None, "note_commitment_v2")
        .map_err(|e| JsValue::from_str(&e))?;
    let c = poseidon_commit_spend(
        Fr::from(amount),
        poseidon_pubkey(sk),
        Fr::from_le_bytes_mod_order(&blinding),
        Fr::from_le_bytes_mod_order(&asset_id),
    );
    Ok(hex::encode(fr_to_le_bytes_32(c)))
}

fn rng_from_entropy() -> StdRng {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).expect("browser entropy");
    StdRng::from_seed(seed)
}

const WITHDRAW_V2_NUM_INSTANCE_VARS: usize = 6; // 1 + [root, nullifier, amount, ext_data_hash, asset_id]
const TRANSFER_V2_NUM_INSTANCE_VARS: usize = 7; // 1 + [root, nf0, nf1, oc0, oc1, asset_id]
const TRANSACT_V3_NUM_INSTANCE_VARS: usize = 9; // 1 + [root, public_amount, ext_data_hash, asset_id, nf0, nf1, oc0, oc1]

fn deserialize_and_validate_pk(
    proving_key: &[u8],
    expected_num_inputs: usize,
) -> Result<ProvingKey<Bn254>, String> {
    let mut cursor = proving_key;
    let pk = ProvingKey::<Bn254>::deserialize_compressed(&mut cursor)
        .map_err(|e| format!("bad proving key: {e}"))?;
    if !cursor.is_empty() {
        return Err("bad proving key: trailing bytes".to_string());
    }
    if pk.vk.gamma_abc_g1.len() != expected_num_inputs {
        return Err(format!(
            "bad proving key: expected {expected_num_inputs} public-input IC points, got {}",
            pk.vk.gamma_abc_g1.len()
        ));
    }
    if !pk.h_query.len().is_power_of_two() {
        return Err(format!(
            "bad proving key: h_query length {} is not a power of two (expected CircomReduction convention)",
            pk.h_query.len()
        ));
    }
    if pk.a_query.len() < expected_num_inputs
        || pk.b_g1_query.len() < expected_num_inputs
        || pk.b_g2_query.len() < expected_num_inputs
        || pk.l_query.is_empty()
    {
        return Err(
            "bad proving key: query vectors shorter than circuit instance count".to_string(),
        );
    }
    Ok(pk)
}

fn verify_generated_proof(
    pk: &ProvingKey<Bn254>,
    public_inputs: &[Fr],
    proof: &ark_groth16::Proof<Bn254>,
) -> Result<(), String> {
    match Groth16ProofSystem::verify(&pk.vk, public_inputs, proof) {
        Ok(true) => Ok(()),
        Ok(false) => {
            Err("prove failed: generated proof did not pass self-verification".to_string())
        }
        Err(e) => Err(format!("prove failed: self-verification error: {e}")),
    }
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
    ensure_nonzero_root(&root).map_err(|e| JsValue::from_str(&e))?;
    let blinding = hex32(blinding_hex)?;
    let privkey = hex32(privkey_hex)?;
    let asset_id = hex32(asset_id_hex)?;
    let dest_recipient = hex32(dest_recipient_hex)?;
    validate_withdrawal_fee_floor(amount, "prove_withdrawal_v2")
        .map_err(|e| JsValue::from_str(&e))?;
    validate_withdrawal_recipient_address(&dest_recipient, "prove_withdrawal_v2")
        .map_err(|e| JsValue::from_str(&e))?;
    validate_asset_id_bytes(
        &asset_id,
        Some(&root),
        Some(&dest_recipient),
        "prove_withdrawal_v2",
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let path_hex: Vec<String> = serde_json::from_str(path_hex_json)
        .map_err(|e| JsValue::from_str(&format!("bad path json: {e}")))?;
    let indices: Vec<bool> = serde_json::from_str(indices_json)
        .map_err(|e| JsValue::from_str(&format!("bad indices json: {e}")))?;
    let merkle_path = merkle_path_from(&path_hex, &indices)?;

    let leaf_index = leaf_index_from(&indices);

    validate_blinding_not_derived_pubkey(&privkey, &blinding, "prove_withdrawal_v2")
        .map_err(|e| JsValue::from_str(&e))?;
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
    let sibling_hashes: Vec<[u8; 32]> = merkle_path.iter().map(|(s, _)| *s).collect();
    validate_merkle_path_sibling_uniqueness_and_isolation(
        &sibling_hashes,
        &[nullifier],
        &[],
        &asset_id,
        Some(&dest_recipient),
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

    let pk = deserialize_and_validate_pk(proving_key, WITHDRAW_V2_NUM_INSTANCE_VARS)
        .map_err(|e| JsValue::from_str(&e))?;
    let proof =
        Groth16ProofSystem::prove::<WithdrawCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;
    let public_inputs = [
        Fr::from_le_bytes_mod_order(&root),
        nullifier_fr,
        Fr::from(amount),
        Fr::from_le_bytes_mod_order(&ext_data_hash),
        Fr::from_le_bytes_mod_order(&asset_id),
    ];
    verify_generated_proof(&pk, &public_inputs, &proof).map_err(|e| JsValue::from_str(&e))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| JsValue::from_str(&format!("serialize failed: {e}")))?;
    validate_pk_and_proof_integrity(&pk, &proof, "prove_withdrawal_v2")
        .map_err(|e| JsValue::from_str(&e))?;

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
    ensure_nonzero_root(&root).map_err(|e| JsValue::from_str(&e))?;
    let asset_id = hex32(asset_id_hex)?;
    validate_asset_id_bytes(&asset_id, Some(&root), None, "prove_transfer_v2")
        .map_err(|e| JsValue::from_str(&e))?;
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
    let mut input_v2_pubkeys = Vec::with_capacity(2);
    let mut input_v3_pubkeys = Vec::with_capacity(2);
    let mut input_paths = Vec::with_capacity(2);
    for inp in &inputs {
        let blinding = hex32(&inp.blinding_hex)?;
        let privkey = hex32(&inp.privkey_hex)?;
        let sk = Fr::from_le_bytes_mod_order(&privkey);
        let v2_pk_fr = poseidon_pubkey(sk);
        input_v2_pubkeys.push(fr_to_le_bytes_32(v2_pk_fr));
        input_v3_pubkeys.push(fr_to_le_bytes_32(v3_pubkey(sk)));
        let commitment_fr = poseidon_commit_spend(
            Fr::from(inp.amount),
            v2_pk_fr,
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
    validate_cross_version_pubkeys_and_output_blindings(
        &input_privkeys,
        &input_blindings,
        &input_v2_pubkeys,
        &input_v3_pubkeys,
        &output_pubkeys,
        &output_blindings,
        "prove_transfer_v2",
    )
    .map_err(|e| JsValue::from_str(&e))?;
    for (idx, p) in input_paths.iter().enumerate() {
        let sibs: Vec<[u8; 32]> = p.iter().map(|(s, _)| *s).collect();
        validate_merkle_path_sibling_uniqueness_and_isolation(
            &sibs,
            &nullifiers,
            &output_commitments,
            &asset_id,
            None,
            &format!("prove_transfer_v2(input[{idx}])"),
        )
        .map_err(|e| JsValue::from_str(&e))?;
    }

    let circuit = TransferCircuitV2::with_witness(
        root,
        nullifiers.clone(),
        output_commitments.clone(),
        input_values.clone(),
        input_blindings.clone(),
        input_privkeys.clone(),
        input_paths,
        output_values.clone(),
        output_blindings.clone(),
        output_pubkeys,
        asset_id,
    );
    validate_two_note_balance_and_blindings(
        [input_values[0], input_values[1]],
        [input_privkeys[0], input_privkeys[1]],
        [input_blindings[0], input_blindings[1]],
        [output_values[0], output_values[1]],
        [output_blindings[0], output_blindings[1]],
        0,
    )
    .map_err(|e| JsValue::from_str(&e))?;
    if nullifiers[0] == nullifiers[1] {
        return Err(JsValue::from_str("duplicate input nullifier"));
    }

    let pk = deserialize_and_validate_pk(proving_key, TRANSFER_V2_NUM_INSTANCE_VARS)
        .map_err(|e| JsValue::from_str(&e))?;
    let proof =
        Groth16ProofSystem::prove::<TransferCircuitV2, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;
    let public_inputs = [
        Fr::from_le_bytes_mod_order(&root),
        Fr::from_le_bytes_mod_order(&nullifiers[0]),
        Fr::from_le_bytes_mod_order(&nullifiers[1]),
        Fr::from_le_bytes_mod_order(&output_commitments[0]),
        Fr::from_le_bytes_mod_order(&output_commitments[1]),
        asset_fr,
    ];
    verify_generated_proof(&pk, &public_inputs, &proof).map_err(|e| JsValue::from_str(&e))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| JsValue::from_str(&format!("serialize failed: {e}")))?;
    validate_pk_and_proof_integrity(&pk, &proof, "prove_transfer_v2")
        .map_err(|e| JsValue::from_str(&e))?;

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
    let pubkey = hex32(pubkey_hex)?;
    let blinding = hex32(blinding_hex)?;
    validate_commitment_helper_params(&pubkey, &blinding, None, "v3_note_commitment")
        .map_err(|e| JsValue::from_str(&e))?;
    let c = v3_commit(
        Fr::from(amount),
        Fr::from_le_bytes_mod_order(&pubkey),
        Fr::from_le_bytes_mod_order(&blinding),
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
    let pubkey = hex32(pubkey_hex)?;
    let blinding = hex32(blinding_hex)?;
    let asset_id = hex32(asset_id_hex)?;
    validate_commitment_helper_params(&pubkey, &blinding, None, "v3_note_commitment_asset")
        .map_err(|e| JsValue::from_str(&e))?;
    validate_asset_id_bytes(&asset_id, None, None, "v3_note_commitment_asset")
        .map_err(|e| JsValue::from_str(&e))?;
    let c = v3_commit(
        Fr::from(amount),
        Fr::from_le_bytes_mod_order(&pubkey),
        Fr::from_le_bytes_mod_order(&blinding),
        Fr::from_le_bytes_mod_order(&asset_id),
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
    if ext_amount < 0 {
        validate_withdrawal_fee_floor(ext_amount.unsigned_abs(), "prove_transact")
            .map_err(|e| JsValue::from_str(&e))?;
    }
    let root = hex32(root_hex)?;
    ensure_nonzero_root(&root).map_err(|e| JsValue::from_str(&e))?;
    let recipient = hex32(recipient_hex)?;
    if ext_amount < 0 {
        validate_withdrawal_recipient_address(&recipient, "prove_transact")
            .map_err(|e| JsValue::from_str(&e))?;
    }

    let inputs: Vec<TransactInputNote> = serde_json::from_str(inputs_json)
        .map_err(|e| JsValue::from_str(&format!("bad inputs json: {e}")))?;
    let outputs: Vec<TransactOutputNote> = serde_json::from_str(outputs_json)
        .map_err(|e| JsValue::from_str(&format!("bad outputs json: {e}")))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(JsValue::from_str("transact is fixed 2-in/2-out"));
    }

    // The shielded asset: all-zero for native SOL, or `mint_to_asset(mint)` for
    // a shielded SPL note (#779). All notes in one transact share one asset.
    let asset_bytes = hex32(asset_id_hex)?;
    validate_asset_id_bytes(
        &asset_bytes,
        Some(&root),
        Some(&recipient),
        "prove_transact",
    )
    .map_err(|e| JsValue::from_str(&e))?;
    let asset = Fr::from_le_bytes_mod_order(&asset_bytes);

    let mut in_amounts = Vec::new();
    let mut in_privkeys = Vec::new();
    let mut in_blindings = Vec::new();
    let mut in_leaf_indices = Vec::new();
    let mut in_paths = Vec::new();
    let mut raw_in_privkeys = Vec::new();
    let mut raw_in_blindings = Vec::new();
    let mut raw_in_v3_pubkeys = Vec::new();
    let mut raw_in_v2_pubkeys = Vec::new();
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
        let v3_pk_fr = v3_pubkey(sk);
        raw_in_privkeys.push(privkey);
        raw_in_blindings.push(blinding);
        raw_in_v3_pubkeys.push(fr_to_le_bytes_32(v3_pk_fr));
        raw_in_v2_pubkeys.push(fr_to_le_bytes_32(poseidon_pubkey(sk)));
        let c = v3_commit(
            Fr::from(inp.amount),
            v3_pk_fr,
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
    let mut raw_out_pubkeys = Vec::new();
    let mut raw_out_blindings = Vec::new();
    let mut output_commitments = Vec::new();
    for outp in &outputs {
        let pubkey = hex32(&outp.pubkey_hex)?;
        let blinding = hex32(&outp.blinding_hex)?;
        raw_out_pubkeys.push(pubkey);
        raw_out_blindings.push(blinding);
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
    validate_cross_version_pubkeys_and_output_blindings(
        &raw_in_privkeys,
        &raw_in_blindings,
        &raw_in_v3_pubkeys,
        &raw_in_v2_pubkeys,
        &raw_out_pubkeys,
        &raw_out_blindings,
        "prove_transact",
    )
    .map_err(|e| JsValue::from_str(&e))?;
    validate_v3_dummy_and_filler_invariants(
        &inputs,
        &in_paths,
        &out_amounts,
        &out_pubkeys,
        ext_amount,
    )
    .map_err(|e| JsValue::from_str(&e))?;
    for (idx, p_opt) in in_paths.iter().enumerate() {
        if let Some(p) = p_opt {
            validate_merkle_path_sibling_uniqueness_and_isolation(
                p,
                &nullifiers,
                &output_commitments,
                &asset_bytes,
                if ext_amount < 0 {
                    Some(&recipient)
                } else {
                    None
                },
                &format!("prove_transact(input[{idx}])"),
            )
            .map_err(|e| JsValue::from_str(&e))?;
        }
    }

    validate_two_note_balance_and_blindings(
        [inputs[0].amount, inputs[1].amount],
        [in_privkeys[0].unwrap(), in_privkeys[1].unwrap()],
        [in_blindings[0].unwrap(), in_blindings[1].unwrap()],
        [outputs[0].amount, outputs[1].amount],
        [out_blindings[0].unwrap(), out_blindings[1].unwrap()],
        ext_amount,
    )
    .map_err(|e| JsValue::from_str(&e))?;
    if nullifiers[0] == nullifiers[1] {
        return Err(JsValue::from_str("duplicate input nullifier"));
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

    let pk = deserialize_and_validate_pk(proving_key, TRANSACT_V3_NUM_INSTANCE_VARS)
        .map_err(|e| JsValue::from_str(&e))?;
    let proof =
        Groth16ProofSystem::prove::<TransactCircuitV3, _>(&pk, circuit, &mut rng_from_entropy())
            .map_err(|e| JsValue::from_str(&format!("prove failed: {e}")))?;
    let public_inputs = [
        Fr::from_le_bytes_mod_order(&root),
        public_amount,
        Fr::from_le_bytes_mod_order(&ext_data_hash),
        asset,
        Fr::from_le_bytes_mod_order(&nullifiers[0]),
        Fr::from_le_bytes_mod_order(&nullifiers[1]),
        Fr::from_le_bytes_mod_order(&output_commitments[0]),
        Fr::from_le_bytes_mod_order(&output_commitments[1]),
    ];
    verify_generated_proof(&pk, &public_inputs, &proof).map_err(|e| JsValue::from_str(&e))?;

    let mut proof_bytes = Vec::new();
    proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(|e| JsValue::from_str(&format!("serialize failed: {e}")))?;
    validate_pk_and_proof_integrity(&pk, &proof, "prove_transact")
        .map_err(|e| JsValue::from_str(&e))?;

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
    for zero in zeros.iter().take(TX_LEVELS) {
        let sibling = if idx & 1 == 0 {
            *level.get(idx + 1).unwrap_or(zero)
        } else {
            level[idx - 1]
        };
        path.push(hex::encode(fr_to_le_bytes_32(sibling)));

        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        for pair in level.chunks(2) {
            let l = pair[0];
            let r = *pair.get(1).unwrap_or(zero);
            next.push(v3_merkle_pair(l, r));
        }
        level = next;
        idx /= 2;
    }

    let root = *level.first().unwrap_or(&zeros[TX_LEVELS]);
    let target_leaf = Fr::from_le_bytes_mod_order(&hex32(&leaves_hex[leaf_index as usize])?);
    let mut folded = target_leaf;
    for (depth, sib_hex) in path.iter().enumerate() {
        let sib = Fr::from_le_bytes_mod_order(&hex32(sib_hex)?);
        if sib == target_leaf || sib == root {
            return Err(JsValue::from_str(
                "merkle path sibling collides with target leaf or root",
            ));
        }
        if ((leaf_index as usize) >> depth) & 1 == 0 {
            folded = v3_merkle_pair(folded, sib);
        } else {
            folded = v3_merkle_pair(sib, folded);
        }
    }
    if folded != root {
        return Err(JsValue::from_str(
            "merkle path bit-fold verification failed against computed root",
        ));
    }
    Ok(format!(
        "{{\"path\":{},\"root\":\"{}\"}}",
        serde_json::to_string(&path).unwrap(),
        hex::encode(fr_to_le_bytes_32(root))
    ))
}

#[cfg(test)]
mod proving_key_and_self_verify_tests {
    use super::*;
    use ark_groth16::{r1cs_to_qap::LibsnarkReduction, Groth16};
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, Result as R1csResult,
    };
    use ark_snark::CircuitSpecificSetupSNARK;

    struct SmallCircuit {
        num_public_inputs: usize,
    }

    impl ConstraintSynthesizer<Fr> for SmallCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> R1csResult<()> {
            let mut inputs = Vec::with_capacity(self.num_public_inputs);
            for i in 0..self.num_public_inputs {
                inputs.push(cs.new_input_variable(|| Ok(Fr::from((i + 1) as u64)))?);
            }
            let a = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?;
            let b = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?;
            cs.enforce_constraint(
                LinearCombination::from(a),
                LinearCombination::from(b),
                LinearCombination::from(inputs[0]),
            )?;
            Ok(())
        }
    }

    #[test]
    fn deserialize_and_validate_pk_accepts_matching_circom_key_and_rejects_mismatches() {
        let mut rng = StdRng::seed_from_u64(0x5150);
        let (pk_withdraw, _) = Groth16ProofSystem::setup(
            SmallCircuit {
                num_public_inputs: WITHDRAW_V2_NUM_INSTANCE_VARS - 1,
            },
            &mut rng,
        )
        .expect("circom setup");

        let mut pk_bytes = Vec::new();
        pk_withdraw.serialize_compressed(&mut pk_bytes).unwrap();

        // Matching circuit public-input count and CircomReduction convention succeeds.
        assert!(deserialize_and_validate_pk(&pk_bytes, WITHDRAW_V2_NUM_INSTANCE_VARS).is_ok());

        // Passing a 5-input (WithdrawCircuitV2) key into TransferCircuitV2 (7) or TransactCircuitV3 (9) fails.
        let err_transfer =
            deserialize_and_validate_pk(&pk_bytes, TRANSFER_V2_NUM_INSTANCE_VARS).unwrap_err();
        assert!(
            err_transfer.contains("public-input IC points"),
            "{err_transfer}"
        );

        let err_transact =
            deserialize_and_validate_pk(&pk_bytes, TRANSACT_V3_NUM_INSTANCE_VARS).unwrap_err();
        assert!(
            err_transact.contains("public-input IC points"),
            "{err_transact}"
        );

        // Trailing bytes are rejected.
        let mut trailing = pk_bytes.clone();
        trailing.extend_from_slice(&[0xaa, 0xbb]);
        let err_trailing =
            deserialize_and_validate_pk(&trailing, WITHDRAW_V2_NUM_INSTANCE_VARS).unwrap_err();
        assert!(err_trailing.contains("trailing bytes"), "{err_trailing}");

        // A key generated under LibsnarkReduction (h_query length = 2^k - 1) is rejected.
        let (pk_libsnark, _) = Groth16::<Bn254, LibsnarkReduction>::setup(
            SmallCircuit {
                num_public_inputs: WITHDRAW_V2_NUM_INSTANCE_VARS - 1,
            },
            &mut rng,
        )
        .expect("libsnark setup");
        let mut libsnark_bytes = Vec::new();
        pk_libsnark
            .serialize_compressed(&mut libsnark_bytes)
            .unwrap();
        let err_conv = deserialize_and_validate_pk(&libsnark_bytes, WITHDRAW_V2_NUM_INSTANCE_VARS)
            .unwrap_err();
        assert!(err_conv.contains("not a power of two"), "{err_conv}");
    }

    #[test]
    fn verify_generated_proof_accepts_valid_and_rejects_mismatched_public_inputs() {
        let mut rng = StdRng::seed_from_u64(0xBEEF);
        let (pk, _) = Groth16ProofSystem::setup(
            SmallCircuit {
                num_public_inputs: WITHDRAW_V2_NUM_INSTANCE_VARS - 1,
            },
            &mut rng,
        )
        .expect("setup");
        let proof = Groth16ProofSystem::prove(
            &pk,
            SmallCircuit {
                num_public_inputs: WITHDRAW_V2_NUM_INSTANCE_VARS - 1,
            },
            &mut rng,
        )
        .expect("prove");

        let valid_inputs = [
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
            Fr::from(5u64),
        ];
        assert!(verify_generated_proof(&pk, &valid_inputs, &proof).is_ok());

        let mut tampered_inputs = valid_inputs;
        tampered_inputs[0] = Fr::from(999u64);
        let err = verify_generated_proof(&pk, &tampered_inputs, &proof).unwrap_err();
        assert!(err.contains("did not pass self-verification"), "{err}");
    }
}

#[cfg(test)]
mod sum_overflow_and_blinding_guard_tests {
    use super::*;

    #[test]
    fn rejects_all_zero_merkle_root() {
        assert!(ensure_nonzero_root(&[0u8; 32]).is_err());
        let mut r = [0u8; 32];
        r[0] = 1;
        assert!(ensure_nonzero_root(&r).is_ok());
    }

    #[test]
    fn rejects_u64_sum_overflow_on_inputs_and_outputs() {
        let sk0 = [1u8; 32];
        let sk1 = [2u8; 32];
        let ib0 = [3u8; 32];
        let ib1 = [4u8; 32];
        let ob0 = [5u8; 32];
        let ob1 = [6u8; 32];

        // Input sum overflows u64
        assert!(validate_two_note_balance_and_blindings(
            [u64::MAX, 1],
            [sk0, sk1],
            [ib0, ib1],
            [u64::MAX, 1],
            [ob0, ob1],
            0,
        )
        .is_err());

        // Output sum overflows u64
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, sk1],
            [ib0, ib1],
            [u64::MAX, 2],
            [ob0, ob1],
            0,
        )
        .is_err());

        // Valid balanced 2-note transfer with distinct non-zero blindings/privkeys
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, sk1],
            [ib0, ib1],
            [400, 100],
            [ob0, ob1],
            -500,
        )
        .is_ok());
    }

    #[test]
    fn rejects_zero_or_reused_blindings_and_privkeys_on_dummy_notes() {
        let sk0 = [1u8; 32];
        let sk1 = [2u8; 32];
        let ib0 = [3u8; 32];
        let ib1 = [4u8; 32];
        let ob0 = [5u8; 32];
        let ob1 = [6u8; 32];

        // Dummy input (amount == 0) with all-zero privkey
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, [0u8; 32]],
            [ib0, ib1],
            [1_000, 0],
            [ob0, ob1],
            0,
        )
        .is_err());

        // Dummy input (amount == 0) with all-zero blinding
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, sk1],
            [ib0, [0u8; 32]],
            [1_000, 0],
            [ob0, ob1],
            0,
        )
        .is_err());

        // Filler output (amount == 0) with all-zero blinding
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, sk1],
            [ib0, ib1],
            [1_000, 0],
            [ob0, [0u8; 32]],
            0,
        )
        .is_err());

        // Reused blinding across inputs
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, sk1],
            [ib0, ib0],
            [1_000, 0],
            [ob0, ob1],
            0,
        )
        .is_err());

        // Reused blinding across outputs (including zero-value filler outputs)
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, sk1],
            [ib0, ib1],
            [0, 0],
            [ob0, ob0],
            -1_000,
        )
        .is_err());

        // Reused blinding between input and output
        assert!(validate_two_note_balance_and_blindings(
            [1_000, 0],
            [sk0, sk1],
            [ib0, ib1],
            [1_000, 0],
            [ib0, ob1],
            0,
        )
        .is_err());
    }
}

#[cfg(test)]
mod cross_version_pubkey_and_output_blinding_tests {
    use super::*;

    #[test]
    fn rejects_cross_version_pubkeys_and_output_blinding_secret_leaks() {
        let sk0 = [11u8; 32];
        let sk1 = [12u8; 32];
        let bl0 = [21u8; 32];
        let bl1 = [22u8; 32];
        let obl0 = [41u8; 32];
        let obl1 = [42u8; 32];

        let sk0_fr = Fr::from_le_bytes_mod_order(&sk0);
        let sk1_fr = Fr::from_le_bytes_mod_order(&sk1);
        let v2_pk0 = fr_to_le_bytes_32(poseidon_pubkey(sk0_fr));
        let v2_pk1 = fr_to_le_bytes_32(poseidon_pubkey(sk1_fr));
        let v3_pk0 = fr_to_le_bytes_32(v3_pubkey(sk0_fr));
        let v3_pk1 = fr_to_le_bytes_32(v3_pubkey(sk1_fr));

        // Valid v3 self/change outputs using v3_pubkey pass
        assert!(validate_cross_version_pubkeys_and_output_blindings(
            &[sk0, sk1],
            &[bl0, bl1],
            &[v3_pk0, v3_pk1],
            &[v2_pk0, v2_pk1],
            &[v3_pk0, [33u8; 32]],
            &[obl0, obl1],
            "prove_transact",
        )
        .is_ok());

        // Passing v2 spend_pubkey as output pubkey in prove_transact is rejected (prevents burning change note)
        assert!(validate_cross_version_pubkeys_and_output_blindings(
            &[sk0, sk1],
            &[bl0, bl1],
            &[v3_pk0, v3_pk1],
            &[v2_pk0, v2_pk1],
            &[v2_pk0, [33u8; 32]],
            &[obl0, obl1],
            "prove_transact",
        )
        .is_err());

        // Passing v3_note_pubkey as output pubkey in prove_transfer_v2 is rejected
        assert!(validate_cross_version_pubkeys_and_output_blindings(
            &[sk0, sk1],
            &[bl0, bl1],
            &[v2_pk0, v2_pk1],
            &[v3_pk0, v3_pk1],
            &[v3_pk0, [33u8; 32]],
            &[obl0, obl1],
            "prove_transfer_v2",
        )
        .is_err());

        // Output blinding colliding with input spend privkey (would leak spend key in encrypted note) is rejected
        assert!(validate_cross_version_pubkeys_and_output_blindings(
            &[sk0, sk1],
            &[bl0, bl1],
            &[v3_pk0, v3_pk1],
            &[v2_pk0, v2_pk1],
            &[v3_pk0, [33u8; 32]],
            &[sk0, obl1],
            "prove_transact",
        )
        .is_err());

        // Output blinding reusing input blinding or colliding with input pubkey is rejected
        assert!(validate_cross_version_pubkeys_and_output_blindings(
            &[sk0, sk1],
            &[bl0, bl1],
            &[v3_pk0, v3_pk1],
            &[v2_pk0, v2_pk1],
            &[v3_pk0, [33u8; 32]],
            &[bl0, obl1],
            "prove_transact",
        )
        .is_err());
        assert!(validate_cross_version_pubkeys_and_output_blindings(
            &[sk0, sk1],
            &[bl0, bl1],
            &[v3_pk0, v3_pk1],
            &[v2_pk0, v2_pk1],
            &[v3_pk0, [33u8; 32]],
            &[v3_pk0, obl1],
            "prove_transact",
        )
        .is_err());

        // Blinding equal to derived spend pubkey in note_commitment_v2 / prove_withdrawal_v2 is rejected
        assert!(validate_blinding_not_derived_pubkey(&sk0, &bl0, "note_commitment_v2").is_ok());
        assert!(validate_blinding_not_derived_pubkey(&sk0, &v2_pk0, "note_commitment_v2").is_err());
        assert!(validate_blinding_not_derived_pubkey(&sk0, &v3_pk0, "note_commitment_v2").is_err());
    }
}

#[cfg(test)]
mod fee_floor_asset_and_commitment_tests {
    use super::*;

    #[test]
    fn validates_withdrawal_fee_floor_asset_id_and_commitment_params() {
        // Withdrawal fee floor: gross < 400 (0 fee at 25 bps) is rejected, gross >= 400 passes
        assert!(validate_withdrawal_fee_floor(0, "test").is_err());
        assert!(validate_withdrawal_fee_floor(399, "test").is_err());
        assert!(validate_withdrawal_fee_floor(400, "test").is_ok());
        assert!(validate_withdrawal_fee_floor(500, "test").is_ok());

        // Native SOL [0; 32] and valid SPL asset pass
        assert!(
            validate_asset_id_bytes(&[0u8; 32], Some(&[1u8; 32]), Some(&[2u8; 32]), "test").is_ok()
        );
        assert!(
            validate_asset_id_bytes(&[7u8; 32], Some(&[1u8; 32]), Some(&[2u8; 32]), "test").is_ok()
        );

        // Raw WSOL/program IDs, mint_to_asset(WSOL_MINT), and ZERO_HASHES[1] (mint_to_asset([0; 32])) are rejected
        assert!(validate_asset_id_bytes(&WSOL_NATIVE_MINT_BYTES, None, None, "test").is_err());
        assert!(validate_asset_id_bytes(&SPL_TOKEN_PROGRAM_BYTES, None, None, "test").is_err());
        assert!(validate_asset_id_bytes(&PARALOOM_PROGRAM_ID_BYTES, None, None, "test").is_err());

        let zero_hash_1 = fr_to_le_bytes_32(v3_merkle_pair(Fr::from(0u64), Fr::from(0u64)));
        assert!(validate_asset_id_bytes(&zero_hash_1, None, None, "test").is_err());

        let wsol_lo = Fr::from_le_bytes_mod_order(&WSOL_NATIVE_MINT_BYTES[..16]);
        let wsol_hi = Fr::from_le_bytes_mod_order(&WSOL_NATIVE_MINT_BYTES[16..]);
        let wsol_asset = fr_to_le_bytes_32(v3_merkle_pair(wsol_lo, wsol_hi));
        assert!(validate_asset_id_bytes(&wsol_asset, None, None, "test").is_err());

        // Non-zero asset_id colliding with root or recipient is rejected
        assert!(validate_asset_id_bytes(&[9u8; 32], Some(&[9u8; 32]), None, "test").is_err());
        assert!(validate_asset_id_bytes(&[9u8; 32], None, Some(&[9u8; 32]), "test").is_err());

        // Commitment helper parameter collisions are rejected
        assert!(validate_commitment_helper_params(&[5u8; 32], &[5u8; 32], None, "test").is_err());
        let sk_pub = fr_to_le_bytes_32(poseidon_pubkey(Fr::from(11u64)));
        assert!(
            validate_commitment_helper_params(&[11u8; 32], &sk_pub, Some(&sk_pub), "test").is_err()
        );
        assert!(
            validate_commitment_helper_params(&[11u8; 32], &[12u8; 32], Some(&sk_pub), "test")
                .is_ok()
        );
    }
}

#[cfg(test)]
mod issue_51_tests {
    use super::*;

    #[test]
    fn rejects_protocol_pda_and_program_withdrawal_recipients() {
        for forbidden in [
            [0u8; 32],
            BRIDGE_VAULT_PDA_BYTES,
            SLASHED_FUNDS_VAULT_PDA_BYTES,
            BRIDGE_STATE_PDA_BYTES,
            MERKLE_TREE_PDA_BYTES,
            VALIDATOR_REGISTRY_PDA_BYTES,
            STAKE_VAULT_AUTHORITY_PDA_BYTES,
            ASSET_VAULT_AUTHORITY_PDA_BYTES,
            STAKE_TOKEN_VAULT_PDA_BYTES,
            PARALOOM_PROGRAM_ID_BYTES,
            SPL_TOKEN_PROGRAM_BYTES,
            SPL_TOKEN_2022_PROGRAM_BYTES,
            ASSOCIATED_TOKEN_PROGRAM_BYTES,
            BPF_LOADER_UPGRADEABLE_BYTES,
            RENT_SYSVAR_BYTES,
            CLOCK_SYSVAR_BYTES,
            WSOL_NATIVE_MINT_BYTES,
        ] {
            assert!(
                validate_withdrawal_recipient_address(&forbidden, "prove_transact").is_err(),
                "expected forbidden recipient {:?} to be rejected",
                forbidden
            );
        }
        assert!(validate_withdrawal_recipient_address(&[3u8; 32], "prove_transact").is_ok());
    }

    #[test]
    fn rejects_nonzero_leaf_index_and_raw_zero_internal_siblings_on_dummy_inputs() {
        let mut valid_dummy_path = vec![[0u8; 32]];
        for depth in 1..TX_LEVELS {
            valid_dummy_path.push([depth as u8; 32]);
        }
        let inputs_bad_idx = vec![
            TransactInputNote {
                amount: 1000,
                privkey_hex: "01".repeat(32),
                blinding_hex: "02".repeat(32),
                leaf_index: 5,
                path_hex: vec![],
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: "03".repeat(32),
                blinding_hex: "04".repeat(32),
                leaf_index: 5,
                path_hex: vec![],
            },
        ];
        assert!(validate_v3_dummy_and_filler_invariants(
            &inputs_bad_idx,
            &[
                Some(valid_dummy_path.clone()),
                Some(valid_dummy_path.clone())
            ],
            &[Some(500), Some(0)],
            &[Some([9u8; 32]), Some([9u8; 32])],
            -500,
        )
        .is_err());

        let mut bad_zero_sib_path = valid_dummy_path.clone();
        bad_zero_sib_path[1] = [0u8; 32];
        let inputs_ok_idx = vec![
            TransactInputNote {
                amount: 1000,
                privkey_hex: "01".repeat(32),
                blinding_hex: "02".repeat(32),
                leaf_index: 0,
                path_hex: vec![],
            },
            TransactInputNote {
                amount: 0,
                privkey_hex: "03".repeat(32),
                blinding_hex: "04".repeat(32),
                leaf_index: 0,
                path_hex: vec![],
            },
        ];
        assert!(validate_v3_dummy_and_filler_invariants(
            &inputs_ok_idx,
            &[Some(valid_dummy_path.clone()), Some(bad_zero_sib_path)],
            &[Some(500), Some(0)],
            &[Some([9u8; 32]), Some([9u8; 32])],
            -500,
        )
        .is_err());

        // Mismatched withdrawal filler pubkey is rejected when outputs[1].amount == 0
        assert!(validate_v3_dummy_and_filler_invariants(
            &inputs_ok_idx,
            &[Some(valid_dummy_path.clone()), Some(valid_dummy_path)],
            &[Some(500), Some(0)],
            &[Some([9u8; 32]), Some([10u8; 32])],
            -500,
        )
        .is_err());
    }

    #[test]
    fn rejects_duplicate_level_siblings_and_sibling_object_collisions() {
        let dup_path = vec![[1u8; 32], [2u8; 32], [1u8; 32]];
        assert!(validate_merkle_path_sibling_uniqueness_and_isolation(
            &dup_path,
            &[[9u8; 32]],
            &[[8u8; 32]],
            &[0u8; 32],
            Some(&[7u8; 32]),
            "test",
        )
        .is_err());

        let distinct_path = vec![[1u8; 32], [2u8; 32], [3u8; 32]];
        assert!(validate_merkle_path_sibling_uniqueness_and_isolation(
            &distinct_path,
            &[[2u8; 32]],
            &[[8u8; 32]],
            &[0u8; 32],
            Some(&[7u8; 32]),
            "test",
        )
        .is_err());
        assert!(validate_merkle_path_sibling_uniqueness_and_isolation(
            &distinct_path,
            &[[9u8; 32]],
            &[[3u8; 32]],
            &[0u8; 32],
            Some(&[7u8; 32]),
            "test",
        )
        .is_err());
        assert!(validate_merkle_path_sibling_uniqueness_and_isolation(
            &distinct_path,
            &[[9u8; 32]],
            &[[8u8; 32]],
            &[1u8; 32],
            Some(&[7u8; 32]),
            "test",
        )
        .is_err());
        assert!(validate_merkle_path_sibling_uniqueness_and_isolation(
            &distinct_path,
            &[[9u8; 32]],
            &[[8u8; 32]],
            &[0u8; 32],
            Some(&[1u8; 32]),
            "test",
        )
        .is_err());
    }
}

#[cfg(test)]
mod issue_55_tests {
    use super::*;
    use ark_ec::CurveGroup;

    #[test]
    fn pk_and_proof_integrity_rejects_toxic_waste_collisions_and_duplicate_ic() {
        let g1_a = G1Affine::generator();
        let g1_b = (g1_a + g1_a).into_affine();
        let g1_c = (g1_b + g1_a).into_affine();
        let g1_d = (g1_c + g1_a).into_affine();
        let g2_a = G2Affine::generator();
        let g2_b = (g2_a + g2_a).into_affine();
        let g2_c = (g2_b + g2_a).into_affine();

        let vk = ark_groth16::VerifyingKey::<Bn254> {
            alpha_g1: g1_a,
            beta_g2: g2_a,
            gamma_g2: g2_b,
            delta_g2: g2_c,
            gamma_abc_g1: vec![g1_a, g1_b, g1_c],
        };
        let pk = ProvingKey::<Bn254> {
            vk,
            beta_g1: g1_b,
            delta_g1: g1_c,
            a_query: vec![g1_a],
            b_g1_query: vec![g1_a],
            b_g2_query: vec![g2_a],
            h_query: vec![g1_a],
            l_query: vec![g1_a],
        };
        let proof = Proof::<Bn254> {
            a: g1_a,
            b: g2_a,
            c: g1_d,
        };
        assert!(validate_pk_and_proof_integrity(&pk, &proof, "test").is_ok());
        assert!(!is_ceremony_transact_v3_vk(&pk.vk));

        // Zero delta_g1 must be rejected.
        let mut bad_pk = pk.clone();
        bad_pk.delta_g1 = G1Affine::zero();
        assert!(validate_pk_and_proof_integrity(&bad_pk, &proof, "test").is_err());

        // Colliding gamma_g2 == delta_g2 must be rejected.
        let mut bad_vk_pk = pk.clone();
        bad_vk_pk.vk.gamma_g2 = bad_vk_pk.vk.delta_g2;
        assert!(validate_pk_and_proof_integrity(&bad_vk_pk, &proof, "test").is_err());

        // Duplicate IC points in gamma_abc_g1 must be rejected.
        let mut dup_ic_pk = pk.clone();
        dup_ic_pk.vk.gamma_abc_g1 = vec![g1_a, g1_b, g1_a];
        assert!(validate_pk_and_proof_integrity(&dup_ic_pk, &proof, "test").is_err());

        // Degenerate proof.a == proof.c must be rejected.
        let bad_proof = Proof::<Bn254> {
            a: g1_a,
            b: g2_a,
            c: g1_a,
        };
        assert!(validate_pk_and_proof_integrity(&pk, &bad_proof, "test").is_err());
    }

    #[test]
    fn v3_merkle_path_verifies_bit_fold_consistency() {
        let leaf0 = v3_commit(
            Fr::from(500u64),
            v3_pubkey(Fr::from(11u64)),
            Fr::from(7u64),
            Fr::from(0u64),
        );
        let leaf1 = v3_commit(
            Fr::from(900u64),
            v3_pubkey(Fr::from(22u64)),
            Fr::from(9u64),
            Fr::from(0u64),
        );
        let leaves_json = serde_json::to_string(&[
            hex::encode(fr_to_le_bytes_32(leaf0)),
            hex::encode(fr_to_le_bytes_32(leaf1)),
        ])
        .unwrap();
        let res = v3_merkle_path(&leaves_json, 1).expect("valid path");
        let parsed: serde_json::Value = serde_json::from_str(&res).unwrap();
        assert_eq!(parsed["path"].as_array().unwrap().len(), TX_LEVELS);
    }
}
