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

use privacy::circuits::{Groth16ProofSystem, TransferCircuitV2, WithdrawCircuitV2, TX_LEVELS};
use privacy::poseidon::{
    poseidon_commit, poseidon_commit_spend, poseidon_nullifier_spend, poseidon_pubkey,
    poseidon_signature,
};
use sha2::{Digest, Sha256};

fn deserialize_u64_or_string<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct U64OrStringVisitor;

    impl<'de> serde::de::Visitor<'de> for U64OrStringVisitor {
        type Value = u64;

        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            formatter.write_str("a 64-bit unsigned integer or decimal string")
        }

        fn visit_u64<E>(self, value: u64) -> Result<u64, E>
        where
            E: serde::de::Error,
        {
            Ok(value)
        }

        fn visit_i64<E>(self, value: i64) -> Result<u64, E>
        where
            E: serde::de::Error,
        {
            if value < 0 {
                return Err(E::custom("amount cannot be negative"));
            }
            Ok(value as u64)
        }

        fn visit_str<E>(self, value: &str) -> Result<u64, E>
        where
            E: serde::de::Error,
        {
            value
                .trim()
                .parse::<u64>()
                .map_err(|e| E::custom(format!("invalid u64 string '{value}': {e}")))
        }
    }

    deserializer.deserialize_any(U64OrStringVisitor)
}

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

/// Build a `(sibling, is_left)` Merkle path from parallel hex/bool arrays.
fn merkle_path_from(
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

    let path_hex: Vec<String> = serde_json::from_str(path_hex_json)
        .map_err(|e| format!("bad path json: {e}"))?;
    let indices: Vec<bool> = serde_json::from_str(indices_json)
        .map_err(|e| format!("bad indices json: {e}"))?;
    if path_hex.len() != TX_LEVELS || indices.len() != TX_LEVELS {
        return Err(format!(
            "expected {TX_LEVELS}-level merkle path and indices, got {} and {}",
            path_hex.len(),
            indices.len()
        ));
    }
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
    ).map_err(|e| JsValue::from_str(&e))
}

/// An input note being spent in a transfer. `path_hex`/`indices` are the
/// root-less Merkle path proving the note's commitment is in the tree, pulled
/// from the path server.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct TransferInputV2 {
    #[serde(deserialize_with = "deserialize_u64_or_string")]
    pub amount: u64,
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
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct TransferOutputV2 {
    #[serde(deserialize_with = "deserialize_u64_or_string")]
    pub amount: u64,
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

    let inputs: Vec<TransferInputV2> = serde_json::from_str(inputs_json)
        .map_err(|e| format!("bad inputs json: {e}"))?;
    let outputs: Vec<TransferOutputV2> = serde_json::from_str(outputs_json)
        .map_err(|e| format!("bad outputs json: {e}"))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(String::from(
            "transfer requires exactly 2 inputs and 2 outputs",
        ));
    }

    if outputs[0].amount == 0 && outputs[1].amount == 0 {
        return Err(String::from("transfer outputs must not both be zero"));
    }

    let mut in_commitments = Vec::with_capacity(2);
    let mut nullifiers = Vec::with_capacity(2);
    let mut input_values = Vec::with_capacity(2);
    let mut input_blindings = Vec::with_capacity(2);
    let mut input_privkeys = Vec::with_capacity(2);
    let mut input_paths = Vec::with_capacity(2);
    for (i, inp) in inputs.iter().enumerate() {
        if inp.amount == 0 {
            return Err(format!(
                "input {i} note amount must be greater than zero in transfer v2"
            ));
        }
        if inp.path_hex.len() != TX_LEVELS || inp.indices.len() != TX_LEVELS {
            return Err(format!(
                "expected {TX_LEVELS}-level merkle path and indices, got {} and {}",
                inp.path_hex.len(),
                inp.indices.len()
            ));
        }

        let blinding = hex32_inner(&inp.blinding_hex)?;
        let privkey = hex32_inner(&inp.privkey_hex)?;
        let sk = Fr::from_le_bytes_mod_order(&privkey);
        let commitment_fr = poseidon_commit_spend(
            Fr::from(inp.amount),
            poseidon_pubkey(sk),
            Fr::from_le_bytes_mod_order(&blinding),
            asset_fr,
        );
        in_commitments.push(commitment_fr);

        let leaf_index = leaf_index_from(&inp.indices);
        let signature = poseidon_signature(sk, commitment_fr, Fr::from(leaf_index));
        let nullifier_fr = poseidon_nullifier_spend(commitment_fr, Fr::from(leaf_index), signature);
        nullifiers.push(fr_to_le_bytes_32(nullifier_fr));
        input_values.push(inp.amount);
        input_blindings.push(blinding);
        input_privkeys.push(privkey);
        input_paths.push(merkle_path_from(&inp.path_hex, &inp.indices)?);
    }

    if in_commitments[0] == in_commitments[1] {
        return Err(String::from("duplicate input note commitments are rejected"));
    }

    let mut output_commitments = Vec::with_capacity(2);
    let mut out_commitments_fr = Vec::with_capacity(2);
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
        out_commitments_fr.push(commitment_fr);
        output_values.push(out.amount);
        output_blindings.push(blinding);
        output_pubkeys.push(pubkey);
    }

    if output_commitments[0] == output_commitments[1] {
        return Err(String::from("duplicate output note commitments are rejected"));
    }

    for oc in &out_commitments_fr {
        if in_commitments.contains(oc) {
            return Err(String::from(
                "output commitment must not collide with input commitment",
            ));
        }
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
    ).map_err(|e| JsValue::from_str(&e))
}

// ===== circuit v3 (#350): unified transact =====

use privacy::circuits::TransactCircuitV3;
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
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct TransactInputNote {
    #[serde(deserialize_with = "deserialize_u64_or_string")]
    pub amount: u64,
    pub privkey_hex: String,
    pub blinding_hex: String,
    #[serde(deserialize_with = "deserialize_u64_or_string")]
    pub leaf_index: u64,
    pub path_hex: Vec<String>,
}

/// An output note being created. A value-0 note is a valid "empty" output.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct TransactOutputNote {
    #[serde(deserialize_with = "deserialize_u64_or_string")]
    pub amount: u64,
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
        return Err(String::from(
            "positive ext_amount: deposits go through deposit_note, not transact",
        ));
    }
    let root = hex32_inner(root_hex)?;
    let recipient = hex32_inner(recipient_hex)?;

    let inputs: Vec<TransactInputNote> = serde_json::from_str(inputs_json)
        .map_err(|e| format!("bad inputs json: {e}"))?;
    let outputs: Vec<TransactOutputNote> = serde_json::from_str(outputs_json)
        .map_err(|e| format!("bad outputs json: {e}"))?;
    if inputs.len() != 2 || outputs.len() != 2 {
        return Err(String::from("transact is fixed 2-in/2-out"));
    }

    if ext_amount == 0 && outputs[0].amount == 0 && outputs[1].amount == 0 {
        return Err(String::from("shielded transfer outputs must not both be zero"));
    }

    // The shielded asset: all-zero for native SOL, or `mint_to_asset(mint)` for
    // a shielded SPL note (#779). All notes in one transact share one asset.
    let asset = Fr::from_le_bytes_mod_order(&hex32_inner(asset_id_hex)?);

    let mut in_commitments = Vec::with_capacity(2);
    let mut in_amounts = Vec::new();
    let mut in_privkeys = Vec::new();
    let mut in_blindings = Vec::new();
    let mut in_leaf_indices = Vec::new();
    let mut in_paths = Vec::new();
    let mut nullifiers = Vec::new();
    for (i, inp) in inputs.iter().enumerate() {
        if inp.amount == 0 && inp.leaf_index != 0 {
            return Err(format!(
                "input {i} dummy note (amount 0) must have leaf_index 0, got {}",
                inp.leaf_index
            ));
        }

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
        in_commitments.push(c);

        let sig = v3_signature(sk, c, Fr::from(inp.leaf_index));
        let nf = v3_nullifier(c, Fr::from(inp.leaf_index), sig);
        nullifiers.push(fr_to_le_bytes_32(nf));

        in_amounts.push(Some(inp.amount));
        in_privkeys.push(Some(privkey));
        in_blindings.push(Some(blinding));
        in_leaf_indices.push(Some(inp.leaf_index));
        in_paths.push(Some(path));
    }

    if in_commitments[0] == in_commitments[1] {
        return Err(String::from("duplicate input note commitments are rejected"));
    }

    let mut out_commitments_fr = Vec::with_capacity(2);
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
        out_commitments_fr.push(oc);

        out_amounts.push(Some(outp.amount));
        out_pubkeys.push(Some(pubkey));
        out_blindings.push(Some(blinding));
    }

    if output_commitments[0] == output_commitments[1] {
        return Err(String::from("duplicate output note commitments are rejected"));
    }

    for oc in &out_commitments_fr {
        if in_commitments.contains(oc) {
            return Err(String::from(
                "output commitment must not collide with input commitment",
            ));
        }
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
    ).map_err(|e| JsValue::from_str(&e))
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

    #[test]
    fn test_deserialize_u64_or_string_transfer_and_transact() {
        let json_int = r#"{"amount": 1000, "privkey_hex": "01", "blinding_hex": "02", "path_hex": [], "indices": []}"#;
        let note: TransferInputV2 = serde_json::from_str(json_int).unwrap();
        assert_eq!(note.amount, 1000);

        let json_str = r#"{"amount": "9007199254740993", "privkey_hex": "01", "blinding_hex": "02", "path_hex": [], "indices": []}"#;
        let note: TransferInputV2 = serde_json::from_str(json_str).unwrap();
        assert_eq!(note.amount, 9007199254740993u64);

        let out_json = r#"{"amount": "500", "pubkey_hex": "01", "blinding_hex": "02"}"#;
        let out_note: TransferOutputV2 = serde_json::from_str(out_json).unwrap();
        assert_eq!(out_note.amount, 500);

        let tx_in_json = r#"{"amount": "12345", "privkey_hex": "01", "blinding_hex": "02", "leaf_index": "42", "path_hex": []}"#;
        let tx_in: TransactInputNote = serde_json::from_str(tx_in_json).unwrap();
        assert_eq!(tx_in.amount, 12345);
        assert_eq!(tx_in.leaf_index, 42);

        let tx_out_json = r#"{"amount": "67890", "pubkey_hex": "01", "blinding_hex": "02"}"#;
        let tx_out: TransactOutputNote = serde_json::from_str(tx_out_json).unwrap();
        assert_eq!(tx_out.amount, 67890);
    }

    #[test]
    fn test_prove_withdrawal_v2_rejects_non_32_level_paths() {
        let dummy_pk = vec![0u8; 32];
        let root = hex::encode([1u8; 32]);
        let blinding = hex::encode([2u8; 32]);
        let privkey = hex::encode([3u8; 32]);
        let asset_id = hex::encode([0u8; 32]);
        let recipient = hex::encode([4u8; 32]);

        // 31 levels instead of 32
        let path = serde_json::to_string(&vec![hex::encode([5u8; 32]); 31]).unwrap();
        let indices = serde_json::to_string(&vec![false; 31]).unwrap();

        let res = prove_withdrawal_v2_inner(
            &dummy_pk,
            &root,
            100,
            &blinding,
            &privkey,
            &asset_id,
            &recipient,
            &path,
            &indices,
        );
        assert!(res.is_err());
        let err_msg = format!("{:?}", res.unwrap_err());
        assert!(err_msg.contains("expected 32-level merkle path"));
    }

    #[test]
    fn test_prove_transfer_v2_rejections() {
        let dummy_pk = vec![0u8; 32];
        let root = hex::encode([1u8; 32]);
        let asset_id = hex::encode([0u8; 32]);

        let in_path_32 = vec![hex::encode([5u8; 32]); 32];
        let in_indices_32 = vec![false; 32];

        // 1. Zero amount in input note
        let zero_in = vec![
            TransferInputV2 {
                amount: 0,
                privkey_hex: hex::encode([1u8; 32]),
                blinding_hex: hex::encode([2u8; 32]),
                path_hex: in_path_32.clone(),
                indices: in_indices_32.clone(),
            },
            TransferInputV2 {
                amount: 100,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                path_hex: in_path_32.clone(),
                indices: in_indices_32.clone(),
            },
        ];
        let outs = vec![
            TransferOutputV2 {
                amount: 50,
                pubkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
            },
            TransferOutputV2 {
                amount: 50,
                pubkey_hex: hex::encode([7u8; 32]),
                blinding_hex: hex::encode([8u8; 32]),
            },
        ];
        let res = prove_transfer_v2_inner(
            &dummy_pk,
            &root,
            &asset_id,
            &serde_json::to_string(&zero_in).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        let err_msg = format!("{:?}", res.unwrap_err());
        assert!(err_msg.contains("amount must be greater than zero"));

        // 2. Both outputs zero
        let valid_ins = vec![
            TransferInputV2 {
                amount: 100,
                privkey_hex: hex::encode([1u8; 32]),
                blinding_hex: hex::encode([2u8; 32]),
                path_hex: in_path_32.clone(),
                indices: in_indices_32.clone(),
            },
            TransferInputV2 {
                amount: 100,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                path_hex: in_path_32.clone(),
                indices: in_indices_32.clone(),
            },
        ];
        let zero_outs = vec![
            TransferOutputV2 {
                amount: 0,
                pubkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
            },
            TransferOutputV2 {
                amount: 0,
                pubkey_hex: hex::encode([7u8; 32]),
                blinding_hex: hex::encode([8u8; 32]),
            },
        ];
        let res = prove_transfer_v2_inner(
            &dummy_pk,
            &root,
            &asset_id,
            &serde_json::to_string(&valid_ins).unwrap(),
            &serde_json::to_string(&zero_outs).unwrap(),
        );
        let err_msg = format!("{:?}", res.unwrap_err());
        assert!(err_msg.contains("transfer outputs must not both be zero"));

        // 3. Duplicate input commitments across distinct indices
        let mut dup_in = valid_ins.clone();
        dup_in[1] = dup_in[0].clone();
        dup_in[1].indices[0] = true; // distinct leaf_index / indices
        let res = prove_transfer_v2_inner(
            &dummy_pk,
            &root,
            &asset_id,
            &serde_json::to_string(&dup_in).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        let err_msg = format!("{:?}", res.unwrap_err());
        assert!(err_msg.contains("duplicate input note commitments are rejected"));
    }

    #[test]
    fn test_prove_transact_rejections() {
        let dummy_pk = vec![0u8; 32];
        let root = hex::encode([1u8; 32]);
        let recipient = hex::encode([2u8; 32]);
        let asset_id = hex::encode([0u8; 32]);
        let path_32 = vec![hex::encode([3u8; 32]); 32];

        // 1. Dummy input note with non-zero leaf index
        let ins_dummy_nonzero_idx = vec![
            TransactInputNote {
                amount: 0,
                privkey_hex: hex::encode([1u8; 32]),
                blinding_hex: hex::encode([2u8; 32]),
                leaf_index: 5, // non-zero
                path_hex: path_32.clone(),
            },
            TransactInputNote {
                amount: 100,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                leaf_index: 10,
                path_hex: path_32.clone(),
            },
        ];
        let outs = vec![
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
            },
            TransactOutputNote {
                amount: 50,
                pubkey_hex: hex::encode([7u8; 32]),
                blinding_hex: hex::encode([8u8; 32]),
            },
        ];
        let res = prove_transact_inner(
            &dummy_pk,
            &root,
            0,
            &recipient,
            &asset_id,
            &serde_json::to_string(&ins_dummy_nonzero_idx).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        let err_msg = format!("{:?}", res.unwrap_err());
        assert!(err_msg.contains("dummy note (amount 0) must have leaf_index 0"));

        // 2. Pure shielded transfer with both outputs zero
        let valid_ins = vec![
            TransactInputNote {
                amount: 50,
                privkey_hex: hex::encode([1u8; 32]),
                blinding_hex: hex::encode([2u8; 32]),
                leaf_index: 0,
                path_hex: path_32.clone(),
            },
            TransactInputNote {
                amount: 50,
                privkey_hex: hex::encode([3u8; 32]),
                blinding_hex: hex::encode([4u8; 32]),
                leaf_index: 1,
                path_hex: path_32.clone(),
            },
        ];
        let zero_outs = vec![
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([5u8; 32]),
                blinding_hex: hex::encode([6u8; 32]),
            },
            TransactOutputNote {
                amount: 0,
                pubkey_hex: hex::encode([7u8; 32]),
                blinding_hex: hex::encode([8u8; 32]),
            },
        ];
        let res = prove_transact_inner(
            &dummy_pk,
            &root,
            0,
            &recipient,
            &asset_id,
            &serde_json::to_string(&valid_ins).unwrap(),
            &serde_json::to_string(&zero_outs).unwrap(),
        );
        let err_msg = format!("{:?}", res.unwrap_err());
        assert!(err_msg.contains("shielded transfer outputs must not both be zero"));

        // 3. Duplicate input commitments across distinct leaf_index
        let mut dup_ins = valid_ins.clone();
        dup_ins[1] = dup_ins[0].clone();
        dup_ins[1].leaf_index = 99; // different leaf_index
        let res = prove_transact_inner(
            &dummy_pk,
            &root,
            0,
            &recipient,
            &asset_id,
            &serde_json::to_string(&dup_ins).unwrap(),
            &serde_json::to_string(&outs).unwrap(),
        );
        let err_msg = format!("{:?}", res.unwrap_err());
        assert!(err_msg.contains("duplicate input note commitments are rejected"));
    }
}
