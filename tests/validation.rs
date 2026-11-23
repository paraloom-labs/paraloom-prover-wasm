use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use paraloom_prover_wasm::{
    is_canonical_field, last_error, mint_to_asset, note_commitment, note_commitment_v2,
    prove_transact, prove_transfer_v2, prove_withdrawal_v2, spend_pubkey, v3_merkle_path,
    v3_note_commitment, v3_note_commitment_asset, v3_note_pubkey, MIN_WITHDRAWAL_AMOUNT,
    WITHDRAWAL_FEE_BPS,
};

fn fr_to_le(f: &Fr) -> [u8; 32] {
    let mut out = [0u8; 32];
    let le = f.into_bigint().to_bytes_le();
    out[..le.len().min(32)].copy_from_slice(&le[..le.len().min(32)]);
    out
}

fn non_canonical_scalar() -> [u8; 32] {
    // BN254 scalar field modulus r in 32-byte LE + 1.
    // 0xFF...FF is also well above r (~2^254).
    [0xffu8; 32]
}

fn modulus_scalar() -> [u8; 32] {
    // Exact modulus r as 32 LE bytes (r mod r == 0, so non-canonical).
    let ple = <Fr as PrimeField>::MODULUS.to_bytes_le();
    let mut out = [0u8; 32];
    out[..ple.len().min(32)].copy_from_slice(&ple[..ple.len().min(32)]);
    out
}

#[test]
fn test_withdrawal_fee_constants() {
    assert_eq!(WITHDRAWAL_FEE_BPS, 25);
    assert_eq!(MIN_WITHDRAWAL_AMOUNT, 400);
    assert_eq!(10_000 / WITHDRAWAL_FEE_BPS, MIN_WITHDRAWAL_AMOUNT);
}

#[test]
fn test_is_canonical_field() {
    let zero = [0u8; 32];
    assert!(is_canonical_field(&zero));

    let one = fr_to_le(&Fr::from(1u64));
    assert!(is_canonical_field(&one));

    let non_canon = non_canonical_scalar();
    assert!(!is_canonical_field(&non_canon));

    let modulus = modulus_scalar();
    assert!(!is_canonical_field(&modulus));
}

#[test]
fn test_prove_withdrawal_v2_sub_400_rejected() {
    let dummy_pk = vec![];
    let root = hex::encode([0u8; 32]);
    let blinding = hex::encode([1u8; 32]);
    let privkey = hex::encode([2u8; 32]);
    let asset_id = hex::encode([0u8; 32]);
    let dest_recipient = hex::encode([3u8; 32]);
    let path = "[]";
    let indices = "[]";

    // Amounts 0, 1, and 399 must be rejected
    for amt in [0, 1, 399] {
        let res = prove_withdrawal_v2(
            &dummy_pk,
            &root,
            amt,
            &blinding,
            &privkey,
            &asset_id,
            &dest_recipient,
            path,
            indices,
        );
        assert!(res.is_err());
        let err = last_error().unwrap();
        assert!(
            err.contains("withdrawal amount must be at least 400"),
            "expected fee truncation error, got: {err}"
        );
    }
}

#[test]
fn test_prove_transact_sub_400_withdrawal_rejected() {
    let dummy_pk = vec![];
    let root = hex::encode([0u8; 32]);
    let recipient = hex::encode([3u8; 32]);
    let asset_id = hex::encode([0u8; 32]);
    let inputs = "[]";
    let outputs = "[]";

    // ext_amount -1 and -399 are sub-400 withdrawals
    for ext_amt in [-1, -399] {
        let res = prove_transact(
            &dummy_pk, &root, ext_amt, &recipient, &asset_id, inputs, outputs,
        );
        assert!(res.is_err());
        let err = last_error().unwrap();
        assert!(
            err.contains("withdrawal amount must be at least 400"),
            "expected fee truncation error, got: {err}"
        );
    }

    // positive ext_amount must still be rejected
    for ext_amt in [1, 500] {
        let res = prove_transact(
            &dummy_pk, &root, ext_amt, &recipient, &asset_id, inputs, outputs,
        );
        assert!(res.is_err());
        let err = last_error().unwrap();
        assert!(
            err.contains("positive ext_amount"),
            "expected deposit rejection, got: {err}"
        );
    }
}

#[test]
fn test_poisoned_asset_id_rejected() {
    let dummy_pk = vec![];
    let bad_asset = hex::encode(non_canonical_scalar());
    let valid_canon = hex::encode([0u8; 32]);
    let valid_priv = hex::encode(fr_to_le(&Fr::from(42u64)));
    let valid_blind = hex::encode(fr_to_le(&Fr::from(99u64)));
    let valid_pub = hex::encode(fr_to_le(&Fr::from(123u64)));

    // prove_transact with poisoned asset_id_hex
    let res = prove_transact(
        &dummy_pk,
        &valid_canon,
        -500,
        &valid_canon,
        &bad_asset,
        "[]",
        "[]",
    );
    assert!(res.is_err());
    let err = last_error().unwrap();
    assert!(err.contains("non-canonical asset_id"), "got: {err}");

    // prove_withdrawal_v2 with poisoned asset_id_hex
    let res = prove_withdrawal_v2(
        &dummy_pk,
        &valid_canon,
        500,
        &valid_blind,
        &valid_priv,
        &bad_asset,
        &valid_canon,
        "[]",
        "[]",
    );
    assert!(res.is_err());
    let err = last_error().unwrap();
    assert!(err.contains("non-canonical asset_id"), "got: {err}");

    // note_commitment_v2 with poisoned asset_id_hex
    let res = note_commitment_v2(100, &valid_priv, &valid_blind, &bad_asset);
    assert!(res.is_err());
    let err = last_error().unwrap();
    assert!(err.contains("non-canonical asset_id"), "got: {err}");

    // v3_note_commitment_asset with poisoned asset_id_hex
    let res = v3_note_commitment_asset(100, &valid_pub, &valid_blind, &bad_asset);
    assert!(res.is_err());
    let err = last_error().unwrap();
    assert!(err.contains("non-canonical asset_id"), "got: {err}");

    // prove_transfer_v2 with poisoned asset_id_hex
    let res = prove_transfer_v2(&dummy_pk, &valid_canon, &bad_asset, "[]", "[]");
    assert!(res.is_err());
    let err = last_error().unwrap();
    assert!(err.contains("non-canonical asset_id"), "got: {err}");
}

#[test]
fn test_commitment_helpers_reject_colliding_witness_parameters() {
    let bad_param = hex::encode(non_canonical_scalar());
    let canon_param = hex::encode(fr_to_le(&Fr::from(10u64)));

    // note_commitment
    let res1 = note_commitment(100, &bad_param, &canon_param);
    assert!(res1.is_err());
    assert!(last_error().unwrap().contains("non-canonical randomness"));

    let res2 = note_commitment(100, &canon_param, &bad_param);
    assert!(res2.is_err());
    assert!(last_error().unwrap().contains("non-canonical recipient"));

    // spend_pubkey
    let res = spend_pubkey(&bad_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical privkey"));

    // note_commitment_v2
    let res = note_commitment_v2(100, &bad_param, &canon_param, &canon_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical privkey"));

    let res = note_commitment_v2(100, &canon_param, &bad_param, &canon_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical blinding"));

    // v3_note_pubkey
    let res = v3_note_pubkey(&bad_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical privkey"));

    // v3_note_commitment
    let res = v3_note_commitment(100, &bad_param, &canon_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical pubkey"));

    let res = v3_note_commitment(100, &canon_param, &bad_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical blinding"));

    // v3_note_commitment_asset
    let res = v3_note_commitment_asset(100, &bad_param, &canon_param, &canon_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical pubkey"));

    let res = v3_note_commitment_asset(100, &canon_param, &bad_param, &canon_param);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical blinding"));

    // v3_merkle_path
    let leaves_json = serde_json::to_string(&[bad_param]).unwrap();
    let res = v3_merkle_path(&leaves_json, 0);
    assert!(res.is_err());
    assert!(last_error().unwrap().contains("non-canonical leaf"));
}

#[test]
fn test_mint_to_asset_derives_canonical_field_element() {
    // An arbitrary 32-byte Solana mint pubkey (which can exceed the field modulus)
    let non_canon_mint = hex::encode([0xffu8; 32]);
    let asset_hex = mint_to_asset(&non_canon_mint).expect("mint_to_asset must succeed");
    let asset_bytes: [u8; 32] = hex::decode(&asset_hex).unwrap().try_into().unwrap();
    assert!(
        is_canonical_field(&asset_bytes),
        "mint_to_asset must derive a canonical field element"
    );
}

#[test]
fn test_canonical_commitment_helpers_happy_path() {
    let privkey = hex::encode(fr_to_le(&Fr::from(12345u64)));
    let blinding = hex::encode(fr_to_le(&Fr::from(67890u64)));
    let asset_id = hex::encode([0u8; 32]);

    let pk_v2 = spend_pubkey(&privkey).expect("spend_pubkey");
    assert_eq!(pk_v2.len(), 64);

    let c_v2 = note_commitment_v2(500, &privkey, &blinding, &asset_id).expect("note_commitment_v2");
    assert_eq!(c_v2.len(), 64);

    let pk_v3 = v3_note_pubkey(&privkey).expect("v3_note_pubkey");
    assert_eq!(pk_v3.len(), 64);

    let c_v3 = v3_note_commitment(500, &pk_v3, &blinding).expect("v3_note_commitment");
    assert_eq!(c_v3.len(), 64);

    let c_v3_asset = v3_note_commitment_asset(500, &pk_v3, &blinding, &asset_id)
        .expect("v3_note_commitment_asset");
    assert_eq!(c_v3, c_v3_asset);
}
