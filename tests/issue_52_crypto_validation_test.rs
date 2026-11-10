use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use paraloom_prover_wasm::{
    note_commitment, note_commitment_v2, spend_pubkey, v3_note_commitment,
    v3_note_commitment_asset, v3_note_pubkey, ZERO_HASHES,
};

fn hx(bytes: &[u8]) -> String {
    hex::encode(bytes)
}

fn fr_to_le(fr: &Fr) -> [u8; 32] {
    let mut v = fr.into_bigint().to_bytes_le();
    v.resize(32, 0);
    let mut o = [0u8; 32];
    o.copy_from_slice(&v[..32]);
    o
}

#[test]
fn test_spend_pubkey_validation() {
    // 1. All-zero private key rejected
    let zero_hex = "00".repeat(32);
    assert!(spend_pubkey(&zero_hex).is_err(), "all-zero private key must be rejected");

    // 2. Non-canonical scalar (Fr::MODULUS or all 0xff) rejected
    let non_canonical = "ff".repeat(32);
    assert!(spend_pubkey(&non_canonical).is_err(), "non-canonical scalar must be rejected");

    // 3. Reserved zero-hash constant rejected
    let reserved_zh1 = hx(&ZERO_HASHES[1]);
    assert!(spend_pubkey(&reserved_zh1).is_err(), "reserved zero hash must be rejected");

    // 4. Valid canonical private key succeeds
    let valid_priv = hx(&fr_to_le(&Fr::from(42u64)));
    assert!(spend_pubkey(&valid_priv).is_ok(), "valid private key must succeed");
}

#[test]
fn test_v3_note_pubkey_validation() {
    let zero_hex = "00".repeat(32);
    assert!(v3_note_pubkey(&zero_hex).is_err(), "all-zero private key must be rejected");

    let non_canonical = "ff".repeat(32);
    assert!(v3_note_pubkey(&non_canonical).is_err(), "non-canonical scalar must be rejected");

    let reserved_zh2 = hx(&ZERO_HASHES[2]);
    assert!(v3_note_pubkey(&reserved_zh2).is_err(), "reserved zero hash must be rejected");

    let valid_priv = hx(&fr_to_le(&Fr::from(42u64)));
    assert!(v3_note_pubkey(&valid_priv).is_ok(), "valid private key must succeed");
}

#[test]
fn test_v3_note_commitment_degenerate_keys_rejected() {
    let valid_blinding = hx(&fr_to_le(&Fr::from(123u64)));
    let valid_pubkey = v3_note_pubkey(&hx(&fr_to_le(&Fr::from(42u64)))).unwrap();

    // 1. All-zero pubkey rejected
    let zero_hex = "00".repeat(32);
    assert!(
        v3_note_commitment(100, &zero_hex, &valid_blinding).is_err(),
        "all-zero pubkey must be rejected"
    );

    // 2. All-zero blinding rejected
    assert!(
        v3_note_commitment(100, &valid_pubkey, &zero_hex).is_err(),
        "all-zero blinding must be rejected"
    );

    // 3. Degenerate zero-key public key Poseidon1(0) rejected
    use paraloom_prover_wasm::privacy::poseidon_circom::v3_pubkey;
    let degenerate_v3_zero_pk = hx(&fr_to_le(&v3_pubkey(Fr::from(0u64))));
    assert!(
        v3_note_commitment(100, &degenerate_v3_zero_pk, &valid_blinding).is_err(),
        "v3_pubkey(0) must be rejected"
    );

    // 4. Degenerate v2 zero-key public key Poseidon(0) rejected
    use paraloom_prover_wasm::privacy::poseidon::poseidon_pubkey;
    let degenerate_v2_zero_pk = hx(&fr_to_le(&poseidon_pubkey(Fr::from(0u64))));
    assert!(
        v3_note_commitment(100, &degenerate_v2_zero_pk, &valid_blinding).is_err(),
        "poseidon_pubkey(0) must be rejected"
    );

    // 5. Reserved zero-hash constant rejected in pubkey or blinding
    let zh_hex = hx(&ZERO_HASHES[1]);
    assert!(v3_note_commitment(100, &zh_hex, &valid_blinding).is_err());
    assert!(v3_note_commitment(100, &valid_pubkey, &zh_hex).is_err());

    // 6. Valid note commitment succeeds
    assert!(v3_note_commitment(100, &valid_pubkey, &valid_blinding).is_ok());

    // 7. Same checks apply to v3_note_commitment_asset
    let asset_hex = "00".repeat(32);
    assert!(v3_note_commitment_asset(100, &zero_hex, &valid_blinding, &asset_hex).is_err());
    assert!(v3_note_commitment_asset(100, &valid_pubkey, &zero_hex, &asset_hex).is_err());
    assert!(v3_note_commitment_asset(100, &degenerate_v3_zero_pk, &valid_blinding, &asset_hex).is_err());
    assert!(v3_note_commitment_asset(100, &valid_pubkey, &valid_blinding, &asset_hex).is_ok());
}

#[test]
fn test_v2_note_commitment_degenerate_keys_rejected() {
    let valid_priv = hx(&fr_to_le(&Fr::from(42u64)));
    let valid_blinding = hx(&fr_to_le(&Fr::from(123u64)));
    let asset_hex = "00".repeat(32);

    // 1. note_commitment_v2 with all-zero privkey
    let zero_hex = "00".repeat(32);
    assert!(note_commitment_v2(100, &zero_hex, &valid_blinding, &asset_hex).is_err());

    // 2. note_commitment_v2 with all-zero blinding
    assert!(note_commitment_v2(100, &valid_priv, &zero_hex, &asset_hex).is_err());

    // 3. note_commitment_v2 with degenerate zero pubkey as blinding
    use paraloom_prover_wasm::privacy::poseidon::poseidon_pubkey;
    let degenerate_v2_zero_pk = hx(&fr_to_le(&poseidon_pubkey(Fr::from(0u64))));
    assert!(note_commitment_v2(100, &valid_priv, &degenerate_v2_zero_pk, &asset_hex).is_err());

    // 4. Valid note_commitment_v2 succeeds
    assert!(note_commitment_v2(100, &valid_priv, &valid_blinding, &asset_hex).is_ok());

    // 5. note_commitment v1 validation
    assert!(note_commitment(100, &zero_hex, &valid_blinding).is_err());
    assert!(note_commitment(100, &valid_blinding, &zero_hex).is_err());
    assert!(note_commitment(100, &valid_blinding, &valid_blinding).is_ok());
}
