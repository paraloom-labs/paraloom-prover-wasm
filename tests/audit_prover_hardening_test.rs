use ark_bn254::{Bn254, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{Proof, ProvingKey, VerifyingKey};
use paraloom_prover_wasm::{
    hex32, hex32_nonzero_scalar, hex32_scalar, is_canonical_le, mint_to_asset, note_commitment,
    note_commitment_v2, prove_transact, spend_pubkey, v3_merkle_path, v3_note_commitment,
    v3_note_commitment_asset, v3_note_pubkey, validate_pk_and_proof,
};

fn fr_to_le(f: &Fr) -> [u8; 32] {
    let mut out = [0u8; 32];
    let le = f.into_bigint().to_bytes_le();
    out[..le.len().min(32)].copy_from_slice(&le[..le.len().min(32)]);
    out
}

fn modulus_le() -> [u8; 32] {
    let ple = <Fr as PrimeField>::MODULUS.to_bytes_le();
    let mut out = [0u8; 32];
    out[..ple.len().min(32)].copy_from_slice(&ple[..ple.len().min(32)]);
    out
}

#[test]
fn test_hex32_prefix_and_bounds() {
    let raw = [7u8; 32];
    let hx = hex::encode(raw);
    assert_eq!(hex32(&hx).unwrap(), raw);
    assert_eq!(hex32(&format!("0x{hx}")).unwrap(), raw);
    assert_eq!(hex32(&format!("0X{hx}")).unwrap(), raw);
    assert_eq!(hex32(&format!("  0x{hx}  ")).unwrap(), raw);

    // Wrong length
    assert!(hex32("0x1234").is_err());
    assert!(hex32(&hex::encode([1u8; 33])).is_err());
    // Invalid characters
    assert!(hex32("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz").is_err());
}

#[test]
fn test_canonical_scalar_checks() {
    let canonical = fr_to_le(&Fr::from(42u64));
    assert!(is_canonical_le(&canonical));
    assert!(hex32_scalar(&hex::encode(canonical), "test").is_ok());

    let mod_bytes = modulus_le();
    assert!(!is_canonical_le(&mod_bytes));
    assert!(hex32_scalar(&hex::encode(mod_bytes), "test_modulus").is_err());

    // Non-canonical scalar rejected in public API
    let mod_hex = hex::encode(mod_bytes);
    assert!(spend_pubkey(&mod_hex).is_err());
    assert!(v3_note_pubkey(&mod_hex).is_err());
    assert!(v3_note_commitment(100, &mod_hex, &hex::encode([1u8; 32])).is_err());
    assert!(v3_note_commitment_asset(100, &hex::encode([1u8; 32]), &mod_hex, &hex::encode([0u8; 32])).is_err());
    assert!(note_commitment(100, &mod_hex, &hex::encode([1u8; 32])).is_err());
    assert!(note_commitment_v2(100, &mod_hex, &hex::encode([1u8; 32]), &hex::encode([0u8; 32])).is_err());
}

#[test]
fn test_reject_zero_privkeys_and_blindings() {
    let zero_hex = hex::encode([0u8; 32]);
    assert!(hex32_nonzero_scalar(&zero_hex, "zero_val").is_err());
    assert!(spend_pubkey(&zero_hex).is_err());
    assert!(v3_note_pubkey(&zero_hex).is_err());
    assert!(v3_note_commitment(100, &hex::encode([1u8; 32]), &zero_hex).is_err());
    assert!(v3_note_commitment(100, &zero_hex, &hex::encode([1u8; 32])).is_err());
}

#[test]
fn test_blinding_leak_privkey_equals_blinding() {
    let key_hex = hex::encode(fr_to_le(&Fr::from(999u64)));
    let res = note_commitment_v2(500, &key_hex, &key_hex, &hex::encode([0u8; 32]));
    assert!(res.is_err());
}

#[test]
fn test_mint_to_asset_rejects_zero_native_mint() {
    let zero_hex = hex::encode([0u8; 32]);
    let res = mint_to_asset(&zero_hex);
    assert!(res.is_err());

    // Non-zero mint succeeds
    let non_zero_mint = hex::encode([5u8; 32]);
    assert!(mint_to_asset(&non_zero_mint).is_ok());
}

#[test]
fn test_v3_merkle_path_validation() {
    assert!(v3_merkle_path("[]", 0).is_err());

    let mod_hex = hex::encode(modulus_le());
    let invalid_leaves = format!("[\"{mod_hex}\"]");
    assert!(v3_merkle_path(&invalid_leaves, 0).is_err());
}

#[test]
fn test_point_at_infinity_checks() {
    let mut pk = ProvingKey::<Bn254> {
        vk: VerifyingKey::<Bn254> {
            alpha_g1: G1Affine::generator(),
            beta_g2: G2Affine::generator(),
            gamma_g2: G2Affine::generator(),
            delta_g2: G2Affine::generator(),
            gamma_abc_g1: vec![G1Affine::generator()],
        },
        beta_g1: G1Affine::generator(),
        delta_g1: G1Affine::generator(),
        a_query: vec![],
        b_g1_query: vec![],
        b_g2_query: vec![],
        h_query: vec![],
        l_query: vec![],
    };

    let valid_proof = Proof::<Bn254> {
        a: G1Affine::generator(),
        b: G2Affine::generator(),
        c: G1Affine::generator(),
    };

    assert!(validate_pk_and_proof(&pk, &valid_proof).is_ok());

    // Proof with point at infinity
    let mut bad_proof = valid_proof.clone();
    bad_proof.a = G1Affine::zero();
    assert!(validate_pk_and_proof(&pk, &bad_proof).is_err());

    let mut bad_proof_c = valid_proof.clone();
    bad_proof_c.c = G1Affine::zero();
    assert!(validate_pk_and_proof(&pk, &bad_proof_c).is_err());

    // Proving key with point at infinity
    pk.vk.alpha_g1 = G1Affine::zero();
    assert!(validate_pk_and_proof(&pk, &valid_proof).is_err());
}

#[test]
fn test_prove_transact_validation_gates() {
    let dummy_pk = vec![0u8; 64];
    let root_hex = hex::encode([1u8; 32]);
    let zero_root_hex = hex::encode([0u8; 32]);
    let recipient_hex = hex::encode([2u8; 32]);
    let asset_hex = hex::encode([0u8; 32]);

    let input_path: Vec<String> = (0..32).map(|_| hex::encode([1u8; 32])).collect();
    let path_json = serde_json::to_string(&input_path).unwrap();

    let valid_inputs = format!(
        r#"[
          {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}},
          {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}}
        ]"#,
        hex::encode(fr_to_le(&Fr::from(10u64))),
        hex::encode(fr_to_le(&Fr::from(20u64))),
        hex::encode(fr_to_le(&Fr::from(30u64))),
        hex::encode(fr_to_le(&Fr::from(40u64))),
    );

    let valid_outputs = format!(
        r#"[
          {{"amount":400,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":100,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hex::encode(fr_to_le(&Fr::from(50u64))),
        hex::encode(fr_to_le(&Fr::from(60u64))),
        hex::encode(fr_to_le(&Fr::from(70u64))),
        hex::encode(fr_to_le(&Fr::from(80u64))),
    );

    // 1. Positive ext_amount rejected
    let res = prove_transact(&dummy_pk, &root_hex, 500, &recipient_hex, &asset_hex, &valid_inputs, &valid_outputs);
    assert!(res.is_err());

    // 2. All-zero Merkle root rejected
    let res = prove_transact(&dummy_pk, &zero_root_hex, -500, &recipient_hex, &asset_hex, &valid_inputs, &valid_outputs);
    assert!(res.is_err());

    // 3. Value conservation violation (in_sum: 1000, ext_amount: -500, out_sum: 500 => sum_ins - 500 == 500)
    // If ext_amount is -600, in_sum - 600 = 400 != 500 => error!
    let res = prove_transact(&dummy_pk, &root_hex, -600, &recipient_hex, &asset_hex, &valid_inputs, &valid_outputs);
    assert!(res.is_err());

    // 4. Duplicate/reused blinding across inputs or outputs
    let duplicate_blinding_outputs = format!(
        r#"[
          {{"amount":400,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":100,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hex::encode(fr_to_le(&Fr::from(50u64))),
        hex::encode(fr_to_le(&Fr::from(20u64))), // Reusing input 0's blinding (20)
        hex::encode(fr_to_le(&Fr::from(70u64))),
        hex::encode(fr_to_le(&Fr::from(80u64))),
    );
    let res = prove_transact(&dummy_pk, &root_hex, -500, &recipient_hex, &asset_hex, &valid_inputs, &duplicate_blinding_outputs);
    assert!(res.is_err());

    // 5. Blinding equals private key
    let leak_inputs = format!(
        r#"[
          {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}},
          {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}}
        ]"#,
        hex::encode(fr_to_le(&Fr::from(10u64))),
        hex::encode(fr_to_le(&Fr::from(10u64))), // privkey == blinding
        hex::encode(fr_to_le(&Fr::from(30u64))),
        hex::encode(fr_to_le(&Fr::from(40u64))),
    );
    let res = prove_transact(&dummy_pk, &root_hex, -500, &recipient_hex, &asset_hex, &leak_inputs, &valid_outputs);
    assert!(res.is_err());
}
