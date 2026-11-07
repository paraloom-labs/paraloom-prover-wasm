use ark_bn254::{Bn254, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::VerifyingKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{rngs::StdRng, SeedableRng};

use paraloom_prover_wasm::privacy::circuits::{Groth16ProofSystem, WithdrawCircuitV2};
use paraloom_prover_wasm::privacy::poseidon_circom::{v3_commit, v3_pubkey};
use paraloom_prover_wasm::transact_vk_data::{
    VK_ALPHA_G1, VK_BETA_G2, VK_DELTA_G2, VK_GAMMA_G2, VK_IC,
};
use paraloom_prover_wasm::{
    g1_to_wire, g2_to_wire, prove_transact, prove_withdrawal_v2, v3_merkle_path,
    v3_merkle_path_inner, validate_proving_key, verify_transact_ceremony_vk,
};

fn wire_to_g1(wire: &[u8; 64]) -> G1Affine {
    let mut le = [0u8; 64];
    for (i, b) in wire[..32].iter().rev().enumerate() {
        le[i] = *b;
    }
    for (i, b) in wire[32..64].iter().rev().enumerate() {
        le[32 + i] = *b;
    }
    G1Affine::deserialize_uncompressed(&le[..]).expect("valid G1 wire point")
}

fn wire_to_g2(wire: &[u8; 128]) -> G2Affine {
    let mut le = [0u8; 128];
    for (i, b) in wire[32..64].iter().rev().enumerate() {
        le[i] = *b;
    }
    for (i, b) in wire[0..32].iter().rev().enumerate() {
        le[32 + i] = *b;
    }
    for (i, b) in wire[96..128].iter().rev().enumerate() {
        le[64 + i] = *b;
    }
    for (i, b) in wire[64..96].iter().rev().enumerate() {
        le[96 + i] = *b;
    }
    G2Affine::deserialize_uncompressed(&le[..]).expect("valid G2 wire point")
}

fn ceremony_vk() -> VerifyingKey<Bn254> {
    VerifyingKey {
        alpha_g1: wire_to_g1(&VK_ALPHA_G1),
        beta_g2: wire_to_g2(&VK_BETA_G2),
        gamma_g2: wire_to_g2(&VK_GAMMA_G2),
        delta_g2: wire_to_g2(&VK_DELTA_G2),
        gamma_abc_g1: VK_IC.iter().map(wire_to_g1).collect(),
    }
}

fn fr_to_le(f: &Fr) -> [u8; 32] {
    let mut out = [0u8; 32];
    let le = f.into_bigint().to_bytes_le();
    out[..le.len().min(32)].copy_from_slice(&le[..le.len().min(32)]);
    out
}

fn hx(b: &[u8; 32]) -> String {
    hex::encode(b)
}

#[test]
fn test_ceremony_vk_pinning_exact_match() {
    let vk = ceremony_vk();
    assert_eq!(g1_to_wire(&vk.alpha_g1), VK_ALPHA_G1);
    assert_eq!(g2_to_wire(&vk.beta_g2), VK_BETA_G2);
    assert_eq!(g2_to_wire(&vk.gamma_g2), VK_GAMMA_G2);
    assert_eq!(g2_to_wire(&vk.delta_g2), VK_DELTA_G2);
    assert_eq!(vk.gamma_abc_g1.len(), 9);
    for (i, ic) in vk.gamma_abc_g1.iter().enumerate() {
        assert_eq!(g1_to_wire(ic), VK_IC[i]);
    }

    assert!(verify_transact_ceremony_vk(&vk).is_ok());
}

#[test]
fn test_verify_transact_ceremony_vk_rejects_mismatch() {
    let mut vk = ceremony_vk();

    // Tampered alpha_g1
    vk.alpha_g1 = G1Affine::generator();
    let err = verify_transact_ceremony_vk(&vk).unwrap_err();
    assert!(err.contains("alpha_g1 does not match"));

    // Reset and tamper beta_g2
    let mut vk = ceremony_vk();
    vk.beta_g2 = G2Affine::generator();
    let err = verify_transact_ceremony_vk(&vk).unwrap_err();
    assert!(err.contains("beta_g2 does not match"));

    // Reset and tamper gamma_g2
    let mut vk = ceremony_vk();
    vk.gamma_g2 = wire_to_g2(&VK_DELTA_G2);
    let err = verify_transact_ceremony_vk(&vk).unwrap_err();
    assert!(err.contains("gamma_g2 does not match"));

    // Reset and tamper delta_g2
    let mut vk = ceremony_vk();
    vk.delta_g2 = wire_to_g2(&VK_BETA_G2);
    let err = verify_transact_ceremony_vk(&vk).unwrap_err();
    assert!(err.contains("delta_g2 does not match"));

    // Reset and tamper IC point
    let mut vk = ceremony_vk();
    vk.gamma_abc_g1[3] = G1Affine::generator();
    let err = verify_transact_ceremony_vk(&vk).unwrap_err();
    assert!(err.contains("IC[3] does not match"));

    // Truncated IC
    let mut vk = ceremony_vk();
    vk.gamma_abc_g1.pop();
    let err = verify_transact_ceremony_vk(&vk).unwrap_err();
    assert!(err.contains("IC count mismatch"));
}

#[test]
fn test_validate_proving_key_passes_valid_key() {
    let mut rng = StdRng::seed_from_u64(0x42);
    let (pk, _) = Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");
    if let Err(e) = validate_proving_key(&pk) {
        panic!("validate_proving_key failed on valid key: {e}");
    }
}

#[test]
fn test_validate_proving_key_rejects_zero_points() {
    let mut rng = StdRng::seed_from_u64(0x42);
    let (base_pk, _) =
        Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");

    // alpha_g1 zero
    let mut pk = base_pk.clone();
    pk.vk.alpha_g1 = G1Affine::zero();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("alpha_g1 is point at infinity"));

    // beta_g2 zero
    let mut pk = base_pk.clone();
    pk.vk.beta_g2 = G2Affine::zero();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("beta_g2 is point at infinity"));

    // gamma_g2 zero
    let mut pk = base_pk.clone();
    pk.vk.gamma_g2 = G2Affine::zero();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("gamma_g2 is point at infinity"));

    // delta_g2 zero
    let mut pk = base_pk.clone();
    pk.vk.delta_g2 = G2Affine::zero();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("delta_g2 is point at infinity"));

    // beta_g1 zero
    let mut pk = base_pk.clone();
    pk.beta_g1 = G1Affine::zero();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("beta_g1 is point at infinity"));

    // delta_g1 zero
    let mut pk = base_pk.clone();
    pk.delta_g1 = G1Affine::zero();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("delta_g1 is point at infinity"));

    // gamma_abc_g1 element zero
    let mut pk = base_pk.clone();
    pk.vk.gamma_abc_g1[0] = G1Affine::zero();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("gamma_abc_g1[0] is point at infinity"));

    // gamma_abc_g1 empty
    let mut pk = base_pk.clone();
    pk.vk.gamma_abc_g1.clear();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("gamma_abc_g1 is empty"));
}

#[test]
fn test_validate_proving_key_rejects_empty_or_mismatched_queries() {
    let mut rng = StdRng::seed_from_u64(0x42);
    let (base_pk, _) =
        Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");

    let mut pk = base_pk.clone();
    pk.a_query.clear();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("a_query is empty"));

    let mut pk = base_pk.clone();
    pk.b_g1_query.clear();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("b_g1_query is empty"));

    let mut pk = base_pk.clone();
    pk.b_g2_query.clear();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("b_g2_query is empty"));

    let mut pk = base_pk.clone();
    pk.b_g1_query.pop();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("length mismatch"));

    let mut pk = base_pk;
    pk.h_query.clear();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("h_query is empty"));
}

#[test]
fn test_validate_proving_key_rejects_toxic_waste_collisions() {
    let mut rng = StdRng::seed_from_u64(0x42);
    let (base_pk, _) =
        Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");

    // beta_g1 == delta_g1
    let mut pk = base_pk.clone();
    pk.beta_g1 = pk.delta_g1;
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("beta_g1 == delta_g1"));

    // alpha_g1 == beta_g1
    let mut pk = base_pk.clone();
    pk.vk.alpha_g1 = pk.beta_g1;
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("alpha_g1 == beta_g1"));

    // alpha_g1 == delta_g1
    let mut pk = base_pk.clone();
    pk.vk.alpha_g1 = pk.delta_g1;
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("alpha_g1 == delta_g1"));

    // beta_g2 == delta_g2
    let mut pk = base_pk.clone();
    pk.vk.beta_g2 = pk.vk.delta_g2;
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("beta_g2 == delta_g2"));

    // beta_g2 == gamma_g2
    let mut pk = base_pk.clone();
    pk.vk.beta_g2 = pk.vk.gamma_g2;
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("beta_g2 == gamma_g2"));

    // gamma_g2 == delta_g2
    let mut pk = base_pk;
    pk.vk.gamma_g2 = pk.vk.delta_g2;
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("gamma_g2 == delta_g2"));
}

#[test]
fn test_validate_proving_key_rejects_pairing_mismatch() {
    let mut rng = StdRng::seed_from_u64(0x42);
    let (base_pk, _) =
        Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");

    // Replace beta_g1 with G1 generator (violates e(beta, delta) == e(delta, beta))
    let mut pk = base_pk.clone();
    pk.beta_g1 = G1Affine::generator();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("cross-group pairing mismatch between beta and delta"));

    // Replace delta_g1 with G1 generator
    let mut pk = base_pk;
    pk.delta_g1 = G1Affine::generator();
    let err = validate_proving_key(&pk).unwrap_err();
    assert!(err.contains("cross-group pairing mismatch between beta and delta"));
}

#[test]
fn test_prove_transact_rejects_non_ceremony_vk() {
    let mut rng = StdRng::seed_from_u64(0x7A3C);
    let (pk, _) = Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");

    let mut pk_bytes = Vec::new();
    pk.serialize_compressed(&mut pk_bytes).unwrap();

    let root = Fr::from(100u64);
    let recipient = [3u8; 32];
    let asset = [0u8; 32];
    let path = serde_json::to_string(&vec![hx(&[0u8; 32]); 32]).unwrap();
    let inputs = format!(
        r#"[
          {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
          {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx(&[1u8; 32]),
        hx(&[2u8; 32]),
        hx(&[3u8; 32]),
        hx(&[4u8; 32]),
    );
    let outputs = format!(
        r#"[
          {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[5u8; 32]),
        hx(&[6u8; 32]),
        hx(&[7u8; 32]),
        hx(&[8u8; 32]),
    );

    let res = prove_transact(
        &pk_bytes,
        &hx(&fr_to_le(&root)),
        -500,
        &hx(&recipient),
        &hx(&asset),
        &inputs,
        &outputs,
    );

    assert!(res.is_err(), "prove_transact must reject non-ceremony VK");
}

#[test]
fn test_prove_withdrawal_v2_rejects_degenerate_pk() {
    let mut rng = StdRng::seed_from_u64(0x42);
    let (mut pk, _) = Groth16ProofSystem::setup(WithdrawCircuitV2::new(), &mut rng).expect("setup");
    pk.vk.alpha_g1 = G1Affine::zero(); // degenerate point

    let mut pk_bytes = Vec::new();
    pk.serialize_compressed(&mut pk_bytes).unwrap();

    let res = prove_withdrawal_v2(
        &pk_bytes,
        &hx(&[0u8; 32]),
        100,
        &hx(&[1u8; 32]),
        &hx(&[2u8; 32]),
        &hx(&[0u8; 32]),
        &hx(&[3u8; 32]),
        "[]",
        "[]",
    );

    assert!(
        res.is_err(),
        "prove_withdrawal_v2 must reject degenerate PK"
    );
}

#[test]
fn test_v3_merkle_path_bit_fold_self_verification() {
    // 5 leaves
    let mk = |amt: u64, sk: u64, bl: u64| {
        v3_commit(
            Fr::from(amt),
            v3_pubkey(Fr::from(sk)),
            Fr::from(bl),
            Fr::from(0u64),
        )
    };
    let l0 = mk(100, 10, 1);
    let l1 = mk(200, 20, 2);
    let l2 = mk(300, 30, 3);
    let l3 = mk(400, 40, 4);
    let l4 = mk(500, 50, 5);

    let leaves = vec![
        hx(&fr_to_le(&l0)),
        hx(&fr_to_le(&l1)),
        hx(&fr_to_le(&l2)),
        hx(&fr_to_le(&l3)),
        hx(&fr_to_le(&l4)),
    ];
    let leaves_json = serde_json::to_string(&leaves).unwrap();

    // Verify each leaf passes bit-fold self-verification via both v3_merkle_path and v3_merkle_path_inner
    for idx in 0..5 {
        let out = v3_merkle_path(&leaves_json, idx).expect("valid path");
        let v: serde_json::Value = serde_json::from_str(&out).unwrap();
        let path: Vec<String> = serde_json::from_value(v["path"].clone()).unwrap();
        assert_eq!(path.len(), 32);
        let root_hex = v["root"].as_str().unwrap();
        assert_eq!(root_hex.len(), 64);

        let out_inner = v3_merkle_path_inner(&leaves_json, idx).expect("valid inner path");
        assert_eq!(out, out_inner);
    }

    // Leaf index out of range must fail
    assert!(v3_merkle_path(&leaves_json, 5).is_err());
    assert!(v3_merkle_path(&leaves_json, 100).is_err());

    let err5 = v3_merkle_path_inner(&leaves_json, 5).unwrap_err();
    assert_eq!(err5, "leaf_index out of range");
}
