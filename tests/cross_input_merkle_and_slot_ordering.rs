use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use paraloom_prover_wasm::{prove_transact_native, prove_transfer_v2_native};

fn fr_to_le(f: &Fr) -> [u8; 32] {
    let mut out = [0u8; 32];
    let le = f.into_bigint().to_bytes_le();
    out[..le.len().min(32)].copy_from_slice(&le[..le.len().min(32)]);
    out
}

fn hx(b: &[u8; 32]) -> String {
    hex::encode(b)
}

// -----------------------------------------------------------------------------
// Circuit v3: prove_transact tests
// -----------------------------------------------------------------------------

#[test]
fn transact_rejects_inverted_dummy_input_slot_ordering() {
    let zeros_hex = vec![hx(&[0u8; 32]); 32];
    let path_json = serde_json::to_string(&zeros_hex).unwrap();
    let root_hex = hx(&[1u8; 32]);
    let recipient_hex = hx(&[2u8; 32]);
    let asset_id_hex = hx(&[0u8; 32]);

    // input 0 is dummy (amount 0), input 1 is real (amount 500) -> inverted!
    let inputs = format!(
        r#"[
          {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":1,"path_hex":{path_json}}}
        ]"#,
        hx(&[10u8; 32]),
        hx(&[11u8; 32]),
        hx(&[12u8; 32]),
        hx(&[13u8; 32])
    );
    let outputs = format!(
        r#"[
          {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[20u8; 32]),
        hx(&[21u8; 32]),
        hx(&[22u8; 32]),
        hx(&[23u8; 32])
    );

    let err = prove_transact_native(
        &[],
        &root_hex,
        0,
        &recipient_hex,
        &asset_id_hex,
        &inputs,
        &outputs,
    )
    .unwrap_err();
    assert!(
        err.contains("inverted dummy-input slot ordering"),
        "expected dummy-input ordering error, got: {err}"
    );
}

#[test]
fn transact_rejects_inverted_dummy_output_slot_ordering() {
    let zeros_hex = vec![hx(&[0u8; 32]); 32];
    let path_json = serde_json::to_string(&zeros_hex).unwrap();
    let root_hex = hx(&[1u8; 32]);
    let recipient_hex = hx(&[2u8; 32]);
    let asset_id_hex = hx(&[0u8; 32]);

    // inputs: real input 0, dummy input 1
    let inputs = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}},
          {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}}
        ]"#,
        hx(&[10u8; 32]),
        hx(&[11u8; 32]),
        hx(&[12u8; 32]),
        hx(&[13u8; 32])
    );
    // output 0 is dummy (amount 0), output 1 is real (amount 500) -> inverted!
    let outputs = format!(
        r#"[
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[20u8; 32]),
        hx(&[21u8; 32]),
        hx(&[22u8; 32]),
        hx(&[23u8; 32])
    );

    let err = prove_transact_native(
        &[],
        &root_hex,
        0,
        &recipient_hex,
        &asset_id_hex,
        &inputs,
        &outputs,
    )
    .unwrap_err();
    assert!(
        err.contains("inverted dummy-output slot ordering"),
        "expected dummy-output ordering error, got: {err}"
    );
}

#[test]
fn transact_rejects_duplicate_leaf_index_on_2note_spend() {
    use paraloom_prover_wasm::privacy::poseidon_circom::{v3_commit, v3_merkle_pair, v3_pubkey};

    let mut zeros = vec![Fr::from(0u64)];
    for k in 0..32 {
        zeros.push(v3_merkle_pair(zeros[k], zeros[k]));
    }
    let path_hex: Vec<String> = zeros[..32].iter().map(|z| hx(&fr_to_le(z))).collect();
    let path_json = serde_json::to_string(&path_hex).unwrap();

    let sk0 = Fr::from(100u64);
    let bl0 = Fr::from(10u64);
    let c0 = v3_commit(Fr::from(500u64), v3_pubkey(sk0), bl0, Fr::from(0u64));
    let mut root = c0;
    for z in zeros.iter().take(32) {
        root = v3_merkle_pair(root, *z);
    }

    // Both notes have amount 500 and leaf_index 0 -> duplicate leaf index on 2-note spend!
    let inputs = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path_json}}}
        ]"#,
        hx(&fr_to_le(&sk0)),
        hx(&fr_to_le(&bl0)),
        hx(&fr_to_le(&Fr::from(200u64))),
        hx(&fr_to_le(&Fr::from(20u64))),
    );
    let outputs = format!(
        r#"[
          {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[30u8; 32]),
        hx(&[31u8; 32]),
        hx(&[32u8; 32]),
        hx(&[33u8; 32])
    );

    let err = prove_transact_native(
        &[],
        &hx(&fr_to_le(&root)),
        0,
        &hx(&[5u8; 32]),
        &hx(&[0u8; 32]),
        &inputs,
        &outputs,
    )
    .unwrap_err();
    assert!(
        err.contains("duplicate leaf index 0"),
        "expected duplicate leaf index error, got: {err}"
    );
}

#[test]
fn transact_2note_spend_lca_and_ancestor_consistency() {
    use paraloom_prover_wasm::privacy::poseidon_circom::{v3_commit, v3_merkle_pair, v3_pubkey};

    // Construct a consistent 2-leaf tree with leaf 0 and leaf 1 (adjacent siblings, LCA at level 0)
    let sk0 = Fr::from(111u64);
    let bl0 = Fr::from(11u64);
    let c0 = v3_commit(Fr::from(500u64), v3_pubkey(sk0), bl0, Fr::from(0u64));

    let sk1 = Fr::from(222u64);
    let bl1 = Fr::from(22u64);
    let c1 = v3_commit(Fr::from(500u64), v3_pubkey(sk1), bl1, Fr::from(0u64));

    // At level 0: leaf 0 pairs with leaf 1
    let parent01 = v3_merkle_pair(c0, c1);

    // Padding zeros for levels 1..32
    let mut zeros = vec![Fr::from(0u64)];
    for k in 0..32 {
        zeros.push(v3_merkle_pair(zeros[k], zeros[k]));
    }

    let mut root = parent01;
    for z in zeros[1..32].iter() {
        root = v3_merkle_pair(root, *z);
    }

    // Path for leaf 0: sibling at level 0 is c1, then zeros[1..32]
    let mut path0_fr = vec![c1];
    path0_fr.extend_from_slice(&zeros[1..32]);
    let path0_hex: Vec<String> = path0_fr.iter().map(|z| hx(&fr_to_le(z))).collect();
    let path0_json = serde_json::to_string(&path0_hex).unwrap();

    // Path for leaf 1: sibling at level 0 is c0, then zeros[1..32]
    let mut path1_fr = vec![c0];
    path1_fr.extend_from_slice(&zeros[1..32]);
    let path1_hex: Vec<String> = path1_fr.iter().map(|z| hx(&fr_to_le(z))).collect();
    let path1_json = serde_json::to_string(&path1_hex).unwrap();

    let outputs = format!(
        r#"[
          {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[30u8; 32]),
        hx(&[31u8; 32]),
        hx(&[32u8; 32]),
        hx(&[33u8; 32])
    );

    // 1. Consistent paths: should pass all Merkle checks (fails only at proving key deserialization)
    let inputs_valid = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path0_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":1,"path_hex":{path1_json}}}
        ]"#,
        hx(&fr_to_le(&sk0)),
        hx(&fr_to_le(&bl0)),
        hx(&fr_to_le(&sk1)),
        hx(&fr_to_le(&bl1)),
    );
    let res_valid = prove_transact_native(
        &[],
        &hx(&fr_to_le(&root)),
        0,
        &hx(&[5u8; 32]),
        &hx(&[0u8; 32]),
        &inputs_valid,
        &outputs,
    );
    let err = res_valid.unwrap_err();
    assert!(
        err.contains("bad proving key"),
        "consistent paths must pass validation and reach proving key, got: {err}"
    );

    // 2. Tamper with LCA sibling: change path0's level 0 sibling
    let mut bad_path0_lca = path0_hex.clone();
    bad_path0_lca[0] = hx(&[0x99u8; 32]);
    let bad_path0_lca_json = serde_json::to_string(&bad_path0_lca).unwrap();
    let inputs_bad_lca = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{bad_path0_lca_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":1,"path_hex":{path1_json}}}
        ]"#,
        hx(&fr_to_le(&sk0)),
        hx(&fr_to_le(&bl0)),
        hx(&fr_to_le(&sk1)),
        hx(&fr_to_le(&bl1)),
    );
    let err_lca = prove_transact_native(
        &[],
        &hx(&fr_to_le(&root)),
        0,
        &hx(&[5u8; 32]),
        &hx(&[0u8; 32]),
        &inputs_bad_lca,
        &outputs,
    )
    .unwrap_err();
    assert!(
        err_lca.contains("Merkle") || err_lca.contains("LCA"),
        "expected Merkle validation error for tampered LCA, got: {err_lca}"
    );

    // 3. Ancestor mismatch: both fold to different roots or have differing ancestors above LCA
    let mut bad_path1_ancestor = path1_hex.clone();
    bad_path1_ancestor[5] = hx(&[0x77u8; 32]);
    let bad_path1_ancestor_json = serde_json::to_string(&bad_path1_ancestor).unwrap();
    let inputs_bad_ancestor = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path0_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":1,"path_hex":{bad_path1_ancestor_json}}}
        ]"#,
        hx(&fr_to_le(&sk0)),
        hx(&fr_to_le(&bl0)),
        hx(&fr_to_le(&sk1)),
        hx(&fr_to_le(&bl1)),
    );
    let err_anc = prove_transact_native(
        &[],
        &hx(&fr_to_le(&root)),
        0,
        &hx(&[5u8; 32]),
        &hx(&[0u8; 32]),
        &inputs_bad_ancestor,
        &outputs,
    )
    .unwrap_err();
    assert!(
        err_anc.contains("Merkle") || err_anc.contains("ancestor"),
        "expected ancestor mismatch error, got: {err_anc}"
    );
}

// -----------------------------------------------------------------------------
// Circuit v2: prove_transfer_v2 tests
// -----------------------------------------------------------------------------

#[test]
fn transfer_v2_rejects_inverted_dummy_input_slot_ordering() {
    let zeros_hex = vec![hx(&[0u8; 32]); 32];
    let path_json = serde_json::to_string(&zeros_hex).unwrap();
    let indices_json = serde_json::to_string(&vec![true; 32]).unwrap();
    let root_hex = hx(&[1u8; 32]);
    let asset_id_hex = hx(&[0u8; 32]);

    // input 0 is dummy (amount 0), input 1 is real (amount 500) -> inverted!
    let inputs = format!(
        r#"[
          {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path_json},"indices":{indices_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path_json},"indices":{indices_json}}}
        ]"#,
        hx(&[10u8; 32]),
        hx(&[11u8; 32]),
        hx(&[12u8; 32]),
        hx(&[13u8; 32])
    );
    let outputs = format!(
        r#"[
          {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[20u8; 32]),
        hx(&[21u8; 32]),
        hx(&[22u8; 32]),
        hx(&[23u8; 32])
    );

    let err = prove_transfer_v2_native(&[], &root_hex, &asset_id_hex, &inputs, &outputs).unwrap_err();
    assert!(
        err.contains("inverted dummy-input slot ordering"),
        "expected dummy-input ordering error, got: {err}"
    );
}

#[test]
fn transfer_v2_rejects_inverted_dummy_output_slot_ordering() {
    let zeros_hex = vec![hx(&[0u8; 32]); 32];
    let path_json = serde_json::to_string(&zeros_hex).unwrap();
    let indices_json = serde_json::to_string(&vec![true; 32]).unwrap();
    let root_hex = hx(&[1u8; 32]);
    let asset_id_hex = hx(&[0u8; 32]);

    let inputs = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path_json},"indices":{indices_json}}},
          {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path_json},"indices":{indices_json}}}
        ]"#,
        hx(&[10u8; 32]),
        hx(&[11u8; 32]),
        hx(&[12u8; 32]),
        hx(&[13u8; 32])
    );
    // output 0 is dummy, output 1 is real -> inverted!
    let outputs = format!(
        r#"[
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[20u8; 32]),
        hx(&[21u8; 32]),
        hx(&[22u8; 32]),
        hx(&[23u8; 32])
    );

    let err = prove_transfer_v2_native(&[], &root_hex, &asset_id_hex, &inputs, &outputs).unwrap_err();
    assert!(
        err.contains("inverted dummy-output slot ordering"),
        "expected dummy-output ordering error, got: {err}"
    );
}

#[test]
fn transfer_v2_rejects_duplicate_leaf_index_on_2note_spend() {
    use paraloom_prover_wasm::privacy::poseidon::{
        poseidon_commit_spend, poseidon_merkle_pair, poseidon_pubkey,
    };

    let sk0 = Fr::from(6u64);
    let b0 = Fr::from(3u64);
    let c0 = poseidon_commit_spend(
        Fr::from(500u64),
        poseidon_pubkey(sk0),
        b0,
        Fr::from(0u64),
    );

    let sk1 = Fr::from(7u64);
    let b1 = Fr::from(4u64);
    let c1 = poseidon_commit_spend(
        Fr::from(500u64),
        poseidon_pubkey(sk1),
        b1,
        Fr::from(0u64),
    );

    let root = poseidon_merkle_pair(c0, c1);
    // Both inputs claim leaf_index 0 (indices: [true] -> is_left = true -> index 0)
    let path_json = serde_json::to_string(&vec![hx(&fr_to_le(&c1))]).unwrap();
    let indices_json = serde_json::to_string(&vec![true]).unwrap();

    let inputs = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path_json},"indices":{indices_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path_json},"indices":{indices_json}}}
        ]"#,
        hx(&fr_to_le(&sk0)),
        hx(&fr_to_le(&b0)),
        hx(&fr_to_le(&sk1)),
        hx(&fr_to_le(&b1)),
    );
    let outputs = format!(
        r#"[
          {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[30u8; 32]),
        hx(&[31u8; 32]),
        hx(&[32u8; 32]),
        hx(&[33u8; 32])
    );

    let err = prove_transfer_v2_native(
        &[],
        &hx(&fr_to_le(&root)),
        &hx(&[0u8; 32]),
        &inputs,
        &outputs,
    )
    .unwrap_err();
    assert!(
        err.contains("duplicate leaf index 0"),
        "expected duplicate leaf index error, got: {err}"
    );
}

#[test]
fn transfer_v2_2note_spend_lca_and_ancestor_consistency() {
    use paraloom_prover_wasm::privacy::poseidon::{
        poseidon_commit_spend, poseidon_merkle_pair, poseidon_pubkey,
    };

    let sk0 = Fr::from(6u64);
    let b0 = Fr::from(3u64);
    let c0 = poseidon_commit_spend(
        Fr::from(500u64),
        poseidon_pubkey(sk0),
        b0,
        Fr::from(0u64),
    );

    let sk1 = Fr::from(7u64);
    let b1 = Fr::from(4u64);
    let c1 = poseidon_commit_spend(
        Fr::from(500u64),
        poseidon_pubkey(sk1),
        b1,
        Fr::from(0u64),
    );

    let root = poseidon_merkle_pair(c0, c1);
    // leaf 0: left child (indices: [true]), sibling is c1
    let path0_json = serde_json::to_string(&vec![hx(&fr_to_le(&c1))]).unwrap();
    let indices0_json = serde_json::to_string(&vec![true]).unwrap();

    // leaf 1: right child (indices: [false]), sibling is c0
    let path1_json = serde_json::to_string(&vec![hx(&fr_to_le(&c0))]).unwrap();
    let indices1_json = serde_json::to_string(&vec![false]).unwrap();

    let outputs = format!(
        r#"[
          {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
          {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx(&[30u8; 32]),
        hx(&[31u8; 32]),
        hx(&[32u8; 32]),
        hx(&[33u8; 32])
    );

    // 1. Consistent 2-note spend -> passes Merkle consistency, reaches proving key
    let inputs_valid = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path0_json},"indices":{indices0_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path1_json},"indices":{indices1_json}}}
        ]"#,
        hx(&fr_to_le(&sk0)),
        hx(&fr_to_le(&b0)),
        hx(&fr_to_le(&sk1)),
        hx(&fr_to_le(&b1)),
    );
    let res = prove_transfer_v2_native(
        &[],
        &hx(&fr_to_le(&root)),
        &hx(&[0u8; 32]),
        &inputs_valid,
        &outputs,
    );
    let err = res.unwrap_err();
    assert!(
        err.contains("bad proving key"),
        "consistent paths must reach proving key check, got: {err}"
    );

    // 2. Inconsistent LCA sibling: tamper path0's level 0 sibling
    let bad_path0_json = serde_json::to_string(&vec![hx(&[0x44u8; 32])]).unwrap();
    let inputs_bad_lca = format!(
        r#"[
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{bad_path0_json},"indices":{indices0_json}}},
          {{"amount":500,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path1_json},"indices":{indices1_json}}}
        ]"#,
        hx(&fr_to_le(&sk0)),
        hx(&fr_to_le(&b0)),
        hx(&fr_to_le(&sk1)),
        hx(&fr_to_le(&b1)),
    );
    let err_lca = prove_transfer_v2_native(
        &[],
        &hx(&fr_to_le(&root)),
        &hx(&[0u8; 32]),
        &inputs_bad_lca,
        &outputs,
    )
    .unwrap_err();
    assert!(
        err_lca.contains("Merkle") || err_lca.contains("LCA"),
        "expected LCA mismatch error, got: {err_lca}"
    );
}
