use paraloom_prover_wasm::{
    last_error, prove_transact, prove_transfer_v2, prove_withdrawal_v2,
};
use wasm_bindgen::JsValue;

fn hx32(byte: u8) -> String {
    hex::encode([byte; 32])
}

fn zero32() -> String {
    hex::encode([0u8; 32])
}

fn valid_path_32() -> Vec<String> {
    vec![hx32(1); 32]
}

fn assert_err<T>(res: Result<T, JsValue>, expected_substr: &str) {
    assert!(res.is_err(), "expected Err but got Ok");
    if let Some(err_msg) = last_error() {
        assert!(
            err_msg.contains(expected_substr),
            "expected error containing '{expected_substr}', got '{err_msg}'"
        );
    }
}

#[test]
fn test_prove_transact_rejects_all_zero_root() {
    let path = serde_json::to_string(&valid_path_32()).unwrap();
    let inputs = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(4)
    );
    let outputs = format!(
        r#"[
            {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transact(&[], &zero32(), -500, &hx32(9), &zero32(), &inputs, &outputs),
        "all-zero Merkle root is invalid",
    );
}

#[test]
fn test_prove_transact_rejects_u64_overflow_inputs() {
    let path = serde_json::to_string(&valid_path_32()).unwrap();
    let inputs = format!(
        r#"[
            {{"amount":{},"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":1,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        u64::MAX, hx32(1), hx32(2), hx32(3), hx32(4)
    );
    let outputs = format!(
        r#"[
            {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &inputs, &outputs),
        "input amounts overflow u64",
    );
}

#[test]
fn test_prove_transact_rejects_u64_overflow_outputs() {
    let path = serde_json::to_string(&valid_path_32()).unwrap();
    let inputs = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(4)
    );
    let outputs = format!(
        r#"[
            {{"amount":{},"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":1,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        u64::MAX, hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &inputs, &outputs),
        "output amounts overflow u64",
    );
}

#[test]
fn test_prove_transact_rejects_value_conservation_failure() {
    let path = serde_json::to_string(&valid_path_32()).unwrap();
    let inputs = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(4)
    );
    let outputs = format!(
        r#"[
            {{"amount":900,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &inputs, &outputs),
        "transact value conservation failed",
    );
}

#[test]
fn test_prove_transact_rejects_insufficient_inputs_withdrawal() {
    let path = serde_json::to_string(&valid_path_32()).unwrap();
    let inputs = format!(
        r#"[
            {{"amount":400,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(4)
    );
    let outputs = format!(
        r#"[
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transact(&[], &hx32(10), -500, &hx32(9), &zero32(), &inputs, &outputs),
        "insufficient inputs for external withdrawal",
    );
}

#[test]
fn test_prove_transact_rejects_zero_privkey_and_blinding() {
    let path = serde_json::to_string(&valid_path_32()).unwrap();
    let outputs = format!(
        r#"[
            {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );

    // Zero privkey on input 0
    let in_zero_pk = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        zero32(), hx32(2), hx32(3), hx32(4)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &in_zero_pk, &outputs),
        "input privkey cannot be all-zero",
    );

    // Zero privkey on dummy input 1
    let in_dummy_zero_pk = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), zero32(), hx32(4)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &in_dummy_zero_pk, &outputs),
        "input privkey cannot be all-zero",
    );

    // Zero blinding on dummy input 1
    let in_dummy_zero_bl = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), zero32()
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &in_dummy_zero_bl, &outputs),
        "input blinding cannot be all-zero",
    );
}

#[test]
fn test_prove_transact_rejects_reused_blindings_and_privkeys() {
    let path = serde_json::to_string(&valid_path_32()).unwrap();
    let outputs = format!(
        r#"[
            {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );

    // Reused blinding between input 0 and dummy input 1
    let in_reused_blinding = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(2)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &in_reused_blinding, &outputs),
        "input blindings must be distinct",
    );

    // Dummy note reusing privkey of input 0
    let in_dummy_reused_pk = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(1), hx32(4)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &in_dummy_reused_pk, &outputs),
        "dummy note cannot reuse privkey",
    );

    // Reused output blindings
    let inputs = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","leaf_index":0,"path_hex":{path}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(4)
    );
    let out_reused_blinding = format!(
        r#"[
            {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(6)
    );
    assert_err(
        prove_transact(&[], &hx32(10), 0, &hx32(9), &zero32(), &inputs, &out_reused_blinding),
        "output blindings must be distinct",
    );
}

#[test]
fn test_prove_transfer_v2_rejects_invalid_inputs() {
    let path = serde_json::to_string(&vec![hx32(1)]).unwrap();
    let indices = serde_json::to_string(&vec![true]).unwrap();

    // 1. All-zero Merkle root
    let inputs = format!(
        r#"[
            {{"amount":600,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path},"indices":{indices}}},
            {{"amount":400,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path},"indices":{indices}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(4)
    );
    let outputs = format!(
        r#"[
            {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transfer_v2(&[], &zero32(), &zero32(), &inputs, &outputs),
        "all-zero Merkle root is invalid",
    );

    // 2. Value conservation mismatch
    let bad_outputs = format!(
        r#"[
            {{"amount":500,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":400,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transfer_v2(&[], &hx32(10), &zero32(), &inputs, &bad_outputs),
        "transfer value conservation failed",
    );

    // 3. Dummy note reusing privkey
    let dummy_inputs = format!(
        r#"[
            {{"amount":1000,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path},"indices":{indices}}},
            {{"amount":0,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path},"indices":{indices}}}
        ]"#,
        hx32(1), hx32(2), hx32(1), hx32(4)
    );
    let out_1000 = format!(
        r#"[
            {{"amount":1000,"pubkey_hex":"{}","blinding_hex":"{}"}},
            {{"amount":0,"pubkey_hex":"{}","blinding_hex":"{}"}}
        ]"#,
        hx32(5), hx32(6), hx32(7), hx32(8)
    );
    assert_err(
        prove_transfer_v2(&[], &hx32(10), &zero32(), &dummy_inputs, &out_1000),
        "dummy note cannot reuse privkey",
    );

    // 4. Duplicate input blindings
    let dup_bl_inputs = format!(
        r#"[
            {{"amount":600,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path},"indices":{indices}}},
            {{"amount":400,"privkey_hex":"{}","blinding_hex":"{}","path_hex":{path},"indices":{indices}}}
        ]"#,
        hx32(1), hx32(2), hx32(3), hx32(2)
    );
    assert_err(
        prove_transfer_v2(&[], &hx32(10), &zero32(), &dup_bl_inputs, &outputs),
        "input blindings must be distinct",
    );
}

#[test]
fn test_prove_withdrawal_v2_rejects_zero_fields() {
    let path = serde_json::to_string(&vec![hx32(1)]).unwrap();
    let indices = serde_json::to_string(&vec![true]).unwrap();

    // All-zero root
    assert_err(
        prove_withdrawal_v2(&[], &zero32(), 100, &hx32(1), &hx32(2), &zero32(), &hx32(3), &path, &indices),
        "all-zero Merkle root is invalid",
    );

    // All-zero blinding
    assert_err(
        prove_withdrawal_v2(&[], &hx32(10), 100, &zero32(), &hx32(2), &zero32(), &hx32(3), &path, &indices),
        "blinding cannot be all-zero",
    );

    // All-zero privkey
    assert_err(
        prove_withdrawal_v2(&[], &hx32(10), 100, &hx32(1), &zero32(), &zero32(), &hx32(3), &path, &indices),
        "privkey cannot be all-zero",
    );

    // All-zero dest recipient
    assert_err(
        prove_withdrawal_v2(&[], &hx32(10), 100, &hx32(1), &hx32(2), &zero32(), &zero32(), &path, &indices),
        "dest recipient cannot be all-zero",
    );
}
