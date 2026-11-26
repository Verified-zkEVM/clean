//! Proves a 24-byte SHA-256 preimage for an exported submission without Lean: reads only
//! OUT_DIR/export.json, OUT_DIR/witgen.json (`run.sh --witgen`) and the Filecoin setup, runs the
//! contract's witness program on the message, then derives the key, proves and verifies.
//! Writes OUT_DIR/prove/HEX/{prove.json,proof.bin}, the proof only if accepted; exits non-zero unless the check passed.
//! Prints `vk FINGERPRINT FORMAT raw-sha256 SHA256`: the key's transcript representative (which covers the constraint
//! system), `midnight` or `halo2`, and the SHA-256 of its raw bytes; with no HEX it stops there, reading only
//! export.json and the setup.
//! Usage: OUT_DIR [HEX] [--zk MIDNIGHT_ZK] [--lean WITNESS.json]
//!   [--tamper first|copy | --wrong-digest | --mock],
//! HEX the message as 48 lowercase hex digits. `--lean` compares the advice cell for cell with Lean's evaluation.
//! The verifier's instance is the contract's: column 0 empty, column 1 the digest's 32 bytes. A `MidnightVK` also
//! declares a public-input count, which midnight-zk's verifier requires to be that length; it is checked apart.
//! `--tamper` and `--wrong-digest` are negative checks: the verifier must reject a proof from a tampered advice cell,
//! and the honest proof with another digest. Each writes its `result`: `verifier-rejected` (exit 0), `skipped` (exit
//! 0; `--tamper copy` without an advice-instance copy), or `accepted`, `prover-failed` or `verifier-panicked`.
//! `--mock` runs MockProver instead of proving, as a diagnostic.
use std::{collections::HashMap, fs, marker::PhantomData, panic, path::{Path, PathBuf}, sync::Arc, time::Instant};
use ff::{Field, PrimeField};
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{SimpleFloorPlanner, floor_planner::V1},
    dev::MockProver,
    plonk::{FloorPlanner, create_proof, keygen_pk, keygen_vk_with_k, prepare},
    poly::{commitment::{Guard, PolynomialCommitmentScheme}, kzg::params::ParamsKZG},
    transcript::{CircuitTranscript, Transcript},
};
use midnight_vk_export_native::{JsonCircuit, Vk, field, fingerprint, hex, key_bytes, list, num, params};
use midnight_zk_stdlib::DefaultPCS;
use num_bigint::BigUint;
use rand_core::OsRng;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};

/// The witness program's environment: the cells written so far and the message as the one hint row.
/// `Fast.ordered` admits reads of earlier assignments only, so any other read is an error.
struct Env { cells: HashMap<(u64, usize, usize), Fq>, hint_key: String, hint_width: usize, message: Vec<Fq>, modulus: BigUint }

/// A decimal magnitude, exact (Lean writes field constants as strings, naturals as numbers).
fn big(v: &Json) -> BigUint {
    match v { Json::String(s) => s.parse(), Json::Number(n) => n.to_string().parse(), _ => panic!("constant {v}") }
        .expect("decimal constant")
}

impl Env {
    fn of_nat(&self, n: &BigUint) -> Fq { Fq::from_str_vartime(&(n % &self.modulus).to_string()).unwrap() }
    /// Clean's `FExprOver` schema, in the fragment `Reads.field` admits.
    fn field(&self, e: &Json) -> Fq {
        let f = |k: &str| self.field(&e[k]);
        match e["type"].as_str().unwrap() {
            "expr" => {
                let c = &e["expr"];
                let key = (c["kind"].as_u64().unwrap(), num(&c["column"]), num(&c["row"]));
                *self.cells.get(&key).unwrap_or_else(|| panic!("read of unassigned cell {key:?}"))
            }
            "const" => self.of_nat(&big(&e["value"])),
            "add" => f("lhs") + f("rhs"),
            "mul" => f("lhs") * f("rhs"),
            "inv" => f("arg").invert().unwrap_or(Fq::ZERO),
            "ofU64" => Fq::from(self.u64_expr(&e["arg"])),
            // `hintFor`: one row of the message bytes under its key and width, else no rows (zeros).
            "hintGet" => if e["table"].as_str() == Some(&self.hint_key) && num(&e["width"]) == self.hint_width
                && self.u64_expr(&e["row"]) == 0 { self.message[num(&e["col"])] } else { Fq::ZERO },
            other => panic!("field node {other}"),
        }
    }
    fn u64_expr(&self, e: &Json) -> u64 {
        let ab = || (self.u64_expr(&e["lhs"]), self.u64_expr(&e["rhs"]));
        match e["type"].as_str().unwrap() {
            "const" => e["value"].as_u64()
                .or_else(|| e["value"].as_str().and_then(|s| s.parse().ok()))
                .unwrap_or_else(|| panic!("u64 constant {e}")),
            "val" => u64::from_le_bytes(self.field(&e["arg"]).to_repr().as_ref()[..8].try_into().unwrap()),
            "add" => { let (a, b) = ab(); a.wrapping_add(b) }
            "mul" => { let (a, b) = ab(); a.wrapping_mul(b) }
            // Lean's `UInt64`: x / 0 = 0, x % 0 = x; shifts mask the count mod 64.
            "div" => { let (a, b) = ab(); if b == 0 { 0 } else { a / b } }
            "mod" => { let (a, b) = ab(); if b == 0 { a } else { a % b } }
            "and" => { let (a, b) = ab(); a & b }
            "or" => { let (a, b) = ab(); a | b }
            "xor" => { let (a, b) = ab(); a ^ b }
            "shiftLeft" => { let (a, b) = ab(); a.wrapping_shl(b as u32) }
            "shiftRight" => { let (a, b) = ab(); a.wrapping_shr(b as u32) }
            other => panic!("u64 node {other}"),
        }
    }
}

/// Runs the assignments in order; returns the advice cells (column, row, value) in that order.
fn witness(w: &Json, message: &[u8]) -> Vec<(usize, usize, Fq)> {
    let modulus = BigUint::parse_bytes(Fq::MODULUS.trim_start_matches("0x").as_bytes(), 16).unwrap();
    let mut env = Env { cells: HashMap::new(), hint_key: w["hint"]["key"].as_str().unwrap().into(),
        hint_width: num(&w["hint"]["width"]), message: message.iter().map(|&b| Fq::from(b as u64)).collect(), modulus };
    let mut advice = vec![];
    for a in list(&w["assignments"]) {
        let (kind, column, row) = (a[0].as_u64().unwrap(), num(&a[1]), num(&a[2]));
        let value = env.field(&a[3]);
        assert!(env.cells.insert((kind, column, row), value).is_none(), "cell written twice");
        if kind == 0 { advice.push((column, row, value)); }
    }
    advice
}

fn verify(params: &ParamsKZG<Bls12>, vk: &Vk, instances: &[&[Fq]], proof: &[u8]) -> bool {
    let mut transcript = CircuitTranscript::<blake2b_simd::State>::init_from_bytes(proof);
    prepare::<Fq, DefaultPCS, _>(vk, &[], instances, &mut transcript).is_ok_and(|guard|
        transcript.assert_empty().is_ok() && guard.verify(&DefaultPCS::get_verifier_params(params)).is_ok())
}

/// How a negative check ended. Only a verifier rejection exercises the verifier.
fn negative_result(outcome: &str) -> &'static str {
    match outcome {
        "rejected" => "verifier-rejected",
        "accepted" => "accepted",
        o if o.starts_with("skipped") => "skipped",
        o if o.starts_with("prover") => "prover-failed",
        _ => "verifier-panicked",
    }
}

fn panic_text(payload: Box<dyn std::any::Any + Send>) -> String {
    payload.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_default()
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let usage = "usage: OUT_DIR [HEX] [--zk DIR] [--lean FILE] [CHECK]";
    let [out, rest @ ..] = &args[..] else { panic!("{usage}") };
    let (mut message_hex, mut zk, mut lean, mut check) = (None, None, None, vec![]);
    let mut rest = rest.iter();
    while let Some(arg) = rest.next() {
        let mut value = || rest.next().unwrap_or_else(|| panic!("{usage}: {arg} needs a value"));
        match arg.as_str() {
            "--zk" => zk = Some(PathBuf::from(value())),
            "--lean" => lean = Some(PathBuf::from(value())),
            "--tamper" => check.extend([arg.clone(), value().clone()]),
            flag if flag.starts_with("--") => check.push(arg.clone()),
            hex if message_hex.is_none() => message_hex = Some(hex),
            _ => panic!("{usage}: one HEX only"),
        }
    }
    let zk = zk.or_else(|| std::env::var_os("VK_ZK").map(PathBuf::from))
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../midnight-zk"));
    let checks = lean.is_some() || !check.is_empty();
    assert!(message_hex.is_some() || !checks, "{usage}: checks need HEX");
    let out = Path::new(out);
    let spec: Json = serde_json::from_slice(&fs::read(out.join("export.json")).unwrap()).unwrap();
    let passed = match spec["planner"].as_str().unwrap_or("simple") {
        "simple" => prove::<SimpleFloorPlanner>(spec, "simple", &zk, out, message_hex, lean.as_deref(), &check),
        "v1" => prove::<V1>(spec, "v1", &zk, out, message_hex, lean.as_deref(), &check),
        other => panic!("unknown floor planner {other:?}"),
    };
    std::process::exit(if passed { 0 } else { 1 });
}

/// Derives the key and prints its fingerprint and raw bytes' SHA-256 (a submission's `lean_raw_sha256`); `true` for
/// `MidnightVK`.
fn derive_key<P: FloorPlanner>(spec: &Arc<Json>, planner: &str, params: &ParamsKZG<Bls12>, k: u32)
    -> (Vk, String, bool) {
    let keyed = JsonCircuit::<P> {
        spec: spec.clone(), drop_copy: None, witness: None, planner: PhantomData,
    };
    let vk = keygen_vk_with_k::<Fq, DefaultPCS, _>(params, &keyed, k).unwrap();
    let (stdlib, raw, _) = key_bytes(spec, planner, &keyed, &vk);
    let raw_sha256 = hex(&Sha256::digest(&raw));
    println!("vk {} {} raw-sha256 {raw_sha256}", fingerprint(&vk), if stdlib { "midnight" } else { "halo2" });
    (vk, raw_sha256, stdlib)
}

/// Whether the run passed: the honest proof verified (Lean and any `MidnightVK` header agreeing), or the
/// verifier rejected a check's proof.
fn prove<P: FloorPlanner>(
    spec: Json, planner: &str, zk: &Path, out: &Path, message_hex: Option<&str>,
    lean: Option<&Path>, check: &[String],
) -> bool {
    let Some(message_hex) = message_hex else {
        let (k, _, params) = params(&spec, zk);
        derive_key::<P>(&Arc::new(spec), planner, &params, k);
        return true;
    };
    let message = (0..message_hex.len() / 2).map(|i| u8::from_str_radix(&message_hex[2 * i..2 * i + 2], 16).unwrap())
        .collect::<Vec<_>>();
    assert!(message.len() == 24 && hex(&message) == message_hex, "message: 48 lowercase hex digits");
    let dir = out.join("prove").join(message_hex);
    fs::create_dir_all(&dir).unwrap();
    let write = |name: &str, report: Json| fs::write(dir.join(name), serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    let w: Json = serde_json::from_slice(&fs::read(out.join("witgen.json")).unwrap()).unwrap();
    assert_eq!(w["region_starts"], spec["region_starts"], "witness placement");
    assert!(num(&spec["num_instance"]) == 2, "two instance columns");
    let digest = Sha256::digest(&message);
    // The contract's public input (Rust.lean's `initial`), however the circuit copies to it.
    let mut instances = vec![vec![], digest.iter().map(|&b| Fq::from(b as u64)).collect::<Vec<_>>()];
    let start = Instant::now();
    let mut cells = witness(&w, &message);
    let witness_ms = start.elapsed().as_millis();
    // Lean's evaluation of the same program, cell for cell.
    let lean_mismatches = lean.map(|path| {
        let l: Json = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
        let theirs = list(&l["advice"]).iter().map(|c| (num(&c[0]), num(&c[1]), field(&c[2]))).collect::<Vec<_>>();
        if theirs.len() != cells.len() { return json!({"count": "length differs", "lean": theirs.len(), "rust": cells.len()}); }
        let differ = cells.iter().zip(&theirs).filter(|(a, b)| a != b).map(|(a, _)| json!([a.0, a.1])).collect::<Vec<_>>();
        json!({"count": differ.len(), "first": differ.iter().take(5).collect::<Vec<_>>()})
    });
    let tampered = match (check.first().map(String::as_str), check.get(1).map(String::as_str)) {
        (Some("--tamper"), Some(which)) => {
            let i = match which {
                "first" => Some(0),
                // The advice end of the first copy to an instance cell (a digest byte).
                "copy" => {
                    let perm = list(&spec["permutation"]);
                    let end = |c: &Json, r: &Json| (perm[num(c)][0].as_str().unwrap(), num(&perm[num(c)][1]), num(r));
                    let cell = list(&spec["copies"]).iter().find_map(|c| match (end(&c[0], &c[1]), end(&c[2], &c[3])) {
                        (("advice", column, row), ("instance", _, _)) | (("instance", _, _), ("advice", column, row)) => Some((column, row)),
                        _ => None,
                    });
                    cell.and_then(|cell| cells.iter().position(|&(c, r, _)| (c, r) == cell))
                }
                other => panic!("--tamper {other}"),
            };
            let Some(i) = i else {
                println!("tamper {which}: skipped, no advice-instance copy");
                write(&format!("negative-tamper-{which}.json"), json!({"check": format!("tamper-{which}"),
                    "outcome": "skipped: no advice-instance copy", "result": "skipped"}));
                return true;
            };
            cells[i].2 += Fq::ONE;
            Some((which.to_string(), json!([cells[i].0, cells[i].1])))
        }
        _ => None,
    };
    let (k, _, params) = params(&spec, zk);
    let spec = Arc::new(spec);
    let start = Instant::now();
    let (vk, raw_sha256, midnight) = derive_key::<P>(&spec, planner, &params, k);
    let vk_ms = start.elapsed().as_millis();
    let circuit = JsonCircuit::<P> { spec: spec.clone(), drop_copy: None, witness: Some((Arc::new(cells), true)), planner: PhantomData };
    match check.first().map(String::as_str) {
        Some("--mock") => {
            let result = MockProver::run(&circuit, instances.clone()).map(|m| m.verify());
            let text = match &result {
                Ok(Ok(())) => "satisfied".to_string(),
                Ok(Err(failures)) => failures.iter().take(10).map(|f| format!("{f}")).collect::<Vec<_>>().join("\n"),
                Err(e) => format!("mock error: {e:?}"),
            };
            println!("mock: {text}");
            write("mock.json", json!({"satisfied": matches!(result, Ok(Ok(()))), "failures": text}));
            return matches!(result, Ok(Ok(())));
        }
        Some("--wrong-digest") => {
            instances[1][0] += Fq::ONE;
            let refs = instances.iter().map(|v| &v[..]).collect::<Vec<_>>();
            let proof = fs::read(dir.join("proof.bin")).unwrap();
            let outcome = match panic::catch_unwind(panic::AssertUnwindSafe(|| verify(&params, &vk, &refs, &proof))) {
                Ok(true) => "accepted".to_string(),
                Ok(false) => "rejected".to_string(),
                Err(p) => format!("verifier panic: {}", panic_text(p)),
            };
            let result = negative_result(&outcome);
            println!("wrong digest: {outcome} ({result})");
            write("negative-wrong-digest.json", json!({"check": "wrong-digest", "outcome": outcome, "result": result}));
            return result == "verifier-rejected";
        }
        Some("--tamper") | None => {}
        Some(other) => panic!("unknown check {other}"),
    }
    if tampered.is_none() { let _ = fs::remove_file(dir.join("proof.bin")); }
    let refs = instances.iter().map(|v| &v[..]).collect::<Vec<_>>();
    let start = Instant::now();
    let pk = keygen_pk(vk.clone(), &circuit).unwrap();
    let pk_ms = start.elapsed().as_millis();
    let start = Instant::now();
    let proof = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        let mut transcript = CircuitTranscript::<blake2b_simd::State>::init();
        create_proof::<Fq, DefaultPCS, _, _>(&params, &pk, &circuit, 0, &refs, &mut transcript, OsRng)
            .map(|()| transcript.finalize())
    }));
    let prove_ms = start.elapsed().as_millis();
    let start = Instant::now();
    // A prover error or panic, and a verifier panic, are kept apart from a verifier reject.
    let (verified, outcome, proof) = match proof {
        Err(p) => (false, format!("prover panic: {}", panic_text(p)), None),
        Ok(Err(e)) => (false, format!("prover error: {e:?}"), None),
        Ok(Ok(proof)) => match panic::catch_unwind(panic::AssertUnwindSafe(|| verify(&params, &vk, &refs, &proof))) {
            Ok(verified) => (verified, if verified { "accepted" } else { "rejected" }.to_string(), Some(proof)),
            Err(p) => (false, format!("verifier panic: {}", panic_text(p)), Some(proof)),
        },
    };
    let verify_ms = start.elapsed().as_millis();
    let ms = json!({"witness": witness_ms, "vk": vk_ms, "pk": pk_ms, "prove": prove_ms, "verify": verify_ms});
    if let Some((which, cell)) = tampered {
        let result = negative_result(&outcome);
        println!("tampered advice {cell}: {outcome} ({result})");
        write(&format!("negative-tamper-{which}.json"), json!({"check": format!("tamper-{which}"), "cell": cell,
            "outcome": outcome, "result": result, "ms": ms}));
        return result == "verifier-rejected";
    }
    // midnight-zk's `verify` rejects a `MidnightVK` whose declared count is not the instance's length.
    let header = midnight.then(|| num(&spec["public_inputs"]));
    let header_ok = header.is_none_or(|n| n == instances[1].len());
    if !header_ok { println!("MidnightVK header declares {} public inputs, the digest has 32", header.unwrap()); }
    let proof_bytes = proof.as_ref().map_or(0, Vec::len);
    if let (true, Some(proof)) = (verified, &proof) { fs::write(dir.join("proof.bin"), proof).unwrap(); }
    let agrees = lean_mismatches.as_ref().is_none_or(|m| m["count"] == 0);
    let passed = verified && agrees && header_ok;
    println!("prove {message_hex}: {outcome}, {proof_bytes} bytes, witness {witness_ms} ms, prove {prove_ms} ms, verify {verify_ms} ms");
    write("prove.json", json!({"schema": "midnight-vk-export-prove-v1", "planner": planner,
        "status": if passed { "PASS" } else { "FAIL" }, "outcome": outcome, "verified": verified,
        "message": message_hex, "digest": hex(&digest), "vk": fingerprint(&vk), "vk_raw_sha256": raw_sha256,
        "contract_placement": w["contract_placement"], "proof_bytes": proof_bytes, "advice_cells": circuit.witness.as_ref().unwrap().0.len(),
        "public_inputs": {"instance": instances[1].len(), "midnight_header": header, "consistent": header_ok},
        "lean_mismatches": lean_mismatches, "ms": ms}));
    passed
}
