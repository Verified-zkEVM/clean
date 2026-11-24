//! Rust half of the VK comparison: rebuilds a circuit from the Lean export
//! (`MidnightExport`) as a halo2 `Circuit` and generates its key with
//! midnight-zk keygen. Simple uses `MidnightVK` for stdlib configurations. V1 uses halo2 bytes.
//! Usage: EXPORT.json MIDNIGHT_ZK OUT_DIR [--drop-copy N].
use std::{fs, marker::PhantomData, path::Path, sync::Arc};
use ff::FromUniformBytes;
use group::Curve;
use midnight_curves::{Fq, serde_traits::SerdeObject};
use midnight_proofs::{circuit::{SimpleFloorPlanner, floor_planner::V1}, plonk::{FloorPlanner, keygen_vk_with_k},
    utils::SerdeFormat};
use midnight_vk_export_native::{JsonCircuit, fingerprint, hex, key_bytes, params, scalar};
use midnight_zk_stdlib::DefaultPCS;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let drop_copy = match &args[..] {
        [_, _, _, _] => None,
        [_, _, _, _, flag, n] if flag == "--drop-copy" => Some(n.parse().unwrap()),
        _ => panic!("usage: EXPORT.json MIDNIGHT_ZK OUT_DIR [--drop-copy N]"),
    };
    let (zk, out) = (Path::new(&args[2]), Path::new(&args[3]));
    let spec: Json = serde_json::from_slice(&fs::read(&args[1]).unwrap()).unwrap();
    // Exports written before the planner field was added use Simple.
    let planner = spec.get("planner").map(|v| v.as_str().expect("planner name")).unwrap_or("simple");
    match planner {
        "simple" => export::<SimpleFloorPlanner>(spec, "simple", zk, out, drop_copy),
        "v1" => export::<V1>(spec, "v1", zk, out, drop_copy),
        other => panic!("unknown floor planner {other:?}"),
    }
}

fn export<P: FloorPlanner>(spec: Json, planner: &str, zk: &Path, out: &Path, drop_copy: Option<usize>) {
    let start = std::time::Instant::now();
    let (k, file_k, params) = params(&spec, zk);
    let loaded = start.elapsed().as_millis();
    let circuit = JsonCircuit::<P> { spec: Arc::new(spec.clone()), drop_copy, witness: None, planner: PhantomData };
    let vk = keygen_vk_with_k::<Fq, DefaultPCS, _>(&params, &circuit, k).unwrap();
    let keygen = start.elapsed().as_millis() - loaded;

    let (stdlib, raw, processed) = key_bytes(&spec, planner, &circuit, &vk);
    let inner = vk.to_bytes(SerdeFormat::RawBytes);
    let domain = format!("{:?}", vk.get_domain().pinned());
    let pinned = format!("{:?}", vk.cs().pinned());
    let transcript = [inner, domain.into_bytes(), pinned.clone().into_bytes()].concat();
    let hash = blake2b_simd::Params::new().hash_length(64).personal(b"Halo2-Verify-Key").hash(&transcript);
    assert_eq!(Fq::from_uniform_bytes(hash.as_array()), vk.transcript_repr(), "rebuilt transcript input");
    let digest = Sha256::digest(&raw);
    let static_vks = fs::read_dir(zk.join("zk_stdlib/tests/static_vks")).unwrap()
        .map(|e| e.unwrap().path()).filter(|p| fs::read(p).unwrap() == digest[..])
        .map(|p| p.file_name().unwrap().to_string_lossy().into_owned()).collect::<Vec<_>>();
    let cs = vk.cs();
    fs::write(out.join("rust.raw.bin"), &raw).unwrap();
    fs::write(out.join("rust.processed.bin"), &processed).unwrap();
    let points = vk.phase0_commitment().0.iter().map(|c| hex(&c.as_point().to_affine().to_raw_bytes()))
        .collect::<Vec<_>>();
    let report = json!({"schema": "midnight-vk-export-rust-v1", "k": k, "srs": format!("bls_filecoin_2p{file_k}"),
        "planner": planner, "drop_copy": drop_copy, "static_vks": static_vks,
        "key": {"format": if stdlib { "midnight" } else { "halo2" }, "points": points, "raw": hex(&raw), "processed": hex(&processed), "transcript_input": hex(&transcript),
            "transcript_repr": scalar(vk.transcript_repr()), "fingerprint": fingerprint(&vk), "pinned_cs": pinned, "degree": cs.degree(),
            "blinding_factors": cs.blinding_factors(), "num_fixed": cs.num_fixed_columns(),
            "permutation_columns": cs.permutation().get_columns().len()},
        "ms": {"srs": loaded, "keygen": keygen}});
    fs::write(out.join("rust.json"), serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    println!("rust: keygen {keygen} ms, vk {}, raw sha256 {}, static {:?}", fingerprint(&vk), hex(&digest), static_vks);
}
