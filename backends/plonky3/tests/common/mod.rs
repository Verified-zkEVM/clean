use clean_backend::{
    generate_table_traces, parse_table_json, parse_trace, parse_trace_matrix,
    prove, verify, AirInfo,
    CleanAirInstance, MainAir, PreprocessedTableAir, ProverTableAir, StarkConfig,
};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{create_test_fri_params, TwoAdicFriPcs};
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::rngs::SmallRng;
use rand::SeedableRng;
use std::process::Command;

pub mod setup {
    use super::*;

    pub type Val = BabyBear;
    pub type Perm = Poseidon2BabyBear<16>;
    pub type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    pub type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    pub type ValMmcs = MerkleTreeMmcs<
        <Val as Field>::Packing,
        <Val as Field>::Packing,
        MyHash,
        MyCompress,
        8,
    >;
    pub type Challenge = BinomialExtensionField<Val, 4>;
    pub type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    pub type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
    pub type Dft = Radix2DitParallel<Val>;
    pub type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    pub type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

    pub fn test_config(seed: u64) -> MyConfig {
        let mut rng = SmallRng::seed_from_u64(seed);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        let val_mmcs = ValMmcs::new(hash, compress);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let dft = Dft::default();
        let fri = create_test_fri_params(challenge_mmcs, 2);
        let pcs = Pcs::new(dft, val_mmcs, fri);
        let challenger = Challenger::new(perm);
        MyConfig::new(pcs, challenger)
    }
}

/// Run a single Lean script via `lake env lean --run` and return the content of its output file.
///
/// `extra_args` are passed between the script name and the output path (e.g. a step count).
pub fn run_lean_script(script: &str, extra_args: &[&str], output_path: &str) -> String {
    let backend_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = backend_dir.join("tests").join("fixtures");
    let clean_root = backend_dir.parent().unwrap().parent().unwrap();
    std::fs::create_dir_all(tests_dir.join("output")).unwrap();
    let _ = std::fs::remove_file(tests_dir.join(output_path));

    let lean_file = tests_dir.join(script);
    let output_file = tests_dir.join(output_path);

    let mut cmd = Command::new("lake");
    cmd.args(["env", "lean", "--run"]);
    cmd.arg(&lean_file);
    for arg in extra_args {
        cmd.arg(arg);
    }
    cmd.arg(&output_file);
    cmd.current_dir(clean_root);

    let result = cmd.output().expect("Failed to run lake");
    assert!(
        result.status.success(),
        "Lean script '{}' failed: {}",
        script,
        String::from_utf8_lossy(&result.stderr)
    );

    std::fs::read_to_string(&output_file)
        .unwrap_or_else(|e| panic!("Failed to read output '{}': {}", output_path, e))
}

/// Generate Fibonacci trace using the simplified Lean script
pub fn generate_trace_from_lean<F: Field + PrimeCharacteristicRing>(
    steps: usize,
    output_filename: &str,
) -> Result<Vec<Vec<F>>, Box<dyn std::error::Error>> {
    let output_path = format!("output/{}", output_filename);
    let steps_str = steps.to_string();
    let json_content = run_lean_script("FibTraceGen.lean", &[&steps_str], &output_path);
    let trace = parse_trace::<F>(&json_content);
    Ok(trace)
}

/// Helper function to read JSON file content from the tests directory
pub fn read_test_json(filename: &str) -> String {
    let tests_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests").join("fixtures");
    let json_path = tests_dir.join(filename);
    std::fs::read_to_string(json_path)
        .unwrap_or_else(|e| panic!("Failed to read JSON file '{}': {}", filename, e))
}

/// Run a pair of Lean generators (circuit + trace) and return their JSON content.
pub fn run_lean_scripts(
    circuit_lean_file: &str,
    circuit_output: &str,
    trace_lean_file: &str,
    trace_output: &str,
) -> (String, String) {
    let circuit_json = run_lean_script(circuit_lean_file, &[], circuit_output);
    let trace_json = run_lean_script(trace_lean_file, &[], trace_output);
    (circuit_json, trace_json)
}

/// Parse circuit + trace JSON, build AIR instances, prove and verify.
pub fn prove_and_verify_from_json(
    circuit_json_str: &str,
    trace_json_str: &str,
) {
    let config = setup::test_config(500);

    // --- Parse circuit JSON (verifier information) ---
    let circuit_value: serde_json::Value =
        serde_json::from_str(circuit_json_str).expect("Failed to parse circuit JSON");
    let constraints = circuit_value["constraints"].clone();
    let num_columns = circuit_value["num_columns"].as_u64().unwrap() as usize;
    let preprocessed_tables = &circuit_value["preprocessed_tables"];

    let program_air: PreprocessedTableAir<BabyBear> =
        PreprocessedTableAir::from_json("program".into(), &preprocessed_tables["program"]);

    let prover_tables_meta = &circuit_value["prover_tables"];
    let mem_width = prover_tables_meta["memory"]["width"].as_u64().unwrap() as usize;
    let mem_air = ProverTableAir::<BabyBear>::new("memory".into(), mem_width);

    // --- Parse trace JSON (prover data) ---
    let trace_value: serde_json::Value =
        serde_json::from_str(trace_json_str).expect("Failed to parse trace JSON");
    let main_trace_str = trace_value["main_trace"].to_string();
    let main_trace = parse_trace_matrix::<BabyBear>(&main_trace_str);

    assert_eq!(
        main_trace.width(),
        num_columns,
        "Trace width {} doesn't match circuit num_columns {}",
        main_trace.width(),
        num_columns
    );

    let prover_tables = &trace_value["prover_tables"];
    let mem_data_matrix = parse_table_json::<BabyBear>(&prover_tables["memory"]);

    // --- Build AIR instances (circuit info + trace_height) ---
    let main_air_instance = MainAir::<BabyBear>::from_value(
        constraints,
        num_columns,
        main_trace.height(),
    );
    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(CleanAirInstance::Main(main_air_instance)),
        AirInfo::new(CleanAirInstance::Preprocessed(program_air)),
        AirInfo::new(CleanAirInstance::ProverTable(mem_air)),
    ];

    // --- Prove and verify ---
    let table_traces = generate_table_traces::<BabyBear, setup::MyConfig>(
        &air_infos,
        &main_trace,
        &[("memory", &mem_data_matrix)],
    );
    let mut traces = vec![main_trace];
    traces.extend(table_traces);

    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis)
        .expect("FemtoCairo end-to-end verification failed");
}
