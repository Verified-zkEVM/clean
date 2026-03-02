use clean_backend::{
    generate_table_traces, parse_trace, parse_trace_matrix,
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

/// Generate Fibonacci trace using the simplified Lean script
pub fn generate_trace_from_lean<F: Field + PrimeCharacteristicRing>(
    steps: usize,
    output_filename: &str,
) -> Result<Vec<Vec<F>>, Box<dyn std::error::Error>> {
    let backend_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = backend_dir.join("tests").join("fixtures");
    let output_path = format!("output/{}", output_filename);

    // Create the output directory if it doesn't exist
    let output_dir = tests_dir.join("output");
    std::fs::create_dir_all(&output_dir)?;

    // Run the trace generation script
    let output = Command::new("bash")
        .arg(tests_dir.join("run_lean.sh"))
        .arg("FibTraceGen.lean")
        .arg(steps.to_string())
        .arg(&output_path)
        .current_dir(&tests_dir)
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("Failed to generate trace: {}", stderr).into());
    }

    // Read the generated JSON file
    let json_path = tests_dir.join(&output_path);
    let json_content = std::fs::read_to_string(json_path)?;

    // Parse the trace using the existing parse_trace function
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

/// Run a pair of Lean generators (circuit + trace) via run_lean.sh and return their JSON content.
pub fn run_lean_scripts(
    circuit_lean_file: &str,
    circuit_output: &str,
    trace_lean_file: &str,
    trace_output: &str,
) -> (String, String) {
    let backend_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = backend_dir.join("tests").join("fixtures");
    std::fs::create_dir_all(tests_dir.join("output")).unwrap();
    let _ = std::fs::remove_file(tests_dir.join(circuit_output));
    let _ = std::fs::remove_file(tests_dir.join(trace_output));

    let circuit_result = Command::new("bash")
        .arg(tests_dir.join("run_lean.sh"))
        .arg(circuit_lean_file)
        .arg(circuit_output)
        .current_dir(&tests_dir)
        .output()
        .expect("Failed to run circuit generation script");
    assert!(
        circuit_result.status.success(),
        "Circuit generation failed: {}",
        String::from_utf8_lossy(&circuit_result.stderr)
    );

    let trace_result = Command::new("bash")
        .arg(tests_dir.join("run_lean.sh"))
        .arg(trace_lean_file)
        .arg(trace_output)
        .current_dir(&tests_dir)
        .output()
        .expect("Failed to run trace generation script");
    assert!(
        trace_result.status.success(),
        "Trace generation failed: {}",
        String::from_utf8_lossy(&trace_result.stderr)
    );

    let circuit_json = std::fs::read_to_string(tests_dir.join(circuit_output))
        .expect("Failed to read generated circuit JSON");
    let trace_json = std::fs::read_to_string(tests_dir.join(trace_output))
        .expect("Failed to read generated trace JSON");

    (circuit_json, trace_json)
}

/// Parse circuit + trace JSON, build AIR instances, prove and verify.
pub fn prove_and_verify_from_json(
    circuit_json_str: &str,
    trace_json_str: &str,
) {
    let config = setup::test_config(500);

    let circuit_value: serde_json::Value =
        serde_json::from_str(circuit_json_str).expect("Failed to parse circuit JSON");
    let constraints = circuit_value["constraints"].clone();
    let preprocessed_tables = &circuit_value["preprocessed_tables"];

    let trace_value: serde_json::Value =
        serde_json::from_str(trace_json_str).expect("Failed to parse trace JSON");
    let main_trace_str = trace_value["main_trace"].to_string();
    let main_trace = parse_trace_matrix::<BabyBear>(&main_trace_str);

    let prover_tables = &trace_value["prover_tables"];
    let (mem_air, mem_data_matrix) =
        ProverTableAir::<BabyBear>::from_json("memory".into(), &prover_tables["memory"]);

    let program_air: PreprocessedTableAir<BabyBear> =
        PreprocessedTableAir::from_json("program".into(), &preprocessed_tables["program"]);

    let main_air_instance = MainAir::<BabyBear>::from_value(
        constraints,
        main_trace.width(),
        main_trace.height(),
    );
    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(CleanAirInstance::Main(main_air_instance)),
        AirInfo::new(CleanAirInstance::Preprocessed(program_air)),
        AirInfo::new(CleanAirInstance::ProverTable(mem_air)),
    ];

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
