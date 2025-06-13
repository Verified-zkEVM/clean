use clean_backend::{
    generate_lookup_traces, parse_init_trace, prove, verify, AirInfo, ByteRangeAir, CleanAirInstance, MainAir, StarkConfig
};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{create_test_fri_config, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::rngs::SmallRng;
use rand::SeedableRng;
use std::process::Command;

const JSON_PATH: &str = "clean_fib.json";

/// Generate Fibonacci trace using the simplified Lean script
fn generate_trace_from_lean<F: Field + PrimeCharacteristicRing>(
    steps: usize,
    output_filename: &str
) -> Result<Vec<Vec<F>>, Box<dyn std::error::Error>> {
    let backend_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = backend_dir.join("tests");
    let script_path = tests_dir.join("generate_trace.sh");
    let output_path = format!("output/{}", output_filename);
    
    // Create the output directory if it doesn't exist
    let output_dir = tests_dir.join("output");
    std::fs::create_dir_all(&output_dir)?;
    
    // Run the simplified trace generation script
    let output = Command::new("bash")
        .arg(&script_path)
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
    
    // Parse the trace using the existing parse_init_trace function
    let trace = parse_init_trace::<F>(&json_content);
    Ok(trace)
}

/// Helper function to read JSON file content from the tests directory
fn read_test_json(filename: &str) -> String {
    let tests_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let json_path = tests_dir.join(filename);
    std::fs::read_to_string(json_path)
        .unwrap_or_else(|e| panic!("Failed to read JSON file '{}': {}", filename, e))
}

/// test fibonacci8 exported from clean
#[test]
fn test_clean_fib() {
    // Initialize tracing subscriber to see tracing output
    let _ = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(tracing::Level::INFO)
        .try_init();

    type Val = BabyBear;
    type Perm = Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type ValMmcs =
        MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 8>;
    type Challenge = BinomialExtensionField<Val, 4>;
    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
    type Dft = Radix2DitParallel<Val>;
    type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let config = create_test_fri_config(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, config);

    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    let steps = 512; // Number of steps for the Fibonacci sequence
    // Generate trace from Lean with 256 steps, fallback to static file if it fails
    let init_trace = match generate_trace_from_lean::<BabyBear>(steps, "trace.json") {
        Ok(trace) => {
            println!("Successfully generated trace from Lean with {} rows", trace.len());
            trace
        }
        Err(e) => {
            panic!("Warning: Could not generate trace from Lean: {}", e);
        }
    };

    let width = init_trace[0].len();

    let main_trace: RowMajorMatrix<BabyBear> =
        RowMajorMatrix::new(init_trace.iter().flatten().cloned().collect(), width);

    // Get the result
    let x = main_trace.get(main_trace.height() - 1, 1).unwrap();

    // Read the JSON file content
    let json_content = read_test_json(JSON_PATH);

    // Create the MainAir from JSON content
    let main_air = MainAir::new(&json_content, main_trace.width());
    let air_instance = CleanAirInstance::Main(main_air);

    // Create a single VK with multiple AirInfo instances
    let byte_range_air = ByteRangeAir::new();
    let byte_range_air_instance = CleanAirInstance::ByteRange(byte_range_air);
    
    // Create VK with multiple air instances (main + lookup)
    let air_instances = vec![
        (air_instance, main_trace.width()),
        (byte_range_air_instance, 1), // ByteRange has width 1
    ];

    let air_infos: Vec<AirInfo<BabyBear>> = air_instances
        .into_iter()
        .map(|(air, trace_width)| AirInfo::new(air, trace_width))
        .collect();
    
    // Generate lookup traces using the AirInfo instances from the VK
    let lookup_traces = generate_lookup_traces::<BabyBear, MyConfig>(&air_infos, &main_trace);
    // Collect all traces: main trace + lookup traces
    let mut traces = vec![main_trace.clone()];
    traces.extend(lookup_traces);


    let pis = vec![BabyBear::ZERO, BabyBear::ONE, x];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("verification failed");
}
