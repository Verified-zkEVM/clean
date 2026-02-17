use clean_backend::{
    byte_range_air, generate_multiplicity_traces, parse_init_trace, prove, verify, AirInfo,
    CleanAirInstance, MainAir, PreprocessedTableAir, StarkConfig,
};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{create_test_fri_params, TwoAdicFriPcs};
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
    output_filename: &str,
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
    let config = create_test_fri_params(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, config);

    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    let steps = 512; // Number of steps for the Fibonacci sequence
                     // Generate trace from Lean with 256 steps, fallback to static file if it fails
    let init_trace = match generate_trace_from_lean::<BabyBear>(steps, "trace.json") {
        Ok(trace) => {
            println!(
                "Successfully generated trace from Lean with {} rows",
                trace.len()
            );
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
    let byte_range = byte_range_air::<BabyBear>();
    let byte_range_air_instance = CleanAirInstance::Preprocessed(byte_range);

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
    let lookup_traces = generate_multiplicity_traces::<BabyBear, MyConfig>(&air_infos, &main_trace);
    // Collect all traces: main trace + lookup traces
    let mut traces = vec![main_trace.clone()];
    traces.extend(lookup_traces);

    let pis = vec![BabyBear::ZERO, BabyBear::ONE, x];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("verification failed");
}

/// Test multi-column lookups with RLC compression.
/// Demonstrates a 2-column preprocessed table (address, value) with
/// multi-column sends from the main trace.
#[test]
fn test_multi_column_lookup() {
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

    let mut rng = SmallRng::seed_from_u64(99);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let config = create_test_fri_params(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, config);
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Circuit JSON: lookup of (var0, var1) into "Memory" table.
    // Two-column lookup: address (col 0) and value (col 1).
    let json_content = r#"[
      {
        "type": "EveryRowExceptLast",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "Memory",
                "entry": [
                  { "type": "var", "index": 0 },
                  { "type": "var", "index": 1 }
                ]
              }
            }
          ],
          "assignment": {
            "vars": [
              { "row": 0, "column": 0 },
              { "row": 0, "column": 1 }
            ],
            "offset": 2,
            "aux_length": 0
          }
        }
      }
    ]"#;

    // Preprocessed "Memory" table: 16 rows × 2 columns (address, value).
    // Row i: (i, 100*(i+1))
    let num_rows = 16;
    let memory_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i| {
            vec![
                BabyBear::from_u64(i as u64),
                BabyBear::from_u64(100 * (i + 1) as u64),
            ]
        })
        .collect();
    let memory_preprocessed = RowMajorMatrix::new(memory_data, 2);

    // Main trace: 16 rows × 2 columns, matching the preprocessed table exactly.
    let main_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i| {
            vec![
                BabyBear::from_u64(i as u64),
                BabyBear::from_u64(100 * (i + 1) as u64),
            ]
        })
        .collect();
    let main_trace = RowMajorMatrix::new(main_data, 2);

    let main_air = MainAir::<BabyBear>::new(json_content, 2);
    let air_instance = CleanAirInstance::Main(main_air);

    let memory_air = PreprocessedTableAir::new("Memory".into(), memory_preprocessed);
    let memory_instance = CleanAirInstance::Preprocessed(memory_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance, 2),
        AirInfo::new(memory_instance, 1),
    ];

    let lookup_traces =
        generate_multiplicity_traces::<BabyBear, MyConfig>(&air_infos, &main_trace);
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::ONE];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("multi-column lookup verification failed");
}

/// Test multi-column lookups with expression entries (not just simple variable refs).
/// Demonstrates lookup entries like (var0, var1 + const(1)).
#[test]
fn test_expression_lookup() {
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

    let mut rng = SmallRng::seed_from_u64(77);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let config = create_test_fri_params(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, config);
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Circuit JSON: lookup of (var0, var0 + const(1)) into "Table".
    // The second entry is an expression: column_0 + 1.
    let json_content = r#"[
      {
        "type": "EveryRowExceptLast",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "Table",
                "entry": [
                  { "type": "var", "index": 0 },
                  {
                    "type": "add",
                    "lhs": { "type": "var", "index": 0 },
                    "rhs": { "type": "const", "value": 1 }
                  }
                ]
              }
            }
          ],
          "assignment": {
            "vars": [
              { "row": 0, "column": 0 }
            ],
            "offset": 1,
            "aux_length": 0
          }
        }
      }
    ]"#;

    // Preprocessed table: 16 rows × 2 columns.
    // Row i: (i, i+1) — matches the expression (var0, var0+1).
    let num_rows = 16;
    let table_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i| {
            vec![
                BabyBear::from_u64(i as u64),
                BabyBear::from_u64((i + 1) as u64),
            ]
        })
        .collect();
    let table_preprocessed = RowMajorMatrix::new(table_data, 2);

    // Main trace: 16 rows × 1 column, values 0..15.
    let main_data: Vec<BabyBear> = (0..num_rows)
        .map(|i| BabyBear::from_u64(i as u64))
        .collect();
    let main_trace = RowMajorMatrix::new(main_data, 1);

    let main_air = MainAir::<BabyBear>::new(json_content, 1);
    let air_instance = CleanAirInstance::Main(main_air);

    let table_air = PreprocessedTableAir::new("Table".into(), table_preprocessed);
    let table_instance = CleanAirInstance::Preprocessed(table_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance, 1),
        AirInfo::new(table_instance, 1),
    ];

    let lookup_traces =
        generate_multiplicity_traces::<BabyBear, MyConfig>(&air_infos, &main_trace);
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::ONE];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("expression lookup verification failed");
}

/// Test a 16-entry range-check table to demonstrate the generic lookup framework
/// works with arbitrary table names and sizes.
#[test]
fn test_range_check_16() {
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

    let mut rng = SmallRng::seed_from_u64(42);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let config = create_test_fri_params(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, config);
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Minimal JSON: an EveryRowExceptLast op with a lookup of column 0 into "Range16".
    // No arithmetic constraints -- only the lookup.
    let json_content = r#"[
      {
        "type": "EveryRowExceptLast",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "Range16",
                "entry": [{ "type": "var", "index": 0 }]
              }
            }
          ],
          "assignment": {
            "vars": [
              { "row": 0, "column": 0 }
            ],
            "offset": 1,
            "aux_length": 0
          }
        }
      }
    ]"#;

    // Main trace: 16 rows, 1 column. Column 0 has values in [0,15].
    let num_rows = 16;
    let width = 1;
    let trace_data: Vec<BabyBear> = (0..num_rows)
        .map(|i| BabyBear::from_u64(i as u64))
        .collect();
    let main_trace = RowMajorMatrix::new(trace_data, width);

    let main_air = MainAir::<BabyBear>::new(json_content, width);
    let air_instance = CleanAirInstance::Main(main_air);

    // Create a 16-entry preprocessed table (values 0..15)
    let range16_data: Vec<BabyBear> = (0..16).map(|i| BabyBear::from_u64(i as u64)).collect();
    let range16_preprocessed = RowMajorMatrix::new(range16_data, 1);
    let range16_air = PreprocessedTableAir::new("Range16".into(), range16_preprocessed);
    let range16_instance = CleanAirInstance::Preprocessed(range16_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance, width),
        AirInfo::new(range16_instance, 1),
    ];

    let lookup_traces =
        generate_multiplicity_traces::<BabyBear, MyConfig>(&air_infos, &main_trace);
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    // Public values: [0, 1, 1] (matching the default public_values in LookupBuilder)
    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::ONE];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("range-check-16 verification failed");
}
