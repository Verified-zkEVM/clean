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

mod setup {
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

const JSON_PATH: &str = "clean_fib.json";

/// Generate Fibonacci trace using the simplified Lean script
fn generate_trace_from_lean<F: Field + PrimeCharacteristicRing>(
    steps: usize,
    output_filename: &str,
) -> Result<Vec<Vec<F>>, Box<dyn std::error::Error>> {
    let backend_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = backend_dir.join("tests").join("fixtures");
    let script_path = tests_dir.join("generate_fib_trace.sh");
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
    let tests_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests").join("fixtures");
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

    let config = setup::test_config(1);

    let steps = 512;
    let init_trace = match generate_trace_from_lean::<BabyBear>(steps, "trace.json") {
        Ok(trace) => {
            println!(
                "Successfully generated trace from Lean with {} rows",
                trace.len()
            );
            trace
        }
        Err(e) => {
            panic!("Could not generate trace from Lean: {}", e);
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
    let main_air = MainAir::new(&json_content, main_trace.width(), main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    // Create a single VK with multiple AirInfo instances
    let byte_range = byte_range_air::<BabyBear>();
    let byte_range_air_instance = CleanAirInstance::Preprocessed(byte_range);

    // Create VK with multiple air instances (main + lookup)
    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(byte_range_air_instance),
    ];

    // Generate lookup traces using the AirInfo instances from the VK
    let lookup_traces = generate_multiplicity_traces::<BabyBear, setup::MyConfig>(&air_infos[1..], &main_trace, air_infos[0].preprocessed.as_ref(), &air_infos[0].lookups, &air_infos[0].lookup_row_scopes);
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

    let config = setup::test_config(99);

    // Circuit JSON: lookup of (var0, var1) into "Memory" table.
    // Two-column lookup: address (col 0) and value (col 1).
    let json_content = r#"[
      {
        "type": "EveryRow",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "Memory",
                "entry": [
                  { "type": "var", "index": 0 },
                  { "type": "var", "index": 1 }
                ],
                "direction": "receive"
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
    // Deliberately NON-sequential column-0 values to test that the multiplicity
    // computation matches on all columns, not just column 0 as a row index.
    let addresses: Vec<u64> = vec![
        42, 7, 100, 3, 255, 10, 0, 99, 50, 15, 200, 1, 77, 33, 128, 64,
    ];
    let memory_data: Vec<BabyBear> = addresses
        .iter()
        .enumerate()
        .flat_map(|(_i, &addr)| {
            vec![
                BabyBear::from_u64(addr),
                BabyBear::from_u64(addr * 10 + 1),
            ]
        })
        .collect();
    let memory_preprocessed = RowMajorMatrix::new(memory_data, 2);

    // Main trace: 16 rows × 2 columns, matching the preprocessed table entries
    // but NOT necessarily in the same order.
    // Reverse the order to further stress the lookup.
    let main_data: Vec<BabyBear> = addresses
        .iter()
        .rev()
        .flat_map(|&addr| {
            vec![
                BabyBear::from_u64(addr),
                BabyBear::from_u64(addr * 10 + 1),
            ]
        })
        .collect();
    let main_trace = RowMajorMatrix::new(main_data, 2);

    let main_air = MainAir::<BabyBear>::new(json_content, 2, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    let memory_air = PreprocessedTableAir::new("Memory".into(), memory_preprocessed);
    let memory_instance = CleanAirInstance::Preprocessed(memory_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(memory_instance),
    ];

    let lookup_traces =
        generate_multiplicity_traces::<BabyBear, setup::MyConfig>(&air_infos[1..], &main_trace, air_infos[0].preprocessed.as_ref(), &air_infos[0].lookups, &air_infos[0].lookup_row_scopes);
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![];
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

    let config = setup::test_config(77);

    // Circuit JSON: lookup of (var0, var0 + const(1)) into "Table".
    // The second entry is an expression: column_0 + 1.
    let json_content = r#"[
      {
        "type": "EveryRow",
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
                ],
                "direction": "receive"
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

    let main_air = MainAir::<BabyBear>::new(json_content, 1, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    let table_air = PreprocessedTableAir::new("Table".into(), table_preprocessed);
    let table_instance = CleanAirInstance::Preprocessed(table_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(table_instance),
    ];

    let lookup_traces =
        generate_multiplicity_traces::<BabyBear, setup::MyConfig>(&air_infos[1..], &main_trace, air_infos[0].preprocessed.as_ref(), &air_infos[0].lookups, &air_infos[0].lookup_row_scopes);
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("expression lookup verification failed");
}

/// Test Direction::Send from the main AIR.
/// Both Send and Receive lookups target the same table "MemTable", forming
/// a permutation check between two column pairs — no preprocessed table needed.
#[test]
fn test_main_air_send_direction() {
    let config = setup::test_config(55);

    // Circuit JSON: two lookups to "MemTable":
    // 1. Send (col0, col1) with direction "send"
    // 2. Receive (col2, col3) with direction "receive"
    let json_content = r#"[
      {
        "type": "EveryRow",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "MemTable",
                "entry": [
                  { "type": "var", "index": 0 },
                  { "type": "var", "index": 1 }
                ],
                "direction": "send"
              }
            },
            {
              "lookup": {
                "table": "MemTable",
                "entry": [
                  { "type": "var", "index": 2 },
                  { "type": "var", "index": 3 }
                ],
                "direction": "receive"
              }
            }
          ],
          "assignment": {
            "vars": [
              { "row": 0, "column": 0 },
              { "row": 0, "column": 1 },
              { "row": 0, "column": 2 },
              { "row": 0, "column": 3 }
            ],
            "offset": 4,
            "aux_length": 0
          }
        }
      }
    ]"#;

    // Main trace: 16 rows × 4 columns.
    // Cols (0,1) = (i, 10*i), Cols (2,3) = (15-i, 10*(15-i))
    // This is a permutation (reverse) of the same multiset.
    let num_rows = 16usize;
    let main_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i| {
            let j = num_rows - 1 - i;
            vec![
                BabyBear::from_u64(i as u64),
                BabyBear::from_u64(10 * i as u64),
                BabyBear::from_u64(j as u64),
                BabyBear::from_u64(10 * j as u64),
            ]
        })
        .collect();
    let main_trace = RowMajorMatrix::new(main_data, 4);

    let main_air = MainAir::<BabyBear>::new(json_content, 4, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    // Only the main AIR — no preprocessed tables needed
    let air_infos: Vec<AirInfo<BabyBear>> = vec![AirInfo::new(air_instance)];

    let lookup_traces = generate_multiplicity_traces::<BabyBear, setup::MyConfig>(
        &air_infos[1..], &main_trace, air_infos[0].preprocessed.as_ref(), &air_infos[0].lookups, &air_infos[0].lookup_row_scopes,
    );
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis)
        .expect("send direction permutation check verification failed");
}

/// Test that a misbalanced Send/Receive pair is rejected.
/// Same setup as test_main_air_send_direction, but the Receive side has one
/// entry replaced so the multisets don't match. Plonky3 detects the
/// imbalance during proving and panics.
#[test]
#[should_panic(expected = "Lookup mismatch")]
fn test_send_receive_misbalance_fails() {
    let config = setup::test_config(55);

    let json_content = r#"[
      {
        "type": "EveryRow",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "MemTable",
                "entry": [
                  { "type": "var", "index": 0 },
                  { "type": "var", "index": 1 }
                ],
                "direction": "send"
              }
            },
            {
              "lookup": {
                "table": "MemTable",
                "entry": [
                  { "type": "var", "index": 2 },
                  { "type": "var", "index": 3 }
                ],
                "direction": "receive"
              }
            }
          ],
          "assignment": {
            "vars": [
              { "row": 0, "column": 0 },
              { "row": 0, "column": 1 },
              { "row": 0, "column": 2 },
              { "row": 0, "column": 3 }
            ],
            "offset": 4,
            "aux_length": 0
          }
        }
      }
    ]"#;

    // Main trace: 16 rows × 4 columns.
    // Send side: (i, 10*i) as before.
    // Receive side: (15-i, 10*(15-i)) EXCEPT row 0 which has (999, 9990)
    // instead of (15, 150). This breaks the permutation.
    let num_rows = 16usize;
    let main_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i| {
            let (recv_a, recv_b) = if i == 0 {
                (999, 9990) // misbalanced entry
            } else {
                let j = num_rows - 1 - i;
                (j, 10 * j)
            };
            vec![
                BabyBear::from_u64(i as u64),
                BabyBear::from_u64(10 * i as u64),
                BabyBear::from_u64(recv_a as u64),
                BabyBear::from_u64(recv_b as u64),
            ]
        })
        .collect();
    let main_trace = RowMajorMatrix::new(main_data, 4);

    let main_air = MainAir::<BabyBear>::new(json_content, 4, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![AirInfo::new(air_instance)];

    let lookup_traces = generate_multiplicity_traces::<BabyBear, setup::MyConfig>(
        &air_infos[1..], &main_trace, air_infos[0].preprocessed.as_ref(), &air_infos[0].lookups, &air_infos[0].lookup_row_scopes,
    );
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![];
    let _proof = prove(&config, &air_infos, &traces, &pis);
}

/// Test a 16-entry range-check table to demonstrate the generic lookup framework
/// works with arbitrary table names and sizes.
#[test]
fn test_range_check_16() {
    let _ = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(tracing::Level::INFO)
        .try_init();

    let config = setup::test_config(42);

    // Minimal JSON: an EveryRow op with a lookup of column 0 into "Range16".
    // No arithmetic constraints -- only the lookup.
    let json_content = r#"[
      {
        "type": "EveryRow",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "Range16",
                "entry": [{ "type": "var", "index": 0 }],
                "direction": "receive"
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

    let main_air = MainAir::<BabyBear>::new(json_content, width, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    // Create a 16-entry preprocessed table (values 0..15)
    let range16_data: Vec<BabyBear> = (0..16).map(|i| BabyBear::from_u64(i as u64)).collect();
    let range16_preprocessed = RowMajorMatrix::new(range16_data, 1);
    let range16_air = PreprocessedTableAir::new("Range16".into(), range16_preprocessed);
    let range16_instance = CleanAirInstance::Preprocessed(range16_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(range16_instance),
    ];

    let lookup_traces =
        generate_multiplicity_traces::<BabyBear, setup::MyConfig>(&air_infos[1..], &main_trace, air_infos[0].preprocessed.as_ref(), &air_infos[0].lookups, &air_infos[0].lookup_row_scopes);
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    // Public values: [0, 1, 1] (matching the default public_values in LookupBuilder)
    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("range-check-16 verification failed");
}

/// End-to-end test: export circuit from Lean, generate trace from Lean, prove and verify.
///
/// Both the circuit (constraints + lookups) and the execution trace are produced
/// by Lean, so this test exercises the full pipeline from Lean definitions down
/// to a verified STARK proof in the Rust backend.
#[test]
fn test_lean_circuit_end_to_end() {
    let _ = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(tracing::Level::INFO)
        .try_init();

    let config = setup::test_config(1);

    // --- Generate circuit JSON from Lean ---
    let backend_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = backend_dir.join("tests").join("fixtures");
    std::fs::create_dir_all(tests_dir.join("output")).unwrap();

    let circuit_output = Command::new("bash")
        .arg(tests_dir.join("generate_fib_circuit.sh"))
        .arg("output/e2e_circuit.json")
        .current_dir(&tests_dir)
        .output()
        .expect("Failed to run circuit generation script");
    assert!(
        circuit_output.status.success(),
        "Circuit generation failed: {}",
        String::from_utf8_lossy(&circuit_output.stderr)
    );
    let circuit_json = std::fs::read_to_string(tests_dir.join("output/e2e_circuit.json"))
        .expect("Failed to read generated circuit JSON");

    // --- Generate trace from Lean ---
    let steps = 512;
    let init_trace = generate_trace_from_lean::<BabyBear>(steps, "e2e_trace.json")
        .expect("Failed to generate trace from Lean");

    let width = init_trace[0].len();
    let main_trace: RowMajorMatrix<BabyBear> =
        RowMajorMatrix::new(init_trace.iter().flatten().cloned().collect(), width);

    // --- Build AIR instances from Lean-generated circuit ---
    let main_air = MainAir::<BabyBear>::new(&circuit_json, main_trace.width(), main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    let byte_range = byte_range_air::<BabyBear>();
    let byte_range_instance = CleanAirInstance::Preprocessed(byte_range);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(byte_range_instance),
    ];

    // --- Prove and verify ---
    let lookup_traces = generate_multiplicity_traces::<BabyBear, setup::MyConfig>(
        &air_infos[1..],
        &main_trace,
        air_infos[0].preprocessed.as_ref(),
        &air_infos[0].lookups,
        &air_infos[0].lookup_row_scopes,
    );
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    // The Lean circuit hardcodes initial Fibonacci values as constants (not public inputs),
    // so no public inputs are needed for constraint satisfaction.
    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis)
        .expect("Lean end-to-end verification failed");
}

/// Test two independent lookup tables to exercise multi-table challenge slicing.
///
/// This is the only test with `num_global_lookups = 2`, so it exercises:
/// - `num_perm_challenges = gadget.num_challenges() * 2 = 4`
/// - `challenges_for_air` returning `[0..2]` for the first table, `[2..4]` for the second
/// - Multiplicity trace generation for 2 independent tables
/// - Permutation trace with 2 auxiliary columns on the main AIR
/// - Global cumulative sum check across 3 AIRs (1 main + 2 tables)
#[test]
fn test_two_table_lookups() {
    let _ = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(tracing::Level::INFO)
        .try_init();

    let config = setup::test_config(200);

    // Circuit JSON: two lookups in one EveryRow gate.
    // col 0 looked up in "Range8", col 1 looked up in "Squares".
    let json_content = r#"[
      {
        "type": "EveryRow",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "Range8",
                "entry": [{ "type": "var", "index": 0 }],
                "direction": "receive"
              }
            },
            {
              "lookup": {
                "table": "Squares",
                "entry": [{ "type": "var", "index": 1 }],
                "direction": "receive"
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

    // Main trace: 8 rows × 2 columns.
    // col 0 = i  (looked up in Range8)
    // col 1 = i² (looked up in Squares)
    let num_rows = 8;
    let main_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i: u64| vec![BabyBear::from_u64(i), BabyBear::from_u64(i * i)])
        .collect();
    let main_trace = RowMajorMatrix::new(main_data, 2);

    let main_air = MainAir::<BabyBear>::new(json_content, 2, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    // "Range8" table: 8 rows × 1 column, values [0..7]
    let range8_data: Vec<BabyBear> = (0..8).map(|i| BabyBear::from_u64(i as u64)).collect();
    let range8_preprocessed = RowMajorMatrix::new(range8_data, 1);
    let range8_air = PreprocessedTableAir::new("Range8".into(), range8_preprocessed);
    let range8_instance = CleanAirInstance::Preprocessed(range8_air);

    // "Squares" table: 8 rows × 1 column, values [0, 1, 4, 9, 16, 25, 36, 49]
    let squares_data: Vec<BabyBear> = (0..8)
        .map(|i: u64| BabyBear::from_u64(i * i))
        .collect();
    let squares_preprocessed = RowMajorMatrix::new(squares_data, 1);
    let squares_air = PreprocessedTableAir::new("Squares".into(), squares_preprocessed);
    let squares_instance = CleanAirInstance::Preprocessed(squares_air);

    // 3 AIR instances: main + Range8 + Squares
    // BTreeMap ordering in MainAir::build_lookups() sorts by table name alphabetically:
    // "Range8" (index 0) before "Squares" (index 1).
    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(range8_instance),
        AirInfo::new(squares_instance),
    ];

    let lookup_traces =
        generate_multiplicity_traces::<BabyBear, setup::MyConfig>(&air_infos[1..], &main_trace, air_infos[0].preprocessed.as_ref(), &air_infos[0].lookups, &air_infos[0].lookup_row_scopes);
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("two-table lookup verification failed");
}

/// Test that lookups inside `EveryRowExceptLast` skip the last row.
///
/// The last row contains a value (999) absent from the byte-range table.
/// Under correct `EveryRowExceptLast` semantics the lookup should not apply
/// on the last row, so this should succeed.
#[test]
fn test_lookup_skips_last_row() {
    let _ = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(tracing::Level::INFO)
        .try_init();

    let config = setup::test_config(333);

    // Circuit JSON: EveryRowExceptLast with a single lookup of column 0 into "Bytes".
    let json_content = r#"[
      {
        "type": "EveryRowExceptLast",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "Bytes",
                "entry": [{ "type": "var", "index": 0 }],
                "direction": "receive"
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

    // Main trace: 8 rows × 1 column.
    // Rows 0–6: valid byte values (0..6), present in the byte table.
    // Row 7 (last): 999, NOT in the byte table.
    let mut main_data: Vec<BabyBear> = (0u64..7).map(|i| BabyBear::from_u64(i)).collect();
    main_data.push(BabyBear::from_u64(999));
    let main_trace = RowMajorMatrix::new(main_data, 1);

    let main_air = MainAir::<BabyBear>::new(json_content, 1, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    // Reuse the 256-entry byte-range preprocessed table (values 0..255).
    let byte_range = byte_range_air::<BabyBear>();
    let byte_range_instance = CleanAirInstance::Preprocessed(byte_range);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(byte_range_instance),
    ];

    // This will panic on buggy code that iterates all rows.
    // Once fixed, the lookup should skip the last row and succeed.
    let lookup_traces = generate_multiplicity_traces::<BabyBear, setup::MyConfig>(
        &air_infos[1..],
        &main_trace,
        air_infos[0].preprocessed.as_ref(),
        &air_infos[0].lookups,
        &air_infos[0].lookup_row_scopes,
    );
    let mut traces = vec![main_trace];
    traces.extend(lookup_traces);

    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis)
        .expect("EveryRowExceptLast lookup should skip last row");
}
