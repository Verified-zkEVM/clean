mod common;

use clean_backend::{
    byte_range_air, generate_table_traces, prove, verify, AirInfo,
    CleanAirInstance, MainAir,
};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use common::setup;

const JSON_PATH: &str = "clean_fib.json";

/// test fibonacci8 exported from clean
#[test]
fn test_clean_fib() {
    let config = setup::test_config(1);

    let steps = 512;
    let trace_rows = match common::generate_trace_from_lean::<BabyBear>(steps, "trace.json") {
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

    let width = trace_rows[0].len();

    let main_trace: RowMajorMatrix<BabyBear> =
        RowMajorMatrix::new(trace_rows.iter().flatten().cloned().collect(), width);

    // Get the result
    let x = main_trace.get(main_trace.height() - 1, 1).unwrap();

    // Read the JSON file content
    let json_content = common::read_test_json(JSON_PATH);

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

    // Generate table traces using the AirInfo instances from the VK
    let table_traces = generate_table_traces::<BabyBear, setup::MyConfig>(
        &air_infos, &main_trace, &[],
    );
    // Collect all traces: main trace + table traces
    let mut traces = vec![main_trace.clone()];
    traces.extend(table_traces);

    let pis = vec![BabyBear::ZERO, BabyBear::ONE, x];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("verification failed");
}

/// End-to-end test: export circuit from Lean, generate trace from Lean, prove and verify.
///
/// Both the circuit (constraints + lookups) and the execution trace are produced
/// by Lean, so this test exercises the full pipeline from Lean definitions down
/// to a verified STARK proof in the Rust backend.
#[test]
fn test_lean_circuit_end_to_end() {
    let config = setup::test_config(1);

    // --- Generate circuit JSON from Lean ---
    let circuit_json = common::run_lean_script(
        "FibCircuitGen.lean",
        &[],
        "output/e2e_circuit.json",
    );

    // --- Generate trace from Lean ---
    let steps = 512;
    let trace_rows = common::generate_trace_from_lean::<BabyBear>(steps, "e2e_trace.json")
        .expect("Failed to generate trace from Lean");

    let width = trace_rows[0].len();
    let main_trace: RowMajorMatrix<BabyBear> =
        RowMajorMatrix::new(trace_rows.iter().flatten().cloned().collect(), width);

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
    let table_traces = generate_table_traces::<BabyBear, setup::MyConfig>(
        &air_infos, &main_trace, &[],
    );
    let mut traces = vec![main_trace];
    traces.extend(table_traces);

    // The Lean circuit hardcodes initial Fibonacci values as constants (not public inputs),
    // so no public inputs are needed for constraint satisfaction.
    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis)
        .expect("Lean end-to-end verification failed");
}
