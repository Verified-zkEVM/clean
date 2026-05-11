use clean_backend::{
    generate_table_traces, parse_table_json, parse_trace_matrix, prove, verify, AirInfo,
    CleanAirInstance, MainAir, PreprocessedTableAir, ProverTableAir,
};
use p3_baby_bear::BabyBear;
use p3_matrix::Matrix;

use crate::common::setup;
use crate::lean_runner::run_lean_script;

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

pub fn prove_and_verify_from_json(circuit_json_str: &str, trace_json_str: &str) {
    let config = setup::test_config(500);

    let circuit_value: serde_json::Value =
        serde_json::from_str(circuit_json_str).expect("Failed to parse circuit JSON");
    let constraints = circuit_value["constraints"].clone();
    let num_columns = circuit_value["num_columns"].as_u64().unwrap() as usize;
    let trace_height = circuit_value["trace_height"].as_u64().unwrap() as usize;
    let preprocessed_tables = &circuit_value["preprocessed_tables"];

    let program_air: PreprocessedTableAir<BabyBear> =
        PreprocessedTableAir::from_json("program".into(), &preprocessed_tables["program"]);

    let prover_tables_meta = &circuit_value["prover_tables"];
    let mem_width = prover_tables_meta["memory"]["width"].as_u64().unwrap() as usize;
    let mem_height = prover_tables_meta["memory"]["height"].as_u64().unwrap() as usize;
    let mem_air = ProverTableAir::<BabyBear>::new("memory".into(), mem_width);

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
    assert_eq!(
        main_trace.height(),
        trace_height,
        "Trace height {} doesn't match circuit trace_height {}",
        main_trace.height(),
        trace_height
    );

    let prover_tables = &trace_value["prover_tables"];
    let mem_data_matrix = parse_table_json::<BabyBear>(&prover_tables["memory"]);

    assert_eq!(
        mem_data_matrix.height(),
        mem_height,
        "Memory table height {} doesn't match circuit mem_height {}",
        mem_data_matrix.height(),
        mem_height
    );

    let main_air_instance = MainAir::<BabyBear>::from_value(
        constraints,
        num_columns,
        trace_height,
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
