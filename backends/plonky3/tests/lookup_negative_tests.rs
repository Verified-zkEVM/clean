mod common;

use clean_backend::{
    generate_table_traces, prove, AirInfo, CleanAirInstance, MainAir, PreprocessedTableAir,
    ProverTableAir,
};
#[cfg(not(debug_assertions))]
use clean_backend::verify;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

use common::setup;

// ---------------------------------------------------------------------------
// Test 1: Tampered preprocessed-table multiplicity (Range16)
// ---------------------------------------------------------------------------

/// Build a Range16 lookup setup (same as `test_range_check_16`), then tamper
/// with the multiplicity trace so that value 0 has one extra phantom "send".
fn build_tampered_preprocessed_setup() -> (
    setup::MyConfig,
    Vec<AirInfo<BabyBear>>,
    Vec<RowMajorMatrix<BabyBear>>,
    Vec<BabyBear>,
) {
    let config = setup::test_config(42);

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

    let num_rows = 16;
    let width = 1;
    let trace_data: Vec<BabyBear> = (0..num_rows)
        .map(|i| BabyBear::from_u64(i as u64))
        .collect();
    let main_trace = RowMajorMatrix::new(trace_data, width);

    let main_air = MainAir::<BabyBear>::new(json_content, width, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    let range16_data: Vec<BabyBear> = (0..16).map(|i| BabyBear::from_u64(i as u64)).collect();
    let range16_preprocessed = RowMajorMatrix::new(range16_data, 1);
    let range16_air = PreprocessedTableAir::new("Range16".into(), range16_preprocessed);
    let range16_instance = CleanAirInstance::Preprocessed(range16_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(range16_instance),
    ];

    let table_traces =
        generate_table_traces::<BabyBear, setup::MyConfig>(&air_infos, &main_trace, &[]);
    let mut traces = vec![main_trace];
    traces.extend(table_traces);

    // Tamper: add 1 to the multiplicity of row 0 in the table trace.
    // traces[1] is the Range16 table trace (width=1, multiplicity only).
    // values[0] = multiplicity for the entry at row 0 (value 0).
    traces[1].values[0] += BabyBear::ONE;

    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::ONE];
    (config, air_infos, traces, pis)
}

/// In debug mode Plonky3's `check_lookups` catches the imbalance and panics.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Lookup mismatch (global lookup 'Range16')")]
fn test_tampered_multiplicity_preprocessed_table_debug() {
    let (config, air_infos, traces, pis) = build_tampered_preprocessed_setup();
    // prove() triggers check_lookups internally in debug mode, which panics.
    let _proof = prove(&config, &air_infos, &traces, &pis);
}

/// In release mode prove() succeeds but verify() must reject.
#[test]
#[cfg(not(debug_assertions))]
fn test_tampered_multiplicity_preprocessed_table_release() {
    let (config, air_infos, traces, pis) = build_tampered_preprocessed_setup();
    let proof = prove(&config, &air_infos, &traces, &pis);
    assert!(
        verify(&config, &air_infos, &proof, &pis).is_err(),
        "verify should reject a tampered preprocessed-table multiplicity"
    );
}

// ---------------------------------------------------------------------------
// Test 2: Tampered prover-table multiplicity (MemTable)
// ---------------------------------------------------------------------------

/// Build a MemTable prover-table lookup setup (same as `test_prover_table_lookup`),
/// then tamper with the multiplicity column so row 0 has one extra phantom "send".
fn build_tampered_prover_table_setup() -> (
    setup::MyConfig,
    Vec<AirInfo<BabyBear>>,
    Vec<RowMajorMatrix<BabyBear>>,
    Vec<BabyBear>,
) {
    let config = setup::test_config(444);

    let json_content = r#"[
      {
        "type": "EveryRowExceptLast",
        "context": {
          "circuit": [
            {
              "lookup": {
                "table": "MemTable",
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

    let num_rows = 16usize;

    let main_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i| {
            let val = if i < num_rows - 1 { i } else { 0 };
            vec![
                BabyBear::from_u64(val as u64),
                BabyBear::from_u64(10 * val as u64),
            ]
        })
        .collect();
    let main_trace = RowMajorMatrix::new(main_data, 2);

    let main_air = MainAir::<BabyBear>::new(json_content, 2, main_trace.height());
    let air_instance = CleanAirInstance::Main(main_air);

    let mem_table_air = ProverTableAir::<BabyBear>::new("MemTable".into(), 2);
    let mem_table_instance = CleanAirInstance::ProverTable(mem_table_air);

    let air_infos: Vec<AirInfo<BabyBear>> = vec![
        AirInfo::new(air_instance),
        AirInfo::new(mem_table_instance),
    ];

    let prover_data: Vec<BabyBear> = (0..num_rows)
        .flat_map(|i| {
            vec![
                BabyBear::from_u64(i as u64),
                BabyBear::from_u64(10 * i as u64),
            ]
        })
        .collect();
    let prover_data_matrix = RowMajorMatrix::new(prover_data, 2);

    let table_traces = generate_table_traces::<BabyBear, setup::MyConfig>(
        &air_infos,
        &main_trace,
        &[("MemTable", &prover_data_matrix)],
    );
    let mut traces = vec![main_trace];
    traces.extend(table_traces);

    // Tamper: add 1 to the multiplicity of row 0 in the prover-table trace.
    // traces[1] is the MemTable trace (width=3: 2 data cols + 1 multiplicity col).
    // Row 0 layout in values: [col0, col1, mult] => values[2] is the multiplicity.
    traces[1].values[2] += BabyBear::ONE;

    let pis = vec![];
    (config, air_infos, traces, pis)
}

/// In debug mode Plonky3's `check_lookups` catches the imbalance and panics.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Lookup mismatch (global lookup 'MemTable')")]
fn test_tampered_multiplicity_prover_table_debug() {
    let (config, air_infos, traces, pis) = build_tampered_prover_table_setup();
    let _proof = prove(&config, &air_infos, &traces, &pis);
}

/// In release mode prove() succeeds but verify() must reject.
#[test]
#[cfg(not(debug_assertions))]
fn test_tampered_multiplicity_prover_table_release() {
    let (config, air_infos, traces, pis) = build_tampered_prover_table_setup();
    let proof = prove(&config, &air_infos, &traces, &pis);
    assert!(
        verify(&config, &air_infos, &proof, &pis).is_err(),
        "verify should reject a tampered prover-table multiplicity"
    );
}
