extern crate alloc;

mod common;

#[allow(dead_code, unused_parens)]
mod generated {
    include!("generated/femtocairo_flat_air.rs");
}

use clean_backend::witness_generation::WitnessGenerationError;
use clean_backend::{prove_ensemble, verify_ensemble};
use common::setup;
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Matrix;

fn field(value: u64) -> BabyBear {
    BabyBear::from_u64(value)
}

fn memory(values: [u64; 8]) -> Vec<BabyBear> {
    values.into_iter().map(field).collect()
}

#[test]
fn extracted_femtocairo_witness_uses_committed_memory_data() {
    let prover_input = memory([0, 5, 3, 7, 2, 10, 0, 0]);
    let witness = generated::generate(&[field(32), field(0), field(0)], &prover_input)
        .expect("extracted FemtoCairo witness generation failed");

    assert_eq!(
        witness.tables.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![8, 8, 32]
    );
    assert_eq!(witness.tables[1][5][0], field(5));
    assert_eq!(witness.tables[1][5][1], field(10));
    assert!(witness.tables[1][5][2].as_canonical_u64() > 0);
}

#[test]
fn extracted_femtocairo_accepts_runtime_private_memories() {
    let public_values = vec![field(32), field(0), field(0)];
    let first = memory([0, 5, 3, 7, 2, 10, 0, 0]);
    let second = memory([0, 5, 3, 7, 2, 10, 0, 99]);

    let first_witness = generated::generate(&public_values, &first)
        .expect("first runtime memory should generate a witness");
    let second_witness = generated::generate(&public_values, &second)
        .expect("second runtime memory should generate a witness");
    assert_eq!(first_witness.tables[1][7][1], field(0));
    assert_eq!(second_witness.tables[1][7][1], field(99));

    let config = setup::test_config(13);
    let traces = second_witness
        .into_traces()
        .expect("second runtime memory produced invalid traces");
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = generated::FemtoCairoFlatAirProgramStatement::<BabyBear>::new(&trace_heights)
        .expect("invalid generated AIR shape");
    let (proof, _) = prove_ensemble(&config, &statement, traces, &public_values)
        .expect("second runtime memory produced an invalid proving shape");
    verify_ensemble(&config, &statement, &proof, &public_values)
        .expect("proof with the second runtime memory failed verification");
}

#[test]
fn extracted_femtocairo_rejects_malformed_prover_input() {
    let error = generated::generate(&[field(32), field(0), field(0)], &[field(0); 7])
        .expect_err("short private memory should be rejected");
    assert_eq!(
        error,
        WitnessGenerationError::ProverInputWidth {
            expected: 8,
            actual: 7,
        }
    );
}

#[test]
fn extracted_femtocairo_air_proves_and_verifies() {
    let config = setup::test_config(7);
    let public_values = vec![field(32), field(0), field(0)];
    let prover_input = memory([0, 5, 3, 7, 2, 10, 0, 0]);
    let witness = generated::generate(&public_values, &prover_input)
        .expect("extracted FemtoCairo witness generation failed");
    let traces = witness.into_traces().expect("invalid extracted traces");

    assert_eq!(
        traces.iter().map(Matrix::height).collect::<Vec<_>>(),
        vec![8, 8, 32]
    );
    assert_eq!(
        traces.iter().map(Matrix::width).collect::<Vec<_>>(),
        vec![33, 2, 1]
    );

    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = generated::FemtoCairoFlatAirProgramStatement::<BabyBear>::new(&trace_heights)
        .expect("invalid generated AIR shape");
    let (proof, _) =
        prove_ensemble(&config, &statement, traces, &public_values).expect("invalid proving shape");
    verify_ensemble(&config, &statement, &proof, &public_values)
        .expect("extracted FemtoCairo AIR proof failed verification");
}
