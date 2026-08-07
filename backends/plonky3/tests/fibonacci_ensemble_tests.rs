extern crate alloc;

mod common;

mod generated {
    include!("generated/fibonacci_ensemble.rs");
}

use clean_backend::witness_generation::{
    self, DataSchema, Interaction, Mode, Padding, Program, WitnessData, WitnessField,
};
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleShapeError, EnsembleVerificationError,
};
use common::setup;
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Matrix;
use std::time::Instant;

fn field(value: u64) -> BabyBear {
    BabyBear::from_u64(value)
}

#[test]
fn extracted_rust_generates_fibonacci_ensemble_witness() {
    let witness = generated::generate(&[field(32), field(5), field(226)])
        .expect("extracted Rust witness generation failed");

    assert_eq!(
        witness.tables.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![32, 32, 256]
    );
    let bytes = witness.tables[2]
        .iter()
        .map(|row| row[1])
        .collect::<Vec<_>>();
    assert_eq!(
        bytes
            .iter()
            .map(|value| value.as_canonical_u64())
            .sum::<u64>(),
        32
    );
    assert_eq!(
        bytes.iter().map(|value| value.as_canonical_u64()).max(),
        Some(2)
    );
}

#[test]
fn extracted_rust_coalesces_repeated_chip_pulls() {
    let witness = generated::generate(&[field(400), field(219), field(61)])
        .expect("extracted Rust witness generation failed");

    assert_eq!(
        witness.tables.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![512, 512, 256]
    );
}

#[test]
fn extracted_fibonacci_air_proves_and_verifies() {
    let config = setup::test_config(7);
    let public_values = vec![field(4096), field(59), field(29)];
    let witness_started = Instant::now();
    let witness =
        generated::generate(&public_values).expect("extracted Rust witness generation failed");

    let traces = witness.into_traces().expect("invalid extracted traces");
    assert_eq!(
        traces.iter().map(Matrix::height).collect::<Vec<_>>(),
        vec![4096, 512, 256]
    );
    assert_eq!(
        traces.iter().map(Matrix::width).collect::<Vec<_>>(),
        vec![5, 5, 1]
    );

    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let airs = generated::FibonacciEnsembleProgramAir::all(&trace_heights)
        .expect("invalid generated AIR shape");
    let witness_elapsed = witness_started.elapsed();
    let proving_started = Instant::now();
    let (proof, _) =
        prove_ensemble(&config, &airs, traces, &public_values).expect("invalid proving shape");
    let proving_elapsed = proving_started.elapsed();
    let proof_json_bytes = serde_json::to_vec(&proof)
        .expect("proof serialization failed")
        .len();
    let verification_started = Instant::now();
    verify_ensemble(&config, &airs, &proof, &public_values)
        .expect("extracted Fibonacci AIR proof failed verification");
    eprintln!(
        "4096 steps: witness+padding={witness_elapsed:?}, proving={proving_elapsed:?}, verification={:?}, proof_json={proof_json_bytes} bytes",
        verification_started.elapsed()
    );
}

#[test]
fn ensemble_api_reports_shape_errors() {
    let config = setup::test_config(7);
    let public_values = vec![field(32), field(5), field(226)];
    let witness =
        generated::generate(&public_values).expect("extracted Rust witness generation failed");
    let traces = witness.into_traces().expect("invalid extracted traces");
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let airs = generated::FibonacciEnsembleProgramAir::all(&trace_heights)
        .expect("invalid generated AIR shape");
    let mut traces = traces;
    traces.pop();

    assert!(matches!(
        prove_ensemble(&config, &airs, traces, &public_values),
        Err(EnsembleShapeError::TraceCount { airs: 3, traces: 2 })
    ));
    assert!(matches!(
        generated::FibonacciEnsembleProgramAir::all(&trace_heights[..2]),
        Err(EnsembleShapeError::ComponentCount {
            expected: 3,
            trace_heights: 2,
        })
    ));
    let mut wrong_fixed_height = trace_heights.clone();
    wrong_fixed_height[2] = 128;
    assert!(matches!(
        generated::FibonacciEnsembleProgramAir::all(&wrong_fixed_height),
        Err(EnsembleShapeError::FixedTraceHeight {
            component: 2,
            expected: 256,
            actual: 128,
        })
    ));
}

struct Minimum64Program;

impl<F: WitnessField> Program<F> for Minimum64Program {
    const FUEL: usize = <generated::FibonacciEnsembleProgram as Program<F>>::FUEL;
    const COMPONENTS: usize = <generated::FibonacciEnsembleProgram as Program<F>>::COMPONENTS;
    const FIXED_WIDTHS: &'static [usize] =
        <generated::FibonacciEnsembleProgram as Program<F>>::FIXED_WIDTHS;

    fn data_schemas() -> Vec<DataSchema> {
        <generated::FibonacciEnsembleProgram as Program<F>>::data_schemas()
    }

    fn modes() -> Vec<Mode<F>> {
        generated::FibonacciEnsembleProgram::modes()
    }

    fn padding() -> Vec<Padding<F>> {
        generated::FibonacciEnsembleProgram::padding()
            .into_iter()
            .map(|padding| Padding {
                minimum_rows: 64,
                ..padding
            })
            .collect()
    }

    fn complete_row(
        component: usize,
        input: &[F],
        data: &WitnessData<F>,
    ) -> Result<Vec<F>, String> {
        generated::FibonacciEnsembleProgram::complete_row(component, input, data)
    }

    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>> {
        generated::FibonacciEnsembleProgram::interactions(component, row)
    }

    fn verifier_interactions(public_input: &[F]) -> Vec<Interaction<F>> {
        generated::FibonacciEnsembleProgram::verifier_interactions(public_input)
    }
}

#[test]
fn verifier_rejects_a_valid_proof_at_the_wrong_height() {
    let config = setup::test_config(11);
    let public_values = vec![field(32), field(5), field(226)];
    let expected =
        generated::generate(&public_values).expect("extracted Rust witness generation failed");
    let wrong = witness_generation::generate::<BabyBear, Minimum64Program>(&public_values)
        .expect("wrong-height witness generation failed");

    let wrong_traces = wrong.into_traces().expect("invalid wrong-height traces");
    let wrong_heights = wrong_traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let wrong_airs = generated::FibonacciEnsembleProgramAir::all(&wrong_heights)
        .expect("invalid wrong-height AIR shape");
    let (wrong_proof, _) = prove_ensemble(&config, &wrong_airs, wrong_traces, &public_values)
        .expect("invalid wrong-height proving shape");
    verify_ensemble(&config, &wrong_airs, &wrong_proof, &public_values)
        .expect("the wrong-height proof must be otherwise valid");
    let altered_public_values = vec![field(32), field(6), field(226)];
    assert!(matches!(
        verify_ensemble(&config, &wrong_airs, &wrong_proof, &altered_public_values),
        Err(EnsembleVerificationError::Proof(_))
    ));

    let expected_traces = expected.into_traces().expect("invalid expected traces");
    let expected_heights = expected_traces
        .iter()
        .map(Matrix::height)
        .collect::<Vec<_>>();
    let expected_airs = generated::FibonacciEnsembleProgramAir::all(&expected_heights)
        .expect("invalid expected AIR shape");
    assert!(matches!(
        verify_ensemble(&config, &expected_airs, &wrong_proof, &public_values),
        Err(EnsembleVerificationError::Shape(
            EnsembleShapeError::ProofDegreeBits { .. }
        ))
    ));
}
