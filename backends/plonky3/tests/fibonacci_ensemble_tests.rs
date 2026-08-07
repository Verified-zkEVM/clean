extern crate alloc;

mod common;

mod generated {
    include!("generated/fibonacci_ensemble.rs");
}

use clean_backend::witness_generation::pad;
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
        vec![32, 32, 1]
    );
    let bytes = &witness.tables[2][0];
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
        vec![400, 384, 1]
    );
}

#[test]
fn extracted_fibonacci_air_proves_and_verifies() {
    let config = setup::test_config(7);
    let public_values = vec![field(4096), field(59), field(29)];
    let witness_started = Instant::now();
    let witness =
        generated::generate(&public_values).expect("extracted Rust witness generation failed");

    let padded = pad::<BabyBear, generated::FibonacciEnsembleProgram>(witness, 32)
        .expect("failed to pad extracted witness");
    let traces = padded.traces;
    assert_eq!(
        traces.iter().map(Matrix::height).collect::<Vec<_>>(),
        vec![32, 4096, 512, 32]
    );

    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let airs = generated::FibonacciEnsembleProgramAir::all(&trace_heights, &padded.active_rows)
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
    let padded = pad::<BabyBear, generated::FibonacciEnsembleProgram>(witness, 32)
        .expect("failed to pad extracted witness");
    let trace_heights = padded.traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let airs = generated::FibonacciEnsembleProgramAir::all(&trace_heights, &padded.active_rows)
        .expect("invalid generated AIR shape");
    let mut traces = padded.traces;
    traces.pop();

    assert!(matches!(
        prove_ensemble(&config, &airs, traces, &public_values),
        Err(EnsembleShapeError::TraceCount { airs: 4, traces: 3 })
    ));
    assert!(matches!(
        generated::FibonacciEnsembleProgramAir::all(&trace_heights[..3], &padded.active_rows),
        Err(EnsembleShapeError::ComponentCount {
            expected: 4,
            trace_heights: 3,
            active_rows: 4
        })
    ));
}

#[test]
fn verifier_rejects_a_valid_proof_at_the_wrong_height() {
    let config = setup::test_config(11);
    let public_values = vec![field(32), field(5), field(226)];
    let witness =
        generated::generate(&public_values).expect("extracted Rust witness generation failed");
    let expected = pad::<BabyBear, generated::FibonacciEnsembleProgram>(witness.clone(), 32)
        .expect("failed to pad expected witness");
    let wrong = pad::<BabyBear, generated::FibonacciEnsembleProgram>(witness, 64)
        .expect("failed to pad wrong-height witness");

    let wrong_heights = wrong.traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let wrong_airs =
        generated::FibonacciEnsembleProgramAir::all(&wrong_heights, &wrong.active_rows)
            .expect("invalid wrong-height AIR shape");
    let (wrong_proof, _) = prove_ensemble(&config, &wrong_airs, wrong.traces, &public_values)
        .expect("invalid wrong-height proving shape");
    verify_ensemble(&config, &wrong_airs, &wrong_proof, &public_values)
        .expect("the wrong-height proof must be otherwise valid");
    let altered_public_values = vec![field(32), field(6), field(226)];
    assert!(matches!(
        verify_ensemble(&config, &wrong_airs, &wrong_proof, &altered_public_values),
        Err(EnsembleVerificationError::Proof(_))
    ));

    let expected_heights = expected
        .traces
        .iter()
        .map(Matrix::height)
        .collect::<Vec<_>>();
    let expected_airs =
        generated::FibonacciEnsembleProgramAir::all(&expected_heights, &expected.active_rows)
            .expect("invalid expected AIR shape");
    assert!(matches!(
        verify_ensemble(&config, &expected_airs, &wrong_proof, &public_values),
        Err(EnsembleVerificationError::Shape(
            EnsembleShapeError::ProofDegreeBits { .. }
        ))
    ));
}
