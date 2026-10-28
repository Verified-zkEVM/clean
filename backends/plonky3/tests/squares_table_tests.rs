extern crate alloc;

mod common;

mod generated {
    include!("generated/squares_table.rs");
}

use clean_backend::{prove_ensemble, verify_ensemble, EnsembleVerificationError};
use common::setup;
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

const HEIGHT: u64 = 16;

fn field(value: u64) -> BabyBear {
    BabyBear::from_u64(value)
}

/// The committed trace of the table, with its rows `(index, square, last)` starting at `first`.
fn trace(first: u64) -> RowMajorMatrix<BabyBear> {
    let values = (first..first + HEIGHT)
        .flat_map(|index| [index, index * index, u64::from(index + 1 == first + HEIGHT)])
        .map(field)
        .collect();
    RowMajorMatrix::new(values, 3)
}

/// Prove `traces` for the public counter and square, and return whether the proof verifies. The
/// prover checks constraints in debug builds, so proofs of violated constraints exist only in
/// release builds.
fn proves(seed: u64, traces: Vec<RowMajorMatrix<BabyBear>>, public_values: &[BabyBear]) -> bool {
    let config = setup::test_config(seed);
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement =
        generated::Statement::<BabyBear>::new(&trace_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid generated AIR shape");
    let proof =
        prove_ensemble(&config, &statement, traces, public_values).expect("invalid proving shape");
    match verify_ensemble(&config, &statement, &proof, public_values) {
        Ok(()) => true,
        Err(EnsembleVerificationError::Proof(_)) => false,
        Err(error) => panic!("unexpected verification error: {error:?}"),
    }
}

/// The generated rows hold their window cells, the next row's input and the selectors, like the
/// rows Lean generates. The trace commits only the row's own input.
#[test]
fn extracted_rust_generates_squares_with_windows() {
    let witness = generated::generate(&[field(15), field(225)], &[], setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed");
    let rows = witness.tables[0]
        .iter()
        .map(|row| row.iter().map(|value| value.as_canonical_u64()).collect())
        .collect::<Vec<Vec<u64>>>();
    let expected = (0..HEIGHT)
        .map(|index| {
            let next = (index + 1) % HEIGHT;
            let last = u64::from(index + 1 == HEIGHT);
            let next_last = u64::from(next + 1 == HEIGHT);
            vec![
                index,
                index * index,
                last,
                next,
                next * next,
                next_last,
                u64::from(index == 0),
                last,
                1 - last,
            ]
        })
        .collect::<Vec<_>>();
    assert_eq!(rows, expected);
    let traces = witness.into_traces().expect("invalid extracted traces");
    assert_eq!(traces, vec![trace(0)]);
}

/// The transitions are gated by `is_transition`, so the wrap from the last row to the first row is
/// not checked.
#[test]
fn extracted_squares_air_proves_and_verifies() {
    assert!(proves(3, vec![trace(0)], &[field(15), field(225)]));
}

#[test]
fn witness_generation_rejects_a_wrong_square() {
    assert!(
        generated::generate(&[field(15), field(224)], &[], setup::MINIMUM_TRACE_HEIGHT).is_err()
    );
}

/// A table starting at 1 satisfies every transition, and its last row pushes a correct square, but
/// it violates the first-row constraints.
#[cfg(not(debug_assertions))]
#[test]
fn verifier_rejects_a_wrong_first_row() {
    assert!(!proves(5, vec![trace(1)], &[field(16), field(256)]));
}

/// Changing one square breaks the transitions into and out of its row.
#[cfg(not(debug_assertions))]
#[test]
fn verifier_rejects_a_broken_transition() {
    let mut broken = trace(0);
    broken.values[3 * 5 + 1] += BabyBear::ONE;
    assert!(!proves(7, vec![broken], &[field(15), field(225)]));
}

/// Reporting from a row other than the last balances the channel, but violates the last-row and
/// transition constraints.
#[cfg(not(debug_assertions))]
#[test]
fn verifier_rejects_a_report_from_another_row() {
    let mut moved = trace(0);
    moved.values[3 * 15 + 2] = BabyBear::ZERO;
    moved.values[3 * 14 + 2] = BabyBear::ONE;
    assert!(!proves(9, vec![moved], &[field(14), field(196)]));
}
