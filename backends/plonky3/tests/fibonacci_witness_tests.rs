extern crate alloc;

mod common;

mod generated {
    include!("generated/fibonacci_witness.rs");
}

use clean_backend::StarkGenericConfig;
use common::setup;
use p3_baby_bear::BabyBear;
use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_strict_usize;

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
    let public_values = vec![field(32), field(5), field(226)];
    let witness =
        generated::generate(&public_values).expect("extracted Rust witness generation failed");

    let mut tables = witness.tables;
    tables[2].resize(32, vec![BabyBear::ZERO; 256]);
    let mut traces = vec![RowMajorMatrix::new(vec![BabyBear::ZERO; 32], 1)];
    traces.extend(tables.into_iter().map(|rows| {
        let width = rows[0].len();
        RowMajorMatrix::new(rows.into_iter().flatten().collect(), width)
    }));
    assert_eq!(
        traces.iter().map(Matrix::height).collect::<Vec<_>>(),
        vec![32, 32, 32, 32]
    );

    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let airs = generated::FibonacciWitnessProgramAir::all(&trace_heights);
    let log_degrees = traces
        .iter()
        .map(|trace| log2_strict_usize(trace.height()) + config.is_zk())
        .collect::<Vec<_>>();
    let mut prover_airs = airs.clone();
    let prover_data = ProverData::from_airs_and_degrees(&config, &mut prover_airs, &log_degrees);
    let instances = airs
        .iter()
        .zip(traces)
        .zip(prover_data.common.lookups.iter())
        .map(|((air, trace), lookups)| StarkInstance {
            air,
            trace,
            public_values: public_values.clone(),
            lookups: lookups.clone(),
        })
        .collect::<Vec<_>>();

    let proof = prove_batch(&config, &instances, &prover_data);
    let per_air_public_values = airs
        .iter()
        .map(|_| public_values.clone())
        .collect::<Vec<_>>();
    verify_batch(
        &config,
        &airs,
        &proof,
        &per_air_public_values,
        &prover_data.common,
    )
    .expect("extracted Fibonacci AIR proof failed verification");
}
