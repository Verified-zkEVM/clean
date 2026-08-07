extern crate alloc;

mod common;

#[allow(dead_code, unused_parens)]
mod generated {
    include!("generated/femtocairo_flat_air.rs");
}

use clean_backend::{prove_ensemble, verify_ensemble};
use common::setup;
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Matrix;

fn field(value: u64) -> BabyBear {
    BabyBear::from_u64(value)
}

#[test]
fn extracted_femtocairo_witness_uses_committed_memory_data() {
    let witness = generated::generate(&[field(32), field(0), field(0)])
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
fn extracted_femtocairo_air_proves_and_verifies() {
    let config = setup::test_config(7);
    let public_values = vec![field(32), field(0), field(0)];
    let witness = generated::generate(&public_values)
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
    let airs = generated::FemtoCairoFlatAirProgramAir::all(&trace_heights)
        .expect("invalid generated AIR shape");
    let (proof, _) =
        prove_ensemble(&config, &airs, traces, &public_values).expect("invalid proving shape");
    verify_ensemble(&config, &airs, &proof, &public_values)
        .expect("extracted FemtoCairo AIR proof failed verification");
}
