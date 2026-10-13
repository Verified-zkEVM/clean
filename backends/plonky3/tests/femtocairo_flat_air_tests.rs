extern crate alloc;

mod common;

#[allow(dead_code, unused_parens)]
mod generated {
    include!("generated/femtocairo_flat_air.rs");
}

use clean_backend::witness_generation::{Interaction, WitnessData, WitnessField};
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleVerificationError, GeneratedAirSpec,
    GeneratedEnsemble, GeneratedLookup,
};
use common::setup;
use p3_air::{AirBuilderWithPublicValues, SymbolicVariable};
use p3_baby_bear::BabyBear;
use p3_field::Field;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Matrix;

fn field(value: u64) -> BabyBear {
    BabyBear::from_u64(value)
}

/// The prover's memory values, supplied to witness generation as the `memoryValues` hint table.
/// Memory reads propose them for the cells they define.
fn memory(values: [u64; 8]) -> WitnessData<BabyBear> {
    WitnessData::from_entries(vec![(
        "memoryValues",
        values.into_iter().map(|value| vec![field(value)]).collect(),
    )])
}

#[test]
fn extracted_femtocairo_witness_uses_committed_memory_data() {
    let hint = memory([0, 5, 3, 7, 2, 10, 0, 0]);
    let witness = generated::generate(&[field(0), field(0)], &hint)
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
fn extracted_femtocairo_memory_is_defined_by_reads() {
    let public_values = vec![field(0), field(0)];
    let first = memory([0, 5, 3, 7, 2, 10, 0, 0]);
    let second = memory([0, 5, 3, 7, 2, 10, 0, 99]);

    let first_witness = generated::generate(&public_values, &first)
        .expect("first runtime memory should generate a witness");
    let second_witness = generated::generate(&public_values, &second)
        .expect("second runtime memory should generate a witness");
    // The program never reads address 7, so its hinted value does not enter the witness.
    assert_eq!(first_witness.tables[1][7][1], field(0));
    assert_eq!(second_witness.tables[1][7][1], field(0));

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
fn extracted_femtocairo_air_proves_and_verifies() {
    let config = setup::test_config(7);
    let public_values = vec![field(0), field(0)];
    let hint = memory([0, 5, 3, 7, 2, 10, 0, 0]);
    let witness = generated::generate(&public_values, &hint)
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

type Spec = generated::FemtoCairoFlatAirProgramAirSpec;

const MEMORY: usize = 1;

/// The FemtoCairo statement with rows 1 and 2 of the memory address table swapped.
#[derive(Clone, Debug)]
struct PermutedMemoryAddresses;

impl GeneratedAirSpec for PermutedMemoryAddresses {
    const FIELD_ORDER: u64 = Spec::FIELD_ORDER;
    const PUBLIC_VALUES: usize = Spec::PUBLIC_VALUES;
    const WIDTHS: &'static [usize] = Spec::WIDTHS;
    const FIXED_WIDTHS: &'static [usize] = Spec::FIXED_WIDTHS;
    const FIXED_HEIGHTS: &'static [usize] = Spec::FIXED_HEIGHTS;
    const INTERACTIONS_PER_ROW: &'static [usize] = Spec::INTERACTIONS_PER_ROW;
    const VERIFIER_INTERACTIONS: usize = Spec::VERIFIER_INTERACTIONS;

    fn fixed_row<F: WitnessField>(component: usize, row: u64) -> Vec<F> {
        let row = match (component, row) {
            (MEMORY, 1) => 2,
            (MEMORY, 2) => 1,
            _ => row,
        };
        Spec::fixed_row(component, row)
    }

    fn constraints<AB>(component: usize, fixed: &[AB::Var], local: &[AB::Var]) -> Vec<AB::Expr>
    where
        AB: AirBuilderWithPublicValues,
        AB::F: Field + PrimeCharacteristicRing,
    {
        Spec::constraints::<AB>(component, fixed, local)
    }

    fn lookups<F: Field>(
        component: usize,
        fixed: &[SymbolicVariable<F>],
        local: &[SymbolicVariable<F>],
    ) -> Vec<GeneratedLookup<F>> {
        Spec::lookups(component, fixed, local)
    }

    fn verifier_interactions<F: WitnessField>(public_values: &[F]) -> Vec<Interaction<F>> {
        Spec::verifier_interactions(public_values)
    }
}

/// Memory is indexed: permuting (address, value) rows keeps every channel balanced and every
/// constraint satisfied, but needs a different address table, which the verifier fixes.
#[test]
fn verifier_rejects_permuted_memory() {
    let config = setup::test_config(19);
    let public_values = vec![field(0), field(0)];
    let witness = generated::generate(&public_values, &memory([0, 5, 3, 7, 2, 10, 0, 0]))
        .expect("extracted FemtoCairo witness generation failed");
    let mut traces = witness.into_traces().expect("invalid extracted traces");
    let memory_trace = &mut traces[MEMORY];
    let width = memory_trace.width();
    for column in 0..width {
        memory_trace.values.swap(width + column, 2 * width + column);
    }
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();

    let permuted = GeneratedEnsemble::<BabyBear, PermutedMemoryAddresses>::new(&trace_heights)
        .expect("invalid permuted AIR shape");
    let (proof, _) =
        prove_ensemble(&config, &permuted, traces, &public_values).expect("invalid proving shape");
    verify_ensemble(&config, &permuted, &proof, &public_values)
        .expect("the permuted-memory proof must be valid for the permuted address table");

    let statement = generated::FemtoCairoFlatAirProgramStatement::<BabyBear>::new(&trace_heights)
        .expect("invalid generated AIR shape");
    assert!(matches!(
        verify_ensemble(&config, &statement, &proof, &public_values),
        Err(EnsembleVerificationError::Proof(_))
    ));
}
