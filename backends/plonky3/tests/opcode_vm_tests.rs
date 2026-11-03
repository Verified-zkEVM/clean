extern crate alloc;

mod common;

mod generated {
    include!("generated/opcode_vm.rs");
}

use clean_backend::witness_generation::{
    self, DemandMode, HintTable, Interaction, Mode, Program, WitnessData, WitnessField,
};
use common::setup;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

fn field(value: u64) -> BabyBear {
    BabyBear::from_u64(value)
}

/// The program `exampleProgram` takes the initial accumulator 2 to 58.
fn public_values() -> Vec<BabyBear> {
    vec![field(2), field(58)]
}

/// The records `(address, value, time)` that the memory accesses of `exampleProgram` push: the
/// instruction at `pc` accesses the memory at time `pc + 1`.
const ACCESSES: [(usize, u64, usize); 6] = [
    (1, 25, 3),
    (4, 64, 6),
    (1, 25, 7),
    (1, 26, 9),
    (4, 64, 10),
    (1, 26, 12),
];

/// The number of access times, and the number of memory addresses.
const TIMES: usize = 32;
const ADDRESSES: usize = 8;

/// The prover's private input: for every time, the value and time of the record that the access
/// at this time pulls, followed by the value and time of the last record of every address.
fn prover_input() -> Vec<BabyBear> {
    let mut previous = vec![(0, 0); TIMES];
    let mut current = vec![(0, 0); ADDRESSES];
    for (address, value, time) in ACCESSES {
        previous[time] = current[address];
        current[address] = (value, time as u64);
    }
    previous
        .into_iter()
        .chain(current)
        .flat_map(|(value, time)| [field(value), field(time)])
        .collect()
}

#[test]
fn extracted_rust_routes_states_by_opcode() {
    let witness = generated::generate(
        &public_values(),
        &prover_input(),
        setup::MINIMUM_TRACE_HEIGHT,
    )
    .expect("extracted Rust witness generation failed");

    // five `add` steps, padded to eight rows, three steps of each of `mul`, `load` and `store`,
    // padded to the minimum height, the memory table, the range table of times, and the program
    assert_eq!(
        witness.tables.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![
            8,
            setup::MINIMUM_TRACE_HEIGHT,
            setup::MINIMUM_TRACE_HEIGHT,
            setup::MINIMUM_TRACE_HEIGHT,
            ADDRESSES,
            TIMES,
            16
        ]
    );
}

#[test]
fn extracted_rust_rejects_a_wrong_final_state() {
    let error = generated::generate(
        &[field(2), field(59)],
        &prover_input(),
        setup::MINIMUM_TRACE_HEIGHT,
    )
    .expect_err("witness generation for a wrong final state succeeded");
    assert!(error.to_string().contains("unhandled channel imbalance"));
}

#[test]
fn extracted_opcode_vm_proves_and_verifies() {
    let mut key = setup::test_key(7);
    let public_values = public_values();
    let witness = generated::generate(&public_values, &prover_input(), setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed");
    let traces = witness.into_traces().expect("invalid extracted traces");
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement =
        generated::Statement::<BabyBear>::new(&trace_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid generated AIR shape");
    let proof = key
        .prove(&statement, traces, &public_values)
        .expect("invalid proving shape");
    key.verify(&statement, &proof, &public_values)
        .expect("extracted opcode VM proof failed verification");
}

/// The extracted program, but without guards, so that both opcode tables accept every state.
struct UnguardedProgram;

impl<F: WitnessField> Program<F> for UnguardedProgram {
    const FIELD_ORDER: u64 = <generated::Ensemble as Program<F>>::FIELD_ORDER;
    const FUEL: usize = <generated::Ensemble as Program<F>>::FUEL;
    const COMPONENTS: usize = <generated::Ensemble as Program<F>>::COMPONENTS;
    const PUBLIC_INPUTS: usize = <generated::Ensemble as Program<F>>::PUBLIC_INPUTS;
    const PROVER_INPUTS: usize = <generated::Ensemble as Program<F>>::PROVER_INPUTS;
    const HINT_TABLES: &'static [HintTable] = <generated::Ensemble as Program<F>>::HINT_TABLES;
    const ROW_WIDTHS: &'static [usize] = <generated::Ensemble as Program<F>>::ROW_WIDTHS;
    const FIXED_COLUMNS: &'static [&'static [usize]] =
        <generated::Ensemble as Program<F>>::FIXED_COLUMNS;
    const COMPONENT_NAMES: &'static [&'static str] =
        <generated::Ensemble as Program<F>>::COMPONENT_NAMES;

    fn modes() -> Vec<Mode<F>> {
        generated::Ensemble::modes()
            .into_iter()
            .map(|mode| match mode {
                Mode::Demand(mode) => Mode::Demand(DemandMode {
                    guard: |_, _, _| true,
                    ..mode
                }),
                mode => mode,
            })
            .collect()
    }

    fn initial_row(component: usize, row: u64, hint: &WitnessData<F>) -> Vec<F> {
        generated::Ensemble::initial_row(component, row, hint)
    }

    fn complete_row(
        component: usize,
        input: &[F],
        data: &WitnessData<F>,
        hint: &WitnessData<F>,
    ) -> Result<Vec<F>, String> {
        generated::Ensemble::complete_row(component, input, data, hint)
    }

    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>> {
        generated::Ensemble::interactions(component, row)
    }

    fn verifier_interactions(public_input: &[F]) -> Vec<Interaction<F>> {
        generated::Ensemble::verifier_interactions(public_input)
    }
}

#[test]
fn witness_generation_rejects_states_that_several_tables_accept() {
    let error = witness_generation::generate::<BabyBear, UnguardedProgram>(
        &public_values(),
        &prover_input(),
        setup::MINIMUM_TRACE_HEIGHT,
    )
    .expect_err("witness generation without guards succeeded");
    assert_eq!(
        error.to_string(),
        "components add, mul, load, store all accept a message on channel 'state'"
    );
}
