//! Checks the printed AIRs and witness generators of the example ensembles against values that Lean
//! computes for them, see `Clean/Backends/Plonky3/Test/Differential.lean`.

extern crate alloc;

mod fibonacci {
    include!("generated/fibonacci_ensemble.rs");
}

mod femtocairo {
    include!("generated/femtocairo_flat_air.rs");
}

mod opcode_vm {
    include!("generated/opcode_vm.rs");
}

mod expected {
    include!("generated/differential.rs");
}

use clean_backend::witness_generation::{EnsembleWitness, Interaction, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use expected::{ExpectedEnsemble, ExpectedInteraction};
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};

fn field(values: &[u64]) -> Vec<BabyBear> {
    values.iter().copied().map(BabyBear::from_u64).collect()
}

fn canonical(values: &[BabyBear]) -> Vec<u64> {
    values
        .iter()
        .map(|value| value.as_canonical_u64())
        .collect()
}

fn assert_interactions(
    actual: Vec<Interaction<BabyBear>>,
    expected: &[ExpectedInteraction],
    context: &str,
) {
    assert_eq!(actual.len(), expected.len(), "{context}: interaction count");
    for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
        assert_eq!(
            actual.channel, expected.channel,
            "{context}: interaction {index}"
        );
        assert_eq!(
            actual.multiplicity.as_canonical_u64(),
            expected.multiplicity,
            "{context}: interaction {index}"
        );
        assert_eq!(
            canonical(&actual.message),
            expected.message,
            "{context}: interaction {index}"
        );
    }
}

/// Compare the printed AIR of an ensemble with Lean's values: constraints and interactions of every
/// component on pseudo-random rows, fixed rows, and verifier interactions on pseudo-random public
/// inputs.
fn check_air<P: GeneratedAirSpec>(expected: &ExpectedEnsemble) {
    assert_eq!(P::WIDTHS.len(), expected.components.len());
    for (component, expected) in expected.components.iter().enumerate() {
        for (index, row) in expected.rows.iter().enumerate() {
            let context = format!("component {component}, row {index}");
            let row = field(row);
            assert_eq!(
                canonical(&P::constraints(component, &row)),
                expected.constraints[index],
                "{context}: constraints"
            );
            assert_interactions(
                P::interactions(component, &row),
                expected.interactions[index],
                &context,
            );
        }
        let fixed_height = P::FIXED_HEIGHTS[component];
        assert_eq!(
            fixed_height,
            expected.fixed_rows.len(),
            "component {component}: fixed rows"
        );
        for (row, expected) in expected.fixed_rows.iter().enumerate() {
            assert_eq!(
                canonical(&P::fixed_row::<BabyBear>(component, row as u64)),
                *expected,
                "component {component}, fixed row {row}"
            );
        }
    }
    for (index, public) in expected.public_rows.iter().enumerate() {
        assert_interactions(
            P::verifier_interactions(&field(public)),
            expected.verifier_interactions[index],
            &format!("verifier, public input {index}"),
        );
    }
}

/// A printed witness generator.
type Generate = fn(
    &[BabyBear],
    &[BabyBear],
    usize,
) -> Result<EnsembleWitness<BabyBear>, WitnessGenerationError>;

/// Compare the tables of the printed witness generator with the tables Lean generates.
fn check_tables(generate: Generate, expected: &ExpectedEnsemble) {
    let witness = generate(
        &field(expected.public_input),
        &field(expected.prover_input),
        1,
    )
    .expect("printed witness generation failed");
    assert_eq!(witness.tables.len(), expected.tables.len());
    for (component, (table, expected)) in witness.tables.iter().zip(expected.tables).enumerate() {
        assert_eq!(table.len(), expected.len(), "component {component}: height");
        for (row, (actual, expected)) in table.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                canonical(actual),
                *expected,
                "component {component}, row {row}"
            );
        }
    }
}

#[test]
fn fibonacci_matches_lean() {
    check_air::<fibonacci::Ensemble>(&expected::FIBONACCI);
    check_tables(fibonacci::generate::<BabyBear>, &expected::FIBONACCI);
}

#[test]
fn femtocairo_matches_lean() {
    check_air::<femtocairo::Ensemble>(&expected::FEMTOCAIRO);
    check_tables(femtocairo::generate::<BabyBear>, &expected::FEMTOCAIRO);
}

#[test]
fn opcode_vm_matches_lean() {
    check_air::<opcode_vm::Ensemble>(&expected::OPCODE_VM);
    check_tables(opcode_vm::generate::<BabyBear>, &expected::OPCODE_VM);
}
