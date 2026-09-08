extern crate alloc;

#[allow(dead_code)]
mod fibonacci {
    include!("generated/fibonacci_ensemble.rs");
}

#[allow(dead_code, unused_imports, unused_mut, unused_parens, unused_variables)]
mod edges {
    include!("generated/witness_edges.rs");
}

use clean_backend::witness_generation::Program;
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use serde_json::Value;

fn fields(values: &Value) -> Vec<BabyBear> {
    values
        .as_array()
        .unwrap()
        .iter()
        .map(|value| BabyBear::from_u64(value.as_u64().unwrap()))
        .collect()
}

fn reference() -> Value {
    serde_json::from_str(include_str!("generated/witness_reference.json")).unwrap()
}

#[test]
fn generated_witness_edges_match_lean() {
    for case in reference()["edges"].as_array().unwrap() {
        let input = fields(&case["input"]);
        let row = <edges::WitnessEdges as Program<BabyBear>>::complete_row(0, &input).unwrap();
        assert_eq!(row, fields(&case["row"]), "input: {input:?}");
    }
}

#[test]
fn generated_fibonacci_traces_match_lean_cell_for_cell() {
    for case in reference()["fibonacci"].as_array().unwrap() {
        let public_input = fields(&case["public_input"]);
        let witness = fibonacci::generate(&public_input).unwrap();
        let actual: Vec<Vec<Vec<u64>>> = witness
            .tables
            .iter()
            .map(|table| {
                table
                    .iter()
                    .map(|row| row.iter().map(PrimeField64::as_canonical_u64).collect())
                    .collect()
            })
            .collect();
        assert_eq!(
            serde_json::to_value(actual).unwrap(),
            case["tables"],
            "public input: {public_input:?}"
        );
    }
}
