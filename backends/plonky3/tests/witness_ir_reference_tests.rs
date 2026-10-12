extern crate alloc;

#[allow(dead_code, unused_mut, unused_parens, unused_variables)]
mod generated {
    include!("generated/witness_ir_reference.rs");
}

use clean_backend::witness_generation::WitnessData;
use generated::{eval_case, EXPECTED, FIELD_ORDER, INPUT, MEMORY, PROVER_INPUT, ROW_INDICES};
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};

fn fields(values: &[u64]) -> Vec<BabyBear> {
    values.iter().copied().map(BabyBear::from_u64).collect()
}

#[test]
fn generated_witness_ir_matches_lean_semantics() {
    assert_eq!(BabyBear::ORDER_U64, FIELD_ORDER);
    let input = fields(INPUT);
    let prover_input = fields(PROVER_INPUT);
    let data = WitnessData::from_entries(vec![(
        "memory",
        MEMORY.iter().map(|row| fields(row)).collect(),
    )]);
    for (case, expected_rows) in EXPECTED.iter().enumerate() {
        for (&row, expected) in ROW_INDICES.iter().zip(expected_rows.iter()) {
            let actual: Vec<u64> = eval_case(case, &input, row, &prover_input, &data)
                .into_iter()
                .map(|value| value.as_canonical_u64())
                .collect();
            assert_eq!(&actual, expected, "case {case}, row {row}");
        }
    }
}
