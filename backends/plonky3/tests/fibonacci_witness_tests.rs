extern crate alloc;

mod generated {
    include!("generated/fibonacci_witness.rs");
}

use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField64};

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
