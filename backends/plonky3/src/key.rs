use alloc::vec::Vec;
use p3_air::BaseAir;
use p3_air::lookup::Lookup;
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;

use crate::clean_air::CleanAirInstance;

#[derive(Clone)]
pub struct AirInfo<F: Field> {
    pub air: CleanAirInstance<F>,
    pub lookups: Vec<Lookup<F>>,
    pub preprocessed: Option<RowMajorMatrix<F>>,
}

impl<F: Field> AirInfo<F> {
    /// Create a new AirInfo from air instance, building lookups automatically
    pub fn new(mut air: CleanAirInstance<F>) -> Self {
        let lookups = air.build_lookups();
        let preprocessed = air.preprocessed_trace();

        Self {
            air,
            lookups,
            preprocessed,
        }
    }
}
