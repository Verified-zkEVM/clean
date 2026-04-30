use alloc::vec::Vec;
use p3_air::{Air, BaseAir};
use p3_air::lookup::Lookup;
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::SymbolicAirBuilder;

use crate::clean_air::CleanAirInstance;
use crate::clean_ast::LookupRowScope;

#[derive(Clone)]
pub struct AirInfo<F: Field> {
    pub air: CleanAirInstance<F>,
    pub lookups: Vec<Lookup<F>>,
    pub lookup_row_scopes: Vec<LookupRowScope>,
    pub preprocessed: Option<RowMajorMatrix<F>>,
}

impl<F: Field> AirInfo<F> {
    /// Create a new AirInfo from air instance, building lookups automatically
    pub fn new(mut air: CleanAirInstance<F>) -> Self {
        let lookups =
            <CleanAirInstance<F> as Air<SymbolicAirBuilder<F>>>::get_lookups(&mut air);
        let lookup_row_scopes = air.lookup_row_scopes();
        let preprocessed = air.preprocessed_trace();

        Self {
            air,
            lookups,
            lookup_row_scopes,
            preprocessed,
        }
    }
}
