use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_air::lookup::{Direction, Kind, Lookup, LookupInput};
use p3_field::Field;
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_uni_stark::{SymbolicAirBuilder, SymbolicExpression};

#[derive(Clone)]
pub struct PreprocessedTableAir<F> {
    pub name: String,
    pub preprocessed: RowMajorMatrix<F>,
    pub num_lookups: usize,
}

impl<F: Field> PreprocessedTableAir<F> {
    pub fn new(name: String, preprocessed: RowMajorMatrix<F>) -> Self {
        Self {
            name,
            preprocessed,
            num_lookups: 0,
        }
    }

    pub fn table_name(&self) -> &str {
        &self.name
    }

    /// Build the lookup descriptors for this table AIR.
    ///
    /// Creates a single global lookup with Direction::Send (table provides values).
    /// The element expressions are the preprocessed columns and the multiplicity
    /// is the main trace column 0.
    pub fn build_lookups(&mut self) -> Vec<Lookup<F>> {
        let prep_width = self.preprocessed.width();
        let main_width = 1; // multiplicity column

        let symbolic_builder = SymbolicAirBuilder::<F>::new(prep_width, main_width, 0, 0, 0);

        let preprocessed = AirBuilder::preprocessed(&symbolic_builder).unwrap();
        let main = AirBuilder::main(&symbolic_builder);

        let prep_local = preprocessed.row_slice(0).unwrap();
        let main_local = main.row_slice(0).unwrap();

        // Preprocessed columns as lookup values
        let values: Vec<SymbolicExpression<F>> = (0..prep_width)
            .map(|col| prep_local[col].into())
            .collect();

        // Multiplicity from main trace
        let mult: SymbolicExpression<F> = main_local[0].into();

        let lookup_input: LookupInput<F> = (values, mult, Direction::Send);

        // Build lookup manually
        let columns = self.add_lookup_columns_impl();

        let (element_exprs, multiplicities_exprs): (Vec<_>, Vec<_>) = vec![lookup_input]
            .into_iter()
            .map(|(elems, m, dir)| {
                let multiplicity = dir.multiplicity(m);
                (elems, multiplicity)
            })
            .unzip();

        vec![Lookup::new(
            Kind::Global(self.name.clone()),
            element_exprs,
            multiplicities_exprs,
            columns,
        )]
    }

    fn add_lookup_columns_impl(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }
}

/// Convenience constructor for a byte-range (0..255) lookup table.
pub fn byte_range_air<F: Field>() -> PreprocessedTableAir<F> {
    let preprocessed = RowMajorMatrix::new((0..256).map(|i| F::from_u8(i as u8)).collect(), 1);
    PreprocessedTableAir::new("Bytes".into(), preprocessed)
}

impl<F: Field> BaseAir<F> for PreprocessedTableAir<F> {
    /// One column for multiplicity
    fn width(&self) -> usize {
        1
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(self.preprocessed.clone())
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for PreprocessedTableAir<AB::F>
where
    AB::F: Field,
{
    fn eval(&self, _builder: &mut AB) {
        // Lookup constraints are handled via eval_with_lookups / LogUpGadget,
        // not in eval() directly.
    }
}
