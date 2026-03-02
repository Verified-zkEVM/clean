use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PermutationAirBuilder};
use p3_air::lookup::{Direction, Kind, Lookup};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_uni_stark::{SymbolicAirBuilder, SymbolicExpression};

/// Parse the standard `{"width": N, "rows": [[...]]}` table JSON into a matrix.
fn parse_table_json<F: PrimeCharacteristicRing + Send + Sync>(value: &serde_json::Value) -> RowMajorMatrix<F> {
    let width = value["width"].as_u64().expect("missing 'width'") as usize;
    assert!(width > 0, "table width must be positive");
    let rows = value["rows"].as_array().expect("missing 'rows'");
    assert!(!rows.is_empty(), "table must have at least one row");
    let data: Vec<F> = rows
        .iter()
        .enumerate()
        .flat_map(|(i, row)| {
            let row = row.as_array().expect("row is not an array");
            assert_eq!(
                row.len(),
                width,
                "row {i} has {} elements, expected {width}",
                row.len()
            );
            row.iter()
                .map(|v| F::from_u64(v.as_u64().expect("value is not u64")))
        })
        .collect();
    RowMajorMatrix::new(data, width)
}

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

    /// Build a `PreprocessedTableAir` from the standard JSON format produced by
    /// Lean circuit export: `{"width": N, "rows": [[...]]}`.
    pub fn from_json(name: String, value: &serde_json::Value) -> Self
    where
        F: PrimeCharacteristicRing,
    {
        Self::new(name, parse_table_json(value))
    }
}

/// Convenience constructor for a byte-range (0..=255) lookup table.
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

    /// Build the lookup descriptors for this table AIR.
    ///
    /// Creates a single global lookup with Direction::Send (table provides values).
    /// The element expressions are the preprocessed columns and the multiplicity
    /// is the main trace column 0.
    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>
    where
        AB: PermutationAirBuilder + AirBuilderWithPublicValues,
    {
        self.num_lookups = 0;
        let prep_width = self.preprocessed.width();
        let main_width = 1; // multiplicity column

        let symbolic_builder = SymbolicAirBuilder::<AB::F>::new(prep_width, main_width, 0, 0, 0);

        let preprocessed = AirBuilder::preprocessed(&symbolic_builder).unwrap();
        let main = AirBuilder::main(&symbolic_builder);

        let prep_local = preprocessed.row_slice(0).unwrap();
        let main_local = main.row_slice(0).unwrap();

        // Preprocessed columns as lookup values
        let values: Vec<SymbolicExpression<AB::F>> = (0..prep_width)
            .map(|col| prep_local[col].into())
            .collect();

        // Multiplicity from main trace
        let mult: SymbolicExpression<AB::F> = main_local[0].into();

        let lookup_input = (values, mult, Direction::Send);

        vec![Air::<AB>::register_lookup(self, Kind::Global(self.name.clone()), &[lookup_input])]
    }

    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }
}

/// A table AIR whose data is provided by the prover at proving time (not preprocessed).
///
/// The verifier doesn't need to know the table contents — only the lookup
/// constraints are verified.  The trace has `data_width` data columns followed
/// by a multiplicity column (total width = `data_width + 1`).
#[derive(Clone)]
pub struct ProverTableAir<F> {
    pub name: String,
    pub data_width: usize,
    pub num_lookups: usize,
    _phantom: PhantomData<F>,
}

impl<F: Field> ProverTableAir<F> {
    pub fn new(name: String, data_width: usize) -> Self {
        Self {
            name,
            data_width,
            num_lookups: 0,
            _phantom: PhantomData,
        }
    }

    pub fn table_name(&self) -> &str {
        &self.name
    }

    /// Build a `ProverTableAir` and its data matrix from the standard JSON format
    /// produced by Lean trace export: `{"width": N, "rows": [[...]]}`.
    ///
    /// Returns `(air, data_matrix)` since callers always need both.
    pub fn from_json(name: String, value: &serde_json::Value) -> (Self, RowMajorMatrix<F>)
    where
        F: PrimeCharacteristicRing,
    {
        let matrix = parse_table_json(value);
        let width = matrix.width();
        (Self::new(name, width), matrix)
    }
}

impl<F: Field> BaseAir<F> for ProverTableAir<F> {
    /// data columns + 1 multiplicity column
    fn width(&self) -> usize {
        self.data_width + 1
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        None
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for ProverTableAir<AB::F>
where
    AB::F: Field,
{
    fn eval(&self, _builder: &mut AB) {}

    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>
    where
        AB: PermutationAirBuilder + AirBuilderWithPublicValues,
    {
        self.num_lookups = 0;
        let prep_width = 0; // no preprocessed columns
        let main_width = self.data_width + 1; // data + multiplicity

        let symbolic_builder = SymbolicAirBuilder::<AB::F>::new(prep_width, main_width, 0, 0, 0);
        let main = AirBuilder::main(&symbolic_builder);
        let main_local = main.row_slice(0).unwrap();

        // Data columns as lookup values
        let values: Vec<SymbolicExpression<AB::F>> = (0..self.data_width)
            .map(|col| main_local[col].into())
            .collect();

        // Multiplicity from the last main trace column
        let mult: SymbolicExpression<AB::F> = main_local[self.data_width].into();

        let lookup_input = (values, mult, Direction::Send);

        vec![Air::<AB>::register_lookup(self, Kind::Global(self.name.clone()), &[lookup_input])]
    }

    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }
}
