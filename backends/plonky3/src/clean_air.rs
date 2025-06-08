use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use p3_uni_stark::{get_max_constraint_degree, get_symbolic_constraints, SymbolicExpression};
use p3_util::log2_ceil_usize;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder, PermutationAirBuilder, VirtualPairCol};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

use crate::{BaseMessageBuilder, ByteRangeAir, Lookup, LookupBuilder, LookupType};
use crate::permutation::{eval_permutation_constraints, MultiTableBuilder};
use crate::clean_ast::{CleanOp, CleanOps, CircuitOp, LookupOp, VarLocation, LookupRow, AstUtils};

pub trait CleanAir<F> {
    fn lookups(&self) -> &Vec<(Lookup<VirtualPairCol<F>>, bool)> where F: Field;
    fn main(&self) -> &RowMajorMatrix<F>;
    fn preprocessed(&self) -> Option<RowMajorMatrix<F>> {
        None
    }
    fn constraints(&self, public_inputs: usize) -> Vec<SymbolicExpression<F>>;
    fn count_constraints(&self, public_inputs: usize) -> usize;
    fn log_quotient_degree(&self, public_inputs: usize) -> usize;
    fn eval_constraints<AB>(&self, builder: &mut AB) where AB: AirBuilder<F = F> + PermutationAirBuilder + MultiTableBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder;
}

#[derive(Clone)]
pub struct MainAir<F>
where
    F: Field,
{
    /// Operations handler for the clean JSON format
    clean_ops: CleanOps,
    /// Width of the trace, including
    width: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> BaseAir<F> for MainAir<F> {
    fn width(&self) -> usize {
        self.width
    }
}

impl<AB: AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder> Air<AB> for MainAir<AB::F>
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let _preprocessed = builder.preprocessed();

        let pis = builder.public_values();
        if pis.len() >= 3 {
            let a = pis[0];
            let b = pis[1];
            let x = pis[2];

            let (local, next) = (
                main.row_slice(0).expect("Matrix is empty?"),
                main.row_slice(1).expect("Matrix only has 1 row?"),
            );

            // Build constraints from clean ops
            for op in self.clean_ops.ops() {
                match op {
                    CleanOp::Boundary { row, context: _ } => {
                        // When it is the first row
                        if *row == 0 {
                            builder.when_first_row().assert_eq(local[0], a);
                            builder.when_first_row().assert_eq(local[1], b);
                        }

                        // When it is the last row
                        builder.when_last_row().assert_eq(local[1], x);
                    }
                    CleanOp::EveryRowExceptLast { context } => {
                        let val_of = |var_idx: usize| {
                            let var: VarLocation = context.assignment.vars[var_idx].clone();
                            match var {
                                VarLocation::Cell { row, column } => match row {
                                    0 => local[column],
                                    1 => next[column],
                                    _ => panic!("Invalid row index"),
                                },
                                // Currently assume the only aux var is the 3rd column of the next row
                                VarLocation::Aux { .. } => *next.get(2).unwrap(),
                            }
                        };

                        // When it is not the last row
                        let mut when_transition = builder.when_transition();
                        for circuit_op in &context.circuit {
                            match circuit_op {
                                CircuitOp::Assert { assert } => {
                                    let expr = AstUtils::to_expr::<AB>(&assert, &val_of);
                                    when_transition.assert_zero(expr);
                                }
                                CircuitOp::Subcircuit { subcircuit } => {
                                    for sub_op in subcircuit {
                                        if let CircuitOp::Assert { assert } = sub_op {
                                            let expr = AstUtils::to_expr::<AB>(&assert, &val_of);
                                            when_transition.assert_zero(expr);
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        // Apply constraints for lookup columns
        let (local, _next) = (
            main.row_slice(0).expect("Matrix is empty?"),
            main.row_slice(1).expect("Matrix only has 1 row?"),
        );

        let mut lookup_cols = BTreeSet::new();
        self.process_lookups(|_r, c| {
            lookup_cols.insert(c);
        });

        // For now, assume these lookups are for byte range
        for &c in &lookup_cols {
            let v = local[c].into();
            let mul = AB::F::ONE.into();
            let l = Lookup::new(LookupType::ByteRange, v, mul);
            builder.send(l);
        }
    }
}

impl<F: Field> MainAir<F> {
    /// Create a new CleanAir instance from JSON content and trace data
    pub fn new(json_content: &str, width: usize) -> Self {
        let clean_ops = CleanOps::from_json(json_content);
        Self {
            clean_ops,
            width,
            _marker: PhantomData,
        }
    }

    /// Create a new CleanAir instance from CleanOps and trace data
    pub fn from_ops(clean_ops: CleanOps, width: usize) -> Self {
        Self {
            clean_ops,
            width,
            _marker: PhantomData,
        }
    }

    /// Get reference to the clean operations
    pub fn clean_ops(&self) -> &CleanOps {
        &self.clean_ops
    }

    /// Process lookups for all operations (delegates to CleanOps)
    pub fn process_lookups<C>(&self, callback: C)
    where
        C: FnMut(LookupRow, usize),
    {
        self.clean_ops.process_lookups(callback)
    }

    pub fn lookup_ops(&self) -> Vec<LookupOp> {
        self.clean_ops.lookup_ops()
    }
}

/// Helper function to parse initial trace data from JSON
pub fn parse_init_trace<F: Field + PrimeCharacteristicRing>(json_content: &str) -> Vec<Vec<F>> {
    // First parse the JSON as a Vec<Vec<u64>>
    let raw_data: Vec<Vec<u64>> = serde_json::from_str(json_content).expect("Failed to parse JSON");

    // Convert Vec<u64> to Vec<F>
    let raw_data: Vec<Vec<F>> = raw_data
        .into_iter()
        .map(|row| row.into_iter().map(F::from_u64).collect())
        .collect();

    raw_data
}

/// Enum wrapper to handle multiple AIR types in the same vector
#[derive(Clone)]
pub enum CleanAirInstance<F: Field> {
    Main(MainAir<F>),
    ByteRange(ByteRangeAir<F>),
}

impl<F: Field> CleanAirInstance<F> {
    pub fn log_quotient_degree(&self, main: usize, preprocessed: usize, public_inputs: usize) -> usize {
        let d = get_max_constraint_degree(self, preprocessed, public_inputs);

        // todo: cache these lookups in the wrapper's constructor
        let builder = LookupBuilder::<F>::new(main, preprocessed);
        let (sends, receives) = builder.messages();

        // if there are permutations, ensure the degree is at least 3
        if !sends.is_empty() || !receives.is_empty() {
            d.max(3)
        } else {
            d
        }
    }
}

impl<F: Field> BaseAir<F> for CleanAirInstance<F> {
    fn width(&self) -> usize {
        match self {
            CleanAirInstance::Main(air) => air.width(),
            CleanAirInstance::ByteRange(air) => air.width(),
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            CleanAirInstance::Main(air) => air.preprocessed_trace(),
            CleanAirInstance::ByteRange(air) => air.preprocessed_trace(),
        }
    }
}

impl<AB> Air<AB> for CleanAirInstance<AB::F>
where
    AB: AirBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            CleanAirInstance::Main(air) => air.eval(builder),
            CleanAirInstance::ByteRange(air) => air.eval(builder),
        };
    }
}

#[derive(Clone)]
pub struct Table<F: Field> {
    pub air: CleanAirInstance<F>,
    pub trace: RowMajorMatrix<F>,
    /// lookups as pairs of (Lookup, is_send)
    pub lookups: Vec<(Lookup<VirtualPairCol<F>>, bool)>,
}

impl<F: Field> Table<F> {
    /// Create a new CleanAirWrapper that pre-builds the lookups using LookupBuilder
    pub fn new(air: CleanAirInstance<F>, trace: RowMajorMatrix<F>) -> Self {
        Self::from_instance(air, trace)
    }


    /// Create a new CleanAirWrapper from an existing CleanAirInstance and main trace
    pub fn from_instance(inner: CleanAirInstance<F>, main_trace: RowMajorMatrix<F>) -> Self {
        let preprocessed_width = if inner.preprocessed_trace().is_some() {
            inner.preprocessed_trace().unwrap().width()
        } else {
            0 
        };

        // Build lookups using LookupBuilder
        let mut lookup_builder = LookupBuilder::new(preprocessed_width, main_trace.width());
        
        // Evaluate the inner Air to extract lookups
        match &inner {
            CleanAirInstance::Main(air) => {
                air.eval(&mut lookup_builder);
            }
            CleanAirInstance::ByteRange(air) => {
                air.eval(&mut lookup_builder);
            }
        }

        let (s, r) = lookup_builder.messages();
        let lookups = s.into_iter()
            .map(|l| (l, true))
            .chain(r.into_iter()
            .map(|l| (l, false)))
            .collect();

        Self { air: inner, trace: main_trace, lookups }
    }

    /// Access the inner CleanAirInstance
    pub fn inner(&self) -> &CleanAirInstance<F> {
        &self.air
    }

    /// Access the main trace
    pub fn main_trace(&self) -> &RowMajorMatrix<F> {
        &self.trace
    }

    /// Access the cached lookup messages (sends, receives)
    pub fn lookups(&self) -> &Vec<(Lookup<VirtualPairCol<F>>, bool)> {
        &self.lookups
    }

    pub fn as_clean_air(&self) -> Option<&MainAir<F>> {
        if let CleanAirInstance::Main(air) = &self.air {
            Some(air)
        } else {
            None
        }
    }
}

impl<F: Field> CleanAir<F> for Table<F> {
    /// Get symbolic constraints for this air
    fn constraints(&self, public_inputs: usize) -> Vec<SymbolicExpression<F>> {
        let preprocessed = if let Some(pre) = self.air.preprocessed_trace() {
            pre.width()
        } else {
            0 
        };

        get_symbolic_constraints(&self.air, preprocessed, public_inputs)
    }

    fn count_constraints(&self, public_inputs: usize) -> usize {
        let constraints = self.constraints(public_inputs);

        if !self.lookups.is_empty() {
            self.lookups.len() + constraints.len() + 3 // 3 for the first row, last row, and transition constraints
        } else {
            constraints.len()
        }
        // constraints.len()
    }

    /// Get log quotient degree for this air
    fn log_quotient_degree(&self, public_inputs: usize) -> usize {
        let constraints = self.constraints(public_inputs);
        let max_degree = constraints
            .iter()
            .map(|c| c.degree_multiple())
            .max()
            .unwrap_or(0);

        let max_degree = if !self.lookups().is_empty() {
            // if there are permutations, ensure the degree is at least 2, because of the multiplication with selectors.
            max_degree.max(2)
        } else {
            max_degree
        };
        
        // division by vanishing polynomial results in degree - 1
        log2_ceil_usize(max_degree - 1)
        
    }

    fn eval_constraints<AB>(&self, builder: &mut AB) where AB: AirBuilder<F = F> + PermutationAirBuilder + MultiTableBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder {
        self.eval(builder);

        eval_permutation_constraints(self.lookups(), builder);
    }
    
    fn lookups(&self) -> &Vec<(Lookup<VirtualPairCol<F>>, bool)> where F: Field {
        &self.lookups
    }
    
    fn main(&self) -> &RowMajorMatrix<F> {
        &self.trace
    }

    fn preprocessed(&self) -> Option<RowMajorMatrix<F>> {
        self.air.preprocessed_trace()
    }
}

impl<F: Field> BaseAir<F> for Table<F> {
    fn width(&self) -> usize {
        self.air.width()
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        self.air.preprocessed_trace()
    }
}

impl<AB> Air<AB> for Table<AB::F>
where
    AB: AirBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        self.air.eval(builder);
    }
}