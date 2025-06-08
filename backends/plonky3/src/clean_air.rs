use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use p3_uni_stark::{get_max_constraint_degree, SymbolicExpression};
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder, PermutationAirBuilder, VirtualPairCol};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

use crate::{BaseMessageBuilder, ByteRangeAir, Lookup, LookupBuilder, LookupType, VerifyingKey};
use crate::permutation::MultiTableBuilder;
use crate::clean_ast::{CleanOp, CleanOps, CircuitOp, LookupOp, VarLocation, LookupRow, AstUtils};
use crate::key::VK;

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

pub trait CleanAir<F>: VerifyingKey<F> {
    fn main(&self) -> &RowMajorMatrix<F>;
}

#[derive(Clone)]
pub struct Table<F: Field> {
    pub vk: VK<F>,
    // todo: verifier doesn't access to main traces
    pub trace: RowMajorMatrix<F>,
}

impl<F: Field> Table<F> {
    /// Create a new Table that delegates construction to VK
    pub fn new(vk: VK<F>, trace: RowMajorMatrix<F>) -> Self {
        Self { vk, trace }
    }

    /// Access the main trace
    pub fn main_trace(&self) -> &RowMajorMatrix<F> {
        &self.trace
    }

    /// Access the cached lookup messages (sends, receives)
    pub fn lookups(&self) -> &Vec<(Lookup<VirtualPairCol<F>>, bool)> {
        self.vk.lookups()
    }

    pub fn as_clean_air(&self) -> Option<&MainAir<F>> {
        if let CleanAirInstance::Main(air) = &self.vk.air {
            Some(air)
        } else {
            None
        }
    }
}

impl<F: Field> VerifyingKey<F> for Table<F> {
    /// Get symbolic constraints for this air
    fn constraints(&self, public_inputs: usize) -> Vec<SymbolicExpression<F>> {
        self.vk.constraints(public_inputs)
    }

    fn count_constraints(&self, public_inputs: usize) -> usize {
        self.vk.count_constraints(public_inputs)
    }

    /// Get log quotient degree for this air
    fn log_quotient_degree(&self, public_inputs: usize) -> usize {
        self.vk.log_quotient_degree(public_inputs)
    }

    fn eval_constraints<AB>(&self, builder: &mut AB) where AB: AirBuilder<F = F> + PermutationAirBuilder + MultiTableBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder {
        self.vk.eval_constraints(builder);
    }
    
    fn lookups(&self) -> &Vec<(Lookup<VirtualPairCol<F>>, bool)> where F: Field {
        self.vk.lookups()
    }
    
    fn preprocessed(&self) -> Option<RowMajorMatrix<F>> {
        self.vk.preprocessed()
    }
    
    fn width(&self) -> usize {
        self.vk.air.width()
    }
}

impl<F: Field> CleanAir<F> for Table<F> {
    fn main(&self) -> &RowMajorMatrix<F> {
        &self.trace
    }
}

impl<F: Field> BaseAir<F> for Table<F> {
    fn width(&self) -> usize {
        self.vk.air.width()
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        self.vk.air.preprocessed_trace()
    }
}

impl<AB> Air<AB> for Table<AB::F>
where
    AB: AirBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        self.vk.air.eval(builder);
    }
}