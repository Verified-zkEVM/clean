use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use p3_uni_stark::{get_max_constraint_degree, get_symbolic_constraints, SymbolicExpression};
use p3_util::log2_ceil_usize;
use core::fmt;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder, PermutationAirBuilder, VirtualPairCol};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde::de::Visitor;
use serde::{Deserialize, Deserializer};

use crate::{eval_permutation_constraints, BaseMessageBuilder, ByteRangeAir, Lookup, LookupBuilder, LookupType, MultiTableBuilder};

pub trait CleanAir<F> {
    fn constraints(&self, public_inputs: usize) -> Vec<SymbolicExpression<F>>;
    fn count_constraints(&self, public_inputs: usize) -> usize;
    fn log_quotient_degree(&self, public_inputs: usize) -> usize;
    fn eval_constraints<AB>(&self, builder: &mut AB) where AB: AirBuilder<F = F> + PermutationAirBuilder + MultiTableBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder;
}

/// Operations defined in the clean JSON format
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "type")]
pub enum CleanOp {
    Boundary { row: usize, context: OpContext },
    EveryRowExceptLast { context: OpContext },
}

impl CleanOp {
    /// Recursively find all lookup operations
    fn find_lookup_ops(&self, ctx: &Vec<CircuitOp>) -> Vec<LookupOp> {
        let mut lookup_ops = Vec::new();
        for op in ctx {
            match op {
                CircuitOp::Lookup { lookup } => {
                    lookup_ops.push(lookup.clone());
                }
                CircuitOp::Subcircuit { subcircuit } => {
                    lookup_ops.extend(self.find_lookup_ops(subcircuit));
                }
                _ => {}
            }
        }
        lookup_ops
    }

    pub fn lookups(&self) -> Vec<LookupOp> {
        match self {
            CleanOp::Boundary { context, .. } => self.find_lookup_ops(&context.circuit),
            CleanOp::EveryRowExceptLast { context } => self.find_lookup_ops(&context.circuit),
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
pub struct OpContext {
    pub circuit: Vec<CircuitOp>,
    pub assignment: Assignment,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub enum CircuitOp {
    Witness { witness: usize },
    Assert { assert: AssertOp },
    Lookup { lookup: LookupOp },
    Subcircuit { subcircuit: Vec<CircuitOp> },
}

#[derive(Clone, Debug, Deserialize)]
pub struct AssertOp {
    #[serde(rename = "type")]
    pub op_type: String,
    pub lhs: ExprNode,
    pub rhs: ExprNode,
}

#[derive(Clone, Debug, Deserialize)]
pub struct LookupOp {
    pub table: String,
    pub entry: Vec<ExprNode>,
}

/// Expression nodes for the JSON AST
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum ExprNode {
    Var {
        index: usize,
    },
    Const {
        value: u64,
    },
    Add {
        lhs: Box<ExprNode>,
        rhs: Box<ExprNode>,
    },
    Mul {
        lhs: Box<ExprNode>,
        rhs: Box<ExprNode>,
    },
}

#[derive(Clone, Debug, Deserialize)]
pub struct Assignment {
    /// Mapping from `var<i>` → concrete cell
    pub vars: Vec<VarLocation>,
    pub offset: usize,
    pub aux_length: usize,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "lowercase", untagged)]
#[allow(clippy::large_enum_variant)]
pub enum VarLocation {
    Cell { row: usize, column: usize },
    Aux { aux: usize },
}

/// Current or next row transition
#[derive(Debug)]
pub enum Transition {
    Current,
    Next,
}

#[derive(Debug)]
pub enum LookupRow {
    /// Specific row
    Boundary { row: usize },
    Transition(Transition),
}

/// Clean AIR implementation for STARK constraints
#[derive(Clone)]
pub struct MainAir<F>
where
    F: Field,
{
    /// Operations defined in the clean JSON format
    ops: Vec<CleanOp>,
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
            for op in &self.ops {
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
                                    let expr = self.to_expr::<AB>(&assert, &val_of);
                                    when_transition.assert_zero(expr);
                                }
                                CircuitOp::Subcircuit { subcircuit } => {
                                    for sub_op in subcircuit {
                                        if let CircuitOp::Assert { assert } = sub_op {
                                            let expr = self.to_expr::<AB>(&assert, &val_of);
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
        let ops: Vec<CleanOp> = serde_json::from_str(json_content).expect("Failed to parse JSON");
        Self {
            ops,
            width,
            _marker: PhantomData,
        }
    }

    /// Process lookups for all operations
    pub fn process_lookups<C>(&self, mut callback: C)
    where
        C: FnMut(LookupRow, usize),
    {
        for op in &self.ops {
            // Extract context and check for boundary row match if needed
            let (context, boundary_row) = match op {
                CleanOp::Boundary { context, row } => (context, Some(row)),
                CleanOp::EveryRowExceptLast { context } => (context, None),
            };

            // Process all lookups in the context
            for lookup in op.lookups() {
                for entry in lookup.entry.iter() {
                    match entry {
                        ExprNode::Var { index } => {
                            let var = &context.assignment.vars[*index];
                            match var {
                                VarLocation::Cell { row, column } => {
                                    if let Some(r) = boundary_row {
                                        assert_eq!(
                                            r, row,
                                            "Boundary row does not match the lookup row"
                                        );
                                        callback(LookupRow::Boundary { row: *r }, *column);
                                    } else if *row == 0 {
                                        callback(
                                            LookupRow::Transition(Transition::Current),
                                            *column,
                                        );
                                    } else if *row == 1 {
                                        callback(LookupRow::Transition(Transition::Next), *column);
                                    } else {
                                        panic!("Invalid row index in VarLocation");
                                    }
                                }
                                VarLocation::Aux { .. } => {
                                    // Handle aux variables through the callback if needed
                                    todo!()
                                }
                            }
                        }
                        _ => panic!("Invalid lookup entry"),
                    }
                }
            }
        }
    }

    /// Convert ExprNode to AirBuilder::Expr
    fn lower_expr<AB: AirBuilder>(
        expr: &ExprNode,
        lookup_var: &dyn Fn(usize) -> AB::Var,
    ) -> AB::Expr
    where
        AB::F: Field + PrimeCharacteristicRing,
    {
        match expr {
            ExprNode::Var { index } => AB::Var::from(lookup_var(*index)).into(),
            ExprNode::Const { value } => AB::F::from_u64(*value).into(),
            ExprNode::Add { lhs, rhs } => {
                Self::lower_expr::<AB>(lhs, lookup_var) + Self::lower_expr::<AB>(rhs, lookup_var)
            }
            ExprNode::Mul { lhs, rhs } => {
                Self::lower_expr::<AB>(lhs, lookup_var) * Self::lower_expr::<AB>(rhs, lookup_var)
            }
        }
    }

    /// Convert to AB::Expr
    fn to_expr<AB: AirBuilder>(
        &self,
        assert_op: &AssertOp,
        lookup_var: &dyn Fn(usize) -> AB::Var,
    ) -> AB::Expr
    where
        AB::F: Field + PrimeCharacteristicRing,
    {
        match assert_op.op_type.as_str() {
            "add" => {
                Self::lower_expr::<AB>(&assert_op.lhs, lookup_var)
                    + Self::lower_expr::<AB>(&assert_op.rhs, lookup_var)
            }
            "mul" => {
                Self::lower_expr::<AB>(&assert_op.lhs, lookup_var)
                    * Self::lower_expr::<AB>(&assert_op.rhs, lookup_var)
            }
            _ => panic!("Unsupported operation type: {}", assert_op.op_type),
        }
    }

    /// Recursively find all lookup operations
    fn find_lookup_ops(&self, ops: &[CircuitOp]) -> Vec<LookupOp> {
        let mut lookup_ops = Vec::new();
        for op in ops {
            match op {
                CircuitOp::Lookup { lookup } => {
                    lookup_ops.push(lookup.clone());
                }
                CircuitOp::Subcircuit { subcircuit } => {
                    lookup_ops.extend(self.find_lookup_ops(subcircuit));
                }
                _ => {}
            }
        }
        lookup_ops
    }

    pub fn lookup_ops(&self) -> Vec<LookupOp> {
        let ops = self.ops.iter().flat_map(|op| match op {
            CleanOp::Boundary { context, .. } => context.circuit.clone(),
            CleanOp::EveryRowExceptLast { context, .. } => context.circuit.clone(),
        });
        self.find_lookup_ops(&ops.collect::<Vec<_>>())
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
    Clean(MainAir<F>),
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
            CleanAirInstance::Clean(air) => air.width(),
            CleanAirInstance::ByteRange(air) => air.width(),
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            CleanAirInstance::Clean(air) => air.preprocessed_trace(),
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
            CleanAirInstance::Clean(air) => air.eval(builder),
            CleanAirInstance::ByteRange(air) => air.eval(builder),
        };
    }
}

#[derive(Clone)]
pub struct Table<F: Field> {
    pub air: CleanAirInstance<F>,
    pub trace: RowMajorMatrix<F>,
    /// lookups as pairs of (Lookup, is_send)
    lookups: Vec<(Lookup<VirtualPairCol<F>>, bool)>,
}

impl<F: Field> Table<F> {
    /// Create a new CleanAirWrapper that pre-builds the lookups using LookupBuilder
    pub fn new(json_content: &str, trace: RowMajorMatrix<F>) -> Self {
        let inner = CleanAirInstance::Clean(MainAir::new(json_content, trace.width()));
        let main_trace = trace.clone();

        Self::from_instance(inner, main_trace)
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
            CleanAirInstance::Clean(air) => {
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
        if let CleanAirInstance::Clean(air) = &self.air {
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