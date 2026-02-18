use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

use crate::clean_ast::{
    AstUtils, BoundaryRow, CircuitOp, CleanOp, CleanOps, LookupOp, LookupRow, VarLocation,
};
use crate::{BaseMessageBuilder, Lookup, PreprocessedTableAir};

#[derive(Clone)]
pub struct MainAir<F>
where
    F: Field,
{
    /// Imported clean operations
    clean_ops: CleanOps,
    /// Width of the trace
    width: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> BaseAir<F> for MainAir<F> {
    fn width(&self) -> usize {
        self.width
    }
}

impl<AB: AirBuilderWithPublicValues + BaseMessageBuilder> Air<AB> for MainAir<AB::F>
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (local, next) = (
            main.row_slice(0).expect("Matrix is empty?"),
            main.row_slice(1).expect("Matrix only has 1 row?"),
        );

        let pi_values = builder.public_values().to_vec();
        let load_pi = |pi_idx: usize| pi_values[pi_idx].into();

        // Build constraints from clean ops
        for op in self.clean_ops.ops() {
            match op {
                CleanOp::Boundary { row, context } => {
                    let load_var = |var_idx: usize| {
                        let var: VarLocation = context.assignment.vars[var_idx].clone();
                        match var {
                            VarLocation::Cell { row, column } => match row {
                                0 => local[column].clone(),
                                _ => panic!("Invalid row index: {}", row),
                            },
                            VarLocation::Aux { .. } => {
                                unreachable!("All aux vars should be already converted to cells")
                            }
                        }
                    };

                    let mut when_boundary = match row {
                        BoundaryRow::FirstRow => builder.when_first_row(),
                        BoundaryRow::LastRow => builder.when_last_row(),
                    };

                    let mut constraint_builder = |expr: AB::Expr| {
                        when_boundary.assert_zero(expr);
                    };

                    self.apply_clean_constraints::<AB>(
                        &context.circuit,
                        &load_var,
                        &load_pi,
                        &mut constraint_builder,
                    );
                }
                CleanOp::EveryRowExceptLast { context } => {
                    let load_var = |var_idx: usize| {
                        let var: VarLocation = context.assignment.vars[var_idx].clone();
                        match var {
                            VarLocation::Cell { row, column } => match row {
                                0 => local[column].clone(),
                                1 => next[column].clone(),
                                _ => panic!("Invalid row index: {}", row),
                            },
                            VarLocation::Aux { .. } => {
                                unreachable!("All aux vars should be already converted to cells")
                            }
                        }
                    };

                    let mut when_transition = builder.when_transition();

                    let mut constraint_builder = |expr: AB::Expr| {
                        when_transition.assert_zero(expr);
                    };

                    self.apply_clean_constraints::<AB>(
                        &context.circuit,
                        &load_var,
                        &load_pi,
                        &mut constraint_builder,
                    );
                }
            }
        }

        // Apply constraints for lookup columns
        self.apply_lookup_constraints(builder, &local, &next);
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
        C: FnMut(LookupRow, usize, &str),
    {
        self.clean_ops.process_lookups(callback)
    }

    pub fn lookup_ops(&self) -> Vec<LookupOp> {
        self.clean_ops.lookup_ops()
    }

    /// Apply lookup constraints for the air.
    /// Uses expression evaluation to support multi-column lookup entries.
    /// Properly resolves row=0 to local and row=1 to next for next-row references.
    fn apply_lookup_constraints<AB>(
        &self,
        builder: &mut AB,
        local: &[AB::Var],
        next: &[AB::Var],
    ) where
        AB: AirBuilder + BaseMessageBuilder,
        AB::F: Field + PrimeCharacteristicRing,
    {
        use alloc::collections::BTreeSet;
        use alloc::string::String;

        let ops_with_assignments = self.clean_ops.lookup_ops_with_assignments();

        // Deduplicate by (table, entry debug repr) to avoid duplicate sends
        let mut seen: BTreeSet<String> = BTreeSet::new();

        for (lookup_op, assignment) in &ops_with_assignments {
            let key = alloc::format!("{}:{:?}", lookup_op.table, lookup_op.entry);
            if !seen.insert(key) {
                continue;
            }

            let load_var = |var_idx: usize| -> AB::Var {
                let var = &assignment.vars[var_idx];
                match var {
                    VarLocation::Cell { row, column } => match *row {
                        0 => local[*column].clone(),
                        1 => next[*column].clone(),
                        _ => panic!("Invalid row index: {}", row),
                    },
                    VarLocation::Aux { .. } => {
                        unreachable!("All aux vars should be already converted to cells")
                    }
                }
            };
            let load_pi = |_pi_idx: usize| -> AB::Expr { panic!("Pi not supported in lookups") };

            let values: Vec<AB::Expr> = lookup_op
                .entry
                .iter()
                .map(|e| AstUtils::lower_expr::<AB>(e, &load_var, &load_pi))
                .collect();

            let mul = AB::F::ONE.into();
            let l = Lookup::new(lookup_op.table.clone(), values, mul);
            builder.send(l);
        }
    }

    /// Process circuit operations and apply constraints
    fn apply_clean_constraints<AB>(
        &self,
        ops: &[CircuitOp],
        load_var: &dyn Fn(usize) -> AB::Var,
        load_pi: &dyn Fn(usize) -> AB::Expr,
        constraint_builder: &mut dyn FnMut(AB::Expr),
    ) where
        AB: AirBuilder + AirBuilderWithPublicValues + BaseMessageBuilder,
        AB::F: Field + PrimeCharacteristicRing,
    {
        for op in ops {
            match op {
                CircuitOp::Assert { assert } => {
                    let expr = AstUtils::to_expr::<AB>(assert, load_var, load_pi);
                    constraint_builder(expr);
                }
                CircuitOp::Subcircuit { subcircuit } => {
                    // Recursively process subcircuit operations
                    self.apply_clean_constraints::<AB>(
                        subcircuit.operations(),
                        load_var,
                        load_pi,
                        constraint_builder,
                    );
                }
                CircuitOp::NamedBlock { operations } => {
                    self.apply_clean_constraints::<AB>(
                        operations,
                        load_var,
                        load_pi,
                        constraint_builder,
                    );
                }
                CircuitOp::Witness { .. } | CircuitOp::Lookup { .. } => {
                    // Witness and lookup operations are handled elsewhere
                }
            }
        }
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
    Preprocessed(PreprocessedTableAir<F>),
}

impl<F: Field> CleanAirInstance<F> {
    /// Returns the table name if this is a preprocessed table AIR.
    pub fn table_name(&self) -> Option<&str> {
        match self {
            CleanAirInstance::Main(_) => None,
            CleanAirInstance::Preprocessed(air) => Some(air.table_name()),
        }
    }
}

impl<F: Field> BaseAir<F> for CleanAirInstance<F> {
    fn width(&self) -> usize {
        match self {
            CleanAirInstance::Main(air) => air.width(),
            CleanAirInstance::Preprocessed(air) => air.width(),
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            CleanAirInstance::Main(air) => air.preprocessed_trace(),
            CleanAirInstance::Preprocessed(air) => air.preprocessed_trace(),
        }
    }
}

impl<AB> Air<AB> for CleanAirInstance<AB::F>
where
    AB: AirBuilder + AirBuilderWithPublicValues + BaseMessageBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            CleanAirInstance::Main(air) => air.eval(builder),
            CleanAirInstance::Preprocessed(air) => air.eval(builder),
        };
    }
}
