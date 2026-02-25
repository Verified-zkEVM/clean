use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use p3_air::lookup::{Direction, Kind, Lookup, LookupInput};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PermutationAirBuilder};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::{SymbolicAirBuilder, SymbolicExpression};

use crate::clean_ast::{
    AstUtils, BoundaryRow, CircuitOp, CleanOp, CleanOps, LookupOp, LookupRow, LookupRowScope,
};
use crate::PreprocessedTableAir;

#[derive(Clone)]
pub struct MainAir<F>
where
    F: Field,
{
    /// Imported clean operations
    clean_ops: CleanOps,
    /// Width of the trace
    width: usize,
    /// Number of registered lookups (for add_lookup_columns)
    num_lookups: usize,
    /// Row scope for each lookup, parallel to the lookups vec from get_lookups
    pub lookup_row_scopes: Vec<LookupRowScope>,
    /// Preprocessed selector columns for lookup row scopes (0/1 values)
    preprocessed: Option<RowMajorMatrix<F>>,
    /// Maps each LookupRowScope to its preprocessed column index
    scope_to_prep_col: BTreeMap<LookupRowScope, usize>,
}

impl<F: Field> BaseAir<F> for MainAir<F> {
    fn width(&self) -> usize {
        self.width
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        self.preprocessed.clone()
    }
}

impl<AB: AirBuilderWithPublicValues> Air<AB> for MainAir<AB::F>
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
                        let var = &context.assignment.vars[var_idx];
                        match var.row {
                            0 => local[var.column].clone(),
                            _ => panic!("Invalid row index: {}", var.row),
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
                        let var = &context.assignment.vars[var_idx];
                        match var.row {
                            0 => local[var.column].clone(),
                            1 => next[var.column].clone(),
                            _ => panic!("Invalid row index: {}", var.row),
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

        // Lookup constraints are NOT applied here - they are handled via
        // eval_with_lookups / LogUpGadget.
    }

    /// Build lookup descriptors for the main AIR.
    ///
    /// Groups all lookup sends by table name and creates one global Lookup
    /// per table, with Direction::Receive (main AIR reads from tables).
    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>
    where
        AB: PermutationAirBuilder + AirBuilderWithPublicValues,
    {
        self.num_lookups = 0;
        let prep_width = self.scope_to_prep_col.len();
        let symbolic_builder =
            SymbolicAirBuilder::<AB::F>::new(prep_width, self.width, 0, 0, 0);
        let symbolic_main = AirBuilder::main(&symbolic_builder);
        let symbolic_main_local = symbolic_main.row_slice(0).unwrap();

        let ops_with_assignments = self.clean_ops.lookup_ops_with_assignments();

        if ops_with_assignments.is_empty() {
            self.lookup_row_scopes = Vec::new();
            return Vec::new();
        }

        let symbolic_prep = AirBuilder::preprocessed(&symbolic_builder).unwrap();
        let symbolic_prep_local = symbolic_prep.row_slice(0).unwrap();

        // Group by (table_name, scope)
        let mut lookups_by_key: BTreeMap<(String, LookupRowScope), Vec<LookupInput<AB::F>>> =
            BTreeMap::new();

        for (lookup_op, assignment, scope) in &ops_with_assignments {
            let load_var = |var_idx: usize| -> p3_uni_stark::SymbolicVariable<AB::F> {
                let var = &assignment.vars[var_idx];
                symbolic_main_local[var.column]
            };
            let load_pi = |_pi_idx: usize| -> SymbolicExpression<AB::F> {
                panic!("Pi not supported in lookups")
            };

            let values: Vec<SymbolicExpression<AB::F>> = lookup_op
                .entry
                .iter()
                .map(|e| AstUtils::lower_expr::<SymbolicAirBuilder<AB::F>>(e, &load_var, &load_pi))
                .collect();

            // Use preprocessed 0/1 selector column as multiplicity filter.
            // Lagrange selectors (is_first_row, is_last_row, is_transition) are NOT
            // normalized and cannot be used as multiplicity filters for Kind::Global
            // lookups — see p3_air::lookup comment.  Preprocessed columns are proper
            // committed polynomials and work correctly at the OOD evaluation point.
            let col_idx = self.scope_to_prep_col[scope];
            let mult: SymbolicExpression<AB::F> = symbolic_prep_local[col_idx].into();
            let input: LookupInput<AB::F> = (values, mult, Direction::Receive);

            lookups_by_key
                .entry((lookup_op.table.clone(), *scope))
                .or_default()
                .push(input);
        }

        // Create one Lookup per (table, scope) group
        let mut lookups = Vec::new();
        let mut scopes = Vec::new();
        for ((table_name, scope), inputs) in lookups_by_key {
            lookups.push(Air::<AB>::register_lookup(self, Kind::Global(table_name), &inputs));
            scopes.push(scope);
        }
        self.lookup_row_scopes = scopes;

        lookups
    }

    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }
}

impl<F: Field> MainAir<F> {
    /// Create a new MainAir instance from JSON content and trace data
    pub fn new(json_content: &str, width: usize, trace_height: usize) -> Self {
        let clean_ops = CleanOps::from_json(json_content);
        Self::build(clean_ops, width, trace_height)
    }

    /// Create a new MainAir instance from CleanOps and trace data
    pub fn from_ops(clean_ops: CleanOps, width: usize, trace_height: usize) -> Self {
        Self::build(clean_ops, width, trace_height)
    }

    fn build(clean_ops: CleanOps, width: usize, trace_height: usize) -> Self {
        // Collect distinct scopes used in lookups
        let ops_with_assignments = clean_ops.lookup_ops_with_assignments();
        let mut scope_to_prep_col: BTreeMap<LookupRowScope, usize> = BTreeMap::new();
        for (_, _, scope) in &ops_with_assignments {
            scope_to_prep_col.entry(*scope).or_insert(0);
        }
        // Reassign column indices in deterministic BTreeMap key order
        for (i, (_, v)) in scope_to_prep_col.iter_mut().enumerate() {
            *v = i;
        }

        let num_prep_cols = scope_to_prep_col.len();
        let preprocessed = if num_prep_cols > 0 && trace_height > 0 {
            let mut data = vec![F::ZERO; trace_height * num_prep_cols];
            for (&scope, &col_idx) in &scope_to_prep_col {
                for row_idx in 0..trace_height {
                    let active = match scope {
                        LookupRowScope::FirstRow => row_idx == 0,
                        LookupRowScope::LastRow => row_idx == trace_height - 1,
                        LookupRowScope::EveryRowExceptLast => row_idx < trace_height - 1,
                    };
                    if active {
                        data[row_idx * num_prep_cols + col_idx] = F::ONE;
                    }
                }
            }
            Some(RowMajorMatrix::new(data, num_prep_cols))
        } else {
            None
        };

        Self {
            clean_ops,
            width,
            num_lookups: 0,
            lookup_row_scopes: Vec::new(),
            preprocessed,
            scope_to_prep_col,
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

    /// Process circuit operations and apply constraints
    fn apply_clean_constraints<AB>(
        &self,
        ops: &[CircuitOp],
        load_var: &dyn Fn(usize) -> AB::Var,
        load_pi: &dyn Fn(usize) -> AB::Expr,
        constraint_builder: &mut dyn FnMut(AB::Expr),
    ) where
        AB: AirBuilder + AirBuilderWithPublicValues,
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
                        subcircuit,
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

    /// Returns the row scopes for each lookup (parallel to the lookups vec).
    pub fn lookup_row_scopes(&self) -> Vec<LookupRowScope> {
        match self {
            CleanAirInstance::Main(air) => air.lookup_row_scopes.clone(),
            CleanAirInstance::Preprocessed(_) => vec![],
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
    AB: AirBuilder + AirBuilderWithPublicValues,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            CleanAirInstance::Main(air) => air.eval(builder),
            CleanAirInstance::Preprocessed(air) => air.eval(builder),
        };
    }

    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>
    where
        AB: PermutationAirBuilder + AirBuilderWithPublicValues,
    {
        match self {
            CleanAirInstance::Main(air) => Air::<AB>::get_lookups(air),
            CleanAirInstance::Preprocessed(air) => Air::<AB>::get_lookups(air),
        }
    }

    fn add_lookup_columns(&mut self) -> Vec<usize> {
        match self {
            CleanAirInstance::Main(air) => Air::<AB>::add_lookup_columns(air),
            CleanAirInstance::Preprocessed(air) => Air::<AB>::add_lookup_columns(air),
        }
    }
}
