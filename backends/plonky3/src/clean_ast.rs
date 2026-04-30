use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use p3_air::AirBuilder;
use p3_field::{Field, PrimeCharacteristicRing};
use serde::Deserialize;

/// Represents boundary row types for JSON deserialization
#[derive(Clone, Debug, Deserialize)]
#[serde(from = "i32")]
pub enum BoundaryRow {
    FirstRow,
    LastRow,
}

impl From<i32> for BoundaryRow {
    fn from(value: i32) -> Self {
        match value {
            0 => BoundaryRow::FirstRow,
            -1 => BoundaryRow::LastRow,
            _ => panic!(
                "Invalid boundary row value: {}. Expected 0 (FirstRow) or -1 (LastRow)",
                value
            ),
        }
    }
}

/// Operations defined in the clean JSON format
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "type")]
pub enum CleanOp {
    Boundary {
        row: BoundaryRow,
        context: OpContext,
    },
    EveryRowExceptLast {
        context: OpContext,
    },
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
    Pi {
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
pub struct VarLocation {
    pub row: usize,
    pub column: usize,
}

/// Which rows a lookup applies to during trace generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LookupRowScope {
    /// Lookup applies only on row 0.
    FirstRow,
    /// Lookup applies only on the last row (height - 1).
    LastRow,
    /// Lookup applies on rows 0..height-1 (all except last).
    EveryRowExceptLast,
}

impl LookupRowScope {
    /// Whether this scope is active on the given row of a trace with `height` rows.
    pub fn is_active(self, row_idx: usize, height: usize) -> bool {
        if height == 0 {
            return false;
        }
        match self {
            LookupRowScope::FirstRow => row_idx == 0,
            LookupRowScope::LastRow => row_idx == height - 1,
            LookupRowScope::EveryRowExceptLast => row_idx < height - 1,
        }
    }
}

/// AST expression utilities
pub struct AstUtils;

impl AstUtils {
    /// Convert ExprNode to AirBuilder::Expr
    pub fn lower_expr<AB: AirBuilder>(
        expr: &ExprNode,
        var_fn: &dyn Fn(usize) -> AB::Var,
        pi_fn: &dyn Fn(usize) -> AB::Expr,
    ) -> AB::Expr
    where
        AB::F: Field + PrimeCharacteristicRing,
    {
        match expr {
            ExprNode::Var { index } => var_fn(*index).into(),
            ExprNode::Pi { index } => pi_fn(*index),
            ExprNode::Const { value } => AB::F::from_u64(*value).into(),
            ExprNode::Add { lhs, rhs } => {
                Self::lower_expr::<AB>(lhs, var_fn, pi_fn)
                    + Self::lower_expr::<AB>(rhs, var_fn, pi_fn)
            }
            ExprNode::Mul { lhs, rhs } => {
                Self::lower_expr::<AB>(lhs, var_fn, pi_fn)
                    * Self::lower_expr::<AB>(rhs, var_fn, pi_fn)
            }
        }
    }

    /// Convert AssertOp to AB::Expr
    pub fn to_expr<AB: AirBuilder>(
        assert_op: &AssertOp,
        lookup_var: &dyn Fn(usize) -> AB::Var,
        lookup_pi: &dyn Fn(usize) -> AB::Expr,
    ) -> AB::Expr
    where
        AB::F: Field + PrimeCharacteristicRing,
    {
        match assert_op.op_type.as_str() {
            "add" => {
                Self::lower_expr::<AB>(&assert_op.lhs, lookup_var, lookup_pi)
                    + Self::lower_expr::<AB>(&assert_op.rhs, lookup_var, lookup_pi)
            }
            "mul" => {
                Self::lower_expr::<AB>(&assert_op.lhs, lookup_var, lookup_pi)
                    * Self::lower_expr::<AB>(&assert_op.rhs, lookup_var, lookup_pi)
            }
            _ => panic!("Unsupported operation type: {}", assert_op.op_type),
        }
    }

    /// Recursively find all lookup operations
    pub fn find_lookup_ops(ops: &[CircuitOp]) -> Vec<LookupOp> {
        let mut lookup_ops = Vec::new();
        for op in ops {
            match op {
                CircuitOp::Lookup { lookup } => {
                    lookup_ops.push(lookup.clone());
                }
                CircuitOp::Subcircuit { subcircuit } => {
                    lookup_ops.extend(Self::find_lookup_ops(subcircuit));
                }
                _ => {}
            }
        }
        lookup_ops
    }
}

/// Clean operations handler that manages a collection of CleanOp instances
#[derive(Clone, Debug)]
pub struct CleanOps {
    ops: Vec<CleanOp>,
}

impl CleanOps {
    /// Create a new CleanOps instance from JSON content
    pub fn from_json(json_content: &str) -> Self {
        let ops: Vec<CleanOp> = serde_json::from_str(json_content).expect("Failed to parse JSON");
        Self { ops }
    }

    /// Create a new CleanOps instance from a vector of operations
    pub fn new(ops: Vec<CleanOp>) -> Self {
        Self { ops }
    }

    /// Get reference to the operations
    pub fn ops(&self) -> &[CleanOp] {
        &self.ops
    }

    /// Get all lookup operations paired with their assignment context and row scope.
    /// This is needed for expression-based lookups where var indices must
    /// be resolved to trace columns via the assignment.
    pub fn lookup_ops_with_assignments(&self) -> Vec<(LookupOp, Assignment, LookupRowScope)> {
        let mut result = Vec::new();
        for op in &self.ops {
            let (context, scope) = match op {
                CleanOp::Boundary { row: BoundaryRow::FirstRow, context } =>
                    (context, LookupRowScope::FirstRow),
                CleanOp::Boundary { row: BoundaryRow::LastRow, context } =>
                    (context, LookupRowScope::LastRow),
                CleanOp::EveryRowExceptLast { context } =>
                    (context, LookupRowScope::EveryRowExceptLast),
            };
            let lookups = AstUtils::find_lookup_ops(&context.circuit);
            for lookup in lookups {
                result.push((lookup, context.assignment.clone(), scope));
            }
        }
        result
    }
}
