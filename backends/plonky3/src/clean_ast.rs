use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use p3_air::AirBuilder;
use p3_field::{Field, PrimeCharacteristicRing};
use serde::Deserialize;

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

/// AST expression utilities
pub struct AstUtils;

impl AstUtils {
    /// Convert ExprNode to AirBuilder::Expr
    pub fn lower_expr<AB: AirBuilder>(
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

    /// Convert AssertOp to AB::Expr
    pub fn to_expr<AB: AirBuilder>(
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

    /// Get all lookup operations from the clean operations
    pub fn lookup_ops(&self) -> Vec<LookupOp> {
        let ops = self.ops.iter().flat_map(|op| match op {
            CleanOp::Boundary { context, .. } => context.circuit.clone(),
            CleanOp::EveryRowExceptLast { context, .. } => context.circuit.clone(),
        });
        AstUtils::find_lookup_ops(&ops.collect::<Vec<_>>())
    }
}