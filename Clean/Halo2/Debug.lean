import Clean.Halo2.Pinned

namespace Halo2.Pinned.Debug

open Halo2.Pinned

private def indent (n : Nat) : String := String.ofList (List.replicate n ' ')

private def lines (xs : List String) : String := String.intercalate "\n" xs

private def rot : Rotation → String
  | .rot i => s!"Rotation(\n{indent 12}{i},\n{indent 8})"

private def columnKind : ColumnKind → String
  | .Advice => "Advice"
  | .Fixed => "Fixed"
  | .Instance => "Instance"

private def column (n : Nat) (c : Column) : String := lines [
  indent n ++ "Column {",
  s!"{indent (n+4)}index: {c.index},",
  s!"{indent (n+4)}column_type: {columnKind c.columnType},",
  indent n ++ "}"
]

private def rotationBlock (n : Nat) : Rotation → String
  | .rot i => lines [
      s!"{indent n}Rotation(",
      s!"{indent (n+4)}{i},",
      s!"{indent n}),"
    ]

partial def expr (n : Nat) : Expression → String
  | .constant c => lines [s!"{indent n}Constant(", s!"{indent (n+4)}{c},", s!"{indent n})"]
  | .selector idx => lines [s!"{indent n}Selector(", s!"{indent (n+4)}{idx},", s!"{indent n})"]
  | .fixed qi ci r => query n "Fixed" qi ci r
  | .advice qi ci r => query n "Advice" qi ci r
  | .instance qi ci r => query n "Instance" qi ci r
  | .negated e => lines [s!"{indent n}Negated(", expr (n+4) e ++ ",", s!"{indent n})"]
  | .sum a b => binary n "Sum" a b
  | .product a b => binary n "Product" a b
  | .scaled e c => lines [s!"{indent n}Scaled(", expr (n+4) e ++ ",", s!"{indent (n+4)}{c},", s!"{indent n})"]
where
  query (n : Nat) (kind : String) (qi ci : Nat) (r : Rotation) : String := lines [
    indent n ++ kind ++ " {",
    s!"{indent (n+4)}query_index: {qi},",
    s!"{indent (n+4)}column_index: {ci},",
    s!"{indent (n+4)}rotation: {rotationInline (n+4) r}",
    indent n ++ "}"
  ]
  rotationInline (n : Nat) : Rotation → String
    | .rot i => lines ["Rotation(", s!"{indent (n+4)}{i},", s!"{indent n})"]
  binary (n : Nat) (name : String) (a b : Expression) : String := lines [
    s!"{indent n}{name}(",
    expr (n+4) a ++ ",",
    expr (n+4) b ++ ",",
    s!"{indent n})"
  ]

private def queryPair (n : Nat) (q : Column × Rotation) : String := lines [
  s!"{indent n}(",
  column (n+4) q.1 ++ ",",
  rotationBlock (n+4) q.2,
  s!"{indent n}),"
]

private def columnEntry (n : Nat) (c : Column) : String := column n c ++ ","

private def exprEntry (n : Nat) (e : Expression) : String := expr n e ++ ","

private def listBlock (n : Nat) (name : String) (entries : List String) : String :=
  lines ([s!"{indent n}{name}: ["] ++ entries ++ [s!"{indent n}],"])

private def lookup (n : Nat) (l : LookupArgument) : String := lines [
  indent n ++ "Argument {",
  listBlock (n+4) "input_expressions" (l.inputExpressions.map (exprEntry (n+8))),
  listBlock (n+4) "table_expressions" (l.tableExpressions.map (exprEntry (n+8))),
  s!"{indent n}}},"
]

private def permutation (n : Nat) (p : PermutationArgument) : String := lines [
  indent n ++ "permutation: Argument {",
  listBlock (n+4) "columns" (p.columns.map (columnEntry (n+8))),
  s!"{indent n}}},"
]

/-- Render a pinned CS in the same broad pretty-debug shape as halo2_proofs. -/
def constraintSystem (cs : ConstraintSystem) : String := lines [
  "cs: PinnedConstraintSystem {",
  s!"        num_fixed_columns: {cs.numFixedColumns},",
  s!"        num_advice_columns: {cs.numAdviceColumns},",
  s!"        num_instance_columns: {cs.numInstanceColumns},",
  s!"        num_selectors: {cs.numSelectors},",
  listBlock 8 "gates" (cs.gates.map (exprEntry 12)),
  listBlock 8 "advice_queries" (cs.adviceQueries.map (queryPair 12)),
  listBlock 8 "instance_queries" (cs.instanceQueries.map (queryPair 12)),
  listBlock 8 "fixed_queries" (cs.fixedQueries.map (queryPair 12)),
  permutation 8 cs.permutation,
  listBlock 8 "lookups" (cs.lookups.map (lookup 12)),
  listBlock 8 "constants" (cs.constants.map (columnEntry 12)),
  s!"        minimum_degree: {match cs.minimumDegree with | none => "None" | some n => s!"Some({n})"},",
  "    },"
]

end Halo2.Pinned.Debug
