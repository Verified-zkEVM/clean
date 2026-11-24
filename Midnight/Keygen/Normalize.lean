import Clean.Halo2.Keygen.Projection

/-! Rust's `Expression` operators fold literal zeros and ones (`circuit.rs` `Add`, `Mul`), and
`replace_selectors_with_fixed` rebuilds every gate, lookup and trash expression through them,
so a pinned constraint system holds only their normal forms. `Neg` and `Mul<F>` never fold. -/

namespace Halo2.RichExpression
variable {F : Type} [CommRing F] [DecidableEq F]

/-- Rust's `Expression + Expression`. -/
def foldAdd (a b : RichExpression F) : RichExpression F :=
  if a = .constant 0 then b else if b = .constant 0 then a else .sum a b

/-- Rust's `Expression * Expression`. -/
def foldMul (a b : RichExpression F) : RichExpression F :=
  if a = .constant 0 ∨ b = .constant 0 then .constant 0
  else if a = .constant 1 then b else if b = .constant 1 then a else .product a b

/-- The tree Rust's operators build from these nodes. -/
def normalize : RichExpression F → RichExpression F
  | .negated a => .negated a.normalize
  | .sum a b => foldAdd a.normalize b.normalize
  | .product a b => foldMul a.normalize b.normalize
  | .scaled a c => .scaled a.normalize c
  | e => e

/-- Rust's `Expression::degree`. -/
def degree : RichExpression F → Nat
  | .constant _ => 0
  | .negated a | .scaled a _ => a.degree
  | .sum a b => max a.degree b.degree
  | .product a b => a.degree + b.degree
  | _ => 1

end Halo2.RichExpression
