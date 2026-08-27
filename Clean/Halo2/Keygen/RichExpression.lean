import Clean.Halo2.Expression

/-!
# The pinned/verifier gate-polynomial AST

`RichExpression` is the gate (or lookup input/table) polynomial exactly as halo2 evaluates
it during verification (`Expression::evaluate`), with queries as indices into the claimed
evaluations. It mirrors Rust's node shapes for `Expression<F>` in **query-INDEX space** (the
pinned/verifier view): a constant, a fixed/advice/instance query by query index, a
negation / sum / product / scaling, and a (pre-compression only) simple selector by index.

This contrasts with the 4-node `Halo2.Expression` (`var/const/add/mul`) in **query-ATOM
space**, the constraint-authoring language. The VK-matching projection erases the latter
into the former (`Clean.Halo2.Keygen.Projection`).

ironwood keeps its own identical `Expr` (in `Zcash/Common/Expr.lean`): the maintainer ruling
is not to rip a core type out of ironwood; conversion at the boundary is trivial (the
constructors and semantics coincide).
-/

namespace Halo2

/-- A gate (or lookup input/table) polynomial as halo2 evaluates it during verification
(`Expression::evaluate`): a constant, a fixed/advice/instance query (by query index into the
claimed evals), a negation / sum / product / scaling, or a simple selector by index.

Virtual selectors are removed during circuit optimization (`compress_selectors`), so after
compression the `selector` node never appears; it is retained for the pre-compression
projection view. -/
inductive RichExpression (F : Type) where
  | constant : F → RichExpression F
  | fixed : ℕ → RichExpression F
  | advice : ℕ → RichExpression F
  | instance : ℕ → RichExpression F
  | negated : RichExpression F → RichExpression F
  | sum : RichExpression F → RichExpression F → RichExpression F
  | product : RichExpression F → RichExpression F → RichExpression F
  | scaled : RichExpression F → F → RichExpression F
  /-- Pre-compression only: a simple selector, by index. Post-compression this never
  appears (each is substituted by a fixed-column root-finding polynomial). -/
  | selector : ℕ → RichExpression F
deriving DecidableEq, Repr

/-- Carry a gate expression along a ring hom, leaf by leaf. -/
def RichExpression.map {F G : Type} (f : F → G) : RichExpression F → RichExpression G
  | .constant c => .constant (f c)
  | .fixed i => .fixed i
  | .advice i => .advice i
  | .instance i => .instance i
  | .negated e => .negated (e.map f)
  | .sum a b => .sum (a.map f) (b.map f)
  | .product a b => .product (a.map f) (b.map f)
  | .scaled e c => .scaled (e.map f) (f c)
  | .selector i => .selector i

/-- Mapping an expression twice is mapping once along the composite. -/
theorem RichExpression.map_map {F G H : Type} (f : F → G) (g : G → H) (e : RichExpression F) :
    (e.map f).map g = e.map (fun c => g (f c)) := by
  induction e <;> simp_all [RichExpression.map]

/-- Mapping an expression along the identity leaves it unchanged. -/
@[simp] theorem RichExpression.map_id {F : Type} (e : RichExpression F) :
    (e.map fun c => c) = e := by
  induction e <;> simp_all [RichExpression.map]

/-- Evaluate a gate polynomial at the claimed evaluations (halo2 `Expression::evaluate` with
the verifier's closures): queries resolve to `fixedEvals`/`adviceEvals`/`instanceEvals` at
their index. A residual `selector` node (pre-compression only) evaluates to `0`; the
post-compression semantics only evaluate selector-free expressions, so this arm is never
reached there. -/
def RichExpression.eval {F : Type} [CommRing F] (fixedEvals adviceEvals instanceEvals : ℕ → F) :
    RichExpression F → F
  | .constant c => c
  | .fixed i => fixedEvals i
  | .advice i => adviceEvals i
  | .instance i => instanceEvals i
  | .negated a => -(a.eval fixedEvals adviceEvals instanceEvals)
  | .sum a b => a.eval fixedEvals adviceEvals instanceEvals + b.eval fixedEvals adviceEvals instanceEvals
  | .product a b =>
      a.eval fixedEvals adviceEvals instanceEvals * b.eval fixedEvals adviceEvals instanceEvals
  | .scaled a c => a.eval fixedEvals adviceEvals instanceEvals * c
  | .selector _ => 0

end Halo2
