import Clean.Utils.Field
import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

section
variable (N : ℕ+) (p : ℕ) [Fact p.Prime]

/-
  A LookupArgument is an assumption on the inputs to a constraint. For now this is represented
  as a function that takes the inputs and returns a Prop.
  TODO: replace with an actual structure, maybe a class as below for Constraint
-/
structure LookupArgument (N: ℕ+) (M : ℕ) where
  prop : TraceOfLength N M (F p) -> Prop

/-
  A ConstraintGadget is a constraint that can be instantiated with a specific set of inputs.
  It is composed of
  - polys: the list of (multivariate) polynomials that make up the constraint, implicitly the
        constraint holds if all of these polynomials evaluate to 0
  - lookups: the list of lookup arguments that are assumed to hold for the inputs
  - subConstraints: the list of sub-constraints that are instantiated by this constraint
-/
inductive ConstraintGadget (N: ℕ+) (M: ℕ) where
    | mk
    (polys : List (Expression N M (F p)))
    (lookups : List (LookupArgument p N M))
    (subConstraints : List (ConstraintGadget N M))

-- compute the full set of constraints that are implied by this constraint
def fullConstraintSet {N: ℕ+} {M : ℕ} {p : ℕ} [Fact p.Prime] (x : ConstraintGadget p N M) : List (Expression N M (F p)) :=
  match x with
    | ⟨polys, _, subConstraints⟩ => polys ++ (foldl [] subConstraints)
where
  foldl : List (Expression N M (F p)) → List (ConstraintGadget p N M) → List (Expression N M (F p))
    | arr, [] => arr
    | arr, (t :: ts) => foldl (arr ++ fullConstraintSet t) ts

-- compute the full set of lookup arguments that are implied by this constraint
@[simp]
def fullLookupSet {N : ℕ+} {M : ℕ} {p : ℕ} [Fact p.Prime] (x : ConstraintGadget p N M) : List (LookupArgument p N M) :=
  match x with
    | ⟨_, lookups, subConstraints⟩ => lookups ++ (foldl [] subConstraints)
where
  foldl : List (LookupArgument p N M) → List (ConstraintGadget p N M) → List (LookupArgument p N M)
    | arr, [] => arr
    | arr, (t :: ts) => foldl (arr ++ fullLookupSet t) ts

@[simp]
def forallList {α : Type} (v : List α) (p : α -> Prop) : Prop :=
  match v with
  | [] => true
  | (x::xs) => p x ∧ forallList xs p

def constraints_hold {p M: ℕ} {N: ℕ+} [Fact p.Prime] (circuit : ConstraintGadget p N M) (trace : TraceOfLength N M (F p)) :=
  (forallList (fullConstraintSet circuit) (fun constraint => trace.eval constraint = 0))

/-
  A Constraint is a typeclass that packages the definition of the circuit together with its higher
  level specification.
  The equivalence theorem states that the full set of constraints implied by the circuit
  is satisfied if and only if the spec is satisfied, given as assumptions the lookups.
-/
class Constraint (N : ℕ+) (M : ℕ) (p : ℕ) [Fact p.Prime] :=
    -- the constraints
    (circuit : ConstraintGadget p N M)

    -- specification
    (spec : TraceOfLength N M (F p) -> Prop)

    -- equivalence theorem
    (equiv :
      (∀ X : TraceOfLength N M (F p),
        (forallList (fullLookupSet circuit) (fun lookup => lookup.prop X))
        -> (
          (forallList (fullConstraintSet circuit) (fun constraint => X.eval constraint = 0))
          ↔
          spec X
        )
      ))

/--
  Compute an equivalent representation of the conjunction of all the constraints propositions,
  which is more convenient for sub-gadget rewriting.
  Suppose we have two sub-gadgets x and y, and they have as constraints respectively [cx0, cx1] and [cy0, cy1].
  Then the full constraint set of the gadget that combines x and y is cx0 ∧ cx1 ∧ cy0 ∧ cy1.
  What this function does is computing the conjunction but with the grouping (cx0 ∧ cx1) ∧ (cy0 ∧ cy1).
  But only at top level, so it doesn't recurse and apply the grouping into sub-gadgets.
-/
@[simp]
def fullConstraintSetGrouped {N: ℕ+} {M : ℕ} {p : ℕ} [Fact p.Prime]
    (x : ConstraintGadget p N M) (f : Expression N M (F p) -> Prop) : Prop :=
  match x with
    | ⟨polys, _, subConstraints⟩ => (forallList polys f) ∧ (foldl subConstraints)
where
  foldl : List (ConstraintGadget p N M) → Prop
    | [] => true
    | (t :: ts) => (forallList (fullConstraintSet t) f) ∧ (foldl ts)

-- the equivalence theorem for the grouped constraint set
theorem fullConstraintSetGroupedEquivalence {N: ℕ+} {M : ℕ} {p : ℕ} [Fact p.Prime]
    (x : ConstraintGadget p N M) (f : Expression N M (F p) -> Prop) :
  (forallList (fullConstraintSet x) f) ↔ fullConstraintSetGrouped x f :=
  match x with
    | ⟨polys, _, subConstraints⟩ => sorry

end
