/-
This file provides the built-in `assertEquals` gadget, which works for any provable type
and simplifies to an equality statement under `circuit_norm`.
-/
import Clean.Circuit.Loops

variable {F : Type} [Field F]
open Circuit (ConstraintsHold)

namespace Gadgets

def allZero {sentences : PropertySet F} {n} (xs : Vector (Expression F) n) : Circuit sentences Unit :=
  Circuit.forEach xs (body:=assertZero)

theorem allZero.soundness {sentences : PropertySet F} {offset : ℕ} {env : Environment F}
    {yields : YieldContext sentences} {checked : CheckedYields sentences}
    {n} {xs : Vector (Expression F) n} :
    ConstraintsHold.Soundness env yields checked ((allZero (sentences:=sentences) xs).operations offset) →
    ∀ x ∈ xs, x.eval env = 0 := by
  simp only [allZero, circuit_norm]
  intro h_holds x hx
  obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hx
  exact h_holds ⟨i, hi⟩

theorem allZero.completeness {sentences : PropertySet F} {offset : ℕ} {env : Environment F}
    {yields : YieldContext sentences} {n} {xs : Vector (Expression F) n} :
    (∀ x ∈ xs, x.eval env = 0) →
    ConstraintsHold.Completeness env yields ((allZero (sentences:=sentences) xs).operations offset) := by
  simp only [allZero, circuit_norm]
  intro h_holds i
  exact h_holds xs[i] (Vector.mem_of_getElem rfl)

namespace Equality

def main {sentences : PropertySet F} {α : TypeMap} [ProvableType α]
    (input : Var α F × Var α F) : Circuit sentences Unit := do
  let (x, y) := input
  let diffs := (toVars x).zip (toVars y) |>.map (fun (xi, yi) => xi - yi)
  Circuit.forEach diffs (body:=assertZero)

@[reducible]
instance elaborated {sentences : PropertySet F} (α : TypeMap) [ProvableType α] :
    ElaboratedCircuit F sentences (ProvablePair α α) unit where
  main := fun ⟨x, y⟩ => main (sentences:=sentences) (α:=α) (x, y)
  localLength _ := 0
  output _ _ := ()
  localLength_eq _ _ := by simp only [main, circuit_norm, mul_zero]
  subcircuitsConsistent _ := by simp only [main, circuit_norm]

@[simps! (config := {isSimp := false, attrs := [`circuit_norm]})]
def circuit {sentences : PropertySet F} (order : SentenceOrder sentences)
    (α : TypeMap) [ProvableType α] : FormalAssertion order (ProvablePair α α) where
  Assumptions _ := True

  Spec : CheckedYields sentences → α F × α F → Prop
  | _, (x, y) => x = y

  soundness := by
    intro offset env yields checked input_var input h_input _ h_holds
    replace h_holds := allZero.soundness (sentences:=sentences) h_holds
    simp only at h_holds
    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy]
    simp only [eval]
    congr 1
    ext i hi
    simp only [Vector.getElem_map]
    rw [toVars, toVars, ←Vector.forall_getElem] at h_holds
    specialize h_holds i hi
    rw [Vector.getElem_map, Vector.getElem_zip] at h_holds
    simp only [Expression.eval] at h_holds
    rw [neg_one_mul] at h_holds
    exact eq_of_add_neg_eq_zero h_holds

  completeness := by
    intro offset env yields input_var h_env input h_input _ h_spec
    apply allZero.completeness (sentences:=sentences)
    simp only
    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy] at h_spec
    clear hx hy
    apply_fun toElements at h_spec
    simp only [eval, ProvableType.toElements_fromElements, toVars] at h_spec
    rw [Vector.ext_iff] at h_spec
    rw [toVars, toVars, ←Vector.forall_getElem]
    intro i hi
    specialize h_spec i hi
    simp only [Vector.getElem_map] at h_spec
    simp only [Vector.getElem_map, Vector.getElem_zip, Expression.eval, neg_one_mul]
    rw [h_spec]
    ring

-- allow `circuit_norm` to elaborate properties of the `circuit` while keeping main/spec/assumptions opaque
@[circuit_norm ↓]
lemma elaborated_eq {sentences : PropertySet F} (order : SentenceOrder sentences)
    (α : TypeMap) [ProvableType α] :
    (circuit (sentences:=sentences) order α).elaborated = elaborated (sentences:=sentences) α := rfl

-- rewrite soundness/completeness directly

-- convenience lemmas (optional); can be reintroduced if needed

end Equality
end Gadgets

-- A unified `===` notation for asserting equality in circuits.

@[circuit_norm]
def assertEquals {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    {α : TypeMap} [ProvableType α]
    (x y : α (Expression F)) : Circuit sentences Unit :=
  Gadgets.Equality.circuit (F:=F) (sentences:=sentences) order α (x, y)

@[circuit_norm, reducible]
def Expression.assertEquals {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    (x y : Expression F) : Circuit sentences Unit :=
  Gadgets.Equality.circuit (F:=F) (sentences:=sentences) order id (x, y)

class HasAssertEq (β : Type) (F : Type) [Field F]
    (sentences : PropertySet F) (order : SentenceOrder sentences) where
  assert_eq : β → β → Circuit sentences Unit

instance {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences) :
  HasAssertEq (Expression F) F sentences order where
  assert_eq := Expression.assertEquals (F:=F) (sentences:=sentences) order

instance {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    {α : TypeMap} [ProvableType α] :
  HasAssertEq (α (Expression F)) F sentences order where
  assert_eq := @assertEquals F _ sentences order α _

attribute [circuit_norm] HasAssertEq.assert_eq
-- Explicit-order variant only: `x ===[order] y`
syntax:50 term:51 " ===[" term "] " term:51 : term
macro_rules
  | `($x ===[$ord] $y) => `(HasAssertEq.assert_eq (F:=_) (sentences:=_) (order:=$ord) $x $y)

-- A unified `<==` notation for witness assignment with equality assertion in circuits.

class HasAssignEq (β : Type) (F : Type) [Field F]
    (sentences : PropertySet F) (order : SentenceOrder sentences) where
  assignEq : β → Circuit sentences β

instance {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences) :
  HasAssignEq (Expression F) F sentences order where
  assignEq := fun rhs => do
    let witness ← witnessField (sentences:=sentences) (F:=F) (fun env => rhs.eval env)
    Gadgets.Equality.circuit (F:=F) (sentences:=sentences) order id (witness, rhs)
    return witness

instance {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    {α : TypeMap} [ProvableType α] :
  HasAssignEq (α (Expression F)) F sentences order where
  assignEq := fun rhs => do
    let witness ← ProvableType.witness (sentences:=sentences) (F:=F) (fun env => eval env rhs)
    Gadgets.Equality.circuit (F:=F) (sentences:=sentences) order α (witness, rhs)
    return witness

instance {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences) {n : ℕ} :
  HasAssignEq (Vector (Expression F) n) F sentences order :=
  inferInstanceAs (HasAssignEq (fields n (Expression F)) F sentences order)

attribute [circuit_norm] HasAssignEq.assignEq

-- Custom syntax to allow `let var <== expr` without monadic arrow
-- Only explicit-order variants
syntax "let " ident " <==[" term "] " term : doElem
syntax "let " ident " : " term " <==[" term "] " term : doElem

macro_rules
  | `(doElem| let $x <==[$ord] $e) => `(doElem| let $x ← HasAssignEq.assignEq (F:=_) (sentences:=_) (order:=$ord) $e)
  | `(doElem| let $x : $t <==[$ord] $e) => `(doElem| let $x : $t ← HasAssignEq.assignEq (F:=_) (sentences:=_) (order:=$ord) $e)
