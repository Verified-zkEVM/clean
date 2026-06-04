/-
This file provides the built-in `assertEquals` gadget, which works for any provable type
and smoothly simplifies to an equality statement under `circuit_norm`.
-/
import Clean.Circuit.Loops
import Clean.Circuit.Explicit

variable {F : Type} [Field F] {M : TypeMap} [ProvableType M]

namespace Gadgets
def allZero {n} (xs : Vector (Expression F) n) : Circuit F Unit := .forEach xs assertZero

theorem allZero.soundness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    ConstraintsHold.Soundness env ((allZero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  simp only [allZero, circuit_norm]
  intro h_holds x hx
  obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hx
  exact h_holds ⟨i, hi⟩

theorem allZero.completeness {offset : ℕ} {env : ProverEnvironment F} {n} {xs : Vector (Expression F) n} :
    (∀ x ∈ xs, x.eval env = 0) →
    ConstraintsHold.Completeness env ((allZero xs).operations offset) := by
  simp only [allZero, circuit_norm]
  intro h_holds i
  exact h_holds xs[i] (Vector.mem_of_getElem rfl)

namespace Equality
def main (input : Var M F × Var M F) : Circuit F Unit := do
  let (x, y) := input
  let diffs := (toElements (M:=M) x).zip (toElements y) |>.map (fun (xi, yi) => xi - yi)
  .forEach diffs assertZero

@[reducible]
instance elaborated (M : TypeMap) [ProvableType M] : ElaboratedCircuit F (ProvablePair M M) unit main := by
  elaborate_circuit

@[simps! (attr := circuit_norm) (config := {isSimp := false})]
def circuit (M : TypeMap) [ProvableType M] : FormalAssertion F (ProvablePair M M) where
  main

  Spec : M F × M F → Prop
  | (x, y) => x = y

  soundness := by
    intro offset env input_var input h_input _ h_holds
    replace h_holds := allZero.soundness h_holds
    simp only at h_holds
    constructor; swap
    · simp only [main, circuit_norm]

    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy]
    simp only [CircuitType.eval_expression, ProvableType.eval]
    congr 1
    ext i hi
    simp only [Vector.getElem_map]

    rw [←Vector.forall_getElem] at h_holds
    specialize h_holds i hi
    rw [Vector.getElem_map, Vector.getElem_zip] at h_holds
    simp only [Expression.eval] at h_holds
    rw [neg_one_mul] at h_holds
    exact eq_of_add_neg_eq_zero h_holds

  completeness := by
    intro offset env input_var h_env input  h_input _ h_spec
    apply allZero.completeness
    simp only

    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy] at h_spec
    clear hx hy
    apply_fun toElements at h_spec
    simp only [CircuitType.eval_expression, ProvableType.eval,
      ProvableType.toElements_fromElements] at h_spec
    rw [Vector.ext_iff] at h_spec

    rw [←Vector.forall_getElem]
    intro i hi
    specialize h_spec i hi
    simp only [Vector.getElem_map] at h_spec
    simp only [Vector.getElem_map, Vector.getElem_zip, Expression.eval, neg_one_mul]
    rw [h_spec]
    ring

-- allow `circuit_norm` to elaborate properties of the `circuit` while keeping main/spec/assumptions opaque
@[circuit_norm ↓, explicit_circuit_norm]
lemma elaborated_eq : (circuit M (F:=F)).elaborated = elaborated M := rfl

@[circuit_norm, explicit_circuit_norm]
lemma localLength_eq (input : Var (ProvablePair M M) F) :
  (circuit M).localLength input = 0 := by simp only [circuit_norm, circuit]
@[circuit_norm, explicit_circuit_norm]
lemma output_eq (input : Var (ProvablePair M M) F) (offset : ℕ) :
  (circuit M).output input offset = () := by simp only [circuit_norm, circuit]
@[circuit_norm, explicit_circuit_norm]
lemma channelsWithGuarantees_eq :
  (circuit M (F:=F)).channelsWithGuarantees = [] := by simp only [circuit_norm, circuit]
@[circuit_norm, explicit_circuit_norm]
lemma channelsWithRequirements_eq :
  (circuit M (F:=F)).channelsWithRequirements = [] := by simp only [circuit_norm, circuit]

-- rewrite spec/proverAssumptions/proverSpec directly

@[circuit_norm]
theorem spec (n : ℕ) (env : Environment F) (x y : Var M F) :
    ((circuit M).toSubcircuit n (x, y)).Spec env = (eval env x = eval env y) := by
  simp only [circuit_norm, circuit]

@[circuit_norm]
theorem proverAssumptions (n : ℕ) (env : ProverEnvironment F) (x y : Var M F) :
    ((circuit M).toSubcircuit n (x, y)).ProverAssumptions env = (eval env x = eval env y) := by
  simp only [circuit_norm, circuit]

@[circuit_norm]
theorem proverSpec (n : ℕ) (env : ProverEnvironment F) (x y : Var M F) :
    ((circuit M).toSubcircuit n (x, y)).ProverSpec env = True := by
  simp only [FormalAssertion.toSubcircuit, circuit]

end Equality
end Gadgets

-- Defines a unified `===` notation for asserting equality in circuits.

@[circuit_norm]
def assertEquals (x y : M (Expression F)) : Circuit F Unit :=
  Gadgets.Equality.circuit M (x, y)

@[circuit_norm, reducible]
def Expression.assertEquals (x y : Expression F) : Circuit F Unit :=
  Gadgets.Equality.circuit id (x, y)

class HasAssertEq (β : Type) (F : outParam Type) [Field F] where
  assert_eq : β → β → Circuit F Unit

instance : HasAssertEq (Expression F) F where
  assert_eq := Expression.assertEquals

instance : HasAssertEq (M (Expression F)) F where
  assert_eq := @assertEquals F _ M _

attribute [circuit_norm] HasAssertEq.assert_eq
infix:50 " === " => HasAssertEq.assert_eq

-- Defines a unified `<==` notation for witness assignment with equality assertion in circuits.

class HasAssignEq (β : Type) (F : outParam Type) [Field F] where
  assignEq : β → Circuit F β

instance : HasAssignEq (Expression F) F where
  assignEq := fun rhs => do
    let witness ← witnessField fun env => rhs.eval env
    witness === rhs
    return witness

instance : HasAssignEq (M (Expression F)) F where
  assignEq := fun rhs => do
    let witness ← ProvableType.witness fun env => eval env rhs
    witness === rhs
    return witness

instance {n : ℕ} : HasAssignEq (Vector (Expression F) n) F :=
  inferInstanceAs (HasAssignEq (fields n (Expression F)) F)

attribute [circuit_norm] HasAssignEq.assignEq

-- Custom syntax to allow `let var <== expr` without monadic arrow
syntax "let " ident " <== " term : doElem
syntax "let " ident " : " term " <== " term : doElem

macro_rules
  | `(doElem| let $x <== $e) => `(doElem| let $x ← HasAssignEq.assignEq $e)
  | `(doElem| let $x : $t <== $e) => `(doElem| let $x : $t ← HasAssignEq.assignEq $e)

-- `ExplicitCircuit` integration

instance {x y : Expression F} : ExplicitCircuit (Expression.assertEquals x y) := inferInstance

instance {x y : M (Expression F)} :
    ExplicitCircuit (assertEquals x y) := inferInstanceAs <|
  ExplicitCircuit (Gadgets.Equality.circuit M (x, y))

instance {x y : M (Expression F)} : ExplicitCircuit (HasAssertEq.assert_eq x y) :=
  inferInstanceAs (ExplicitCircuit (assertEquals x y))

instance {x y : Expression F} : ExplicitCircuit (HasAssertEq.assert_eq x y) :=
  inferInstanceAs (ExplicitCircuit (Expression.assertEquals x y))
