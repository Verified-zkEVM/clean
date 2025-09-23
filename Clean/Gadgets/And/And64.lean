import Clean.Utils.Primes
import Clean.Circuit.Subcircuit
import Clean.Types.U64
import Clean.Gadgets.And.And8

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.And.And64
structure Inputs (F : Type) where
  x: U64 F
  y: U64 F

instance : ProvableStruct Inputs where
  components := [U64, U64]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var Inputs (F p)) : Circuit sentences (Var U64 (F p))  := do
  let ⟨x, y⟩ := input
  let z0 ← And8.circuit order ⟨ x.x0, y.x0 ⟩
  let z1 ← And8.circuit order ⟨ x.x1, y.x1 ⟩
  let z2 ← And8.circuit order ⟨ x.x2, y.x2 ⟩
  let z3 ← And8.circuit order ⟨ x.x3, y.x3 ⟩
  let z4 ← And8.circuit order ⟨ x.x4, y.x4 ⟩
  let z5 ← And8.circuit order ⟨ x.x5, y.x5 ⟩
  let z6 ← And8.circuit order ⟨ x.x6, y.x6 ⟩
  let z7 ← And8.circuit order ⟨ x.x7, y.x7 ⟩
  return U64.mk z0 z1 z2 z3 z4 z5 z6 z7

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : Inputs (F p)) :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : Inputs (F p)) (z : U64 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value &&& y.value ∧ z.Normalized

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs U64 where
  main := main order
  localLength _ := 8
  output _ i := varFromOffset U64 i
  yields _ _ _ := ∅
  yields_eq := by
    intros env input offset
    simp only [circuit_norm, main, ElaboratedCircuit.yields_eq]
    simp [And8.circuit, circuit_norm]

omit [Fact (Nat.Prime p)] p_large_enough in
theorem soundness_to_u64 {sentences : PropertySet (F p)} {x y z : U64 (F p)}
  (x_norm : x.Normalized) (y_norm : y.Normalized)
  (h_eq :
    z.x0.val = x.x0.val &&& y.x0.val ∧
    z.x1.val = x.x1.val &&& y.x1.val ∧
    z.x2.val = x.x2.val &&& y.x2.val ∧
    z.x3.val = x.x3.val &&& y.x3.val ∧
    z.x4.val = x.x4.val &&& y.x4.val ∧
    z.x5.val = x.x5.val &&& y.x5.val ∧
    z.x6.val = x.x6.val &&& y.x6.val ∧
    z.x7.val = x.x7.val &&& y.x7.val) : Spec (sentences := sentences) ∅ { x, y } z := by
  simp only [Spec]
  have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := x_norm
  have ⟨ hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7 ⟩ := y_norm

  have z_norm : z.Normalized := by
    simp only [U64.Normalized, h_eq]
    exact ⟨ Nat.and_lt_two_pow (n:=8) _ hy0, Nat.and_lt_two_pow (n:=8) _ hy1,
      Nat.and_lt_two_pow (n:=8) _ hy2, Nat.and_lt_two_pow (n:=8) _ hy3,
      Nat.and_lt_two_pow (n:=8) _ hy4, Nat.and_lt_two_pow (n:=8) _ hy5,
      Nat.and_lt_two_pow (n:=8) _ hy6, Nat.and_lt_two_pow (n:=8) _ hy7 ⟩

  suffices z.value = x.value &&& y.value from ⟨ this, z_norm ⟩
  simp only [U64.value_xor_horner, x_norm, y_norm, z_norm, h_eq]
  repeat rw [and_xor_sum]
  repeat assumption

theorem soundness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro i env state_var checked input_var ⟨ x, y ⟩ h_input h_assumptions h_holds
  cases x; cases y
  constructor
  · -- Prove yielded sentences hold (vacuous - no yields)
    intros s
    simp [elaborated]
  apply soundness_to_u64 (sentences:=sentences) h_assumptions.left h_assumptions.right
  simp only [circuit_norm, explicit_provable_type, Vector.mapRange,
    elaborated, main, Assumptions, And8.circuit, And8.Assumptions, And8.Spec,
    U64.Normalized] at h_assumptions h_holds h_input ⊢
  simp_all

theorem completeness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  intro i env yielded input_var h_env ⟨ x, y ⟩ h_input h_assumptions
  cases x; cases y
  simp only [circuit_norm, explicit_provable_type,
    elaborated, main, And8.circuit, And8.CompletenessAssumptions, And8.Assumptions] at h_input ⊢
  simp only [CompletenessAssumptions, Assumptions, U64.Normalized] at h_assumptions
  simp_all

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order Inputs U64 where
  elaborated := elaborated order
  Assumptions := Assumptions
  CompletenessAssumptions := CompletenessAssumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness
  completenessAssumptions_implies_assumptions := fun _ _ h => h

end Gadgets.And.And64
