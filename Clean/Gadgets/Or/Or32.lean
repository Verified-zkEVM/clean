import Clean.Circuit.Provable
import Clean.Utils.Tactics
import Clean.Types.U32
import Clean.Gadgets.Or.Or8

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 512)]

namespace Gadgets.Or32
open Gadgets.Or

structure Inputs (F : Type) where
  x : U32 F
  y : U32 F

instance : ProvableStruct Inputs where
  components := [U32, U32]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var Inputs (F p)) : Circuit sentences (Var U32 (F p))  := do
  let ⟨x, y⟩ := input

  let z0 ← Or8.circuit order ⟨x.x0, y.x0⟩
  let z1 ← Or8.circuit order ⟨x.x1, y.x1⟩
  let z2 ← Or8.circuit order ⟨x.x2, y.x2⟩
  let z3 ← Or8.circuit order ⟨x.x3, y.x3⟩

  return ⟨z0, z1, z2, z3⟩

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ||| y.value ∧ z.Normalized

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs U32 where
  main := main order
  localLength _ := 4

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  circuit_proof_start
  have l_components := U32.or_componentwise h_assumptions.1 h_assumptions.2
  rcases input_x
  rcases input_y
  rcases input_var_x
  rcases input_var_y
  simp only [U32.Normalized] at *
  simp only [explicit_provable_type, ProvableType.fromElements_eq_iff, toVars, fromElements] at h_input ⊢ l_components
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.mk.injEq] at h_input ⊢ l_components
  simp only [Or8.circuit, Or8.Assumptions, Or8.Spec, h_input] at h_holds
  rcases h_holds with ⟨h_holds1, h_holds⟩
  specialize h_holds1 (by omega)
  rcases h_holds with ⟨h_holds2, h_holds⟩
  specialize h_holds2 (by omega)
  rcases h_holds with ⟨h_holds3, h_holds4⟩
  specialize h_holds3 (by omega)
  specialize h_holds4 (by omega)
  simp only [U32.value] at ⊢ l_components
  simp only [h_holds1.2, h_holds2.2, h_holds3.2, h_holds4.2] -- use the Normalized conditions
  simp only [h_holds1.1, h_holds2.1, h_holds3.1, h_holds4.1, l_components]
  ring_nf
  simp

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) Assumptions := by
  circuit_proof_start
  rcases input_x
  rcases input_y
  simp only [explicit_provable_type, ProvableType.fromElements_eq_iff, toVars, fromElements] at h_input ⊢
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.mk.injEq] at h_input ⊢
  simp only [Or8.circuit, Or8.Assumptions, h_input]
  simp only [Assumptions, U32.Normalized] at h_assumptions
  omega

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit (F p) sentences order Inputs U32 :=
  { elaborated := elaborated order, Assumptions, Spec, soundness := soundness order, completeness := completeness order }

end Gadgets.Or32
end
