import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Utils.Bitwise
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

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p))  := do
  let ⟨x, y⟩ := input

  let z0 ← Or8.circuit ⟨x.x0, y.x0⟩
  let z1 ← Or8.circuit ⟨x.x1, y.x1⟩
  let z2 ← Or8.circuit ⟨x.x2, y.x2⟩
  let z3 ← Or8.circuit ⟨x.x3, y.x3⟩

  return ⟨z0, z1, z2, z3⟩

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ||| y.value ∧ z.Normalized

instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main
  localLength _ := 4

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  have l_components := U32.or_componentwise h_assumptions.1 h_assumptions.2
  rcases input_x with ⟨x0, x1, x2, x3⟩
  rcases input_y with ⟨y0, y1, y2, y3⟩
  rcases input_var_x with ⟨x0_var, x1_var, x2_var, x3_var⟩
  rcases input_var_y with ⟨y0_var, y1_var, y2_var, y3_var⟩
  simp only [U32.Normalized] at *
  simp only [explicit_provable_type, ProvableType.fromElements_eq_iff, toVars, fromElements] at h_input ⊢ l_components
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.mk.injEq] at h_input ⊢ l_components
  rcases h_holds with ⟨h_holds1, h_holds⟩
  specialize h_holds1 (by simp only [Or8.circuit, Or8.Assumptions, h_input]; omega)
  rcases h_holds with ⟨h_holds2, h_holds⟩
  specialize h_holds2 (by simp only [Or8.circuit, Or8.Assumptions, h_input]; omega)
  rcases h_holds with ⟨h_holds3, h_holds4⟩
  specialize h_holds3 (by simp only [Or8.circuit, Or8.Assumptions, h_input]; omega)
  specialize h_holds4 (by simp only [Or8.circuit, Or8.Assumptions, h_input]; omega)
  simp only [Or8.circuit, Or8.Spec] at h_holds1 h_holds2 h_holds3 h_holds4
  simp only [U32.value] at ⊢ l_components
  simp only [h_holds1.2, h_holds2.2, h_holds3.2, h_holds4.2]
  simp only [h_holds1.1, h_holds2.1, h_holds3.1, h_holds4.1]
  simp only [h_input]
  simp only [l_components]
  ring_nf
  simp

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  rcases input_x
  rcases input_y
  simp only [explicit_provable_type, ProvableType.fromElements_eq_iff, toVars, fromElements] at h_input ⊢
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.mk.injEq] at h_input ⊢
  simp only [Or8.circuit, Or8.Assumptions, h_input]
  simp only [Assumptions, U32.Normalized] at h_assumptions
  obtain ⟨ ⟨ hx0, hx1, hx2, hx3 ⟩, ⟨ hy0, hy1, hy2, hy3 ⟩ ⟩ := h_assumptions
  omega

def circuit : FormalCircuit (F p) Inputs U32 :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.Or32
end
