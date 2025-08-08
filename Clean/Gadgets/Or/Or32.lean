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

  -- Apply Or8.circuit to each byte pair
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

-- General lemma: operations defined with bitwise can be computed componentwise on U32
lemma U32.bitwise_componentwise (f : Bool → Bool → Bool)
    {x y : U32 (F p)} (x_norm : x.Normalized) (y_norm : y.Normalized) :
    Nat.bitwise f x.value y.value =
    Nat.bitwise f x.x0.val y.x0.val +
    256 * (Nat.bitwise f x.x1.val y.x1.val +
    256 * (Nat.bitwise f x.x2.val y.x2.val +
    256 * Nat.bitwise f x.x3.val y.x3.val)) := by
  sorry -- This follows from the fact that bitwise operations respect base-256 representation

-- Specific lemma for OR on U32
lemma U32.or_componentwise {x y : U32 (F p)} (x_norm : x.Normalized) (y_norm : y.Normalized) :
    x.value ||| y.value =
    (x.x0.val ||| y.x0.val) +
    256 * ((x.x1.val ||| y.x1.val) +
    256 * ((x.x2.val ||| y.x2.val) +
    256 * (x.x3.val ||| y.x3.val))) := by
  -- Use the fact that ||| is Nat.lor which is defined as bitwise or
  show Nat.lor x.value y.value = _
  -- Nat.lor is definitionally equal to bitwise or
  show Nat.bitwise or x.value y.value = _
  rw [U32.bitwise_componentwise or x_norm y_norm]
  rfl

theorem soundness_to_u32 {x y z : U32 (F p)}
  (x_norm : x.Normalized) (y_norm : y.Normalized)
  (h_eq :
    z.x0.val = x.x0.val ||| y.x0.val ∧
    z.x1.val = x.x1.val ||| y.x1.val ∧
    z.x2.val = x.x2.val ||| y.x2.val ∧
    z.x3.val = x.x3.val ||| y.x3.val) :
    Spec { x, y } z := by
  simp only [Spec]
  have ⟨hx0, hx1, hx2, hx3⟩ := x_norm
  have ⟨hy0, hy1, hy2, hy3⟩ := y_norm

  have z_norm : z.Normalized := by
    simp only [U32.Normalized, h_eq]
    exact ⟨Nat.or_lt_two_pow (n:=8) hx0 hy0, Nat.or_lt_two_pow (n:=8) hx1 hy1,
      Nat.or_lt_two_pow (n:=8) hx2 hy2, Nat.or_lt_two_pow (n:=8) hx3 hy3⟩

  suffices z.value = x.value ||| y.value from ⟨this, z_norm⟩
  rw [U32.or_componentwise x_norm y_norm]
  simp only [U32.value]
  omega

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
  specialize h_holds1 (by sorry)
  rcases h_holds with ⟨h_holds2, h_holds⟩
  specialize h_holds2 (by sorry)
  rcases h_holds with ⟨h_holds3, h_holds4⟩
  specialize h_holds3 (by sorry)
  specialize h_holds4 (by sorry)
  simp only [Or8.circuit, Or8.Spec] at h_holds1 h_holds2 h_holds3 h_holds4
  simp only [U32.value] at ⊢ l_components
  simp only [h_holds1, h_holds2, h_holds3, h_holds4]
  simp only [h_input]
  apply And.intro
  · simp only [l_components]
    ring
  · constructor
    · apply Nat.or_lt_two_pow (n:=8) (x:=ZMod.val x0) (y:=ZMod.val y0) <;> omega
    constructor
    · apply Nat.or_lt_two_pow (n:=8) (x:=ZMod.val x1) (y:=ZMod.val y1) <;> omega
    constructor
    · apply Nat.or_lt_two_pow (n:=8) (x:=ZMod.val x2) (y:=ZMod.val y2) <;> omega
    · apply Nat.or_lt_two_pow (n:=8) (x:=ZMod.val x3) (y:=ZMod.val y3) <;> omega

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro _ env _ h_env _ h_input h_assumptions
  -- Unfold main manually
  simp only [circuit_norm, main]
  simp only [elaborated, varFromOffset, Inputs.mk.injEq, U32.mk.injEq] at h_input h_env ⊢
  obtain ⟨ rfl, rfl ⟩ := h_input
  simp only [Assumptions, U32.Normalized] at h_assumptions
  obtain ⟨ ⟨ hx0, hx1, hx2, hx3 ⟩, ⟨ hy0, hy1, hy2, hy3 ⟩ ⟩ := h_assumptions

  -- Apply Or8 completeness to each byte
  have c0 := Or8.completeness _ env _ h_env _ rfl ⟨hx0, hy0⟩
  have c1 := Or8.completeness _ env _ h_env _ rfl ⟨hx1, hy1⟩
  have c2 := Or8.completeness _ env _ h_env _ rfl ⟨hx2, hy2⟩
  have c3 := Or8.completeness _ env _ h_env _ rfl ⟨hx3, hy3⟩

  exact ⟨c0, c1, c2, c3⟩

def circuit : FormalCircuit (F p) Inputs U32 :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.Or32
end
