import Clean.Utils.Primes
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64

section
variable {p : ℕ} [Fact p.Prime] variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.Not
def not8 (x : Expression (F p)) : Expression (F p) := 255 - x

def main (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  return ⟨ not8 x0, not8 x1, not8 x2, not8 x3, not8 x4, not8 x5, not8 x6, not8 x7 ⟩

theorem not_zify (n : ℕ) {x : ℕ} (hx : x < n) : ((n - 1 - x : ℕ) : ℤ) = ↑n - 1 - ↑x := by
  have n_ge_1 : 1 ≤ n := by linarith
  have x_le : x ≤ n - 1 := Nat.le_pred_of_lt hx
  rw [Nat.cast_sub x_le, Nat.cast_sub n_ge_1]
  rfl

def circuit : FormalCircuit (F p) U64 U64 where
  main
  assumptions x := x.is_normalized
  spec x z := z.value = 2^64 - 1 - x.value

  local_length _ := 0
  output x _ := ⟨
    255 - x.x0, 255 - x.x1, 255 - x.x2, 255 - x.x3,
    255 - x.x4, 255 - x.x5, 255 - x.x6, 255 - x.x7 ⟩

  soundness := by
    intro i env x_var x h_input h_assumptions h_holds
    cases x
    simp only [circuit_norm, subcircuit_norm, eval, var_from_offset,
      main, not8, U64.is_normalized] at h_holds h_input ⊢
    simp_all only [gt_iff_lt, U64.mk.injEq]

    have h_not_val : ∀ {x : F p}, x.val < 256 → ((255 + -x).val : ℤ) = 255 - x.val := by
      intro x hx
      have val_255 : (255 : F p).val = 255 := FieldUtils.val_lt_p 255 (by linarith [p_large_enough.elim])
      have hx' : x.val ≤ (255 : F p).val := by linarith
      rw [←sub_eq_add_neg, ZMod.val_sub hx', val_255]
      exact not_zify 256 hx

    have h_not_val_64 : ∀ {x : U64 (F p)}, x.is_normalized → ((2^64 - 1 - x.value : ℕ) : ℤ) = 2^64 - 1 - (x.value : ℤ) := by
      intro x hx
      exact not_zify (2^64) (U64.value_lt_of_normalized hx)

    have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := h_assumptions
    rw [U64.value]
    zify
    rw [h_not_val_64 h_assumptions, U64.value]
    zify
    repeat rw [h_not_val]
    ring
    repeat assumption

  completeness _ := by
    -- there are no constraints to satisfy!
    intros
    exact trivial

end Gadgets.Not
