import Clean.Utils.Primes
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64

section
variable {p : ℕ} [Fact p.Prime] variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.Not
def not8 (x : Expression (F p)) := 255 - x

def not64 (x : Var U64 (F p)) : Var U64 (F p) :=
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  ⟨ not8 x0, not8 x1, not8 x2, not8 x3, not8 x4, not8 x5, not8 x6, not8 x7 ⟩

theorem not_zify (n : ℕ) {x : ℕ} (hx : x < n) : ((n - 1 - x : ℕ) : ℤ) = ↑n - 1 - ↑x := by
  have n_ge_1 : 1 ≤ n := by linarith
  have x_le : x ≤ n - 1 := Nat.le_pred_of_lt hx
  rw [Nat.cast_sub x_le, Nat.cast_sub n_ge_1]
  rfl

theorem not_lt (n : ℕ) {x : ℕ} (hx : x < n) : n - 1 - (x : ℤ) < n := by
  rw [←not_zify n hx, Int.ofNat_lt]
  exact Nat.sub_one_sub_lt_of_lt hx

def circuit : FormalCircuit (F p) U64 U64 where
  main x := pure (not64 x)
  assumptions x := x.is_normalized
  spec x z := z.value = 2^64 - 1 - x.value ∧ z.is_normalized

  local_length _ := 0
  output x _ := not64 x

  soundness := by
    intro i env x_var x h_input h_assumptions h_holds
    cases x
    simp only [circuit_norm, subcircuit_norm, eval, var_from_offset,
      not8, not64] at h_holds h_input ⊢
    simp_all only [U64.mk.injEq]
    clear h_input

    have h_not_val : ∀ {x : F p}, x.val < 256 → ((255 + -x).val : ℤ) = 255 - ↑x.val := by
      intro x hx
      have val_255 : (255 : F p).val = 255 := FieldUtils.val_lt_p 255 (by linarith [p_large_enough.elim])
      have hx' : x.val ≤ (255 : F p).val := by linarith
      rw [←sub_eq_add_neg, ZMod.val_sub hx', val_255]
      exact not_zify 256 hx

    have h_not_val_64 : ∀ {x : U64 (F p)}, x.is_normalized → ((2^64 - 1 - x.value : ℕ) : ℤ) = 2^64 - 1 - ↑x.value := by
      intro x hx
      exact not_zify (2^64) (U64.value_lt_of_normalized hx)

    have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := h_assumptions
    rw [U64.value, U64.is_normalized]
    zify
    rw [h_not_val_64 h_assumptions, U64.value]
    zify
    repeat rw [h_not_val]
    constructor
    · ring
    exact ⟨ not_lt 256 hx0, not_lt 256 hx1, not_lt 256 hx2, not_lt 256 hx3,
      not_lt 256 hx4, not_lt 256 hx5, not_lt 256 hx6, not_lt 256 hx7 ⟩
    repeat assumption

  completeness _ := by
    -- there are no constraints to satisfy!
    intros
    exact trivial

end Gadgets.Not
