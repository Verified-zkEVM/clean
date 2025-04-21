import Clean.Utils.Primes
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Not
def not64_bytewise (x : Var U64 (F p)) : Var U64 (F p) :=
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  ⟨ 255 - x0, 255 - x1, 255 - x2, 255 - x3, 255 - x4, 255 - x5, 255 - x6, 255 - x7 ⟩

def not64_bytewise_value (x : U64 (F p)) : U64 (F p) :=
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  ⟨ 255 - x0, 255 - x1, 255 - x2, 255 - x3, 255 - x4, 255 - x5, 255 - x6, 255 - x7 ⟩

def u64_max : ℕ := 0xffffffffffffffff

def not64 (a : ℕ) : ℕ := a ^^^ 0xffffffffffffffff

theorem not_zify (n : ℕ) {x : ℕ} (hx : x < n) : ((n - 1 - x : ℕ) : ℤ) = ↑n - 1 - ↑x := by
  have n_ge_1 : 1 ≤ n := by linarith
  have x_le : x ≤ n - 1 := Nat.le_pred_of_lt hx
  rw [Nat.cast_sub x_le, Nat.cast_sub n_ge_1]
  rfl

theorem not_lt (n : ℕ) {x : ℕ} (hx : x < n) : n - 1 - (x : ℤ) < n := by
  rw [←not_zify n hx, Int.ofNat_lt]
  exact Nat.sub_one_sub_lt_of_lt hx

theorem not_bytewise_eq_sub {x : U64 (F p)} :
    x.is_normalized → (not64_bytewise_value x).value = 2^64 - 1 - x.value := by
  sorry

theorem not_eq_sub {x : ℕ} :
    x < 2^64 → not64 x = 2^64 - 1 - x := by
  sorry

theorem not_bytewise_normalized {x : U64 (F p)} :
    x.is_normalized → (not64_bytewise_value x).is_normalized := by
  intro h
  sorry

def circuit : FormalCircuit (F p) U64 U64 where
  main x := pure (not64_bytewise x)
  assumptions x := x.is_normalized
  spec x z := z.value = not64 x.value ∧ z.is_normalized

  local_length _ := 0
  output x _ := not64_bytewise x

  soundness := by
    intro i env x_var x h_input h_assumptions h_holds
    cases x
    simp only [circuit_norm, subcircuit_norm, eval, var_from_offset,
      not64_bytewise] at h_holds h_input ⊢
    have x_lt := U64.value_lt_of_normalized h_assumptions
    rw [not_eq_sub x_lt]
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
