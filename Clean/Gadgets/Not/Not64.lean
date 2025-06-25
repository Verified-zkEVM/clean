import Clean.Utils.Primes
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Not
open Bitwise (not64 not64_eq_sub)

def not64_bytewise (x : Var U64 (F p)) : Var U64 (F p) := U64.map x (fun x => 255 - x)

def not64_bytewise_value (x : U64 (F p)) : U64 (F p) := x.map (fun x => 255 - x)

omit p_large_enough in
lemma eval_not {env} {x_var : Var U64 (F p)} :
    eval env (not64_bytewise x_var) = not64_bytewise_value (eval env x_var) := by
  rw [not64_bytewise, not64_bytewise_value, U64.map, U64.map]
  simp only [not64_bytewise, circuit_norm, explicit_provable_type]
  ring_nf

theorem not_zify (n : ℕ) {x : ℕ} (hx : x < n) : ((n - 1 - x : ℕ) : ℤ) = ↑n - 1 - ↑x := by
  have n_ge_1 : 1 ≤ n := by linarith
  have x_le : x ≤ n - 1 := Nat.le_pred_of_lt hx
  rw [Nat.cast_sub x_le, Nat.cast_sub n_ge_1]
  rfl

theorem not_lt (n : ℕ) {x : ℕ} (hx : x < n) : n - 1 - (x : ℤ) < n := by
  rw [←not_zify n hx, Int.ofNat_lt]
  exact Nat.sub_one_sub_lt_of_lt hx

theorem not_bytewise_value_spec {x : U64 (F p)} (x_lt : x.Normalized) :
    (not64_bytewise_value x).value = not64 x.value
    ∧ (not64_bytewise_value x).Normalized := by

  rw [not64_eq_sub (U64.value_lt_of_normalized x_lt)]

  have h_not_val : ∀ {x : F p}, x.val < 256 → ((255 - x).val : ℤ) = 255 - ↑x.val := by
    intro x hx
    have val_255 : (255 : F p).val = 255 := FieldUtils.val_lt_p 255 (by linarith [p_large_enough.elim])
    have hx' : x.val ≤ (255 : F p).val := by linarith
    rw [ZMod.val_sub hx', val_255]
    exact not_zify 256 hx

  rw [U64.value, U64.Normalized, not64_bytewise_value, U64.map]
  zify
  rw [not_zify (2^64) (U64.value_lt_of_normalized x_lt), U64.value]
  zify
  have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := x_lt
  repeat rw [h_not_val (by assumption)]
  constructor; ring
  exact ⟨ not_lt 256 hx0, not_lt 256 hx1, not_lt 256 hx2, not_lt 256 hx3,
      not_lt 256 hx4, not_lt 256 hx5, not_lt 256 hx6, not_lt 256 hx7 ⟩

def circuit : FormalCircuit (F p) U64 U64 where
  main x := pure (not64_bytewise x)
  assumptions x := x.Normalized
  spec x z := z.value = not64 x.value ∧ z.Normalized

  localLength _ := 0
  output x _ := not64_bytewise x

  soundness := by
    intro i env x_var x h_input x_norm h_holds
    simp_all only [circuit_norm, subcircuit_norm, eval_not]
    exact not_bytewise_value_spec x_norm

  completeness _ := by
    -- there are no constraints to satisfy!
    intros
    exact trivial

end Gadgets.Not
