import Clean.Circuit.Loops
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [prime: Fact p.Prime] [p_large_enough: Fact (p > 2)]

def to_bit (x : ZMod p) : Bool := x == 1

def to_bits (n : ℕ) (x : ZMod p) : Vector Bool n :=
  .ofFn fun i => x.val.testBit i

def from_bits {n : ℕ} (x : Vector Bool n) : ZMod p :=
  Nat.ofBits fun i => x[i.val]

def from_bits_expr {n: ℕ} (bits : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2^i : F p)) 0

@[reducible] def BitVector (n : ℕ) := ProvableVector field n

namespace ToBits
def main {n: ℕ} (x : Expression (F p)) := do
  let bits ← witness_vector n fun (eval : Environment (F p)) =>
    .ofFn fun i =>
      let bit : Bool := (eval x).val.testBit i
      (if bit then 1 else 0 : F p)

  Circuit.forEach bits fun bit => assertion Boolean.circuit bit

  let x' := Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2^i : F p)) 0
  x.assert_equals x'

  return bits

def circuit (n : ℕ) (hn : 2^n < p) : FormalCircuit (F p) field (BitVector n) where
  main
  local_length _ := n
  output _ i := var_from_offset (BitVector n) i

  initial_offset_eq _ n := by simp only [main, circuit_norm]
  local_length_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl
  output_eq _ _ := by
    simp only [main, circuit_norm, Boolean.circuit, Circuit.forEach.apply_eq, var_from_offset_vector]
    -- rfl

  assumptions (x : F p) := x.val < 2^n

  spec (x : F p) (xs : Vector (F p) n) :=
    ∀ (i : ℕ) (hi : i < n), xs[i] = if x.val.testBit i then 1 else 0

  soundness := by
    intro k env x_var x h_input h_assumptions h_holds
    dsimp only [main] at *
    simp only [main, circuit_norm, Boolean.circuit, true_and, eval_vector, var_from_offset_vector] at *
    split at h_holds
    · rename_i h_eq
      obtain rfl : n = 0 := Circuit.forEach.no_empty h_eq
      simp
    rename_i h_eq; clear h_eq
    simp only [h_input, circuit_norm, subcircuit_norm, true_implies] at h_holds
    clear h_input

    obtain ⟨ h_bits, h_eq ⟩ := h_holds
    let bits i := env.get (k + i)
    replace h_bits : ∀ (i : ℕ) (hi : i < n), bits i = 0 ∨ bits i = 1
      | i, hi => h_bits ⟨ i, hi ⟩

    have ⟨_, h_eq'⟩ : x.val < 2^n ∧ x.val = Fin.foldl n (fun acc ⟨i, _⟩ => acc + (bits i).val * 2^i) 0 := by
      rw [congrArg ZMod.val h_eq]
      clear h_assumptions h_eq
      induction n with
      | zero => simp only [Fin.foldl_zero, Expression.eval, ZMod.val_zero]; trivial
      | succ n ih =>
        simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last, Expression.eval]

        -- instantiate induction hypothesis
        have : 2*2^n < p := by rw [←Nat.pow_succ']; exact hn
        have : 2^n < p := by linarith
        have h_bits' : ∀ j (hj : j < n), bits j = 0 ∨ bits j = 1
          | j, hj => h_bits j (Nat.lt_succ_of_lt hj)
        obtain ⟨ ih_lt, ih_eq ⟩ := ih ‹2^n < p› h_bits'; clear ih

        -- lift from ZMod to Nat
        have : (bits n).val < 2 := FieldUtils.boolean_lt_2 (h_bits n (Nat.lt_succ_self _))
        have two_pow_val : ZMod.val (2 ^ n : F p) = 2 ^ n := by
          have : @ZMod.val p 2 = 2 := ZMod.val_natCast_of_lt (by linarith [p_large_enough.elim])
          rw [ZMod.val_pow, this]
          rwa [this]
        let xn : F p := Expression.eval env <| Fin.foldl n (fun acc ⟨i, _⟩ => acc + var (F:=F p) ⟨ k + i ⟩ * (2 ^ i : F p)) 0
        have h_lt : xn.val + (bits n).val * 2^n < 2^(n + 1) := by
          have : (env.get (k + n)).val * 2^n ≤ 1 * 2^n := Nat.mul_le_mul_right (2 ^ n) (by linarith)
          rw [Nat.pow_succ']
          linarith
        have h_to_nat : ZMod.val (xn + (bits n) * 2 ^ n) = xn.val + (bits n).val * ZMod.val (2 ^ n : F p) := by
          field_to_nat
          rw [two_pow_val]
          linarith

        -- now we have everything in place
        rw [h_to_nat, two_pow_val, ←ih_eq]
        exact ⟨ h_lt, rfl ⟩

    have ⟨_, h_testbit⟩ : x.val < 2^n ∧ ∀ {i : ℕ} (hi : i < n), x.val.testBit i = ((bits i).val == 1) := by
      rw [h_eq']
      clear h_assumptions h_eq h_eq' ‹ZMod.val x < 2 ^ n› hn
      simp only
      induction n with
      | zero =>
        simp only [Fin.foldl_zero]
        exact ⟨ by trivial, fun i => by trivial ⟩
      | succ n ih =>
        simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]
        have h_bits_prev : ∀ j (hj : j < n), bits j = 0 ∨ bits j = 1
          | j, hj => h_bits j (Nat.lt_succ_of_lt hj)
        have h_bits_n : bits n = 0 ∨ bits n = 1 := h_bits n (Nat.lt_succ_self _)
        obtain ⟨ ih_lt, ih_eq ⟩ := ih h_bits_prev; clear h_bits_prev h_bits ih
        have : 2 ^ n * ZMod.val (bits n) ≤ 2^n := by
          simp only [Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right]
          rcases h_bits_n <;> simp [*, ZMod.val_one]
        constructor
        · rw [Nat.pow_succ']; linarith
        intro i hi
        rw [mul_comm _ (2^n), add_comm _ (2^n * _), Nat.testBit_two_pow_mul_add _ ih_lt]
        by_cases hin : i < n <;> simp only [hin, reduceIte]
        · exact ih_eq hin
        have : n = i := by linarith
        subst this
        rcases h_bits_n <;> simp [*, ZMod.val_one]

    intro i hi
    specialize h_bits i hi
    simp only at h_bits
    rw [h_testbit hi]
    simp only [beq_iff_eq]
    rcases h_bits with h|h
    · simp [h, bits]
    · simp [h, bits, ZMod.val_one]

  completeness := by
    intro k env x_var h_env x h_input h_assumptions
    simp only [main, circuit_norm, eval_vector, var_from_offset_vector] at *
    sorry

end Gadgets.ToBits
