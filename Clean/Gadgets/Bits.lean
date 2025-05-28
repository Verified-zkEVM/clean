import Clean.Circuit.Loops
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [prime: Fact p.Prime] [p_large_enough: Fact (p > 2)]

def to_bits (n : ℕ) (x : F p) : Vector (F p) n :=
  .mapRange n fun i => if x.val.testBit i then 1 else 0

def from_bits {n : ℕ} (bits : Vector (F p) n) : F p :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * 2^i) 0

def from_bits_expr {n: ℕ} (bits : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2^i : F p)) 0

namespace ToBits
def main (n: ℕ) (x : Expression (F p)) := do
  -- witness the bits of `x`
  let bits ← witness_vector n fun env => to_bits n (x.eval env)

  -- add boolean constraints on all bits
  Circuit.forEach bits (assertion Boolean.circuit)

  -- check that the bits correctly sum to `x`
  x.assert_equals (from_bits_expr bits)
  return bits

-- theorems about to/from bits that we need

omit p_large_enough in
/-- evaluation commutes with bits accumulation -/
theorem from_bits_eval {n: ℕ} {eval : Environment (F p)} (bits : Vector (Expression (F p)) n) :
    eval (from_bits_expr bits) = from_bits (bits.map eval) := by
  simp only [from_bits_expr, from_bits]
  induction n with
  | zero => simp only [Fin.foldl_zero, Expression.eval]
  | succ n ih =>
    obtain ih := ih bits.pop
    simp only [Vector.getElem_pop'] at ih
    simp [Fin.foldl_succ_last, ih, Expression.eval]

/-- main lemma which establishes the behaviour of `from_bits` and `to_bits` by induction -/
lemma to_bits_from_bits_aux {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (from_bits bits).val < 2^n ∧ to_bits n (from_bits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [from_bits, to_bits, Vector.getElem_mapRange]
  induction n with
  | zero => simp_all
  | succ n ih =>
    simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]

    -- instantiate induction hypothesis
    have : 2*2^n < p := by rw [←Nat.pow_succ']; exact hn
    have : 2^n < p := by linarith
    let bits' : Vector (F p) n := bits.pop
    have h_bits' : ∀ j (hj : j < n), bits'[j] = 0 ∨ bits'[j] = 1
      | j, hj => by
        simp only [Vector.getElem_pop', bits']
        exact h_bits j (Nat.lt_succ_of_lt hj)

    have h_bits_n : bits[n] = 0 ∨ bits[n] = 1 := h_bits n (Nat.lt_succ_self _)
    obtain ⟨ ih_lt, ih_eq ⟩ := ih ‹_› bits' h_bits'; clear h_bits' h_bits ih
    simp only [Vector.getElem_pop', bits'] at ih_eq ih_lt

    -- lift from ZMod to Nat
    have : 2 < p := p_large_enough.elim
    have two_pow_val : ZMod.val (2 ^ n : F p) = 2 ^ n := by
      have : @ZMod.val p 2 = 2 := ZMod.val_natCast_of_lt (by linarith)
      rw [ZMod.val_pow, this]
      rwa [this]

    let xn : F p := Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2 ^ i : F p)) 0
    have : bits[n].val ≤ 1 := by rcases h_bits_n <;> simp [*, ZMod.val_one]
    have h_lt : xn.val + bits[n].val * 2^n < 2^(n + 1) := by
      have : bits[n].val * 2^n ≤ 1 * 2^n := Nat.mul_le_mul_right (2 ^ n) (by linarith)
      rw [Nat.pow_succ']
      linarith

    have h_to_nat : ZMod.val (xn + bits[n] * 2 ^ n) = xn.val + bits[n].val * 2 ^ n := by
      field_to_nat
      · rw [two_pow_val]
      · rw [two_pow_val]; linarith

    -- now everything is in place to finish the proof
    rw [h_to_nat]
    constructor
    · exact h_lt

    intro i hi
    rw [mul_comm _ (2^n), add_comm _ (2^n * _), Nat.testBit_two_pow_mul_add _ ih_lt]
    by_cases hin : i < n <;> simp only [hin, reduceIte]
    · exact ih_eq i hin
    have : n = i := by linarith
    subst this
    rcases h_bits_n <;> simp [*, ZMod.val_one]

/-- the result of `from_bits` is less than 2^n -/
theorem from_bits_lt {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (from_bits bits).val < 2^n := (to_bits_from_bits_aux hn bits h_bits).left

/-- `to_bits` is a left-inverse of `from_bits` -/
theorem to_bits_from_bits {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    to_bits n (from_bits bits) = bits := (to_bits_from_bits_aux hn bits h_bits).right

omit p_large_enough in
/-- on numbers less than `2^n`, `to_bits n` is injective -/
theorem to_bits_injective (n: ℕ) {x y : F p} : x.val < 2^n → y.val < 2^n →
    to_bits n x = to_bits n y → x = y := by
  intro hx hy h_eq
  rw [Vector.ext_iff] at h_eq
  simp only [to_bits, Vector.getElem_mapRange] at h_eq
  have h_eq' : ∀ i (hi : i < n), x.val.testBit i = y.val.testBit i := by
    intro i hi
    specialize h_eq i hi
    by_cases hx_i : x.val.testBit i <;> by_cases hy_i : y.val.testBit i <;>
      simp_all
  apply FieldUtils.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h_eq' i hi
  have : n ≤ i := by linarith
  have : 2^n ≤ 2^i := Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
  replace hx : x.val < 2^i := by linarith
  replace hy : y.val < 2^i := by linarith
  rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

/-- on numbers less than `2^n`, `to_bits` is a right-inverse of `from_bits` -/
theorem from_bits_to_bits {n: ℕ} (hn : 2^n < p) {x : F p} (hx : x.val < 2^n) :
    from_bits (to_bits n x) = x := by
  have h_bits : ∀ i (hi : i < n), (to_bits n x)[i] = 0 ∨ (to_bits n x)[i] = 1 := by
    intro i hi; simp [to_bits]
  apply to_bits_injective n (from_bits_lt hn _ h_bits) hx
  rw [to_bits_from_bits hn _ h_bits]

-- formal circuit that implements `to_bits` like a function, assuming `x.val < 2^n`

def circuit (n : ℕ) (hn : 2^n < p) : FormalCircuit (F p) field (fields n) where
  main := main n
  local_length _ := n
  output _ i := var_from_offset (fields n) i

  initial_offset_eq _ n := by simp only [main, circuit_norm]
  local_length_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl
  output_eq _ _ := by simp only [main, circuit_norm]

  assumptions (x : F p) := x.val < 2^n

  spec (x : F p) (bits : Vector (F p) n) :=
    bits = to_bits n x

  soundness := by
    intro k eval x_var x h_input h_assumptions h_holds
    dsimp only [main] at *
    simp only [main, circuit_norm, Boolean.circuit, true_and] at *
    -- TODO: simp [circuit_norm] is not able to exclude the case that `forEach` results in empty operations
    -- which leads to this case split and hard-to-discover proof that dicharges the empty case
    split at h_holds
    · rename_i h_eq
      rcases (Circuit.forEach.no_empty h_eq) with h|h
      · obtain rfl : n = 0 := h
        simp [Vector.mapRange_zero]
      obtain ⟨_, _, h⟩ := h
      exact Operations.noConfusion h
    rename_i h_eq; clear h_eq
    simp only [h_input, circuit_norm, subcircuit_norm, true_implies] at h_holds
    clear h_input

    obtain ⟨ h_bits, h_eq ⟩ := h_holds

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨k + ·⟩)
    let bits : Vector (F p) n := bit_vars.map eval

    replace h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1
      | i, hi => by
        simp only [circuit_norm, bits, bit_vars]
        exact h_bits ⟨ i, hi ⟩

    change x = eval (from_bits_expr bit_vars) at h_eq
    rw [h_eq, from_bits_eval bit_vars, to_bits_from_bits hn bits h_bits]

  completeness := by
    intro k eval x_var h_env x h_input h_assumptions
    simp only [main, circuit_norm, Boolean.circuit] at *
    -- TODO: simp [circuit_norm] is not able to exclude the case that `forEach` results in empty operations
    -- which leads to this case split and hard-to-discover proof that dicharges the empty case
    split
    · rename_i h_eq
      rcases (Circuit.forEach.no_empty h_eq) with h|h
      · obtain rfl : n = 0 := h
        simp_all [Expression.eval, from_bits_expr]
      obtain ⟨_, _, h⟩ := h
      exact Operations.noConfusion h
    rename_i h_eq; clear h_eq
    simp only [h_input, circuit_norm, subcircuit_norm, true_implies, true_and, and_true] at h_env ⊢
    obtain ⟨ h_bits, right ⟩ := h_env; clear right;

    constructor
    · intro i
      rw [h_bits i]
      simp [to_bits]

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨k + ·⟩)

    have h_bits_eq : bit_vars.map eval = to_bits n x := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm, bit_vars]
      exact h_bits ⟨ i, hi ⟩

    show x = eval (from_bits_expr bit_vars)
    rw [from_bits_eval bit_vars, h_bits_eq, from_bits_to_bits hn h_assumptions]

-- formal assertion that uses the same circuit to implement a range check. without input assumption

def range_check (n : ℕ) (hn : 2^n < p) : FormalAssertion (F p) field where
  main x := do _ ← main n x -- discard the output
  local_length _ := n

  initial_offset_eq _ n := by simp only [main, circuit_norm]
  local_length_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl

  assumptions _ := True
  spec (x : F p) := x.val < 2^n

  soundness := by
    sorry

  completeness := by
    sorry
end Gadgets.ToBits
