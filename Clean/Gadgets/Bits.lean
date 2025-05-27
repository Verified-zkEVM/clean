import Clean.Circuit.Loops
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [prime: Fact p.Prime] [p_large_enough: Fact (p > 2)]

def to_bit (x : ZMod p) (_ : x.val = 0 ∨ x.val = 1) : Bool := x == 1

def from_bits {n : ℕ} (bits : Vector ℕ n) : ℕ :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * 2^i) 0

def from_bits_expr {n: ℕ} (bits : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2^i : F p)) 0

theorem from_bits_eval {n: ℕ} (hn : 2^n < p) {env} (bits : Vector (Expression (F p)) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i].eval env = 0 ∨ bits[i].eval env = 1) :
    ((from_bits_expr bits).eval env).val = from_bits (bits.map (fun b => (b.eval env).val)) := by

  -- strengthen the goal for use in induction
  suffices h_stronger :
      ((from_bits_expr bits).eval env).val < 2^n
      ∧ ((from_bits_expr bits).eval env).val = from_bits (bits.map (fun b => (b.eval env).val))
    from h_stronger.right

  simp only [from_bits_expr]

  induction n with
  | zero => simp only [Fin.foldl_zero, Expression.eval, ZMod.val_zero, from_bits]; simp
  | succ n ih =>
    simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last, Expression.eval, from_bits,
      Vector.getElem_map]
    simp only [from_bits, Vector.getElem_map] at ih

    -- instantiate induction hypothesis
    have : 2*2^n < p := by rw [←Nat.pow_succ']; exact hn
    have : 2^n < p := by linarith
    let bits' : Vector (Expression (F p)) n := bits.pop
    have h_bits' : ∀ j (hj : j < n), bits'[j].eval env = 0 ∨ bits'[j].eval env = 1
      | j, hj => by
        simp only [Vector.getElem_pop', bits']
        exact h_bits j (Nat.lt_succ_of_lt hj)

    obtain ⟨ ih_lt, ih_eq ⟩ := ih ‹_› bits' h_bits'; clear ih
    simp only [Vector.getElem_pop', bits'] at ih_eq ih_lt

    -- lift from ZMod to Nat
    let bitn := bits[n].eval env
    have : bitn.val < 2 := FieldUtils.boolean_lt_2 (h_bits n (Nat.lt_succ_self _))
    have : 2 < p := p_large_enough.elim
    have two_pow_val : ZMod.val (2 ^ n : F p) = 2 ^ n := by
      have : @ZMod.val p 2 = 2 := ZMod.val_natCast_of_lt (by linarith)
      rw [ZMod.val_pow, this]
      rwa [this]

    let xn : F p := Expression.eval env <| Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2 ^ i : F p)) 0
    have h_lt : xn.val + bitn.val * 2^n < 2^(n + 1) := by
      have : bitn.val * 2^n ≤ 1 * 2^n := Nat.mul_le_mul_right (2 ^ n) (by linarith)
      rw [Nat.pow_succ']
      linarith

    have h_to_nat : ZMod.val (xn + bitn * 2 ^ n) = xn.val + bitn.val * ZMod.val (2 ^ n : F p) := by
      field_to_nat
      rw [two_pow_val]
      linarith

    -- now we have everything in place
    rw [h_to_nat, two_pow_val, ←ih_eq]
    exact ⟨ h_lt, rfl ⟩

theorem from_bits_testBit {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    ∀ (i : ℕ) (hi : i < n), (from_bits bits).testBit i = (bits[i] == 1) := by

  -- strengthen the goal for use in induction
  suffices h_stronger :
      from_bits bits < 2^n
      ∧ ∀ (i : ℕ) (hi : i < n), (from_bits bits).testBit i = (bits[i] == 1)
    from h_stronger.right

  simp only [from_bits]
  induction n with
  | zero => simp_all
  | succ n ih =>
    simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]

    let bits' : Vector ℕ n := bits.pop
    have h_bits' : ∀ j (hj : j < n), bits'[j] = 0 ∨ bits'[j] = 1
      | j, hj => by
        simp only [Vector.getElem_pop', bits']
        exact h_bits j (Nat.lt_succ_of_lt hj)

    have h_bits_n : bits[n] = 0 ∨ bits[n] = 1 := h_bits n (Nat.lt_succ_self _)
    obtain ⟨ ih_lt, ih_eq ⟩ := ih bits' h_bits'; clear h_bits' h_bits ih
    simp only [Vector.getElem_pop', bits'] at ih_eq ih_lt

    have : bits[n] * 2 ^ n ≤ 2^n := by
      simp only [Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_left, bits']
      rcases h_bits_n <;> simp [*, ZMod.val_one]
    constructor
    · rw [Nat.pow_succ']; linarith

    intro i hi
    rw [mul_comm _ (2^n), add_comm _ (2^n * _), Nat.testBit_two_pow_mul_add _ ih_lt]
    by_cases hin : i < n <;> simp only [hin, reduceIte]
    · exact ih_eq i hin
    have : n = i := by linarith
    subst this
    rcases h_bits_n <;> simp [*, ZMod.val_one]

@[reducible] def BitVector (n : ℕ) := ProvableVector field n

namespace ToBits
def main {n: ℕ} (x : Expression (F p)) := do
  let bits ← witness_vector n fun (eval : Environment (F p)) =>
    .ofFn fun i =>
      let bit : Bool := (eval x).val.testBit i
      (if bit then 1 else 0 : F p)

  Circuit.forEach bits fun bit => assertion Boolean.circuit bit

  let x' := from_bits_expr bits
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

    let bit_vars : Vector (Expression (F p)) n := .mapRange n fun i => var ⟨k + i⟩
    let bits : Vector ℕ n := bit_vars.map (fun b => (b.eval env).val)

    have h_bit_vars : ∀ (i : ℕ) (hi : i < n), bit_vars[i].eval env = 0 ∨ bit_vars[i].eval env = 1
      | i, hi => by
        simp only [Vector.getElem_mapRange, bit_vars]
        exact h_bits ⟨ i, hi ⟩

    replace h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1
      | i, hi => by
        simp only [Vector.getElem_map, bits]
        rcases h_bit_vars i hi with h|h
        · left; rw [h, ZMod.val_zero]
        · right; rw [h, ZMod.val_one]

    change x = (from_bits_expr bit_vars).eval env at h_eq
    rw [h_eq, from_bits_eval hn bit_vars h_bit_vars]
    intro i hi

    show env.get (k + i) = if (from_bits bits).testBit i then 1 else 0

    have h_bit_i : (env.get (k + i)).val = bits[i] := by
      simp [Vector.getElem_map, bits, bit_vars, Expression.eval]
    apply FieldUtils.ext
    rw [h_bit_i, from_bits_testBit bits h_bits i hi]
    specialize h_bits i hi
    rcases h_bits <;> simp [*, bits, ZMod.val_one]

  completeness := by
    intro k env x_var h_env x h_input h_assumptions
    simp only [main, circuit_norm, Boolean.circuit, eval_vector, var_from_offset_vector, from_bits_expr] at *
    split
    · rename_i h_eq
      obtain rfl : n = 0 := Circuit.forEach.no_empty h_eq
      simp_all [Expression.eval]
    rename_i h_eq; clear h_eq
    simp only [h_input, circuit_norm, subcircuit_norm, true_implies, true_and, and_true] at h_env ⊢
    sorry

end Gadgets.ToBits
