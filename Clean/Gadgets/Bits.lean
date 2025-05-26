import Clean.Circuit.Loops
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [prime: Fact p.Prime]

def to_bit (x : ZMod p) : Bool := x == 1

def to_bits (n : ℕ) (x : ZMod p) : Vector Bool n :=
  .ofFn fun i => x.val.testBit i

def from_bits {n : ℕ} (x : Vector Bool n) : ZMod p :=
  Nat.ofBits fun i => x[i.val]

def from_bits_expr {n: ℕ} (xs : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc i => acc + xs[i] * .const (2^i.val)) 0

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

def circuit (n : ℕ) : FormalCircuit (F p) field (BitVector n) where
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
    replace h_eq := congrArg ZMod.val h_eq
    -- generalize x.val = x
    -- set x := x.val
    stop
    have h_eq' x : x = Fin.foldl n (fun acc ⟨i, _⟩ => acc + (env.get (k + i)).val * 2^i) 0 := by
      induction n with
      | zero => simp only [Fin.foldl_zero]; linarith
      | succ n ih =>
        have h_split : x = (x % 2^n) + (x / 2^n) * 2^n := Eq.symm (Nat.mod_add_div' x (2 ^ n))
        set x' := x % 2^n
        have x'_lt : x' < 2^n := Nat.mod_lt x (by norm_num)
        rw [h_split]
        simp only [Fin.foldl_succ_last]

        have h_bits' : ∀ (j : Fin n), env.get (k + j.val) = 0 ∨ env.get (k + j.val) = 1 := by
          intro j
          specialize h_bits j
          simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc] at h_bits
          exact h_bits

        specialize ih x' x'_lt h_bits'
        simp only [eval_vector, var_from_offset_vector] at h_eq
        exact h_eq
    have h_testbit i : x.val.testBit i = ((env.get (k + i)).val == 1) := by
      sorry
    intro i hi
    specialize h_bits ⟨ i, hi ⟩ trivial
    simp only at h_bits
    rw [h_testbit]
    simp only [beq_iff_eq]
    set bi := env.get (k + i)
    rcases h_bits with h|h
    · simp [h]
    · simp [h, ZMod.val_one]

  completeness := by
    intro k env x_var h_env x h_input h_assumptions
    simp only [main, circuit_norm, eval_vector, var_from_offset_vector] at *
    sorry

end Gadgets.ToBits
