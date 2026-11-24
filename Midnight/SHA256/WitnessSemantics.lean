import Midnight.SHA256.WitnessIR
import Midnight.SHA256.Semantics.Bitwise

/-! Mathematical meaning of the actual native SHA witness computations. These
lemmas refine the executable bit operations, independently of gate soundness. -/
namespace Midnight.SHA256.Witness

theorem compactEven_testBit_low (value i : Nat) (hi : i < 32) :
    (compactEven value).testBit i = value.testBit (2*i) := by
  interval_cases i <;>
    simp only [compactEven, evenMask, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight] <;>
    norm_num [Nat.testBit_eq_decide_div_mod_eq]

theorem compactEven_lt (value : Nat) : compactEven value < 2^32 := by
  unfold compactEven
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem compactEven_testBit (value i : Nat) :
    (compactEven value).testBit i = (decide (i < 32) && value.testBit (2*i)) := by
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    exact compactEven_testBit_low value i hi
  · have hb := (compactEven_lt value).trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 32 ≤ i))
    simp only [hi, decide_false, Bool.false_and, Nat.testBit_lt_two_pow hb]

private theorem term_testBit (value index bit : Nat) :
    ((((value >>> index) &&& 1) <<< (2*index))).testBit bit =
      (decide (bit = 2*index) && value.testBit index) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
    Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · rintro ⟨hbound, hvalue, hzero⟩
    have hbit : bit = 2*index := by omega
    subst bit
    simpa using hvalue
  · rintro ⟨rfl, hvalue⟩
    simpa using hvalue

private theorem fold_testBit (items : List Nat) (value initial bit : Nat) :
    (items.foldl (fun acc i => acc ||| (((value >>> i) &&& 1) <<< (2*i))) initial).testBit bit =
      (initial.testBit bit || items.any (fun i => decide (bit = 2*i) && value.testBit i)) := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, term_testBit, List.any_cons]
    exact Bool.or_assoc _ _ _

theorem spread32_testBit_even (value i : Nat) :
    (spread32 value).testBit (2*i) = (decide (i < 32) && value.testBit i) := by
  unfold spread32
  rw [fold_testBit]
  simp only [Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨index, hindex, heq, hvalue⟩
    have : index = i := by omega
    subst index
    exact ⟨hindex,hvalue⟩
  · rintro ⟨hi,hvalue⟩
    exact ⟨i,hi,rfl,hvalue⟩

theorem spread32_testBit_odd (value i : Nat) :
    (spread32 value).testBit (2*i+1) = false := by
  unfold spread32
  rw [fold_testBit]
  simp only [Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨index,_,heq,_⟩
  omega

/-- The Rust loop is precisely the table's mathematical spread function, with
its source u32 truncation made explicit for arbitrary natural inputs. -/
theorem spread32_eq_spread_mod (value : Nat) :
    spread32 value = SHA256.spread (value % 2^32) := by
  apply (Semantics.eq_spread_iff _ _).mpr
  constructor
  · intro i
    rw [spread32_testBit_even, Nat.testBit_mod_two_pow]
  · exact spread32_testBit_odd value

theorem spread32_eq_spread (value : Nat) (bound : value < 2^32) :
    spread32 value = SHA256.spread value := by
  rw [spread32_eq_spread_mod, Nat.mod_eq_of_lt bound]

theorem evenBits_lt (value : Nat) : evenBits value < 2^32 := compactEven_lt value

theorem oddBits_lt (value : Nat) : oddBits value < 2^32 := compactEven_lt (value >>> 1)

/-- The two honest parity witnesses reconstruct exactly the source's low64bits. -/
theorem interleave_even_odd_mod (value : Nat) :
    Semantics.interleave (evenBits value) (oddBits value) = value % 2^64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi : i = 2*(i/2)+i%2 := by omega
  rcases Nat.mod_two_eq_zero_or_one i with hzero | hone
  · conv_lhs => rw [hi, hzero, Nat.add_zero]
    rw [Semantics.interleave_testBit_even, evenBits, compactEven_testBit,
      Nat.testBit_mod_two_pow]
    have heq : 2*(i/2)=i := by omega
    rw [heq]
    have hbound : (i/2 < 32) ↔ i < 64 := by omega
    simp only [hbound]
  · conv_lhs => rw [hi, hone]
    rw [Semantics.interleave_testBit_odd, oddBits, compactEven_testBit,
      Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
    have heq : 1+2*(i/2)=i := by omega
    rw [heq]
    have hbound : (i/2 < 32) ↔ i < 64 := by omega
    simp only [hbound]

theorem interleave_even_odd (value : Nat) (bound : value < 2^64) :
    Semantics.interleave (evenBits value) (oddBits value) = value := by
  rw [interleave_even_odd_mod, Nat.mod_eq_of_lt bound]

end Midnight.SHA256.Witness

namespace Midnight.SHA256.WitnessIR
open Halo2

section Evaluation
variable {Env : Type} [Witgen.WitgenEnv F Env (AssignedCell F)]
variable (ctx : Witgen.CtxOver F Env)

end Evaluation
end Midnight.SHA256.WitnessIR
