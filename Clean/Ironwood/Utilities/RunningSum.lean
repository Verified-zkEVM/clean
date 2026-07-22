import Clean.Circuit
import Clean.Ironwood.Specs.Pallas
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Running-sum range-check theory

The value-level layer of `halo2_gadgets`' `decompose_running_sum` range check: the
`range_check(word, range)` product polynomial, the `InRange` predicate it enforces, and
the step relation `word = z_cur - 2^W * z_next`. Consumed by the running-sum
decomposition circuit (`Zcash.Circuits.DecomposeRunningSum`) and the
fixed-base scalar-multiplication canonicity proofs.
-/

namespace Zcash.Circuits

open Clean

namespace Utilities

variable {F : Type} [FiniteField F]

/-!
References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities.rs`
- `range_check`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/decompose_running_sum.rs`
- `RunningSumConfig::configure`
- `range check`

The source helper constrains `WINDOW_NUM_BITS <= 3`; this assertion models one enabled
running-sum row for any fixed `windowNumBits`, with the same arithmetic relation:
`word = z_cur - 2^K * z_next` and `range_check(word, 2^K) = 0`.
-/

namespace RunningSum

structure Step (F : Type) where
  zCur : F
  zNext : F
deriving ProvableStruct

def twoPowWindow (windowNumBits : ℕ) : F :=
  (2 ^ windowNumBits : ℕ)

def rangeCheckValues (range : ℕ) : List F :=
  (List.range range).drop 1 |>.map fun i => (i : F)

def rangeCheckPoly (range : ℕ) (word : F) : F :=
  rangeCheckValues (F := F) range |>.foldl (fun acc i => acc * (i - word)) word

def word (windowNumBits : ℕ) (step : Step F) : F :=
  step.zCur - twoPowWindow windowNumBits * step.zNext

def InRange (range : ℕ) (word : F) : Prop :=
  word = 0 ∨ ∃ i, i ∈ rangeCheckValues (F := F) range ∧ word = i

def Spec (windowNumBits : ℕ) (step : Step Fp) : Prop :=
  InRange (2 ^ windowNumBits) (word windowNumBits step)

private theorem rangeCheckFoldl_eq_zero_iff
    (xs : List F) (word acc : F) :
    xs.foldl (fun acc i => acc * (i - word)) acc = 0 ↔
      acc = 0 ∨ ∃ i, i ∈ xs ∧ word = i := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.mem_cons]
      rw [ih (acc * (i - word))]
      constructor
      · intro h
        rcases h with hprod | hmem
        · rcases mul_eq_zero.mp hprod with hacc | hi
          · exact Or.inl hacc
          · exact Or.inr ⟨i, Or.inl rfl, (sub_eq_zero.mp hi).symm⟩
        · rcases hmem with ⟨j, hj, hword⟩
          exact Or.inr ⟨j, Or.inr hj, hword⟩
      · intro h
        rcases h with hacc | hmem
        · exact Or.inl (by rw [hacc]; simp)
        · rcases hmem with ⟨j, hj, hword⟩
          rcases hj with hj | hj
          · subst j
            exact Or.inl (by rw [hj]; ring)
          · exact Or.inr ⟨j, hj, hword⟩

theorem rangeCheckPoly_eq_zero_iff (range : ℕ) (word : F) :
    rangeCheckPoly range word = 0 ↔ InRange range word := by
  unfold rangeCheckPoly InRange
  exact rangeCheckFoldl_eq_zero_iff (rangeCheckValues range) word word

end RunningSum

end Utilities
end Zcash.Circuits
