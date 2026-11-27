module

public import Clean.Circuit
public import Clean.Ironwood.Specs.Pallas
public import Clean.Ironwood.Specs.Bitrange
public import Clean.Utils.Tactics.ProvableStructDeriving

@[expose] public section

/-!
# Running-sum range-check theory

The value-level layer of `halo2_gadgets`' `decompose_running_sum` range check: the
`range_check(word, range)` product polynomial, the `InRange` predicate it enforces, and
the step relation `word = z_cur - 2^W * z_next`. Consumed by the running-sum
decomposition circuit (`Zcash.Circuits.DecomposeRunningSum`) and the
fixed-base scalar-multiplication canonicity proofs.
-/

namespace Zcash.Circuits

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

/-! ## The honest running sum as a witness program -/

namespace Witgen

open CompElliptic.Fields.Pasta (Fp)

variable {V Env : Type}

/-- The running sum `z_j = x ≫ (K·j)`, computed in the field as halo2 does:
`z_{j+1} = (z_j − k_j) · 2^{−K}`, where the word `k_j` is bits `K·j .. K·j+K-1` of `x`. -/
def FExprOver.runningSum (K : ℕ) (x : FExprOver Fp V) : ℕ → FExprOver Fp V
  | 0 => x
  | j + 1 => .mul (.sub (x.runningSum K j) (x.bitrange (K * j) K)) (.const ((2 : Fp) ^ K)⁻¹)

@[simp, circuit_norm]
theorem FExprOver.eval_runningSum [WitgenEnv Fp Env V] (ctx : CtxOver Fp Env) (K : ℕ)
    (x : FExprOver Fp V) (j : ℕ) :
    (x.runningSum K j).eval ctx = (((x.eval ctx).val / 2 ^ (K * j) : ℕ) : Fp) := by
  induction j with
  | zero => simp [FExprOver.runningSum]
  | succ j ih =>
    set a := (x.eval ctx).val / 2 ^ (K * j)
    have hdiv : (x.eval ctx).val / 2 ^ (K * (j + 1)) = a / 2 ^ K := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ]
    have hcast : (a : Fp) - ((a % 2 ^ K : ℕ) : Fp) = (2 : Fp) ^ K * ((a / 2 ^ K : ℕ) : Fp) := by
      have h := congrArg (Nat.cast (R := Fp)) (Nat.div_add_mod a (2 ^ K))
      push_cast at h
      linear_combination -h
    have h2K : (2 : Fp) ^ K ≠ 0 := pow_ne_zero _ Zcash.Circuits.two_ne_zero
    simp only [FExprOver.runningSum, FExprOver.sub, FExprOver.eval, ih, FExprOver.eval_bitrange,
      Zcash.Circuits.Specs.bitrange, hdiv]
    rw [show (a : Fp) + -1 * ((a % 2 ^ K : ℕ) : Fp) = (a : Fp) - ((a % 2 ^ K : ℕ) : Fp) by ring,
      hcast, mul_comm, ← mul_assoc, inv_mul_cancel₀ h2K, one_mul]

end Witgen
