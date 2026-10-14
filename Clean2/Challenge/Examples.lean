/-
Challenges in an ordinary circuit, row by row, and what they cost on R1CS.

`LookupAndPermutation` checks a lookup and a permutation with the same challenge. It is generic
over both checks: it knows nothing about challenges, symbolic meanings or rare events, and its
proofs are one line each.

On R1CS, both errors are measures: they compose like cost, from the closed forms of the parts.
-/
module

public import Clean2.Challenge.GrandProductRow
public import Clean2.Backends.R1CS

@[expose] public section

namespace Clean2

namespace LookupAndPermutation
open Permutation
variable {F : Type} [Field F] [DecidableEq F]

/-- `f` is looked up in `t` with multiplicities `μ`, and `b` is a permutation of `a`. -/
@[reducible]
def interface (n l k : ℕ) : Interface F where
  input := ((((Vector F n × Vector F n) × Vector F l) × (Vector F k × Vector F k))) × F
  inputCType := (((.natives n ×ᵗ .natives n) ×ᵗ .natives l) ×ᵗ (.natives k ×ᵗ .natives k)) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun ((((t, μ), f), (a, b)), _) _ => (∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), μ[i]) ∧ elems a = elems b
  ProverAssumptions := fun ((((t, μ), f), (a, b)), _) => (∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), μ[i]) ∧ elems a = elems b

variable {B : Backend} [Field B.Native] [DecidableEq B.Native] {n l k : ℕ}
  (lookup : Impl B (Lookup.interface n l)) (perm : Impl B (PermutationRow.interface k))

/-- Both checks, on one challenge. -/
def impl : Impl B (interface n l k) where
  main | ((((t, μ), f), (a, b)), α) => do
    lookup (((t, μ), f), α)
    perm ((a, b), α)
  spatial := by
    intro ((((t, μ), f), (a, b)), α) s h
    obtain ⟨⟨⟨⟨h_t, h_μ⟩, h_f⟩, ⟨h_a, h_b⟩⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left fun h =>
      ((Backend.footprintT_ctypeProd_subset.mp h).imp_left fun h =>
        (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp).imp_right
          Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
        ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨h_t, h_μ⟩, h_f⟩, h_α⟩,
      fun _ m => ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
        ⟨h_a.trans m, h_b.trans m⟩, h_α.trans m⟩, fun _ _ => Set.empty_subset _⟩⟩
  soundness := by
    intro s env ((((t, μ), f), (a, b)), α) _ h
    simp only [circuit_norm] at h ⊢
    exact h
  completeness := by
    intro s env ((((t, μ), f), (a, b)), α) _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    exact h_prover

end LookupAndPermutation

/-! ## On R1CS, with both errors as measures -/

section R1CS
variable {F : Type} [Field F] [DecidableEq F]

instance (n : Arith.Name F) : Impl.Measured errorBound (R1CS.arith n) where
  value := 0
  value_eq input s := by cases n <;> rfl
instance (n : Arith.Name F) : Impl.Measured honestErrorBound (R1CS.arith n) where
  value := 0
  value_eq input s := by cases n <;> rfl

omit [DecidableEq F] in
theorem errorBound_of_arith (n : Arith.Name F) : errorBound.of (R1CS.arith n) = 0 := rfl
omit [DecidableEq F] in
theorem honestErrorBound_of_arith (n : Arith.Name F) : honestErrorBound.of (R1CS.arith n) = 0 := rfl

def inverseR1CS : Impl (R1CS F) Inverse.interface := Inverse.impl R1CS.arith
instance : Impl.Measured errorBound (inverseR1CS (F := F)) where
  value := 0
  value_eq := by measure [inverseR1CS, Inverse.impl]
instance : Impl.Measured honestErrorBound (inverseR1CS (F := F)) where
  value := 0
  value_eq := by measure [inverseR1CS, Inverse.impl]

def logUpRowR1CS : Impl (R1CS F) LogUpRow.interface := LogUpRow.impl R1CS.arith inverseR1CS
instance : Impl.Measured errorBound (logUpRowR1CS (F := F)) where
  value := 0
  value_eq := by measure [logUpRowR1CS, LogUpRow.impl]
instance : Impl.Measured honestErrorBound (logUpRowR1CS (F := F)) where
  value := 1
  value_eq := by measure [logUpRowR1CS, LogUpRow.impl, LogUpRow.event]

def logUpSumR1CS (n : ℕ) : Impl (R1CS F) (LogUpSum.interface n) := LogUpSum.impl R1CS.arith logUpRowR1CS n
instance (n : ℕ) : Impl.Measured honestErrorBound (logUpSumR1CS (F := F) n) where
  value := n
  value_eq := by
    intro ((v, m), α) s
    simp only [logUpSumR1CS, LogUpSum.impl, LogUpSum.loop, circuit_norm]
    rw [Circuit.foldr_measure_const honestErrorBound _ _ 1 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 1 = n
    simp

instance (n : ℕ) : Impl.Measured errorBound (logUpSumR1CS (F := F) n) where
  value := 0
  value_eq := by
    intro ((v, m), α) s
    simp only [logUpSumR1CS, LogUpSum.impl, LogUpSum.loop, circuit_norm]
    rw [Circuit.foldr_measure_const errorBound _ _ 0 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 0 = 0
    simp

omit [DecidableEq F] in
theorem errorBound_of_logUpSum (n : ℕ) : errorBound.of (logUpSumR1CS (F := F) n) = 0 := rfl
omit [DecidableEq F] in
theorem honestErrorBound_of_logUpSum (n : ℕ) : honestErrorBound.of (logUpSumR1CS (F := F) n) = n := rfl

/-- The boundary: its expression's degree bound, for soundness; nothing for completeness. -/
def boundaryR1CS (k d : ℕ) (R : Vector F k → RatFunc F) : Impl (R1CS F) (AssertIdentity.interface k d R) :=
  AssertIdentity.impl R1CS.arith d R
instance (k d : ℕ) (R : Vector F k → RatFunc F) : Impl.Measured errorBound (boundaryR1CS k d R) where
  value := d
  value_eq := by measure [boundaryR1CS, AssertIdentity.impl, AssertIdentity.event, errorBound_of_arith]
instance (k d : ℕ) (R : Vector F k → RatFunc F) : Impl.Measured honestErrorBound (boundaryR1CS k d R) where
  value := 0
  value_eq := by measure [boundaryR1CS, AssertIdentity.impl, honestErrorBound_of_arith]

omit [DecidableEq F] in
theorem errorBound_of_boundary (k d : ℕ) (R : Vector F k → RatFunc F) :
    errorBound.of (boundaryR1CS k d R) = d := rfl
omit [DecidableEq F] in
theorem honestErrorBound_of_boundary (k d : ℕ) (R : Vector F k → RatFunc F) :
    honestErrorBound.of (boundaryR1CS k d R) = 0 := rfl

noncomputable def lookupR1CS (n l : ℕ) : Impl (R1CS F) (Lookup.interface n l) :=
  Lookup.impl R1CS.arith (logUpSumR1CS n) (logUpSumR1CS l) (boundaryR1CS _ _ _)
instance (n l : ℕ) : Impl.Measured errorBound (lookupR1CS (F := F) n l) where
  value := n + l
  value_eq := by measure [lookupR1CS, Lookup.impl, errorBound_of_arith, errorBound_of_logUpSum,
    errorBound_of_boundary]
instance (n l : ℕ) : Impl.Measured honestErrorBound (lookupR1CS (F := F) n l) where
  value := n + l
  value_eq := by measure [lookupR1CS, Lookup.impl, honestErrorBound_of_arith, honestErrorBound_of_logUpSum,
    honestErrorBound_of_boundary]

def productRowR1CS : Impl (R1CS F) ProductRow.interface := ProductRow.impl R1CS.arith inverseR1CS
instance : Impl.Measured errorBound (productRowR1CS (F := F)) where
  value := 0
  value_eq := by measure [productRowR1CS, ProductRow.impl]
instance : Impl.Measured honestErrorBound (productRowR1CS (F := F)) where
  value := 1
  value_eq := by measure [productRowR1CS, ProductRow.impl, ProductRow.event]

def productLoopR1CS (n : ℕ) : Impl (R1CS F) (ProductLoop.interface n) :=
  ProductLoop.impl R1CS.arith productRowR1CS n
instance (n : ℕ) : Impl.Measured errorBound (productLoopR1CS (F := F) n) where
  value := 0
  value_eq := by
    intro ((v, m), α) s
    simp only [productLoopR1CS, ProductLoop.impl, ProductLoop.loop, circuit_norm]
    rw [Circuit.foldr_measure_const errorBound _ _ 0 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 0 = 0
    simp
instance (n : ℕ) : Impl.Measured honestErrorBound (productLoopR1CS (F := F) n) where
  value := n
  value_eq := by
    intro ((v, m), α) s
    simp only [productLoopR1CS, ProductLoop.impl, ProductLoop.loop, circuit_norm]
    rw [Circuit.foldr_measure_const honestErrorBound _ _ 1 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 1 = n
    simp

omit [DecidableEq F] in
theorem errorBound_of_productLoop (n : ℕ) : errorBound.of (productLoopR1CS (F := F) n) = 0 := rfl
omit [DecidableEq F] in
theorem honestErrorBound_of_productLoop (n : ℕ) : honestErrorBound.of (productLoopR1CS (F := F) n) = n := rfl

noncomputable def permutationRowR1CS (n : ℕ) : Impl (R1CS F) (PermutationRow.interface n) :=
  PermutationRow.impl R1CS.arith (productLoopR1CS n) (boundaryR1CS _ _ _)
instance (n : ℕ) : Impl.Measured errorBound (permutationRowR1CS (F := F) n) where
  value := n
  value_eq := by measure [permutationRowR1CS, PermutationRow.impl, errorBound_of_arith, errorBound_of_productLoop,
    errorBound_of_boundary]
instance (n : ℕ) : Impl.Measured honestErrorBound (permutationRowR1CS (F := F) n) where
  value := n
  value_eq := by measure [permutationRowR1CS, PermutationRow.impl, honestErrorBound_of_arith,
    honestErrorBound_of_productLoop, honestErrorBound_of_boundary]

theorem errorBound_of_lookup (n l : ℕ) : errorBound.of (lookupR1CS (F := F) n l) = n + l := rfl
theorem honestErrorBound_of_lookup (n l : ℕ) : honestErrorBound.of (lookupR1CS (F := F) n l) = n + l := rfl
omit [DecidableEq F] in
theorem errorBound_of_permutationRow (n : ℕ) : errorBound.of (permutationRowR1CS (F := F) n) = n := rfl
omit [DecidableEq F] in
theorem honestErrorBound_of_permutationRow (n : ℕ) : honestErrorBound.of (permutationRowR1CS (F := F) n) = n := rfl

/-- A lookup and a permutation check on one challenge. -/
noncomputable def lookupAndPermutationR1CS (n l k : ℕ) :
    Impl (R1CS F) (LookupAndPermutation.interface n l k) :=
  LookupAndPermutation.impl (lookupR1CS n l) (permutationRowR1CS k)
instance (n l k : ℕ) : Impl.Measured errorBound (lookupAndPermutationR1CS (F := F) n l k) where
  value := n + l + k
  value_eq := by measure [lookupAndPermutationR1CS, LookupAndPermutation.impl, errorBound_of_lookup,
    errorBound_of_permutationRow]
instance (n l k : ℕ) : Impl.Measured honestErrorBound (lookupAndPermutationR1CS (F := F) n l k) where
  value := n + l + k
  value_eq := by measure [lookupAndPermutationR1CS, LookupAndPermutation.impl, honestErrorBound_of_lookup,
    honestErrorBound_of_permutationRow]

/-- **Both errors, read off the parts.** A lookup of `l` values into a table of `n`, and a
permutation of `k` values, on one challenge: a false statement is accepted at no more than
`n + l + k` challenges, and the honest prover fails at no more than `n + l + k`. -/
theorem errors_lookupAndPermutationR1CS (n l k : ℕ) :
    errorBound.of (lookupAndPermutationR1CS (F := F) n l k) = n + l + k ∧
      honestErrorBound.of (lookupAndPermutationR1CS (F := F) n l k) = n + l + k :=
  ⟨rfl, rfl⟩

end R1CS

end Clean2
