/-
Challenges in an ordinary circuit, and what they cost, on R1CS.

`PermutationChain` checks that `c` is a permutation of `a` through an intermediate `b`, with two
permutation checks on the same challenge. It is generic over the permutation check: it knows
nothing about challenges, identities or rare events, and its proofs are one line each.

On R1CS, the error measure composes like any other measure: an identity check costs its
expression's bound, a permutation check costs `n`, the chain `2 n`.
-/
module

public import Clean2.Challenge.ZeroCheck
public import Clean2.Challenge.Permutation
public import Clean2.Challenge.PermutationRunning
public import Clean2.Challenge.LogUp
public import Clean2.Backends.R1CS

@[expose] public section

namespace Clean2
open Permutation

namespace PermutationChain
variable {Native : Type} [Field Native]

/-- `c` is a permutation of `a`. -/
@[reducible]
def interface (n : ℕ) : Interface Native where
  input := ((Vector Native n × Vector Native n) × Vector Native n) × Native
  inputCType := ((.natives n ×ᵗ .natives n) ×ᵗ .natives n) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun (((a, _), c), _) _ => elems a = elems c
  ProverAssumptions := fun (((a, b), c), _) => elems a = elems b ∧ elems b = elems c

variable {B : Backend} [Field B.Native]

/-- Through `b`, with any permutation check. -/
def impl {n : ℕ} (perm : Impl B (Permutation.interface n)) : Impl B (interface n) where
  main | (((a, b), c), α) => do
    perm ((a, b), α)
    perm ((b, c), α)
  spatial := by
    intro (((a, b), c), α) s h
    obtain ⟨⟨⟨h_a, h_b⟩, h_c⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      fun h => (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    refine ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨h_a, h_b⟩, h_α⟩,
      fun _ h_mono => ⟨Backend.footprintT_ctypeProd_subset.mpr
        ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨h_b.trans h_mono, h_c.trans h_mono⟩, h_α.trans h_mono⟩,
        fun _ _ => Set.empty_subset _⟩⟩
  soundness := by
    intro s env (((a, b), c), α) _ h
    simp only [circuit_norm] at h ⊢
    exact h.1.trans h.2
  completeness := by
    intro s env (((a, b), c), α) _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    exact h_prover

end PermutationChain

/-! ## On R1CS -/

section R1CS
variable {F : Type} [Field F]

/-- R1CS arithmetic uses no challenge. -/
theorem R1CS.errorBound_arith (n : Arith.Name F) (input : (Arith.interface n).Input (R1CS F).Var) (s : ℕ) :
    errorBound.ofOps (((R1CS.arith n).main input).operations s) = 0 := by
  cases n <;> rfl

instance {k : ℕ} (e : RExpr F k) : Impl.Measured errorBound (Identity.impl (R1CS.arith (Native := F)) e) where
  value := e.bound
  value_eq := Identity.errorBound_impl R1CS.arith (fun n input s => R1CS.errorBound_arith n input s) e

/-- The product-form expression has bound `n`. -/
theorem Permutation.bound_expr (n : ℕ) : (Permutation.expr (Native := F) n).bound = n := by
  have h : ∀ (m : ℕ) (g : Fin m → Fin (n + n)),
      (RExpr.prod (F := F) m fun i => RExpr.X - RExpr.leaf (g i)).degN = m ∧
      (RExpr.prod (F := F) m fun i => RExpr.X - RExpr.leaf (g i)).degD = 0 ∧
      (RExpr.prod (F := F) m fun i => RExpr.X - RExpr.leaf (g i)).divDeg = 0 := by
    intro m
    induction m with
    | zero => intro g; exact ⟨rfl, rfl, rfl⟩
    | succ m ih =>
      intro g
      obtain ⟨h1, h2, h3⟩ := ih fun i => g i.succ
      simp only [RExpr.prod, RExpr.degN_mul, RExpr.degD_mul, RExpr.divDeg_mul, RExpr.degN_sub, RExpr.degD_sub,
        RExpr.divDeg_sub, RExpr.degN_X, RExpr.degD_X, RExpr.divDeg_X, RExpr.degN_leaf, RExpr.degD_leaf,
        RExpr.divDeg_leaf, h1, h2, h3]
      exact ⟨by omega, trivial, trivial⟩
  obtain ⟨h1, h2, h3⟩ := h n fun i => Fin.castAdd n i
  obtain ⟨h1', h2', h3'⟩ := h n fun i => Fin.natAdd n i
  simp only [Permutation.expr, RExpr.bound, RExpr.degN_sub, RExpr.divDeg_sub, h1, h2, h3, h1', h2', h3']
  omega

/-- A permutation check on R1CS. -/
def permutationR1CS (n : ℕ) : Impl (R1CS F) (Permutation.interface n) :=
  Permutation.impl (Identity.impl R1CS.arith) n

instance (n : ℕ) : Impl.Measured errorBound (permutationR1CS (F := F) n) where
  value := (Permutation.expr (Native := F) n).bound
  value_eq := by measure [permutationR1CS, Permutation.impl]

/-- Two of them, on one challenge. -/
def permutationChainR1CS (n : ℕ) : Impl (R1CS F) (PermutationChain.interface n) :=
  PermutationChain.impl (permutationR1CS n)

instance (n : ℕ) : Impl.Measured errorBound (permutationChainR1CS (F := F) n) where
  value := 2 • errorBound.of (permutationR1CS (F := F) n)
  value_eq := by measure [permutationChainR1CS, PermutationChain.impl]

/-- The chain's soundness error: `2 n` bad challenges. -/
theorem errorBound_permutationChainR1CS (n : ℕ) : errorBound.of (permutationChainR1CS (F := F) n) = 2 * n := by
  show 2 • (Permutation.expr (Native := F) n).bound = 2 * n
  rw [Permutation.bound_expr, smul_eq_mul]

end R1CS
end Clean2
