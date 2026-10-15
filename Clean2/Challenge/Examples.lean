/-
Challenges in an ordinary circuit, row by row, and what they cost.

- `LookupAndPermutation` checks a lookup and a permutation with the same challenge. It is generic
  over both checks: it knows nothing about challenges, symbolic meanings or rare events, and its
  proofs are one line each.
- `Stack`: the whole stack of gadgets, on any backend, for any challenge field: generic over the
  native arithmetic and the arithmetic of the challenge field. Both errors are measures, read off
  the parts.
- On R1CS, closed into protocols with the native `challenge` operation, twice: with the challenge
  in the native field (`KArith.native`), and in an extension of degree `d` (`KArith.ofBasis`),
  drawn as `d` native challenges. The same gadgets, the same bounds, counted in `K`.
-/
module

public import Clean2.Challenge.GrandProductRow
public import Clean2.Backends.R1CS
public import Clean2.Backends.Plonkish
public import Clean2.Challenge.Extension

@[expose] public section

namespace Clean2

namespace LookupAndPermutation
open Permutation
variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- `f` is looked up in `t` with multiplicities `μ`, and `b` is a permutation of `a`. -/
@[reducible]
def contract (n l k : ℕ) : Interface F where
  input := ((Vector F n × Vector F n) × Vector F l) × (Vector F k × Vector F k)
  inputCType := ((.natives n ×ᵗ .natives n) ×ᵗ .natives l) ×ᵗ (.natives k ×ᵗ .natives k)
  output := Unit
  outputCType := .unit
  Spec := fun (((t, μ), f), (a, b)) _ => (∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), μ[i]) ∧ elems a = elems b
  ProverAssumptions := fun (((t, μ), f), (a, b)) => (∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), μ[i]) ∧ elems a = elems b

/-- The check, given a challenge: everything else is committed. -/
@[reducible]
def interface (kty : CType F K) (n l k : ℕ) : Interface F := (contract n l k).withChallenge kty

@[reducible]
def phases (kty : CType F K) (n l k : ℕ) : (interface kty n l k).Phases := Interface.withChallenge.phases _ _

variable {B : Backend} [Field B.Native] [DecidableEq B.Native] [Algebra B.Native K] {kty : CType B.Native K}
  [kty.Faithful] {n l k : ℕ} (lookup : Impl B (Lookup.interface kty n l)) (perm : Impl B (PermutationRow.interface kty k))

/-- Both checks, on one challenge. -/
def impl : Impl B (interface kty n l k) where
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

instance [Impl.Phased lookup (Lookup.phases kty n l)] [Impl.Phased perm (PermutationRow.phases kty k)] :
    Impl.Phased (impl lookup perm) (phases kty n l k) := by
  phased [impl]

end LookupAndPermutation

/-! ## The stack, on any backend and any challenge field -/

namespace Stack
variable {B : Backend} [Field B.Native] [DecidableEq B.Native] {K : Type} [Field K] [Algebra B.Native K]
  (kty : CType B.Native K) [kty.Faithful]
  (arith : ∀ n, Impl B (Arith.interface n)) [∀ n, Impl.NoEvents (arith n)]
  (karith : ∀ n, Impl B (KArith.interface kty n)) [∀ n, Impl.NoEvents (karith n)]

def logUpRow : Impl B (LogUpRow.interface kty) := LogUpRow.impl kty karith
instance : Impl.Phased (logUpRow kty karith) (LogUpRow.phases kty) :=
  inferInstanceAs (Impl.Phased (LogUpRow.impl kty karith) _)
instance : Impl.Measured errorBound (logUpRow kty karith) where
  value := 0
  value_eq := by measure [logUpRow, LogUpRow.impl]
instance : Impl.Measured honestErrorBound (logUpRow kty karith) where
  value := 1
  value_eq := by measure [logUpRow, LogUpRow.impl, LogUpRow.event]

def logUpSum (n : ℕ) : Impl B (LogUpSum.interface kty n) := LogUpSum.impl kty karith (logUpRow kty karith) n
instance (n : ℕ) : Impl.Phased (logUpSum kty karith n) (LogUpSum.phases kty n) :=
  inferInstanceAs (Impl.Phased (LogUpSum.impl kty karith (logUpRow kty karith) n) _)
instance (n : ℕ) : Impl.Measured errorBound (logUpSum kty karith n) where
  value := 0
  value_eq := by
    intro ((v, m), α) s
    simp only [logUpSum, LogUpSum.impl, LogUpSum.loop, circuit_norm]
    rw [Circuit.foldr_measure_const errorBound _ _ 0 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 0 = 0
    simp
instance (n : ℕ) : Impl.Measured honestErrorBound (logUpSum kty karith n) where
  value := n
  value_eq := by
    intro ((v, m), α) s
    simp only [logUpSum, LogUpSum.impl, LogUpSum.loop, circuit_norm]
    rw [Circuit.foldr_measure_const honestErrorBound _ _ 1 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 1 = n
    simp

omit [DecidableEq B.Native] in
theorem errorBound_logUpSum (n : ℕ) : errorBound.of (logUpSum kty karith n) = 0 := rfl
omit [DecidableEq B.Native] in
theorem honestErrorBound_logUpSum (n : ℕ) : honestErrorBound.of (logUpSum kty karith n) = n := rfl

/-- The boundary: its expression's degree bound, for soundness; nothing for completeness. -/
def boundary (k d : ℕ) (R : Vector B.Native k → RatFunc K) : Impl B (AssertIdentity.interface kty k d R) :=
  AssertIdentity.impl kty karith d R
instance (k d : ℕ) (R : Vector B.Native k → RatFunc K) :
    Impl.Phased (boundary kty karith k d R) (AssertIdentity.phases kty k d R) :=
  inferInstanceAs (Impl.Phased (AssertIdentity.impl kty karith d R) _)
instance (k d : ℕ) (R : Vector B.Native k → RatFunc K) : Impl.Measured errorBound (boundary kty karith k d R) where
  value := d
  value_eq := by measure [boundary, AssertIdentity.impl, AssertIdentity.event]
instance (k d : ℕ) (R : Vector B.Native k → RatFunc K) :
    Impl.Measured honestErrorBound (boundary kty karith k d R) where
  value := 0
  value_eq := by measure [boundary, AssertIdentity.impl]

omit [DecidableEq B.Native] in
theorem errorBound_boundary (k d : ℕ) (R : Vector B.Native k → RatFunc K) :
    errorBound.of (boundary kty karith k d R) = d := rfl
omit [DecidableEq B.Native] in
theorem honestErrorBound_boundary (k d : ℕ) (R : Vector B.Native k → RatFunc K) :
    honestErrorBound.of (boundary kty karith k d R) = 0 := rfl

noncomputable def lookup (n l : ℕ) : Impl B (Lookup.interface kty n l) :=
  Lookup.impl arith karith (logUpSum kty karith n) (logUpSum kty karith l) (boundary kty karith _ _ _)
instance (n l : ℕ) : Impl.Phased (lookup kty arith karith n l) (Lookup.phases kty n l) :=
  inferInstanceAs (Impl.Phased (Lookup.impl arith karith (logUpSum kty karith n) (logUpSum kty karith l)
    (boundary kty karith _ _ _)) _)
instance (n l : ℕ) : Impl.Measured errorBound (lookup kty arith karith n l) where
  value := n + l
  value_eq := by measure [lookup, Lookup.impl, errorBound_logUpSum, honestErrorBound_logUpSum,
    errorBound_boundary, honestErrorBound_boundary]
instance (n l : ℕ) : Impl.Measured honestErrorBound (lookup kty arith karith n l) where
  value := n + l
  value_eq := by measure [lookup, Lookup.impl, errorBound_logUpSum, honestErrorBound_logUpSum,
    errorBound_boundary, honestErrorBound_boundary]

theorem errorBound_lookup (n l : ℕ) : errorBound.of (lookup kty arith karith n l) = n + l := rfl
theorem honestErrorBound_lookup (n l : ℕ) : honestErrorBound.of (lookup kty arith karith n l) = n + l := rfl

def productRow : Impl B (ProductRow.interface kty) := ProductRow.impl kty karith
instance : Impl.Phased (productRow kty karith) (ProductRow.phases kty) :=
  inferInstanceAs (Impl.Phased (ProductRow.impl kty karith) _)
instance : Impl.Measured errorBound (productRow kty karith) where
  value := 0
  value_eq := by measure [productRow, ProductRow.impl]
instance : Impl.Measured honestErrorBound (productRow kty karith) where
  value := 1
  value_eq := by measure [productRow, ProductRow.impl, ProductRow.event]

def productLoop (n : ℕ) : Impl B (ProductLoop.interface kty n) :=
  ProductLoop.impl kty karith (productRow kty karith) n
instance (n : ℕ) : Impl.Phased (productLoop kty karith n) (ProductLoop.phases kty n) :=
  inferInstanceAs (Impl.Phased (ProductLoop.impl kty karith (productRow kty karith) n) _)
instance (n : ℕ) : Impl.Measured errorBound (productLoop kty karith n) where
  value := 0
  value_eq := by
    intro ((v, m), α) s
    simp only [productLoop, ProductLoop.impl, ProductLoop.loop, circuit_norm]
    rw [Circuit.foldr_measure_const errorBound _ _ 0 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 0 = 0
    simp
instance (n : ℕ) : Impl.Measured honestErrorBound (productLoop kty karith n) where
  value := n
  value_eq := by
    intro ((v, m), α) s
    simp only [productLoop, ProductLoop.impl, ProductLoop.loop, circuit_norm]
    rw [Circuit.foldr_measure_const honestErrorBound _ _ 1 fun i acc s => by simp only [circuit_norm]; rfl]
    show 0 + n • 1 = n
    simp

omit [DecidableEq B.Native] in
theorem errorBound_productLoop (n : ℕ) : errorBound.of (productLoop kty karith n) = 0 := rfl
omit [DecidableEq B.Native] in
theorem honestErrorBound_productLoop (n : ℕ) : honestErrorBound.of (productLoop kty karith n) = n := rfl

noncomputable def permutation (n : ℕ) : Impl B (PermutationRow.interface kty n) :=
  PermutationRow.impl karith (productLoop kty karith n) (boundary kty karith _ _ _)
instance (n : ℕ) : Impl.Phased (permutation kty karith n) (PermutationRow.phases kty n) :=
  inferInstanceAs (Impl.Phased (PermutationRow.impl karith (productLoop kty karith n) (boundary kty karith _ _ _)) _)
instance (n : ℕ) : Impl.Measured errorBound (permutation kty karith n) where
  value := n
  value_eq := by measure [permutation, PermutationRow.impl, errorBound_productLoop, honestErrorBound_productLoop,
    errorBound_boundary, honestErrorBound_boundary]
instance (n : ℕ) : Impl.Measured honestErrorBound (permutation kty karith n) where
  value := n
  value_eq := by measure [permutation, PermutationRow.impl, errorBound_productLoop, honestErrorBound_productLoop,
    errorBound_boundary, honestErrorBound_boundary]

omit [DecidableEq B.Native] in
theorem errorBound_permutation (n : ℕ) : errorBound.of (permutation kty karith n) = n := rfl
omit [DecidableEq B.Native] in
theorem honestErrorBound_permutation (n : ℕ) : honestErrorBound.of (permutation kty karith n) = n := rfl

/-- A lookup and a permutation check on one challenge. -/
noncomputable def lookupAndPermutation (n l k : ℕ) : Impl B (LookupAndPermutation.interface kty n l k) :=
  LookupAndPermutation.impl (lookup kty arith karith n l) (permutation kty karith k)
instance (n l k : ℕ) :
    Impl.Phased (lookupAndPermutation kty arith karith n l k) (LookupAndPermutation.phases kty n l k) :=
  inferInstanceAs (Impl.Phased (LookupAndPermutation.impl (lookup kty arith karith n l) (permutation kty karith k)) _)
instance (n l k : ℕ) : Impl.Measured errorBound (lookupAndPermutation kty arith karith n l k) where
  value := n + l + k
  value_eq := by measure [lookupAndPermutation, LookupAndPermutation.impl, errorBound_lookup,
    honestErrorBound_lookup, errorBound_permutation, honestErrorBound_permutation]
instance (n l k : ℕ) : Impl.Measured honestErrorBound (lookupAndPermutation kty arith karith n l k) where
  value := n + l + k
  value_eq := by measure [lookupAndPermutation, LookupAndPermutation.impl, errorBound_lookup,
    honestErrorBound_lookup, errorBound_permutation, honestErrorBound_permutation]

/-- **Both errors, read off the parts.** A lookup of `l` values into a table of `n`, and a
permutation of `k` values, on one challenge: a false statement is accepted at no more than
`n + l + k` values of the challenge, and the honest prover fails at no more than `n + l + k`. -/
theorem errors_lookupAndPermutation (n l k : ℕ) :
    errorBound.of (lookupAndPermutation kty arith karith n l k) = n + l + k ∧
      honestErrorBound.of (lookupAndPermutation kty arith karith n l k) = n + l + k :=
  ⟨rfl, rfl⟩

end Stack

/-! ## On R1CS -/

section R1CS
variable {F : Type} [Field F] [DecidableEq F]

instance (n : Arith.Name F) : Impl.NoEvents (R1CS.arith n) where
  events_eq input s := by cases n <;> rfl
  honestEvents_eq input s := by cases n <;> rfl

def inverseR1CS : Impl (R1CS F) Inverse.interface := Inverse.impl R1CS.arith
instance : Impl.NoEvents (inverseR1CS (F := F)) := inferInstanceAs (Impl.NoEvents (Inverse.impl R1CS.arith))

/-! ### The challenge in the native field -/

/-- The arithmetic of the native field, as a challenge field. -/
def karithR1CS : ∀ n, Impl (R1CS F) (KArith.interface .native n) := KArith.native R1CS.arith inverseR1CS
instance (n : KArith.Name F F) : Impl.NoEvents (karithR1CS n) :=
  inferInstanceAs (Impl.NoEvents (KArith.native R1CS.arith inverseR1CS n))

/-- A challenge on R1CS: one native operation, a fresh cell. -/
def challengeR1CS (m : ℕ) : Impl (R1CS F) (Challenge.interface m .native) where
  main vars := R1CS.challenge vars
  spatial := by
    intro vars s h
    simp only [circuit_norm]
    exact ⟨h, Linear.singleton_subset_alloc_succ s⟩
  soundness := by
    intro s env _ _ _
    simp [circuit_norm]
  completeness := by
    intro s env _ _ _
    simp [circuit_norm]

instance (m : ℕ) : Impl.NoEvents (challengeR1CS (F := F) m) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance (m : ℕ) : Challenge.Free (challengeR1CS (F := F) m) := ⟨fun _ _ _ => ⟨trivial, trivial⟩⟩
instance (m : ℕ) : Impl.Measured R1CS.cost (challengeR1CS (F := F) m) where
  value := (1, 0)
  value_eq _ _ := rfl

/-- The lookup argument, closed: commit to the table, its multiplicities and the lookups, draw
the challenge, check. It implements `Lookup.contract`, which mentions no challenge. -/
noncomputable def lookupProtocolR1CS (n l : ℕ) : Impl (R1CS F) (Lookup.contract n l) :=
  Protocol.impl (challengeR1CS _) (Stack.lookup .native R1CS.arith karithR1CS n l)

/-- **The lookup argument on R1CS.** Fix the committed table, multiplicities and lookups. A false
lookup is accepted at no more than `n + l` values of the drawn challenge, and the honest prover
fails at no more than `n + l`. -/
theorem lookupProtocolR1CS_error (n l : ℕ) (s : ℕ) (x : (Lookup.contract (F := F) n l).Input (R1CS F).Var)
    (h_in : (R1CS F).footprintT x ⊆ (R1CS F).Alloc s) (x₀ : (Lookup.contract (F := F) n l).input) :
    (Protocol.BadChallenges (challengeR1CS _) (Stack.lookup .native R1CS.arith karithR1CS n l) s x x₀).encard ≤
        ↑(n + l) ∧
      (Protocol.HonestFailures (challengeR1CS _) (Stack.lookup .native R1CS.arith karithR1CS n l) s x x₀).encard ≤
        ↑(n + l) := by
  have h₁ := Protocol.soundness_error (challengeR1CS _) (Stack.lookup .native R1CS.arith karithR1CS n l) rfl s x x₀
  have h₂ := Protocol.completeness_error (challengeR1CS _) (Stack.lookup .native R1CS.arith karithR1CS n l) s x h_in x₀
  rw [Stack.errorBound_lookup] at h₁
  rw [Stack.honestErrorBound_lookup] at h₂
  exact ⟨h₁, h₂⟩

/-- **A lookup and a permutation on R1CS, end to end.** One challenge, drawn after committing to
all of it, shared by the two checks and by the two sides of the lookup. Fix the committed values:
a false statement is accepted at no more than `n + l + k` values of the drawn challenge, and the
honest prover fails at no more than `n + l + k`. -/
theorem lookupAndPermutationProtocolR1CS_error (n l k : ℕ) (s : ℕ)
    (x : (LookupAndPermutation.contract (F := F) n l k).Input (R1CS F).Var)
    (h_in : (R1CS F).footprintT x ⊆ (R1CS F).Alloc s)
    (x₀ : (LookupAndPermutation.contract (F := F) n l k).input) :
    (Protocol.BadChallenges (challengeR1CS _) (Stack.lookupAndPermutation .native R1CS.arith karithR1CS n l k)
        s x x₀).encard ≤ ↑(n + l + k) ∧
      (Protocol.HonestFailures (challengeR1CS _) (Stack.lookupAndPermutation .native R1CS.arith karithR1CS n l k)
        s x x₀).encard ≤ ↑(n + l + k) := by
  have h₁ := Protocol.soundness_error (challengeR1CS _)
    (Stack.lookupAndPermutation .native R1CS.arith karithR1CS n l k) rfl s x x₀
  have h₂ := Protocol.completeness_error (challengeR1CS _)
    (Stack.lookupAndPermutation .native R1CS.arith karithR1CS n l k) s x h_in x₀
  rw [(Stack.errors_lookupAndPermutation _ _ _ n l k).1] at h₁
  rw [(Stack.errors_lookupAndPermutation _ _ _ n l k).2] at h₂
  exact ⟨h₁, h₂⟩

/-! ### The challenge in an extension field -/

section Extension
open Module
variable {K : Type} [Field K] [Algebra (R1CS F).Native K] {d : ℕ} (b : Basis (Fin d) (R1CS F).Native K)

/-- A challenge in `K`, on R1CS: `d` native challenges, its coordinates in the basis `b`. -/
def challengeExtR1CS (m : ℕ) : Impl (R1CS F) (Challenge.interface m (KArith.basisType b)) where
  main vars := Circuit.mapFin d fun _ => R1CS.challenge vars
  consistent := by
    intro vars s
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro vars s h
    simp only [circuit_norm] at h ⊢
    exact Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
      (fun i s h_mono => by
        simp only [circuit_norm]
        exact ⟨h.trans h_mono, Linear.singleton_subset_alloc_succ s⟩) id
  soundness := by
    intro s env _ _ _
    simp [circuit_norm]
  completeness := by
    intro s env _ h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm]) h

instance (m : ℕ) : Impl.NoEvents (challengeExtR1CS b m) := by no_events [challengeExtR1CS]

omit [DecidableEq F] in
/-- Challenges constrain nothing. -/
theorem challenges_holds (n m : ℕ) (vars : Vector (LinComb F) m) (s : ℕ) (env : ℕ → F) :
    ((Circuit.mapFin n fun _ => R1CS.challenge vars).operations s).ConstraintsHold env s := by
  induction n generalizing s with
  | zero => simp [circuit_norm, Ops.ConstraintsHold, Ops.toFlat, Backend.FlatHolds]
  | succ n ih =>
    simp only [circuit_norm] at ih ⊢
    simp only [Ops.ConstraintsHold, Ops.toFlat_append, Backend.flatHolds_append] at ih ⊢
    exact ⟨ih s, by simp [Ops.toFlat, Backend.FlatHolds, circuit_norm]⟩

instance (m : ℕ) : Challenge.Free (challengeExtR1CS b m) := ⟨fun vars s env => challenges_holds d m vars s env⟩

/-- The arithmetic of `K`, from the basis `b` and the native arithmetic of R1CS. -/
noncomputable def karithExtR1CS : ∀ n, Impl (R1CS F) (KArith.interface (KArith.basisType b) n) :=
  KArith.ofBasis b R1CS.arith
instance (n : KArith.Name (R1CS F).Native K) : Impl.NoEvents (karithExtR1CS b n) :=
  inferInstanceAs (Impl.NoEvents (KArith.ofBasis b R1CS.arith n))

/-- **A lookup and a permutation on R1CS, with the challenge in an extension.** The same gadgets
and the same proofs as over the native field. Fix the committed values: a false statement is
accepted at no more than `n + l + k` values of the drawn challenge in `K`, and the honest prover
fails at no more than `n + l + k`; with `|K| = |F|^d`, a much smaller fraction. -/
theorem lookupAndPermutationProtocolExtR1CS_error (n l k : ℕ) (s : ℕ)
    (x : (LookupAndPermutation.contract (F := F) n l k).Input (R1CS F).Var)
    (h_in : (R1CS F).footprintT x ⊆ (R1CS F).Alloc s)
    (x₀ : (LookupAndPermutation.contract (F := F) n l k).input) :
    (Protocol.BadChallenges (challengeExtR1CS b _)
        (Stack.lookupAndPermutation _ R1CS.arith (karithExtR1CS b) n l k) s x x₀).encard ≤ ↑(n + l + k) ∧
      (Protocol.HonestFailures (challengeExtR1CS b _)
        (Stack.lookupAndPermutation _ R1CS.arith (karithExtR1CS b) n l k) s x x₀).encard ≤ ↑(n + l + k) := by
  have h₁ := Protocol.soundness_error (challengeExtR1CS b _)
    (Stack.lookupAndPermutation _ R1CS.arith (karithExtR1CS b) n l k) rfl s x x₀
  have h₂ := Protocol.completeness_error (challengeExtR1CS b _)
    (Stack.lookupAndPermutation _ R1CS.arith (karithExtR1CS b) n l k) s x h_in x₀
  rw [(Stack.errors_lookupAndPermutation _ _ _ n l k).1] at h₁
  rw [(Stack.errors_lookupAndPermutation _ _ _ n l k).2] at h₂
  exact ⟨h₁, h₂⟩

end Extension

end R1CS

/-! ## On Plonkish: the same stack, another backend -/

section Plonkish
variable {F : Type} [Field F] [DecidableEq F]

instance (n : Arith.Name F) : Impl.NoEvents (Plonkish.arith n) where
  events_eq input s := by cases n <;> rfl
  honestEvents_eq input s := by cases n <;> rfl

/-- The arithmetic of the native field, from gates. -/
def karithPlonkish : ∀ n, Impl (Plonkish F) (KArith.interface .native n) :=
  KArith.native Plonkish.arith (Inverse.impl Plonkish.arith)
instance (n : KArith.Name F F) : Impl.NoEvents (karithPlonkish n) :=
  inferInstanceAs (Impl.NoEvents (KArith.native Plonkish.arith (Inverse.impl Plonkish.arith) n))

/-- A challenge on Plonkish: a fresh row holding it. -/
def challengePlonkish (m : ℕ) : Impl (Plonkish F) (Challenge.interface m .native) where
  main vars := Plonkish.challenge vars
  spatial := by
    intro vars s h
    simp only [circuit_norm]
    exact ⟨h, by simp [Plonkish.mem_alloc]⟩
  soundness := by
    intro s env _ _ _
    simp [circuit_norm]
  completeness := by
    intro s env _ _ _
    simp [circuit_norm]

instance (m : ℕ) : Impl.NoEvents (challengePlonkish (F := F) m) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance (m : ℕ) : Challenge.Free (challengePlonkish (F := F) m) := ⟨fun _ _ _ => ⟨trivial, trivial⟩⟩

/-- **A lookup and a permutation on Plonkish, end to end.** The same gadgets and the same bounds as
on R1CS: only the arithmetic and the challenge operation differ. -/
theorem lookupAndPermutationProtocolPlonkish_error (n l k : ℕ) (s : ℕ)
    (x : (LookupAndPermutation.contract (F := F) n l k).Input (Plonkish F).Var)
    (h_in : (Plonkish F).footprintT x ⊆ (Plonkish F).Alloc s)
    (x₀ : (LookupAndPermutation.contract (F := F) n l k).input) :
    (Protocol.BadChallenges (challengePlonkish _)
        (Stack.lookupAndPermutation .native Plonkish.arith karithPlonkish n l k) s x x₀).encard ≤ ↑(n + l + k) ∧
      (Protocol.HonestFailures (challengePlonkish _)
        (Stack.lookupAndPermutation .native Plonkish.arith karithPlonkish n l k) s x x₀).encard ≤ ↑(n + l + k) := by
  have h₁ := Protocol.soundness_error (challengePlonkish _)
    (Stack.lookupAndPermutation .native Plonkish.arith karithPlonkish n l k) rfl s x x₀
  have h₂ := Protocol.completeness_error (challengePlonkish _)
    (Stack.lookupAndPermutation .native Plonkish.arith karithPlonkish n l k) s x h_in x₀
  rw [(Stack.errors_lookupAndPermutation _ _ _ n l k).1] at h₁
  rw [(Stack.errors_lookupAndPermutation _ _ _ n l k).2] at h₂
  exact ⟨h₁, h₂⟩

end Plonkish

end Clean2
