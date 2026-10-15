/-
Verifier challenges in ordinary circuits: what the rare-event assumptions cost.

A challenge is a field element that the verifier samples after the prover has committed to some
values. In Clean 2 it is an ordinary variable, passed to the gadgets that use it like any other
input. Gadgets that use it may assume that a *rare event* does not happen (`RareEvent` in
`Clean2/Core/Circuit.lean`): a predicate on committed values and the challenge that holds at no
more than `bound` challenges, whatever the committed values are. There are two kinds:

- for soundness (`Circuit.assumeRare`): soundness proofs may assume it, the verifier does not
  check it. A boundary (`AssertIdentity`) assumes one: "the identity fails, but not at `α`".
- for completeness (`Circuit.assumeRareHonest`): the honest prover may assume it. A row that
  divides by `α - v` assumes one: "`α = v`".

Everything else is unchanged: interfaces, specs, `Impl`, composition. A circuit that uses no
challenge assumes no rare event. This file proves, once, what the assumptions cost:

- `errorBound`, `honestErrorBound`: the sums of the bounds of the two kinds of events. Measures,
  so that a parent reads them off its children's closed forms (`Impl.Measured`), like cost.
- `Impl.soundness_error`: with the committed cells fixed, the challenges at which some assignment
  satisfies the real constraints but not the spec are at most `errorBound` many. For a circuit
  without challenges, the bound is `0`: ordinary soundness.
- `Impl.completeness_error`: with the committed cells fixed, the challenges at which the honest
  prover can fail are at most `honestErrorBound` many.

Why the committed values must be fixed first: a cheating prover chooses the cells it fills after
the challenge as arbitrary functions of it. That is why a rare event may only depend on committed
values, and why constraints mentioning a challenge are never read as identities in `F[X]`
(`NaiveSymbolic.lean`). In both theorems, every cell outside the committed ones is quantified
after the challenge, which over-approximates the real protocol.
-/
module

public import Clean2.Challenge.Phase
public import Lean.Elab.Tactic
meta import Clean2.Core.Spatial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Clean2
open Polynomial

/-! ## Counting -/

section Counting
variable {F : Type} [Field F]

/-- The bad challenges of a polynomial check: `P` is not zero, but vanishes at `α`. -/
def polyBad (P : F[X]) (α : F) : Prop := P ≠ 0 ∧ P.eval α = 0

/-- A nonzero polynomial vanishes at no more points than its degree. -/
theorem encard_polyBad_le (P : F[X]) : {α | polyBad P α}.encard ≤ P.natDegree := by
  classical
  by_cases hP : P = 0
  · simp [polyBad, hP]
  have h : {α | polyBad P α} = ↑P.roots.toFinset := by
    ext α
    simp [polyBad, hP, mem_roots hP, IsRoot]
  rw [h, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  exact (Multiset.toFinset_card_le _).trans (card_roots' P)

omit [Field F] in
/-- The bad sets of several rare events: the bounds add. -/
theorem encard_iUnion_list_le {ι : Type} (l : List ι) (S : ι → Set F) (b : ι → ℕ)
    (h : ∀ i ∈ l, (S i).encard ≤ b i) :
    {α | ∃ i ∈ l, α ∈ S i}.encard ≤ ((l.map b).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have h_union : {α | ∃ j ∈ i :: l, α ∈ S j} = S i ∪ {α | ∃ j ∈ l, α ∈ S j} := by
      ext α; simp
    rw [h_union, List.map_cons, List.sum_cons, Nat.cast_add]
    exact (Set.encard_union_le _ _).trans
      (add_le_add (h i (by simp)) (ih fun j hj => h j (by simp [hj])))

end Counting

/-! ## The soundness error of a circuit -/

variable {B : Backend}

/-- The soundness error of a circuit, as a number of bad challenges: the sum of the bounds of the
rare events it assumes for soundness. A measure, so that it composes like any other. -/
def errorBound : B.Measure ℕ where
  op _ := 0
  rare ev := ev.bound

/-- The completeness error of a circuit, as a number of bad challenges: the sum of the bounds of
the rare events the honest prover assumes. -/
def honestErrorBound : B.Measure ℕ where
  op _ := 0
  rareHonest ev := ev.bound

@[circuit_norm] theorem errorBound_op (op : B.Op) : (errorBound (B := B)).op op = 0 := rfl
@[circuit_norm] theorem errorBound_rare (ev : RareEvent B) : (errorBound (B := B)).rare ev = ev.bound := rfl
@[circuit_norm] theorem errorBound_rareHonest (ev : RareEvent B) : (errorBound (B := B)).rareHonest ev = 0 := rfl
@[circuit_norm] theorem honestErrorBound_op (op : B.Op) : (honestErrorBound (B := B)).op op = 0 := rfl
@[circuit_norm] theorem honestErrorBound_rare (ev : RareEvent B) : (honestErrorBound (B := B)).rare ev = 0 := rfl
@[circuit_norm] theorem honestErrorBound_rareHonest (ev : RareEvent B) :
    (honestErrorBound (B := B)).rareHonest ev = ev.bound := rfl

/-- A call contributes the measure of the callee's operations. -/
theorem measure_call {M : Type} [AddCommMonoid M] (μ : B.Measure M) {c : Interface B.Native} (impl : Impl B c)
    (s : B.State) (input : c.Input B.Var) :
    μ.flat (impl.toSubcircuit s input).ops +
      μ.rares (impl.toSubcircuit s input).events (impl.toSubcircuit s input).honestEvents =
      μ.ofOps ((impl.main input).operations s) :=
  Backend.Measure.flat_toFlat _ _

theorem errorBound_ofOps (ops : Ops B) : errorBound.ofOps ops = (ops.events.map RareEvent.bound).sum := by
  rw [← Backend.Measure.flat_toFlat]
  have h0 : ∀ l : List B.Op, errorBound.flat l = 0 := by
    intro l; induction l <;> simp_all [Backend.Measure.flat, errorBound]
  have h1 : ∀ l : List (RareEvent B), (l.map errorBound.rareHonest).sum = 0 := by
    intro l; induction l <;> simp_all [errorBound]
  rw [h0, zero_add, Backend.Measure.rares, h1, add_zero]
  rfl

theorem honestErrorBound_ofOps (ops : Ops B) :
    honestErrorBound.ofOps ops = (ops.honestEvents.map RareEvent.bound).sum := by
  rw [← Backend.Measure.flat_toFlat]
  have h0 : ∀ l : List B.Op, honestErrorBound.flat l = 0 := by
    intro l; induction l <;> simp_all [Backend.Measure.flat, honestErrorBound]
  have h1 : ∀ l : List (RareEvent B), (l.map honestErrorBound.rare).sum = 0 := by
    intro l; induction l <;> simp_all [honestErrorBound]
  rw [h0, zero_add, Backend.Measure.rares, h1, zero_add]
  rfl

/-- A circuit that assumes no rare event has no soundness error: every circuit that does not use
a challenge, once it says so (`Impl.NoEvents`). -/
instance (priority := low) Impl.errorBound_of_noEvents {c : Interface B.Native} (impl : Impl B c)
    [h : Impl.NoEvents impl] : Impl.Measured errorBound impl where
  value := 0
  value_eq input s := by rw [errorBound_ofOps, h.events_eq]; rfl

/-- A circuit that assumes no rare event has no completeness error. -/
instance (priority := low) Impl.honestErrorBound_of_noEvents {c : Interface B.Native} (impl : Impl B c)
    [h : Impl.NoEvents impl] : Impl.Measured honestErrorBound impl where
  value := 0
  value_eq input s := by rw [honestErrorBound_ofOps, h.honestEvents_eq]; rfl

@[circuit_norm]
theorem errorBound_of_noEvents {c : Interface B.Native} (impl : Impl B c) [Impl.NoEvents impl] :
    errorBound.of (inst := Impl.errorBound_of_noEvents impl) impl = 0 := rfl

@[circuit_norm]
theorem honestErrorBound_of_noEvents {c : Interface B.Native} (impl : Impl B c) [Impl.NoEvents impl] :
    honestErrorBound.of (inst := Impl.honestErrorBound_of_noEvents impl) impl = 0 := rfl

/-- What a concatenation of committed values reads. For the spatial obligation of a call. -/
theorem Backend.footprintT_append_subset {n m : ℕ} {a : Vector B.Var n} {b : Vector B.Var m} {S : Set B.Cell}
    (ha : B.footprintT (M := natives n) a ⊆ S) (hb : B.footprintT (M := natives m) b ⊆ S) :
    B.footprintT (M := natives (n + m)) (a ++ b) ⊆ S := by
  rw [Backend.footprintT_natives] at ha hb ⊢
  refine Set.iUnion_subset fun i => ?_
  rw [Fin.getElem_fin, Vector.getElem_append]
  split
  · exact (Set.subset_iUnion (fun j : Fin n => B.footprint a[j]) ⟨i, by omega⟩).trans ha
  · exact (Set.subset_iUnion (fun j : Fin m => B.footprint b[j]) ⟨i - n, by omega⟩).trans hb

namespace Impl
variable {c : Interface B.Native}

/-- The rare events, each with the challenges at which it happens for the committed value `x`:
together, a superset of the bad challenges, of size at most the sum of the bounds. -/
theorem encard_bad_le {κ T : Type} {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}
    (evs : List (RareEvent B)) (h : ∀ ev ∈ evs, ev.Phased K A) (x : κ) (S : Set T)
    (hS : ∀ a ∈ S, ∃ ev ∈ evs, ∃ env, K env = x ∧ A env = a ∧ ev.Happens env) :
    S.encard ≤ ((evs.map RareEvent.bound).sum : ℕ) :=
  (Set.encard_le_encard fun a ha => hS a ha).trans
    (encard_iUnion_list_le evs (fun ev => {a | ∃ env, K env = x ∧ A env = a ∧ ev.Happens env})
      RareEvent.bound fun ev hev => (h ev hev).encard_le x)

/-- The bad challenges for soundness, with the committed part `x` of the input fixed: those at which
some assignment, with that committed part and satisfying the assumptions, satisfies the real
constraints but not the spec. -/
def BadChallenges {ph : c.Phases} (impl : Impl B c) (_ : Phased impl ph) (s : B.State) (input : c.Input B.Var)
    (x : ph.Committed) : Set ph.Challenge :=
  {a | ∃ env : B.Cell → B.Native, ph.key input env = x ∧ ph.chal input env = a ∧
    c.inputCType.Valid (B.evalT env input) ∧ c.Assumptions (c.inputCType.decode (B.evalT env input)) ∧
    ((impl.main input).operations s).ConstraintsHold env s ∧
    ¬(c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
      c.Spec (c.inputCType.decode (B.evalT env input))
        (c.outputCType.decode (B.evalT env (impl.output input s))))}

/-- The bad challenges for completeness, with the committed part `x` of the input fixed: those at
which the honest prover can fail, starting from some assignment of the heap with that committed
part and satisfying the prover assumptions. -/
def HonestFailures {ph : c.Phases} (impl : Impl B c) (_ : Phased impl ph) (s : B.State) (input : c.Input B.Var)
    (x : ph.Committed) : Set ph.Challenge :=
  {a | ∃ env₀ : B.Cell → B.Native, ph.key input env₀ = x ∧ ph.chal input env₀ = a ∧
    c.inputCType.Valid (B.evalT env₀ input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env₀ input)) ∧
    ¬∃ env : B.Cell → B.Native, (∀ x ∈ B.Alloc s, env x = env₀ x) ∧
      ((impl.main input).operations s).ConstraintsHold env s}

/-- The soundness error, for any committed key `K` and challenge `A` with respect to which the
rare events are phased: the form for a circuit that draws its challenge itself (`Protocol`). -/
theorem soundness_error_ops {κ T : Type} (impl : Impl B c) (s : B.State) (input : c.Input B.Var)
    {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}
    (h_phased : ((impl.main input).operations s).Phased K A) (x : κ) :
    {a | ∃ env : B.Cell → B.Native, K env = x ∧ A env = a ∧
      c.inputCType.Valid (B.evalT env input) ∧ c.Assumptions (c.inputCType.decode (B.evalT env input)) ∧
      ((impl.main input).operations s).ConstraintsHold env s ∧
      ¬(c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
        c.Spec (c.inputCType.decode (B.evalT env input))
          (c.outputCType.decode (B.evalT env (impl.output input s))))}.encard ≤
      errorBound.ofOps ((impl.main input).operations s) := by
  rw [errorBound_ofOps]
  refine encard_bad_le _ (fun ev hev => h_phased ev (List.mem_append_left _ hev)) x _ ?_
  rintro a ⟨env, h_K, rfl, h_valid, h_assumptions, h_holds, h_spec⟩
  -- some rare event happens: otherwise soundness would give the spec
  by_contra h_none
  push Not at h_none
  exact h_spec (impl.soundness s env input ⟨h_valid, h_assumptions⟩
    (Ops.soundnessHold_of_constraintsHold (impl.consistent input s)
      (fun ev hev h_happens => h_none ev hev env h_K rfl h_happens) h_holds))

/-- The completeness error, for any committed key `K` and challenge `A` that are fixed by the heap
and with respect to which the rare events of the honest prover are phased. -/
theorem completeness_error_ops {κ T : Type} (impl : Impl B c) (s : B.State) (input : c.Input B.Var)
    (h_in : B.footprintT input ⊆ B.Alloc s)
    {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}
    (h_phased : ((impl.main input).operations s).Phased K A)
    (h_heap : ∀ env env₀ : B.Cell → B.Native, (∀ x ∈ B.Alloc s, env x = env₀ x) → K env = K env₀ ∧ A env = A env₀)
    (x : κ) :
    {a | ∃ env₀ : B.Cell → B.Native, K env₀ = x ∧ A env₀ = a ∧
      c.inputCType.Valid (B.evalT env₀ input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env₀ input)) ∧
      ¬∃ env : B.Cell → B.Native, (∀ x ∈ B.Alloc s, env x = env₀ x) ∧
        ((impl.main input).operations s).ConstraintsHold env s}.encard ≤
      honestErrorBound.ofOps ((impl.main input).operations s) := by
  rw [honestErrorBound_ofOps]
  refine encard_bad_le _ (fun ev hev => h_phased ev (List.mem_append_right _ hev)) x _ ?_
  rintro a ⟨env₀, h_K, rfl, h_valid, h_prover, h_fail⟩
  -- if no rare event of the honest prover happens, an honest assignment is accepted
  by_contra h_none
  push Not at h_none
  refine h_fail ?_
  have h_hev : ∀ env : B.Cell → B.Native, (∀ x ∈ B.Alloc s, env x = env₀ x) →
      ∀ ev ∈ ((impl.main input).operations s).honestEvents, ¬ev.Happens env := by
    intro env h_agree ev hev h_happens
    obtain ⟨h_K', h_A'⟩ := h_heap env env₀ h_agree
    exact h_none ev hev env (h_K'.trans h_K) h_A' h_happens
  obtain ⟨env, h_agree, h_holds, -⟩ := impl.exists_honest_env input s env₀ h_in ⟨h_valid, h_prover⟩ h_hev
  exact ⟨env, h_agree, h_holds⟩

/-- **Soundness error.** Fix the committed part `x` of the input. The challenges at which some
assignment, with that committed part and satisfying the assumptions, satisfies the real
constraints but not the spec are at most `errorBound` many.

The committed part and the challenge are those of the interface's phase annotation `ph`, and the
phase contract (`Impl.Phased`) is what makes the rare events depend on nothing else. -/
theorem soundness_error {ph : c.Phases} (impl : Impl B c) [h_phased : Phased impl ph]
    (s : B.State) (input : c.Input B.Var) (x : ph.Committed) :
    (impl.BadChallenges h_phased s input x).encard ≤ errorBound.ofOps ((impl.main input).operations s) :=
  impl.soundness_error_ops s input (h_phased.phased input s) x

/-- **Completeness error.** Fix the committed part `x` of the input, which exists in the heap.
The challenges at which the honest prover can fail, starting from some assignment of the heap
with that committed part and satisfying the prover assumptions, are at most `honestErrorBound`
many. -/
theorem completeness_error {ph : c.Phases} (impl : Impl B c) [h_phased : Phased impl ph]
    (s : B.State) (input : c.Input B.Var) (h_in : B.footprintT input ⊆ B.Alloc s) (x : ph.Committed) :
    (impl.HonestFailures h_phased s input x).encard ≤ honestErrorBound.ofOps ((impl.main input).operations s) := by
  refine impl.completeness_error_ops s input h_in (h_phased.phased input s) (fun env env₀ h_agree => ?_) x
  -- the input, hence its committed part and its challenge, is in the heap
  have h_eq : B.evalT env input = B.evalT env₀ input :=
    Backend.evalT_frame env env₀ input fun x hx => h_agree x (h_in hx)
  simp only [Interface.Phases.key, Interface.Phases.chal, h_eq, and_self]

/-- The soundness error, read off the closed form of `errorBound`. -/
theorem soundness_error_of {ph : c.Phases} (impl : Impl B c) [h_phased : Phased impl ph] [Measured errorBound impl]
    (s : B.State) (input : c.Input B.Var) (x : ph.Committed) :
    (impl.BadChallenges h_phased s input x).encard ≤ errorBound.of impl := by
  rw [Backend.Measure.of, ← Measured.value_eq input s]
  exact impl.soundness_error s input x

/-- The completeness error, read off the closed form of `honestErrorBound`. -/
theorem completeness_error_of {ph : c.Phases} (impl : Impl B c) [h_phased : Phased impl ph]
    [Measured honestErrorBound impl] (s : B.State) (input : c.Input B.Var) (h_in : B.footprintT input ⊆ B.Alloc s)
    (x : ph.Committed) :
    (impl.HonestFailures h_phased s input x).encard ≤ honestErrorBound.of impl := by
  rw [Backend.Measure.of, ← Measured.value_eq input s]
  exact impl.completeness_error s input h_in x

end Impl

/-- The second half of `spatial`: split a normalized spatial goal along `∧` and `→` and close the
leaves from the hypotheses. For loop lemmas, where the goal is not an `Impl`'s obligation. -/
syntax "spatial_split" : tactic

meta section
open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| spatial_split) => spatialSplit #[]
end

end Clean2
