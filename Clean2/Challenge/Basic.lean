/-
Verifier challenges in ordinary circuits.

A challenge is a field element that the verifier samples after the prover has committed to some
values. In Clean 2 a challenge is an ordinary variable, passed to the gadgets that use it like any
other input. A gadget that uses it to check something assumes that a *rare event* does not happen
(`Circuit.assumeRare`, `RareEvent` in `Clean2/Core/Circuit.lean`): the event is a predicate on
committed values and the challenge that holds at no more than `bound` challenges, whatever the
committed values are. Soundness proofs may use the assumption; the verifier does not check it.
Everything else is unchanged: interfaces, specs, `Impl`, composition. A circuit that uses no
challenge assumes no rare event.

This file proves, once, what the assumptions cost:

- `errorBound`: the sum of the bounds of the rare events of a circuit, a `Measure`, so that a
  parent reads it off its children's closed forms (`Impl.Measured errorBound`);
- `Impl.soundness_error`: fix the values of a set `C` of committed cells, which contains the
  inputs and everything the rare events depend on (except the challenge). Then the challenges at
  which some assignment satisfies the real constraints but not the spec are at most
  `errorBound`. For a circuit without challenges, the bound is `0`: ordinary soundness.

Why the committed values must be fixed first: a cheating prover chooses the cells it fills after
the challenge as arbitrary functions of it. That is why a rare event may only depend on committed
values (and why constraints mentioning a challenge are never read as identities in `F[X]`, see
`NaiveSymbolic.lean`). In `soundness_error`, every cell outside `C` is quantified after the
challenge, which over-approximates the real protocol.
-/
module

public import Clean2.Core
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
rare events it assumes. A measure, so that it composes like any other. -/
def errorBound : B.Measure ℕ where
  op _ := 0
  rare ev := ev.bound

@[circuit_norm] theorem errorBound_op (op : B.Op) : (errorBound (B := B)).op op = 0 := rfl
@[circuit_norm] theorem errorBound_rare (ev : RareEvent B) : (errorBound (B := B)).rare ev = ev.bound := rfl

/-- A call contributes the error of the callee's operations. -/
theorem errorBound_call {c : Interface B.Native} (impl : Impl B c) (s : B.State) (input : c.Input B.Var) :
    errorBound.flat (impl.toSubcircuit s input).ops + errorBound.rares (impl.toSubcircuit s input).events =
      errorBound.ofOps ((impl.main input).operations s) :=
  Backend.Measure.flat_toFlat _ _

theorem errorBound_ofOps (ops : Ops B) : errorBound.ofOps ops = (ops.events.map RareEvent.bound).sum := by
  rw [← Backend.Measure.flat_toFlat]
  have h0 : ∀ l : List B.Op, errorBound.flat l = 0 := by
    intro l; induction l <;> simp_all [Backend.Measure.flat, errorBound]
  rw [h0, zero_add]
  simp [Backend.Measure.rares, errorBound]

namespace Impl
variable {c : Interface B.Native}

/-- **Soundness error.** Fix the values `env₁` of a set `C` of committed cells, which contains the
input and everything the rare events of the circuit depend on (except the challenge `α`). If the
input satisfies the assumptions, then the challenges at which some assignment agreeing with `env₁`
on `C` satisfies the real constraints but not the spec are at most `errorBound` many. -/
theorem soundness_error (impl : Impl B c) (s : B.State) (input : c.Input B.Var)
    (C : Set B.Cell) (α : B.Var) (env₁ : B.Cell → B.Native)
    (h_input : B.footprintT input ⊆ C)
    (h_events : ∀ ev ∈ ((impl.main input).operations s).events,
      (∀ i : Fin ev.m, B.footprint ev.committed[i] ⊆ C) ∧ ev.challenge = α)
    (h_assumptions : c.inputCType.Valid (B.evalT env₁ input) ∧
      c.Assumptions (c.inputCType.decode (B.evalT env₁ input))) :
    {a | ∃ env : B.Cell → B.Native, (∀ x ∈ C, env x = env₁ x) ∧ B.eval env α = a ∧
      ((impl.main input).operations s).ConstraintsHold env s ∧
      ¬(c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
        c.Spec (c.inputCType.decode (B.evalT env₁ input))
          (c.outputCType.decode (B.evalT env (impl.output input s))))}.encard ≤
      errorBound.ofOps ((impl.main input).operations s) := by
  rw [errorBound_ofOps]
  refine (Set.encard_le_encard fun a ha => ?_).trans
    (encard_iUnion_list_le ((impl.main input).operations s).events
      (fun ev => {a | ev.Bad (ev.committed.map (B.eval env₁)) a})
      RareEvent.bound fun ev _ => ev.encard_bad_le _)
  obtain ⟨env, h_agree, rfl, h_holds, h_spec⟩ := ha
  have h_input_eq : B.evalT env input = B.evalT env₁ input :=
    Backend.evalT_frame env env₁ input fun x hx => h_agree x (h_input hx)
  -- some rare event happens: otherwise soundness would give the spec
  by_contra h_none
  apply h_spec
  rw [← h_input_eq]
  refine impl.soundness s env input (by rw [h_input_eq]; exact h_assumptions)
    (Ops.soundnessHold_of_constraintsHold (impl.consistent input s) (fun ev hev h_happens => ?_) h_holds)
  apply h_none
  refine ⟨ev, hev, ?_⟩
  -- and it depends only on the committed values, and the challenge
  obtain ⟨h_committed, h_challenge⟩ := h_events ev hev
  have h_map : ev.committed.map (B.eval env) = ev.committed.map (B.eval env₁) := by
    ext i hi
    simp only [Vector.getElem_map]
    exact B.eval_frame env env₁ _ fun x hx => h_agree x (h_committed ⟨i, hi⟩ hx)
  simp only [RareEvent.Happens, h_map, h_challenge] at h_happens
  exact h_happens

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
