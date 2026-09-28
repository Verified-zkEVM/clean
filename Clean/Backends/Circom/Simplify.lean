/-
Certified R1CS constraint simplification.

This module implements the substitution pass over Clean's exported constraints and
proves it correct (`simplifyConstraints_equisat`): the simplified system is
`Equisat`-equivalent to the original with respect to the forbidden (public) signals, in
both directions. See `R1CSSemantics.lean` for the definitions.

## The pass

Constraints are processed in order. Each is first rewritten with the substitutions
found so far and normalized (`simpConstraint`). Then:

* a trivial constraint (`0 = 0`) is dropped;
* a linear constraint on one or two signals whose eliminable side is not forbidden
  becomes a substitution `x ↦ r` (`classify`), which is added to the map while
  keeping it non-overlapping (`addEntry` substitutes `x` in the existing right-hand
  sides);
* everything else is kept.

At the end, the kept constraints are rewritten once more with the final map.

Processing sequentially is what makes contradictions survive: after `x ↦ 3`, the
constraint `x = 5` becomes the constant constraint `-2 = 0`, whose only signal is the
forbidden constant signal `0`, so it is kept. circom's "compute all substitutions,
then apply" order loses it.

The invariant `Inv` maintained across the fold is the substance of the proof: the
substitution map together with the kept constraints is equivalent to the prefix of
constraints processed so far.
-/
module

public import Clean.Backends.Circom.R1CSSemantics

@[expose] public section

namespace Backends.Circom

variable {F : Type} [FiniteField F]

/-! ## Concrete substitution store -/

/-- Substitution entries: `(x, r)` means `x` was eliminated and equals `r`. -/
abbrev SubstEntries (F : Type) := List (ℕ × List (ℕ × F))

def lookupSig : SubstEntries F → ℕ → Option (List (ℕ × F))
  | [], _ => none
  | (j, r) :: rest, i => if i = j then some r else lookupSig rest i

/-- The single substitution `x ↦ r`. -/
def single (x : ℕ) (r : List (ℕ × F)) : Subst F :=
  fun i => if i = x then some r else none

/-- Add `x ↦ r`, substituting `x` in all existing right-hand sides, so that the map stays
non-overlapping. -/
def addEntry (es : SubstEntries F) (x : ℕ) (r : List (ℕ × F)) : SubstEntries F :=
  (x, r) :: es.map fun (y, ry) => (y, applySubst (single x r) ry)

theorem lookupSig_map_applySubst (es : SubstEntries F) (t : Subst F) (i : ℕ) :
    lookupSig (es.map fun (y, ry) => (y, applySubst t ry)) i =
      (lookupSig es i).map (applySubst t) := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨y, ry⟩ := hd
    simp only [List.map_cons, lookupSig]
    split_ifs <;> simp [ih]

theorem lookupSig_addEntry (es : SubstEntries F) (x : ℕ) (r : List (ℕ × F)) (i : ℕ) :
    lookupSig (addEntry es x r) i =
      if i = x then some r else (lookupSig es i).map (applySubst (single x r)) := by
  simp only [addEntry, lookupSig]
  split_ifs with h
  · rfl
  · exact lookupSig_map_applySubst es _ i

theorem lookupSig_addEntry_of_ne {es : SubstEntries F} {x p : ℕ} {r : List (ℕ × F)}
    (hpx : p ≠ x) (hp : lookupSig es p = none) : lookupSig (addEntry es x r) p = none := by
  rw [lookupSig_addEntry, if_neg hpx, hp]; rfl

theorem respects_single {w : ℕ → F} {x : ℕ} {r : List (ℕ × F)} :
    Respects w (single x r) ↔ w x = evalLC w r := by
  constructor
  · intro h
    exact h x r (by simp [single])
  · intro h i r' hi
    by_cases hix : i = x
    · subst hix
      simp [single] at hi
      subst hi
      exact h
    · simp [single, hix] at hi

theorem respects_addEntry {w : ℕ → F} {es : SubstEntries F} {x : ℕ} {r : List (ℕ × F)}
    (hx : lookupSig es x = none) :
    Respects w (lookupSig (addEntry es x r)) ↔ w x = evalLC w r ∧ Respects w (lookupSig es) := by
  constructor
  · intro h
    have hxr : w x = evalLC w r := h x r (by rw [lookupSig_addEntry]; simp)
    refine ⟨hxr, fun i ri hi => ?_⟩
    have hix : i ≠ x := by
      rintro rfl
      rw [hx] at hi
      cases hi
    have h' := h i (applySubst (single x r) ri) (by rw [lookupSig_addEntry, if_neg hix, hi]; rfl)
    rw [h', evalLC_applySubst (respects_single.mpr hxr)]
  · rintro ⟨hxr, hres⟩ i ri hi
    rw [lookupSig_addEntry] at hi
    split_ifs at hi with hix
    · subst hix
      rw [← Option.some.inj hi]
      exact hxr
    · cases hli : lookupSig es i with
      | none => simp [hli] at hi
      | some ri' =>
        simp only [hli, Option.map_some, Option.some.injEq] at hi
        subst hi
        rw [evalLC_applySubst (respects_single.mpr hxr)]
        exact hres i ri' hli

theorem nonOverlapping_addEntry {es : SubstEntries F} {x : ℕ} {r : List (ℕ × F)}
    (hNO : NonOverlapping (lookupSig es)) (hx : lookupSig es x = none)
    (hr : KeyFree (lookupSig es) r) (hxr : ∀ c, (x, c) ∉ r) :
    NonOverlapping (lookupSig (addEntry es x r)) := by
  have hnone : ∀ j, j ≠ x → lookupSig es j = none → lookupSig (addEntry es x r) j = none :=
    fun j hj hjn => lookupSig_addEntry_of_ne hj hjn
  -- every signal of `r` is untouched by the new map
  have hrfree : KeyFree (lookupSig (addEntry es x r)) r := by
    intro j c hj
    exact hnone j (fun h => by subst h; exact hxr _ hj) (hr j c hj)
  intro i ri hi
  rw [lookupSig_addEntry] at hi
  split_ifs at hi with hix
  · rw [← Option.some.inj hi]
    exact hrfree
  · cases hli : lookupSig es i with
    | none => simp [hli] at hi
    | some ri' =>
      simp only [hli, Option.map_some, Option.some.injEq] at hi
      subst hi
      refine keyFree_applySubst_of ?_ ?_
      · intro j' c' hj' hsj'
        have hjx : j' ≠ x := by
          intro h
          simp [single, h] at hsj'
        exact hnone j' hjx (hNO i ri' hli j' c' hj')
      · intro j' r' hj'
        by_cases hjx : j' = x
        · simp [single, hjx] at hj'
          subst hj'
          exact hrfree
        · simp [single, hjx] at hj'

/-! ## Substitution rules -/

/-- What the pass does with a (substituted, normalized) constraint. -/
inductive Action (F : Type) where
  | drop
  | subst (x : ℕ) (r : List (ℕ × F))
  | keep

/-- Rules on a normalized linear constraint `lc = 0`: `x = 0`, `x = k` and `cx·x + cy·y = 0`.
The eliminated signal must not be forbidden (`fb`); among two eliminable signals the larger
index goes. -/
def classify (fb : ℕ → Bool) : Constraint F → Action F
  | ([], [], []) => .drop
  | ([], [], [(x, cx)]) => if fb x = true ∨ cx = 0 then .keep else .subst x []
  | ([], [], [(x, cx), (y, cy)]) =>
    if x = y ∨ cx = 0 ∨ cy = 0 then .keep
    else if fb x = false ∧ (fb y = true ∨ y < x) then .subst x [(y, -(cy / cx))]
    else if fb y = false then .subst y [(x, -(cx / cy))]
    else .keep
  | _ => .keep

theorem classify_drop {fb : ℕ → Bool} {c : Constraint F} (h : classify fb c = .drop) (w : ℕ → F) :
    Constraint.Holds w c := by
  match c, h with
  | ([], [], []), _ => simp [Constraint.Holds]
  | ([], [], [(x', cx)]), h =>
    simp only [classify] at h
    split_ifs at h
  | ([], [], [(x', cx), (y', cy)]), h =>
    simp only [classify] at h
    split_ifs at h
  | (_ :: _, _, _), h => cases h
  | ([], _ :: _, _), h => cases h
  | ([], [], _ :: _ :: _ :: _), h => cases h

/-- Specification of a substitution produced by `classify`: it eliminates a non-forbidden
signal of the constraint, its right-hand side only mentions other signals of the
constraint, and it is equivalent to the constraint. -/
theorem classify_subst {fb : ℕ → Bool} {c : Constraint F} {x : ℕ} {r : List (ℕ × F)}
    (h : classify fb c = .subst x r) :
    fb x = false ∧ (∀ d, (x, d) ∉ r) ∧ (∃ d, (x, d) ∈ c.2.2) ∧
    (∀ i d, (i, d) ∈ r → ∃ d', (i, d') ∈ c.2.2) ∧
    (∀ w : ℕ → F, Constraint.Holds w c ↔ w x = evalLC w r) := by
  match c, h with
  | ([], [], []), h => cases h
  | ([], [], [(x', cx)]), h =>
    simp only [classify] at h
    by_cases hk : fb x' = true ∨ cx = 0
    · rw [if_pos hk] at h
      cases h
    · rw [if_neg hk] at h
      simp only [Action.subst.injEq] at h
      obtain ⟨hx, hr⟩ := h
      rw [← hx, ← hr]
      simp only [not_or, Bool.not_eq_true] at hk
      obtain ⟨hfx, hcx⟩ := hk
      refine ⟨hfx, by simp, ⟨cx, by simp⟩, by simp, fun w => ?_⟩
      simp only [Constraint.Holds, evalLC_cons, evalLC_nil, mul_zero, add_zero]
      constructor
      · intro h
        rcases mul_eq_zero.mp h.symm with h | h
        · exact absurd h hcx
        · exact h
      · intro h
        rw [h, mul_zero]
  | ([], [], [(x', cx), (y', cy)]), h =>
    simp only [classify] at h
    by_cases hA : x' = y' ∨ cx = 0 ∨ cy = 0
    · rw [if_pos hA] at h
      cases h
    · rw [if_neg hA] at h
      simp only [not_or] at hA
      obtain ⟨hxy, hcx, hcy⟩ := hA
      by_cases hB : fb x' = false ∧ (fb y' = true ∨ y' < x')
      · rw [if_pos hB] at h
        simp only [Action.subst.injEq] at h
        obtain ⟨hx, hr⟩ := h
        rw [← hx, ← hr]
        refine ⟨hB.1, ?_, ⟨cx, by simp⟩, ?_, fun w => ?_⟩
        · intro d hd
          simp only [List.mem_singleton, Prod.mk.injEq] at hd
          exact hxy hd.1
        · intro i d hi
          simp only [List.mem_singleton, Prod.mk.injEq] at hi
          exact ⟨cy, by simp [hi.1]⟩
        · simp only [Constraint.Holds, evalLC_cons, evalLC_nil, mul_zero, add_zero]
          constructor
          · intro h
            linear_combination (-cx⁻¹) * h - (w x') * (mul_inv_cancel₀ hcx)
          · intro h
            rw [h]
            linear_combination (cy * w y') * (mul_inv_cancel₀ hcx)
      · rw [if_neg hB] at h
        by_cases hC : fb y' = false
        · rw [if_pos hC] at h
          simp only [Action.subst.injEq] at h
          obtain ⟨hx, hr⟩ := h
          rw [← hx, ← hr]
          refine ⟨hC, ?_, ⟨cy, by simp⟩, ?_, fun w => ?_⟩
          · intro d hd
            simp only [List.mem_singleton, Prod.mk.injEq] at hd
            exact hxy hd.1.symm
          · intro i d hi
            simp only [List.mem_singleton, Prod.mk.injEq] at hi
            exact ⟨cx, by simp [hi.1]⟩
          · simp only [Constraint.Holds, evalLC_cons, evalLC_nil, mul_zero, add_zero]
            constructor
            · intro h
              linear_combination (-cy⁻¹) * h - (w y') * (mul_inv_cancel₀ hcy)
            · intro h
              rw [h]
              linear_combination (cx * w x') * (mul_inv_cancel₀ hcy)
        · rw [if_neg hC] at h
          cases h
  | (_ :: _, _, _), h => cases h
  | ([], _ :: _, _), h => cases h
  | ([], [], _ :: _ :: _ :: _), h => cases h

/-! ## The pass -/

structure SimpState (F : Type) where
  subst : SubstEntries F := []
  /-- Kept constraints, most recent first. -/
  kept : List (Constraint F) := []

/-- Process one constraint: substitute, normalize, then drop / turn into a substitution / keep. -/
def step (fb : ℕ → Bool) (st : SimpState F) (c : Constraint F) : SimpState F :=
  let c' := simpConstraint (lookupSig st.subst) c
  match classify fb c' with
  | .drop => st
  | .subst x r => { st with subst := addEntry st.subst x r }
  | .keep => { st with kept := c' :: st.kept }

/-- The certified simplification pass. `fb` marks the forbidden (public) signals; `fb 0`
must be `true`. Returns the simplified constraints and the substitution map, from which
the eliminated signals' values can be recomputed with `extend`. -/
def simplifyConstraints (fb : ℕ → Bool) (cs : List (Constraint F)) :
    List (Constraint F) × SubstEntries F :=
  let st := cs.foldl (step fb) {}
  (st.kept.reverse.map (simpConstraint (lookupSig st.subst)), st.subst)

/-! ## Correctness -/

/-- The fold invariant: the substitution map is non-overlapping and never eliminates a
forbidden signal, and `(subst, kept)` is equivalent to the processed prefix `pre`. -/
structure Inv (fb : ℕ → Bool) (pre : List (Constraint F)) (st : SimpState F) : Prop where
  nonOverlapping : NonOverlapping (lookupSig st.subst)
  forbidden : ∀ p, fb p = true → lookupSig st.subst p = none
  fwd : ∀ w, Sat w pre → Respects w (lookupSig st.subst) ∧ ∀ c ∈ st.kept, Constraint.Holds w c
  bwd : ∀ w, w 0 = 1 → Respects w (lookupSig st.subst) → (∀ c ∈ st.kept, Constraint.Holds w c) →
    ∀ c ∈ pre, Constraint.Holds w c

/-- The initial invariant holds for an empty list of constraints and an empty simplification state. -/
theorem inv_init (fb : ℕ → Bool) : Inv fb [] ({} : SimpState F) where
  nonOverlapping := fun i r h => by simp [lookupSig] at h
  forbidden := fun _ _ => rfl
  fwd := fun w _ => ⟨fun i r h => by simp [lookupSig] at h, fun c hc => by simp at hc⟩
  bwd := fun w _ _ _ c hc => by simp at hc

/-- The invariant is preserved by a single simplification step. -/
theorem step_inv {fb : ℕ → Bool} {pre : List (Constraint F)} {st : SimpState F}
    (hinv : Inv fb pre st) (c : Constraint F) : Inv fb (pre ++ [c]) (step fb st c) := by
  obtain ⟨hNO, hforb, hfwd, hbwd⟩ := hinv
  have hkf : KeyFree3 (lookupSig st.subst) (simpConstraint (lookupSig st.subst) c) :=
    keyFree3_simpConstraint hNO c
  have hiff : ∀ w, w 0 = 1 → Respects w (lookupSig st.subst) →
      (Constraint.Holds w (simpConstraint (lookupSig st.subst) c) ↔ Constraint.Holds w c) :=
    fun w hw0 hw => holds_simpConstraint hw0 hw c
  simp only [step]
  cases hcl : classify fb (simpConstraint (lookupSig st.subst) c) with
  | drop =>
    refine ⟨hNO, hforb, ?_, ?_⟩
    · intro w hw
      exact hfwd w (sat_append_singleton.mp hw).1
    · intro w hw0 hr hk d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hbwd w hw0 hr hk d hd
      · rw [List.mem_singleton.mp hd]
        exact (hiff w hw0 hr).mp (classify_drop hcl w)
  | subst x r =>
    obtain ⟨hfx, hxr, ⟨dx, hdx⟩, hrsub, hcx⟩ := classify_subst hcl
    have hx : lookupSig st.subst x = none := hkf.2.2 x dx hdx
    have hr : KeyFree (lookupSig st.subst) r := fun i d hi => by
      obtain ⟨d', hd'⟩ := hrsub i d hi
      exact hkf.2.2 i d' hd'
    refine ⟨nonOverlapping_addEntry hNO hx hr hxr, ?_, ?_, ?_⟩
    · intro p hp
      refine lookupSig_addEntry_of_ne ?_ (hforb p hp)
      intro hpx
      subst hpx
      rw [hp] at hfx
      exact Bool.noConfusion hfx
    · intro w hw
      obtain ⟨hw1, hwc⟩ := sat_append_singleton.mp hw
      obtain ⟨hr', hk⟩ := hfwd w hw1
      exact ⟨(respects_addEntry hx).mpr ⟨(hcx w).mp ((hiff w hw1.1 hr').mpr hwc), hr'⟩, hk⟩
    · intro w hw0 hr' hk d hd
      obtain ⟨hwx, hr''⟩ := (respects_addEntry hx).mp hr'
      rcases List.mem_append.mp hd with hd | hd
      · exact hbwd w hw0 hr'' hk d hd
      · rw [List.mem_singleton.mp hd]
        exact (hiff w hw0 hr'').mp ((hcx w).mpr hwx)
  | keep =>
    refine ⟨hNO, hforb, ?_, ?_⟩
    · intro w hw
      obtain ⟨hw1, hwc⟩ := sat_append_singleton.mp hw
      obtain ⟨hr', hk⟩ := hfwd w hw1
      refine ⟨hr', fun d hd => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact (hiff w hw1.1 hr').mpr hwc
      · exact hk d hd
    · intro w hw0 hr' hk d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hbwd w hw0 hr' (fun e he => hk e (List.mem_cons_of_mem _ he)) d hd
      · rw [List.mem_singleton.mp hd]
        exact (hiff w hw0 hr').mp (hk _ (List.mem_cons_self ..))

/-- The invariant is preserved by folding over a list of constraints. -/
theorem foldl_inv {fb : ℕ → Bool} :
    ∀ (cs pre : List (Constraint F)) (st : SimpState F),
      Inv fb pre st → Inv fb (pre ++ cs) (cs.foldl (step fb) st)
  | [], pre, st, h => by rw [List.append_nil]; exact h
  | c :: cs, pre, st, h => by
    rw [List.foldl_cons, ← List.singleton_append, ← List.append_assoc]
    exact foldl_inv cs (pre ++ [c]) (step fb st c) (step_inv h c)

/-- **The pass is correct**: the simplified system is equisatisfiable with the original
with respect to the forbidden signals, in both directions. -/
theorem simplifyConstraints_equisat (fb : ℕ → Bool) (h0 : fb 0 = true)
    (cs : List (Constraint F)) :
    Equisat (fun p => fb p = true) cs (simplifyConstraints fb cs).1 := by
  have hinv := foldl_inv cs [] {} (inv_init fb)
  rw [List.nil_append] at hinv
  obtain ⟨hNO, hforb, hfwd, hbwd⟩ := hinv
  refine equisat_of_subst (lookupSig (cs.foldl (step fb) {}).subst) cs
    (cs.foldl (step fb) {}).kept.reverse hNO hforb h0 ?_ ?_
  · intro w hw
    obtain ⟨hr, hk⟩ := hfwd w hw
    exact ⟨hr, fun c hc => hk c (List.mem_reverse.mp hc)⟩
  · intro w hw0 hr hk
    exact hbwd w hw0 hr (fun c hc => hk c (List.mem_reverse.mpr hc))

/-- Consequence: the relation on public signals is unchanged. -/
theorem simplifyConstraints_rel_iff (fb : ℕ → Bool) (h0 : fb 0 = true)
    (cs : List (Constraint F)) (v : ℕ → F) :
    Rel (fun p => fb p = true) cs v ↔
      Rel (fun p => fb p = true) (simplifyConstraints fb cs).1 v :=
  (simplifyConstraints_equisat fb h0 cs).rel_iff v

end Backends.Circom
