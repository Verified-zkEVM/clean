/-
R1CS semantics and the certified-simplification framework.

This module gives the exported R1CS constraints (`Constraint F`, see `Compile.lean`)
a meaning, and states what it means for a constraint-simplification pass to be
correct. It is the foundation for the certified simplification pass (`Simplify.lean`).

## Semantics

A witness is an assignment `w : ℕ → F` of field elements to signal numbers. Signal
`0` is the constant `1` (the circom/snarkjs convention), which `Sat` enforces.
A constraint `(a, b, c)` holds when `⟨a, w⟩ · ⟨b, w⟩ = ⟨c, w⟩`.

## What a simplification must preserve

A statement only talks about the *public* signals `P` (constant, public
inputs, outputs): "there exist values for the remaining signals such that all
constraints hold". So a pass may change the private signals freely, but the
relation `Rel P cs` on public assignments must not change. `Equisat P cs cs'`
captures this in the two directions a proof system cares about:

* `forward`: every witness of the original system satisfies the simplified one
  (honest provers are not rejected);
* `backward`: every witness of the simplified system extends, agreeing on `P`, to
  a witness of the original one (no new public assignments are accepted).

## Substitutions

All the passes work by *substitution*: a linear constraint is solved for
a private signal `x = r` and `x` is replaced by `r` everywhere. The generic theorem
`equisat_of_subst` proves `Equisat` for any pass that produces a substitution map
`s` together with kept constraints `out` such that

* `s` is *non-overlapping* (no eliminated signal appears in a right-hand side) and
  never eliminates a public signal;
* the original constraints imply the substitution equations and the kept constraints;
* conversely, the substitution equations plus the kept constraints imply the
  original constraints.

The backward witness is the canonical *witness extension* `extend s w'`: every
eliminated signal is recomputed from its right-hand side.
-/
module

public import Clean.Backends.Circom.Compile
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Backends.Circom

variable {F : Type} [FiniteField F]

/-! ## Linear combinations -/

/-- Evaluate a linear combination `Σ cᵢ · w(i)` under a witness `w`. -/
def evalLC (w : ℕ → F) (lc : List (ℕ × F)) : F :=
  (lc.map fun (i, c) => c * w i).sum

@[simp] theorem evalLC_nil (w : ℕ → F) : evalLC w [] = 0 := rfl

@[simp] theorem evalLC_cons (w : ℕ → F) (i : ℕ) (c : F) (lc : List (ℕ × F)) :
    evalLC w ((i, c) :: lc) = c * w i + evalLC w lc := by
  simp [evalLC]

/-- Evaluate a scaled linear combination `k * lc` is equal to `k` times the evaluation of `lc`. -/
theorem evalLC_scaleLinComb (w : ℕ → F) (k : F) (lc : List (ℕ × F)) :
    evalLC w (scaleLinComb k lc) = k * evalLC w lc := by
  induction lc with
  | nil => simp [scaleLinComb]
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    have h : scaleLinComb k ((i, c) :: tl) = (i, k * c) :: scaleLinComb k tl := rfl
    rw [h, evalLC_cons, evalLC_cons, ih]
    ring

/-- Evaluate the sum of two linear combinations is equal to the sum of their evaluations. -/
theorem evalLC_addLinCombs (w : ℕ → F) :
    ∀ (a b : List (ℕ × F)), evalLC w (addLinCombs a b) = evalLC w a + evalLC w b
  | [], b => by simp [addLinCombs]
  | (i1, c1) :: xs, [] => by simp [addLinCombs]
  | (i1, c1) :: xs, (i2, c2) :: ys => by
    simp only [addLinCombs]
    split_ifs with h1 h2 h3
    · rw [evalLC_cons, evalLC_addLinCombs w xs ((i2, c2) :: ys)]
      simp only [evalLC_cons]
      ring
    · subst h2
      rw [evalLC_addLinCombs w xs ys]
      simp only [evalLC_cons]
      linear_combination -(w i1) * h3
    · subst h2
      rw [evalLC_cons, evalLC_addLinCombs w xs ys]
      simp only [evalLC_cons]
      ring
    · rw [evalLC_cons, evalLC_addLinCombs w ((i1, c1) :: xs) ys]
      simp only [evalLC_cons]
      ring

/-- Membership in a merged linear combination comes from one of the inputs. -/
theorem mem_addLinCombs {i : ℕ} {c : F} :
    ∀ {a b : List (ℕ × F)}, (i, c) ∈ addLinCombs a b →
      (∃ c', (i, c') ∈ a) ∨ (∃ c', (i, c') ∈ b)
  | [], b, h => by simp only [addLinCombs] at h; exact .inr ⟨c, h⟩
  | (i1, c1) :: xs, [], h => by simp only [addLinCombs] at h; exact .inl ⟨c, h⟩
  | (i1, c1) :: xs, (i2, c2) :: ys, h => by
    simp only [addLinCombs] at h
    split_ifs at h with h1 h2 h3
    · rcases List.mem_cons.mp h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact .inl ⟨_, List.mem_cons_self ..⟩
      · rcases mem_addLinCombs h with ⟨c', hc'⟩ | ⟨c', hc'⟩
        · exact .inl ⟨c', List.mem_cons_of_mem _ hc'⟩
        · exact .inr ⟨c', hc'⟩
    · rcases mem_addLinCombs h with ⟨c', hc'⟩ | ⟨c', hc'⟩
      · exact .inl ⟨c', List.mem_cons_of_mem _ hc'⟩
      · exact .inr ⟨c', List.mem_cons_of_mem _ hc'⟩
    · rcases List.mem_cons.mp h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact .inl ⟨_, List.mem_cons_self ..⟩
      · rcases mem_addLinCombs h with ⟨c', hc'⟩ | ⟨c', hc'⟩
        · exact .inl ⟨c', List.mem_cons_of_mem _ hc'⟩
        · exact .inr ⟨c', List.mem_cons_of_mem _ hc'⟩
    · rcases List.mem_cons.mp h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact .inr ⟨_, List.mem_cons_self ..⟩
      · rcases mem_addLinCombs h with ⟨c', hc'⟩ | ⟨c', hc'⟩
        · exact .inl ⟨c', hc'⟩
        · exact .inr ⟨c', List.mem_cons_of_mem _ hc'⟩

/-- Membership in a scaled linear combination comes from the original linear combination. -/
theorem mem_scaleLinComb {i : ℕ} {c k : F} {lc : List (ℕ × F)} (h : (i, c) ∈ scaleLinComb k lc) :
    ∃ c', (i, c') ∈ lc := by
  simp only [scaleLinComb, List.mem_map, Prod.ext_iff] at h
  obtain ⟨⟨i', c'⟩, hmem, hi, _⟩ := h
  exact ⟨c', hi ▸ hmem⟩

/-- Evaluation only depends on the witness at the signals that occur. -/
theorem evalLC_congr {w w' : ℕ → F} {lc : List (ℕ × F)}
    (h : ∀ i c, (i, c) ∈ lc → w i = w' i) : evalLC w lc = evalLC w' lc := by
  induction lc with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    rw [evalLC_cons, evalLC_cons, h i c (List.mem_cons_self ..),
      ih (fun j d hj => h j d (List.mem_cons_of_mem _ hj))]

/-- Remove zero coefficients. -/
def dropZeros : List (ℕ × F) → List (ℕ × F)
  | [] => []
  | (i, c) :: rest => if c = 0 then dropZeros rest else (i, c) :: dropZeros rest

/-- Evaluation is unchanged if zero coefficients are removed. -/
theorem evalLC_dropZeros (w : ℕ → F) (lc : List (ℕ × F)) : evalLC w (dropZeros lc) = evalLC w lc := by
  induction lc with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    simp only [dropZeros]
    split_ifs with h
    · rw [ih, evalLC_cons, h]; ring
    · rw [evalLC_cons, evalLC_cons, ih]

theorem mem_dropZeros {i : ℕ} {c : F} {lc : List (ℕ × F)} (h : (i, c) ∈ dropZeros lc) : (i, c) ∈ lc := by
  induction lc with
  | nil => simp [dropZeros] at h
  | cons hd tl ih =>
    obtain ⟨j, d⟩ := hd
    simp only [dropZeros] at h
    split_ifs at h with hd
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-! ## Constraints and satisfaction -/

/-- `(a, b, c)` holds under `w` iff `⟨a, w⟩ · ⟨b, w⟩ = ⟨c, w⟩`. -/
def Constraint.Holds (w : ℕ → F) : Constraint F → Prop
  | (a, b, c) => evalLC w a * evalLC w b = evalLC w c

/-- A witness satisfies an R1CS: signal `0` is the constant `1`, and every constraint holds. -/
def Sat (w : ℕ → F) (cs : List (Constraint F)) : Prop :=
  w 0 = 1 ∧ ∀ c ∈ cs, Constraint.Holds w c

theorem sat_append_singleton {w : ℕ → F} {cs : List (Constraint F)} {c : Constraint F} :
    Sat w (cs ++ [c]) ↔ Sat w cs ∧ Constraint.Holds w c := by
  simp only [Sat, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, fun c hc => h c (.inl hc)⟩, h c (.inr rfl)⟩
  · rintro ⟨⟨h0, h⟩, hc⟩
    refine ⟨h0, fun c' hc' => ?_⟩
    rcases hc' with hc' | rfl
    · exact h c' hc'
    · exact hc

/-- The relation an R1CS defines on the public signals `P`: an assignment `v` of the
public signals is accepted iff it extends to a full satisfying witness. -/
def Rel (P : ℕ → Prop) (cs : List (Constraint F)) (v : ℕ → F) : Prop :=
  ∃ w, (∀ p, P p → w p = v p) ∧ Sat w cs

/-- `cs'` is a correct simplification of `cs` with respect to the public signals `P`. -/
structure Equisat (P : ℕ → Prop) (cs cs' : List (Constraint F)) : Prop where
  /-- Honest witnesses of the original still satisfy the simplified system. -/
  forward : ∀ w, Sat w cs → Sat w cs'
  /-- Witnesses of the simplified system extend (agreeing on `P`) to witnesses of the original. -/
  backward : ∀ w', Sat w' cs' → ∃ w, (∀ p, P p → w p = w' p) ∧ Sat w cs

/-- Equivalence of R1CS systems with respect to public signals. -/
theorem Equisat.rel_iff {P : ℕ → Prop} {cs cs' : List (Constraint F)}
    (h : Equisat P cs cs') (v : ℕ → F) : Rel P cs v ↔ Rel P cs' v := by
  constructor
  · rintro ⟨w, hw, hsat⟩
    exact ⟨w, hw, h.forward w hsat⟩
  · rintro ⟨w', hw', hsat'⟩
    obtain ⟨w, hagree, hsat⟩ := h.backward w' hsat'
    exact ⟨w, fun p hp => (hagree p hp).trans (hw' p hp), hsat⟩

/-- Reflexivity of equivalence with respect to public signals. -/
theorem Equisat.refl (P : ℕ → Prop) (cs : List (Constraint F)) : Equisat P cs cs where
  forward _ h := h
  backward w' h := ⟨w', fun _ _ => rfl, h⟩

/-- Transitivity of equivalence with respect to public signals. -/
theorem Equisat.trans {P : ℕ → Prop} {cs cs' cs'' : List (Constraint F)}
    (h1 : Equisat P cs cs') (h2 : Equisat P cs' cs'') : Equisat P cs cs'' where
  forward w h := h2.forward w (h1.forward w h)
  backward w'' h := by
    obtain ⟨w', hw', hsat'⟩ := h2.backward w'' h
    obtain ⟨w, hw, hsat⟩ := h1.backward w' hsat'
    exact ⟨w, fun p hp => (hw p hp).trans (hw' p hp), hsat⟩

/-- Unsatisfiability is preserved by any correct simplification. -/
theorem Equisat.unsat_iff {P : ℕ → Prop} {cs cs' : List (Constraint F)}
    (h : Equisat P cs cs') : (∀ w, ¬ Sat w cs) ↔ (∀ w', ¬ Sat w' cs') := by
  constructor
  · intro hu w' hw'
    obtain ⟨w, _, hw⟩ := h.backward w' hw'
    exact hu w hw
  · intro hu w hw
    exact hu w (h.forward w hw)

/-! ## Substitutions -/

/-- A substitution: a partial map from (eliminated) signals to linear combinations. -/
abbrev Subst (F : Type) := ℕ → Option (List (ℕ × F))

/-- `w` respects `s` if every eliminated signal equals its right-hand side under `w`. -/
def Respects (w : ℕ → F) (s : Subst F) : Prop :=
  ∀ i r, s i = some r → w i = evalLC w r

/-- No signal of `lc` is eliminated by `s`. -/
def KeyFree (s : Subst F) (lc : List (ℕ × F)) : Prop :=
  ∀ i c, (i, c) ∈ lc → s i = none

/-- No eliminated signal occurs in any right-hand side. -/
def NonOverlapping (s : Subst F) : Prop :=
  ∀ i r, s i = some r → KeyFree s r

/-- Replace one signal occurrence `c · i` by its right-hand side, if eliminated. -/
def substSig (s : Subst F) (i : ℕ) (c : F) : List (ℕ × F) :=
  match s i with
  | some r => scaleLinComb c r
  | none => [(i, c)]

/-- Apply a substitution to a linear combination. -/
def applySubst (s : Subst F) : List (ℕ × F) → List (ℕ × F)
  | [] => []
  | (i, c) :: rest => addLinCombs (substSig s i c) (applySubst s rest)

/-- Evaluation of a substituted signal equals the evaluation of its right-hand side. -/
theorem evalLC_substSig {w : ℕ → F} {s : Subst F} (hw : Respects w s) (i : ℕ) (c : F) :
    evalLC w (substSig s i c) = c * w i := by
  unfold substSig
  cases h : s i with
  | none => simp
  | some r => rw [evalLC_scaleLinComb, hw i r h]

/-- Evaluation of a substituted linear combination equals the evaluation of the original linear combination. -/
theorem evalLC_applySubst {w : ℕ → F} {s : Subst F} (hw : Respects w s) (lc : List (ℕ × F)) :
    evalLC w (applySubst s lc) = evalLC w lc := by
  induction lc with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    simp only [applySubst]
    rw [evalLC_addLinCombs, evalLC_substSig hw, ih, evalLC_cons]

/-- If no signal of `lc` is eliminated by `s`, the same holds for a scaled version of `lc`. -/
theorem keyFree_scaleLinComb {s : Subst F} {k : F} {lc : List (ℕ × F)} (h : KeyFree s lc) :
    KeyFree s (scaleLinComb k lc) := by
  intro i c hic
  obtain ⟨c', hc'⟩ := mem_scaleLinComb hic
  exact h i c' hc'

/-- If no signal of `a` and `b` is eliminated by `s`, the same holds for their sum. -/
theorem keyFree_addLinCombs {s : Subst F} {a b : List (ℕ × F)}
    (ha : KeyFree s a) (hb : KeyFree s b) : KeyFree s (addLinCombs a b) := by
  intro i c hic
  rcases mem_addLinCombs hic with ⟨c', hc'⟩ | ⟨c', hc'⟩
  · exact ha i c' hc'
  · exact hb i c' hc'

/-- If no signal of `lc` is eliminated by `s`, the same holds after removing zero coefficients. -/
theorem keyFree_dropZeros {s : Subst F} {lc : List (ℕ × F)} (h : KeyFree s lc) :
    KeyFree s (dropZeros lc) :=
  fun i c hic => h i c (mem_dropZeros hic)

omit [FiniteField F] in
theorem keyFree_nil (s : Subst F) : KeyFree s [] := fun _ _ h => by simp at h

/-- Applying `s` produces a combination whose signals are free of `t`, provided the
untouched signals of `lc` are free of `t` and every right-hand side of `s` is. -/
theorem keyFree_applySubst_of {s t : Subst F} {lc : List (ℕ × F)}
    (h1 : ∀ i c, (i, c) ∈ lc → s i = none → t i = none)
    (h2 : ∀ i r, s i = some r → KeyFree t r) : KeyFree t (applySubst s lc) := by
  induction lc with
  | nil => exact keyFree_nil t
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    simp only [applySubst]
    refine keyFree_addLinCombs ?_ (ih fun j d hj => h1 j d (List.mem_cons_of_mem _ hj))
    unfold substSig
    cases h : s i with
    | none =>
      intro j d hj
      simp only [List.mem_singleton, Prod.ext_iff] at hj
      obtain ⟨rfl, _⟩ := hj
      exact h1 j c (List.mem_cons_self ..) h
    | some r => exact keyFree_scaleLinComb (h2 i r h)

/-- Applying a substitution preserves the key-free property for non-overlapping substitutions. -/
theorem keyFree_applySubst {s : Subst F} (hNO : NonOverlapping s) (lc : List (ℕ × F)) :
    KeyFree s (applySubst s lc) :=
  keyFree_applySubst_of (fun _ _ _ h => h) hNO

/-! ## Witness extension -/

/-- Recompute eliminated signals from their right-hand sides: the canonical way to turn a
witness of the simplified system back into a witness of the original one. -/
def extend (s : Subst F) (w' : ℕ → F) : ℕ → F :=
  fun i => match s i with
    | some r => evalLC w' r
    | none => w' i

theorem extend_of_none {s : Subst F} {w' : ℕ → F} {i : ℕ} (h : s i = none) :
    extend s w' i = w' i := by
  simp [extend, h]

theorem evalLC_extend_of_keyFree {s : Subst F} {w' : ℕ → F} {lc : List (ℕ × F)}
    (h : KeyFree s lc) : evalLC (extend s w') lc = evalLC w' lc :=
  evalLC_congr fun i c hic => extend_of_none (h i c hic)

theorem respects_extend {s : Subst F} (hNO : NonOverlapping s) (w' : ℕ → F) :
    Respects (extend s w') s := by
  intro i r hi
  have h1 : extend s w' i = evalLC w' r := by simp [extend, hi]
  rw [h1, evalLC_extend_of_keyFree (hNO i r hi)]

/-! ## Substitution and normalization of constraints -/

/-- Apply a substitution to all three linear combinations of a constraint. -/
def applySubst3 (s : Subst F) : Constraint F → Constraint F
  | (a, b, c) => (applySubst s a, applySubst s b, applySubst s c)

def KeyFree3 (s : Subst F) : Constraint F → Prop
  | (a, b, c) => KeyFree s a ∧ KeyFree s b ∧ KeyFree s c

theorem holds_applySubst3 {w : ℕ → F} {s : Subst F} (hw : Respects w s) (c : Constraint F) :
    Constraint.Holds w (applySubst3 s c) ↔ Constraint.Holds w c := by
  rcases c with ⟨a, b, c⟩
  simp only [applySubst3, Constraint.Holds, evalLC_applySubst hw]

theorem keyFree3_applySubst3 {s : Subst F} (hNO : NonOverlapping s) (c : Constraint F) :
    KeyFree3 s (applySubst3 s c) := by
  rcases c with ⟨a, b, c⟩
  exact ⟨keyFree_applySubst hNO a, keyFree_applySubst hNO b, keyFree_applySubst hNO c⟩

theorem holds_extend_of_keyFree3 {s : Subst F} {w' : ℕ → F} {c : Constraint F}
    (h : KeyFree3 s c) : Constraint.Holds (extend s w') c ↔ Constraint.Holds w' c := by
  rcases c with ⟨a, b, c⟩
  obtain ⟨ha, hb, hc⟩ := h
  simp only [Constraint.Holds, evalLC_extend_of_keyFree ha, evalLC_extend_of_keyFree hb,
    evalLC_extend_of_keyFree hc]

/-- `some k` iff the linear combination is the constant `k` (i.e. `[(0, k)]`). -/
def isConstLC : List (ℕ × F) → Option F
  | [(0, k)] => some k
  | _ => none

omit [FiniteField F] in
theorem isConstLC_eq_some : ∀ {lc : List (ℕ × F)} {k : F}, isConstLC lc = some k → lc = [(0, k)]
  | [(0, k')], k, h => by simp [isConstLC] at h; subst h; rfl
  | [], _, h => by simp [isConstLC] at h
  | [(n + 1, _)], _, h => by simp [isConstLC] at h
  | _ :: _ :: _, _, h => by simp [isConstLC] at h

/-- Canonical form of `(a, b, c)` with zero coefficients already dropped: if
`a` or `b` is empty the product is `0`; if one factor is the constant `k`,
fold it into the linear part as `c - k·(other) = 0`. Linear constraints
are always represented as `([], [], lc)`, meaning `lc = 0`. -/
def normalizeCore (a b c : List (ℕ × F)) : Constraint F :=
  if a = [] ∨ b = [] then ([], [], c)
  else match isConstLC a with
    | some k => ([], [], dropZeros (addLinCombs c (scaleLinComb (-k) b)))
    | none => match isConstLC b with
      | some k => ([], [], dropZeros (addLinCombs c (scaleLinComb (-k) a)))
      | none => (a, b, c)

/-- Bring a constraint into canonical form: drop zero coefficients, then `normalizeCore`. -/
def normalize : Constraint F → Constraint F
  | (a, b, c) => normalizeCore (dropZeros a) (dropZeros b) (dropZeros c)

theorem holds_normalizeCore {w : ℕ → F} (h0 : w 0 = 1) (a b c : List (ℕ × F)) :
    Constraint.Holds w (normalizeCore a b c) ↔ evalLC w a * evalLC w b = evalLC w c := by
  by_cases hab : a = [] ∨ b = []
  · rw [normalizeCore, if_pos hab]
    simp only [Constraint.Holds]
    rcases hab with rfl | rfl <;> simp
  · rw [normalizeCore, if_neg hab]
    cases hka : isConstLC a with
    | some k =>
      obtain rfl := isConstLC_eq_some hka
      simp only [Constraint.Holds, evalLC_dropZeros, evalLC_addLinCombs, evalLC_scaleLinComb,
        evalLC_cons, evalLC_nil, h0, mul_one, add_zero, zero_mul]
      constructor <;> intro h <;> linear_combination h
    | none =>
      cases hkb : isConstLC b with
      | some k =>
        obtain rfl := isConstLC_eq_some hkb
        simp only [Constraint.Holds, evalLC_dropZeros, evalLC_addLinCombs, evalLC_scaleLinComb,
          evalLC_cons, evalLC_nil, h0, mul_one, add_zero, zero_mul]
        constructor <;> intro h <;> linear_combination h
      | none => exact Iff.rfl

/-- If a constraint is brought into canonical form by `normalize`, its evaluation remains the same. -/
theorem holds_normalize {w : ℕ → F} (h0 : w 0 = 1) (c : Constraint F) :
    Constraint.Holds w (normalize c) ↔ Constraint.Holds w c := by
  rcases c with ⟨a, b, c⟩
  show Constraint.Holds w (normalizeCore (dropZeros a) (dropZeros b) (dropZeros c)) ↔ _
  rw [holds_normalizeCore h0]
  simp only [Constraint.Holds, evalLC_dropZeros]

theorem keyFree3_normalizeCore {s : Subst F} {a b c : List (ℕ × F)}
    (ha : KeyFree s a) (hb : KeyFree s b) (hc : KeyFree s c) :
    KeyFree3 s (normalizeCore a b c) := by
  by_cases hab : a = [] ∨ b = []
  · rw [normalizeCore, if_pos hab]
    exact ⟨keyFree_nil s, keyFree_nil s, hc⟩
  · rw [normalizeCore, if_neg hab]
    cases hka : isConstLC a with
    | some k =>
      simp only [KeyFree3]
      exact ⟨keyFree_nil s, keyFree_nil s,
        keyFree_dropZeros (keyFree_addLinCombs hc (keyFree_scaleLinComb hb))⟩
    | none =>
      cases hkb : isConstLC b with
      | some k =>
        simp only [KeyFree3]
        exact ⟨keyFree_nil s, keyFree_nil s,
          keyFree_dropZeros (keyFree_addLinCombs hc (keyFree_scaleLinComb ha))⟩
      | none => exact ⟨ha, hb, hc⟩

/-- If a constraint is brought into canonical form by `normalize`, its key-free property is preserved. -/
theorem keyFree3_normalize {s : Subst F} {c : Constraint F} (h : KeyFree3 s c) :
    KeyFree3 s (normalize c) := by
  rcases c with ⟨a, b, c⟩
  obtain ⟨ha, hb, hc⟩ := h
  exact keyFree3_normalizeCore (keyFree_dropZeros ha) (keyFree_dropZeros hb) (keyFree_dropZeros hc)

/-- Substitute, then normalize. This is the operation every pass applies to a constraint. -/
def simpConstraint (s : Subst F) (c : Constraint F) : Constraint F :=
  normalize (applySubst3 s c)

/-- If a constraint is simplified by `simpConstraint`, its evaluation remains the same. -/
theorem holds_simpConstraint {w : ℕ → F} {s : Subst F} (h0 : w 0 = 1) (hw : Respects w s)
    (c : Constraint F) : Constraint.Holds w (simpConstraint s c) ↔ Constraint.Holds w c := by
  rw [simpConstraint, holds_normalize h0, holds_applySubst3 hw]

theorem keyFree3_simpConstraint {s : Subst F} (hNO : NonOverlapping s) (c : Constraint F) :
    KeyFree3 s (simpConstraint s c) :=
  keyFree3_normalize (keyFree3_applySubst3 hNO c)

/-! ## The generic correctness theorem -/

/--
**Substitution frame theorem.** A pass that eliminates private signals via a
non-overlapping substitution `s` and keeps the constraints `out` is correct, provided
`(s, out)` and the original system `cs` imply each other:

* `hFwd`: every witness of `cs` respects `s` and satisfies `out`;
* `hBwd`: every witness (with `w 0 = 1`) respecting `s` and satisfying `out` satisfies `cs`.

The simplified system is `out` with `s` applied. The backward witness is `extend s w'`.
-/
theorem equisat_of_subst {P : ℕ → Prop} (s : Subst F) (cs out : List (Constraint F))
    (hNO : NonOverlapping s) (hP : ∀ p, P p → s p = none) (h0 : P 0)
    (hFwd : ∀ w, Sat w cs → Respects w s ∧ ∀ c ∈ out, Constraint.Holds w c)
    (hBwd : ∀ w, w 0 = 1 → Respects w s → (∀ c ∈ out, Constraint.Holds w c) →
      ∀ c ∈ cs, Constraint.Holds w c) :
    Equisat P cs (out.map (simpConstraint s)) where
  forward w hw := by
    obtain ⟨hr, hout⟩ := hFwd w hw
    refine ⟨hw.1, fun c' hc' => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    exact (holds_simpConstraint hw.1 hr c).mpr (hout c hc)
  backward w' hw' := by
    have h0' : extend s w' 0 = 1 := (extend_of_none (hP 0 h0)).trans hw'.1
    have hr : Respects (extend s w') s := respects_extend hNO w'
    refine ⟨extend s w', fun p hp => extend_of_none (hP p hp), h0', hBwd _ h0' hr ?_⟩
    intro c hc
    have h1 : Constraint.Holds w' (simpConstraint s c) := hw'.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have h2 : Constraint.Holds (extend s w') (simpConstraint s c) :=
      (holds_extend_of_keyFree3 (keyFree3_simpConstraint hNO c)).mpr h1
    exact (holds_simpConstraint h0' hr c).mp h2

end Backends.Circom
