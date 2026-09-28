/-
Semantics of the exported R1CS constraints.

`exportConstraints` (R1CS.lean) produces constraints over *signals*: a witness is an
assignment `w : ℕ → F`, signal `0` is the constant `1` (the circom/snarkjs convention,
enforced by `Sat`), and a constraint `(a, b, c)` holds when `⟨a, w⟩ · ⟨b, w⟩ = ⟨c, w⟩`.
`Sat w cs` is what a proof system checks. It is the target side of the soundness bridge
(R1CSSoundness.lean) that relates the export to Clean's own constraint semantics on
`Operations`.

`Rel P cs` is the relation an R1CS defines on its public signals `P` (constant, outputs,
inputs): the statement a Groth16 proof over `cs` attests to. `Equisat P cs cs'` says two
systems define the same relation, in the two directions a proof system cares about:

* `forward`: every witness of `cs` satisfies `cs'` (honest provers are not rejected);
* `backward`: every witness of `cs'` extends, agreeing on `P`, to a witness of `cs` (no
  new public assignments are accepted).

It is the specification any R1CS-to-R1CS transformation (dedup, renumbering,
simplification) has to meet.
-/
module

public import Clean.Backends.Circom.Compile
public import Mathlib.Tactic.LinearCombination

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

/-! ## Constraints and satisfaction -/

/-- `(a, b, c)` holds under `w` iff `⟨a, w⟩ · ⟨b, w⟩ = ⟨c, w⟩`. -/
def Constraint.Holds (w : ℕ → F) : Constraint F → Prop
  | (a, b, c) => evalLC w a * evalLC w b = evalLC w c

/-- A witness satisfies an R1CS: signal `0` is the constant `1`, and every constraint holds. -/
def Sat (w : ℕ → F) (cs : List (Constraint F)) : Prop :=
  w 0 = 1 ∧ ∀ c ∈ cs, Constraint.Holds w c

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

end Backends.Circom
