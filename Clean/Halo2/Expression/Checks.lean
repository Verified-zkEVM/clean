module

public import Clean.Halo2.ConstraintSystem
public import Clean.Halo2.QueryCorrect

@[expose] public section

/-! Executable forms of the local gate and lookup laws, so that a closure's body can be checked
by evaluation rather than by a proof elaborated at each call site. -/

namespace Halo2.Expression
variable {F : Type}

/-- Decides `QueryAtom` by its own cases, whatever its rule for fixed rotations. Not an
instance, so existing elaboration is unchanged. -/
def decideQueryAtom (e : Expression F Query) : Decidable e.QueryAtom := by
  cases e with
  | var q =>
    cases q with
    | selector => exact isFalse fun h => h
    | fixed _ rotation => unfold Expression.QueryAtom; infer_instance
    | advice => exact isTrue trivial
    | «instance» => exact isTrue trivial
  | const => exact isFalse fun h => h
  | add => exact isFalse fun h => h
  | mul => exact isFalse fun h => h

/-- Executable `QueryAtom`. -/
def isQueryAtom (e : Expression F Query) : Bool := @decide e.QueryAtom e.decideQueryAtom

theorem queryAtom_of_isQueryAtom {e : Expression F Query} (h : e.isQueryAtom = true) :
    e.QueryAtom :=
  @of_decide_eq_true _ e.decideQueryAtom h

/-- Executable `SelectorFree`. -/
def free : Expression F Query → Bool
  | .var (.selector _) => false
  | .var _ => true
  | .const _ => true
  | .add a b | .mul a b => a.free && b.free

theorem free_iff (e : Expression F Query) : e.free = true ↔ e.SelectorFree := by
  induction e with
  | var q => cases q <;> simp [free, SelectorFree]
  | const _ => simp [free, SelectorFree]
  | add a b iha ihb | mul a b iha ihb => simp [free, SelectorFree, iha, ihb]

theorem free_noSimpleSelectors (e : Expression F Query) (h : e.free = true) :
    e.NoSimpleSelectors := by
  induction e with
  | var q => cases q <;> simp_all [free, NoSimpleSelectors]
  | const _ => trivial
  | add a b iha ihb | mul a b iha ihb =>
    exact ⟨iha (Bool.and_eq_true_iff.mp h).1, ihb (Bool.and_eq_true_iff.mp h).2⟩

/-- Executable `NoSimpleSelectors`. -/
def noSimple : Expression F Query → Bool
  | .var (.selector s) => !s.simple
  | .var _ | .const _ => true
  | .add a b | .mul a b => a.noSimple && b.noSimple

theorem noSimple_iff (e : Expression F Query) : e.noSimple = true ↔ e.NoSimpleSelectors := by
  induction e with
  | var q => cases q <;> simp [noSimple, NoSimpleSelectors]
  | const _ => simp [noSimple, NoSimpleSelectors]
  | add a b iha ihb | mul a b iha ihb => simp [noSimple, NoSimpleSelectors, iha, ihb]

/-- Executable `QueriesDeclared` against a gate's closure-call list. -/
def declared (queries : List Query) : Expression F Query → Bool
  | .var (.selector _) => true
  | .var q => queries.contains q
  | .const _ => true
  | .add a b | .mul a b => a.declared queries && b.declared queries

theorem declared_iff (e : Expression F Query) (queries : List Query) :
    e.declared queries = true ↔ e.QueriesDeclared (queries.map (.var ·)) := by
  induction e with
  | var q => cases q <;> simp [declared, QueriesDeclared, List.mem_map]
  | const _ => simp [declared, QueriesDeclared]
  | add a b iha ihb | mul a b iha ihb => simp [declared, QueriesDeclared, iha, ihb]

/-- The degree in `q` of a polynomial whose every term carries `q` the same number of times and no
other selector, as blake2b's `(q * a) * b` does; `none` otherwise. A sum carrying a simple `q` is
excluded because Rust's `+` panics on simple selectors. -/
def selectorDegree (q : Selector) : Expression F Query → Option Nat
  | .var (.selector s) => if s == q then some 1 else none
  | .var _ | .const _ => some 0
  | .add a b => match a.selectorDegree q, b.selectorDegree q with
    | some d, some e => if d == e && (d == 0 || !q.simple) then some d else none
    | _, _ => none
  | .mul a b => match a.selectorDegree q, b.selectorDegree q with
    | some d, some e => some (d + e)
    | _, _ => none

theorem selectorDegree_selectorsOwnedBy (q : Selector) (e : Expression F Query) {d : Nat}
    (h : e.selectorDegree q = some d) : e.SelectorsOwnedBy q := by
  induction e generalizing d with
  | var v =>
    cases v with
    | selector r =>
      simp only [selectorDegree] at h
      split at h
      · simp_all [SelectorsOwnedBy]
      · simp at h
    | _ => trivial
  | const _ => trivial
  | add a b iha ihb =>
    simp only [selectorDegree] at h
    split at h
    · rename_i d₁ e₁ ha hb
      exact ⟨iha ha, ihb hb⟩
    · simp at h
  | mul a b iha ihb =>
    simp only [selectorDegree] at h
    split at h
    · rename_i d₁ e₁ ha hb
      exact ⟨iha ha, ihb hb⟩
    · simp at h

/-- Setting `q` to `s` scales a polynomial of `q`-degree `d` by `s ^ d`. At a row where `q` is off
(`s = 0`, `d > 0`) it vanishes; where it is on it is the polynomial at `q = 1`, the meaning of
enabling a gate on `q`. -/
theorem eval_scale [Field F] (q : Selector) (e : Expression F Query) {d : Nat}
    (h : e.selectorDegree q = some d) (base : Query → F) (s : F) :
    e.eval (replaceSelectorValue q s base) = s ^ d * e.eval (enabledGateValuation q base) := by
  induction e generalizing d with
  | var v =>
    cases v with
    | selector r =>
      simp only [selectorDegree] at h
      split at h
      · rename_i hr
        simp only [beq_iff_eq] at hr
        subst hr
        simp at h
        subst h
        simp [eval, replaceSelectorValue, enabledGateValuation]
      · simp at h
    | _ =>
      simp [selectorDegree] at h
      subst h
      simp [eval, replaceSelectorValue, enabledGateValuation]
  | const _ =>
    simp [selectorDegree] at h
    subst h
    simp [eval]
  | add a b iha ihb =>
    simp only [selectorDegree] at h
    split at h
    · rename_i d₁ e₁ ha hb
      split at h
      · rename_i hde
        simp only [Bool.and_eq_true, beq_iff_eq] at hde
        simp only [Option.some.injEq] at h
        subst h
        have hb' : b.selectorDegree q = some d₁ := by rw [hde.1]; exact hb
        simp only [eval]
        rw [iha ha, ihb hb']
        exact (mul_add _ _ _).symm
      · simp at h
    · simp at h
  | mul a b iha ihb =>
    simp only [selectorDegree] at h
    split at h
    · rename_i d₁ e₁ ha hb
      simp only [Option.some.injEq] at h
      subst h
      simp only [eval]
      rw [iha ha, ihb hb, pow_add]
      exact mul_mul_mul_comm _ _ _ _
    · simp at h

/-- Every term carries `q`, and no other selector: the polynomial is owned by `q`. -/
def ownedBy (q : Selector) (e : Expression F Query) : Bool :=
  match e.selectorDegree q with
  | some (_ + 1) => true
  | _ => false

theorem exists_selectorDegree_of_ownedBy {q : Selector} {e : Expression F Query}
    (h : e.ownedBy q = true) : ∃ d, e.selectorDegree q = some (d + 1) := by
  unfold ownedBy at h
  split at h
  · rename_i d hd
    exact ⟨d, hd⟩
  · simp at h

end Halo2.Expression
