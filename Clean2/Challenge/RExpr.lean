/-
Rational expressions in committed values and a challenge: the equations a user writes.

`RExpr F k` is the syntax of a rational expression in `k` committed values (`leaf i`) and the
challenge (`X`). It has three meanings:

- `sym x e : K⟮X⟯`, *symbolic*: the challenge is the indeterminate. This is what users reason about:
  an identity `sym x e = 0` is an equation between rational functions.
- `evalAt x α e : F`, *pointwise*: the value at the challenge `α`. This is what a circuit computes.
- `num x e`, `den x e : F[X]`, *syntactic*: a numerator and a denominator, built the way the
  expression is built (no cancellation), whose degrees `degN e`, `degD e` are bounded statically.

The bridge between them is two facts. At a challenge where no divisor vanishes (`Good x α e`), the
pointwise value is `num(α) / den(α)` (`evalAt_eq`). Symbolically, if no divisor is identically zero
(`NZ x e`), `sym = num / den` (`sym_eq`). So a circuit that checks `evalAt x α e = 0` establishes
`sym x e = 0` unless `α` is one of the *bad* challenges (`Bad e x α`): a root of a divisor, or of a
nonzero numerator. There are at most `bound e = degN e + divDeg e` of them, whatever `x` is
(`encard_bad_le`).
-/
module

public import Clean2.Challenge.Symbolic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Clean2
open Polynomial

/-- Rational expressions in `k` committed values and the challenge `X`. -/
inductive RExpr (F : Type) (k : ℕ) where
  | leaf (i : Fin k)
  | const (c : F)
  | X
  | add (a b : RExpr F k)
  | sub (a b : RExpr F k)
  | mul (a b : RExpr F k)
  | div (a b : RExpr F k)

namespace RExpr
variable {F : Type} {k : ℕ}

instance : Add (RExpr F k) := ⟨add⟩
instance : Sub (RExpr F k) := ⟨sub⟩
instance : Mul (RExpr F k) := ⟨mul⟩
instance : Div (RExpr F k) := ⟨div⟩

/-- `∑ i, f i`. -/
def sum [Zero F] : (n : ℕ) → (Fin n → RExpr F k) → RExpr F k
  | 0, _ => const 0
  | n + 1, f => f 0 + sum n fun i => f i.succ

/-- `∏ i, f i`. -/
def prod [One F] : (n : ℕ) → (Fin n → RExpr F k) → RExpr F k
  | 0, _ => const 1
  | n + 1, f => f 0 * prod n fun i => f i.succ

/-- `e ^ n`. -/
def pow [One F] (e : RExpr F k) : ℕ → RExpr F k
  | 0 => const 1
  | n + 1 => pow e n * e

instance [One F] : HPow (RExpr F k) ℕ (RExpr F k) := ⟨pow⟩

/-! ### Static degree bounds -/

mutual
/-- A bound on the degree of the syntactic numerator. -/
def degN : RExpr F k → ℕ
  | leaf _ | const _ => 0
  | X => 1
  | add a b | sub a b => max (degN a + degD b) (degN b + degD a)
  | mul a b => degN a + degN b
  | div a b => degN a + degD b
/-- A bound on the degree of the syntactic denominator. -/
def degD : RExpr F k → ℕ
  | leaf _ | const _ | X => 0
  | add a b | sub a b | mul a b => degD a + degD b
  | div a b => degD a + degN b
end
/-- A bound on the number of challenges at which some divisor vanishes. -/
def divDeg : RExpr F k → ℕ
  | leaf _ | const _ | X => 0
  | add a b | sub a b | mul a b => divDeg a + divDeg b
  | div a b => divDeg a + divDeg b + degN b

/-- The number of bad challenges. -/
def bound (e : RExpr F k) : ℕ := degN e + divDeg e

section Degrees
variable (a b : RExpr F k)
@[simp] theorem degN_X : (X : RExpr F k).degN = 1 := rfl
@[simp] theorem degD_X : (X : RExpr F k).degD = 0 := rfl
@[simp] theorem divDeg_X : (X : RExpr F k).divDeg = 0 := rfl
@[simp] theorem degN_leaf (i : Fin k) : (leaf i : RExpr F k).degN = 0 := rfl
@[simp] theorem degD_leaf (i : Fin k) : (leaf i : RExpr F k).degD = 0 := rfl
@[simp] theorem divDeg_leaf (i : Fin k) : (leaf i : RExpr F k).divDeg = 0 := rfl
@[simp] theorem degN_const (c : F) : (const c : RExpr F k).degN = 0 := rfl
@[simp] theorem degD_const (c : F) : (const c : RExpr F k).degD = 0 := rfl
@[simp] theorem divDeg_const (c : F) : (const c : RExpr F k).divDeg = 0 := rfl
@[simp] theorem degN_add : (a + b).degN = max (a.degN + b.degD) (b.degN + a.degD) := rfl
@[simp] theorem degD_add : (a + b).degD = a.degD + b.degD := rfl
@[simp] theorem divDeg_add : (a + b).divDeg = a.divDeg + b.divDeg := rfl
@[simp] theorem degN_sub : (a - b).degN = max (a.degN + b.degD) (b.degN + a.degD) := rfl
@[simp] theorem degD_sub : (a - b).degD = a.degD + b.degD := rfl
@[simp] theorem divDeg_sub : (a - b).divDeg = a.divDeg + b.divDeg := rfl
@[simp] theorem degN_mul : (a * b).degN = a.degN + b.degN := rfl
@[simp] theorem degD_mul : (a * b).degD = a.degD + b.degD := rfl
@[simp] theorem divDeg_mul : (a * b).divDeg = a.divDeg + b.divDeg := rfl
@[simp] theorem degN_div : (a / b).degN = a.degN + b.degD := rfl
@[simp] theorem degD_div : (a / b).degD = a.degD + b.degN := rfl
@[simp] theorem divDeg_div : (a / b).divDeg = a.divDeg + b.divDeg + b.degN := rfl
end Degrees

/-! ### Semantics -/

variable [Field F] (x : Fin k → F)

/-- The symbolic meaning: a rational function in the challenge. -/
noncomputable def sym : RExpr F k → RatFunc F
  | leaf i => RatFunc.C (x i)
  | const c => RatFunc.C c
  | X => RatFunc.X
  | add a b => sym a + sym b
  | sub a b => sym a - sym b
  | mul a b => sym a * sym b
  | div a b => sym a / sym b

/-- The pointwise meaning: the value at a challenge. -/
def evalAt (α : F) : RExpr F k → F
  | leaf i => x i
  | const c => c
  | X => α
  | add a b => evalAt α a + evalAt α b
  | sub a b => evalAt α a - evalAt α b
  | mul a b => evalAt α a * evalAt α b
  | div a b => evalAt α a / evalAt α b

/-- A numerator and a denominator, built the way the expression is. -/
noncomputable def frac : RExpr F k → F[X] × F[X]
  | leaf i => (C (x i), 1)
  | const c => (C c, 1)
  | X => (Polynomial.X, 1)
  | add a b => ((frac a).1 * (frac b).2 + (frac b).1 * (frac a).2, (frac a).2 * (frac b).2)
  | sub a b => ((frac a).1 * (frac b).2 - (frac b).1 * (frac a).2, (frac a).2 * (frac b).2)
  | mul a b => ((frac a).1 * (frac b).1, (frac a).2 * (frac b).2)
  | div a b => ((frac a).1 * (frac b).2, (frac a).2 * (frac b).1)

/-- No divisor is identically zero. -/
def NZ : RExpr F k → Prop
  | leaf _ | const _ | X => True
  | add a b | sub a b | mul a b => NZ a ∧ NZ b
  | div a b => NZ a ∧ NZ b ∧ sym x b ≠ 0

/-- No divisor vanishes at the challenge `α`. -/
def Good (α : F) : RExpr F k → Prop
  | leaf _ | const _ | X => True
  | add a b | sub a b | mul a b => Good α a ∧ Good α b
  | div a b => Good α a ∧ Good α b ∧ evalAt x α b ≠ 0

/-- The challenges at which checking `evalAt x α e = 0` does not establish `sym x e = 0`. -/
def Bad (e : RExpr F k) (α : F) : Prop :=
  NZ x e ∧ (¬Good x α e ∨ polyBad (frac x e).1 α)

/-! ### Rewriting the meanings of expressions, for users -/

section Simp
variable {x}
variable (a b : RExpr F k) (α : F)

@[simp] theorem sym_leaf (i : Fin k) : sym x (leaf i) = RatFunc.C (x i) := rfl
@[simp] theorem sym_const (c : F) : sym x (const c : RExpr F k) = RatFunc.C c := rfl
@[simp] theorem sym_X : sym x (X : RExpr F k) = RatFunc.X := rfl
@[simp] theorem sym_add : sym x (a + b) = sym x a + sym x b := rfl
@[simp] theorem sym_sub : sym x (a - b) = sym x a - sym x b := rfl
@[simp] theorem sym_mul : sym x (a * b) = sym x a * sym x b := rfl
@[simp] theorem sym_div : sym x (a / b) = sym x a / sym x b := rfl

@[simp] theorem evalAt_leaf (i : Fin k) : evalAt x α (leaf i) = x i := rfl
@[simp] theorem evalAt_const (c : F) : evalAt x α (const c : RExpr F k) = c := rfl
@[simp] theorem evalAt_X : evalAt x α (X : RExpr F k) = α := rfl
@[simp] theorem evalAt_add : evalAt x α (a + b) = evalAt x α a + evalAt x α b := rfl
@[simp] theorem evalAt_sub : evalAt x α (a - b) = evalAt x α a - evalAt x α b := rfl
@[simp] theorem evalAt_mul : evalAt x α (a * b) = evalAt x α a * evalAt x α b := rfl
@[simp] theorem evalAt_div : evalAt x α (a / b) = evalAt x α a / evalAt x α b := rfl

@[simp] theorem NZ_leaf (i : Fin k) : NZ x (leaf i) := trivial
@[simp] theorem NZ_const (c : F) : NZ x (const c : RExpr F k) := trivial
@[simp] theorem NZ_X : NZ x (X : RExpr F k) := trivial
@[simp] theorem NZ_add : NZ x (a + b) ↔ NZ x a ∧ NZ x b := .rfl
@[simp] theorem NZ_sub : NZ x (a - b) ↔ NZ x a ∧ NZ x b := .rfl
@[simp] theorem NZ_mul : NZ x (a * b) ↔ NZ x a ∧ NZ x b := .rfl
@[simp] theorem NZ_div : NZ x (a / b) ↔ NZ x a ∧ NZ x b ∧ sym x b ≠ 0 := .rfl

@[simp] theorem Good_leaf (i : Fin k) : Good x α (leaf i) := trivial
@[simp] theorem Good_const (c : F) : Good x α (const c : RExpr F k) := trivial
@[simp] theorem Good_X : Good x α (X : RExpr F k) := trivial
@[simp] theorem Good_add : Good x α (a + b) ↔ Good x α a ∧ Good x α b := .rfl
@[simp] theorem Good_sub : Good x α (a - b) ↔ Good x α a ∧ Good x α b := .rfl
@[simp] theorem Good_mul : Good x α (a * b) ↔ Good x α a ∧ Good x α b := .rfl
@[simp] theorem Good_div : Good x α (a / b) ↔ Good x α a ∧ Good x α b ∧ evalAt x α b ≠ 0 := .rfl

@[simp] theorem sym_sum : ∀ (n : ℕ) (f : Fin n → RExpr F k), sym x (sum n f) = ∑ i, sym x (f i)
  | 0, _ => by simp [sum]
  | n + 1, f => by rw [sum, sym_add, sym_sum n, Fin.sum_univ_succ]
@[simp] theorem sym_prod : ∀ (n : ℕ) (f : Fin n → RExpr F k), sym x (prod n f) = ∏ i, sym x (f i)
  | 0, _ => by simp [prod]
  | n + 1, f => by rw [prod, sym_mul, sym_prod n, Fin.prod_univ_succ]
@[simp] theorem sym_pow (e : RExpr F k) : ∀ n : ℕ, sym x (e ^ n) = sym x e ^ n
  | 0 => by show sym x (pow e 0) = _; simp [pow]
  | n + 1 => by
    show sym x (pow e n * e) = _
    rw [sym_mul, show pow e n = e ^ n from rfl, sym_pow e n, pow_succ]

@[simp] theorem evalAt_sum : ∀ (n : ℕ) (f : Fin n → RExpr F k), evalAt x α (sum n f) = ∑ i, evalAt x α (f i)
  | 0, _ => by simp [sum]
  | n + 1, f => by rw [sum, evalAt_add, evalAt_sum n, Fin.sum_univ_succ]
@[simp] theorem evalAt_prod : ∀ (n : ℕ) (f : Fin n → RExpr F k), evalAt x α (prod n f) = ∏ i, evalAt x α (f i)
  | 0, _ => by simp [prod]
  | n + 1, f => by rw [prod, evalAt_mul, evalAt_prod n, Fin.prod_univ_succ]
@[simp] theorem evalAt_pow (e : RExpr F k) : ∀ n : ℕ, evalAt x α (e ^ n) = evalAt x α e ^ n
  | 0 => by show evalAt x α (pow e 0) = _; simp [pow]
  | n + 1 => by
    show evalAt x α (pow e n * e) = _
    rw [evalAt_mul, show pow e n = e ^ n from rfl, evalAt_pow e n, pow_succ]

@[simp] theorem NZ_sum : ∀ (n : ℕ) (f : Fin n → RExpr F k), NZ x (sum n f) ↔ ∀ i, NZ x (f i)
  | 0, _ => by simp [sum]
  | n + 1, f => by rw [sum, NZ_add, NZ_sum n, Fin.forall_fin_succ]
@[simp] theorem NZ_prod : ∀ (n : ℕ) (f : Fin n → RExpr F k), NZ x (prod n f) ↔ ∀ i, NZ x (f i)
  | 0, _ => by simp [prod]
  | n + 1, f => by rw [prod, NZ_mul, NZ_prod n, Fin.forall_fin_succ]
@[simp] theorem NZ_pow (e : RExpr F k) : ∀ n : ℕ, NZ x (e ^ n) ↔ n = 0 ∨ NZ x e
  | 0 => by simp [HPow.hPow, pow]
  | n + 1 => by
    show NZ x (pow e n * e) ↔ _
    rw [NZ_mul, show pow e n = e ^ n from rfl, NZ_pow e n]
    tauto

@[simp] theorem Good_sum : ∀ (n : ℕ) (f : Fin n → RExpr F k), Good x α (sum n f) ↔ ∀ i, Good x α (f i)
  | 0, _ => by simp [sum]
  | n + 1, f => by rw [sum, Good_add, Good_sum n, Fin.forall_fin_succ]
@[simp] theorem Good_prod : ∀ (n : ℕ) (f : Fin n → RExpr F k), Good x α (prod n f) ↔ ∀ i, Good x α (f i)
  | 0, _ => by simp [prod]
  | n + 1, f => by rw [prod, Good_mul, Good_prod n, Fin.forall_fin_succ]
@[simp] theorem Good_pow (e : RExpr F k) : ∀ n : ℕ, Good x α (e ^ n) ↔ n = 0 ∨ Good x α e
  | 0 => by simp [HPow.hPow, pow]
  | n + 1 => by
    show Good x α (pow e n * e) ↔ _
    rw [Good_mul, show pow e n = e ^ n from rfl, Good_pow e n]
    tauto

end Simp

/-! ### The bridges -/

local notation "A" => algebraMap F[X] (RatFunc F)

theorem sym_eq (e : RExpr F k) (h : NZ x e) :
    (frac x e).2 ≠ 0 ∧ sym x e = A (frac x e).1 / A (frac x e).2 := by
  induction e with
  | leaf i => simp [frac, sym, RatFunc.algebraMap_C]
  | const c => simp [frac, sym, RatFunc.algebraMap_C]
  | X => simp [frac, sym, RatFunc.algebraMap_X]
  | add a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2
    refine ⟨mul_ne_zero hda hdb, ?_⟩
    rw [sym, frac, hsa, hsb, div_add_div _ _ (RatFunc.algebraMap_ne_zero hda) (RatFunc.algebraMap_ne_zero hdb)]
    simp only [map_add, map_mul]
    ring
  | sub a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2
    refine ⟨mul_ne_zero hda hdb, ?_⟩
    rw [sym, frac, hsa, hsb, div_sub_div _ _ (RatFunc.algebraMap_ne_zero hda) (RatFunc.algebraMap_ne_zero hdb)]
    simp only [map_sub, map_mul]
    ring
  | mul a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2
    refine ⟨mul_ne_zero hda hdb, ?_⟩
    rw [sym, frac, hsa, hsb, div_mul_div_comm]
    simp only [map_mul]
  | div a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2.1
    have hnb : (frac x b).1 ≠ 0 := by
      intro h0
      apply h.2.2
      rw [hsb, h0, map_zero, zero_div]
    refine ⟨mul_ne_zero hda hnb, ?_⟩
    rw [sym, frac, hsa, hsb, div_div_div_eq]
    simp only [map_mul]

theorem evalAt_eq (e : RExpr F k) (α : F) (h : Good x α e) :
    (frac x e).2.eval α ≠ 0 ∧ evalAt x α e = (frac x e).1.eval α / (frac x e).2.eval α := by
  induction e with
  | leaf i => simp [frac, evalAt]
  | const c => simp [frac, evalAt]
  | X => simp [frac, evalAt]
  | add a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2
    refine ⟨by simp only [frac, eval_mul]; exact mul_ne_zero hda hdb, ?_⟩
    rw [evalAt, hsa, hsb, div_add_div _ _ hda hdb]
    simp only [frac, eval_add, eval_mul]
    ring
  | sub a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2
    refine ⟨by simp only [frac, eval_mul]; exact mul_ne_zero hda hdb, ?_⟩
    rw [evalAt, hsa, hsb, div_sub_div _ _ hda hdb]
    simp only [frac, eval_sub, eval_mul]
    ring
  | mul a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2
    refine ⟨by simp only [frac, eval_mul]; exact mul_ne_zero hda hdb, ?_⟩
    rw [evalAt, hsa, hsb, div_mul_div_comm]
    simp only [frac, eval_mul]
  | div a b iha ihb =>
    obtain ⟨hda, hsa⟩ := iha h.1
    obtain ⟨hdb, hsb⟩ := ihb h.2.1
    have hnb : (frac x b).1.eval α ≠ 0 := by
      intro h0
      apply h.2.2
      rw [hsb, h0, zero_div]
    refine ⟨by simp only [frac, eval_mul]; exact mul_ne_zero hda hnb, ?_⟩
    rw [evalAt, hsa, hsb, div_div_div_eq]
    simp only [frac, eval_mul]

theorem natDegree_frac_le (e : RExpr F k) :
    (frac x e).1.natDegree ≤ degN e ∧ (frac x e).2.natDegree ≤ degD e := by
  induction e with
  | leaf i => simp [frac, degN, degD]
  | const c => simp [frac, degN, degD]
  | X => simp only [frac, degN, degD, natDegree_one, le_refl, and_true]; exact natDegree_X_le
  | add a b iha ihb =>
    refine ⟨(natDegree_add_le _ _).trans (max_le_max ?_ ?_), natDegree_mul_le.trans (add_le_add iha.2 ihb.2)⟩
    · exact natDegree_mul_le.trans (add_le_add iha.1 ihb.2)
    · exact natDegree_mul_le.trans (add_le_add ihb.1 iha.2)
  | sub a b iha ihb =>
    refine ⟨(natDegree_sub_le _ _).trans (max_le_max ?_ ?_), natDegree_mul_le.trans (add_le_add iha.2 ihb.2)⟩
    · exact natDegree_mul_le.trans (add_le_add iha.1 ihb.2)
    · exact natDegree_mul_le.trans (add_le_add ihb.1 iha.2)
  | mul a b iha ihb =>
    exact ⟨natDegree_mul_le.trans (add_le_add iha.1 ihb.1), natDegree_mul_le.trans (add_le_add iha.2 ihb.2)⟩
  | div a b iha ihb =>
    exact ⟨natDegree_mul_le.trans (add_le_add iha.1 ihb.2), natDegree_mul_le.trans (add_le_add iha.2 ihb.1)⟩

/-- Some divisor vanishes at no more than `divDeg e` challenges. -/
theorem encard_not_good_le (e : RExpr F k) (h : NZ x e) : {α | ¬Good x α e}.encard ≤ divDeg e := by
  induction e with
  | leaf _ | const _ | X => simp [Good, divDeg]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    refine (Set.encard_le_encard (t := {α | ¬Good x α a} ∪ {α | ¬Good x α b}) fun α hα => ?_).trans
      ((Set.encard_union_le _ _).trans ?_)
    · simp only [Good, Set.mem_ofPred_eq, not_and_or] at hα
      exact hα
    · simp only [divDeg, Nat.cast_add]
      exact add_le_add (iha h.1) (ihb h.2)
  | div a b iha ihb =>
    obtain ⟨hdb, hsb⟩ := sym_eq x b h.2.1
    have hnb : (frac x b).1 ≠ 0 := by
      intro h0
      apply h.2.2
      rw [hsb, h0, map_zero, zero_div]
    refine (Set.encard_le_encard (t := ({α | ¬Good x α a} ∪ {α | ¬Good x α b}) ∪
      {α | polyBad (frac x b).1 α}) fun α hα => ?_).trans
      ((Set.encard_union_le _ _).trans ?_)
    · simp only [Good, Set.mem_ofPred_eq, not_and_or, not_not] at hα
      rcases hα with hα | hα | hα
      · exact .inl (.inl hα)
      · exact .inl (.inr hα)
      · by_cases hb : Good x α b
        · obtain ⟨hdα, hbα⟩ := evalAt_eq x b α hb
          rw [hbα, div_eq_zero_iff] at hα
          exact .inr ⟨hnb, hα.resolve_right hdα⟩
        · exact .inl (.inr hb)
    · simp only [divDeg, Nat.cast_add]
      refine add_le_add ((Set.encard_union_le _ _).trans (add_le_add (iha h.1) (ihb h.2.1))) ?_
      exact (encard_polyBad_le _).trans (Nat.cast_le.mpr (natDegree_frac_le x b).1)

theorem encard_bad_le (e : RExpr F k) : {α | Bad x e α}.encard ≤ bound e := by
  by_cases h : NZ x e
  · refine (Set.encard_le_encard (t := {α | ¬Good x α e} ∪ {α | polyBad (frac x e).1 α})
      fun α hα => hα.2).trans ((Set.encard_union_le _ _).trans ?_)
    rw [bound, Nat.cast_add, add_comm (e.degN : ℕ∞)]
    exact add_le_add (encard_not_good_le x e h)
      ((encard_polyBad_le _).trans (Nat.cast_le.mpr (natDegree_frac_le x e).1))
  · simp [Bad, h]

/-- **Soundness bridge.** Outside the bad challenges, a pointwise zero is a symbolic one. -/
theorem sym_eq_zero (e : RExpr F k) {α : F} (h_nz : NZ x e) (h_bad : ¬Bad x e α)
    (h_zero : evalAt x α e = 0) : sym x e = 0 := by
  simp only [Bad, h_nz, true_and, not_or, not_not] at h_bad
  obtain ⟨h_good, h_poly⟩ := h_bad
  obtain ⟨hd, hs⟩ := sym_eq x e h_nz
  obtain ⟨hdα, hα⟩ := evalAt_eq x e α h_good
  have h_num : (frac x e).1.eval α = 0 := by
    rw [hα, div_eq_zero_iff] at h_zero
    exact h_zero.resolve_right hdα
  have h_num0 : (frac x e).1 = 0 := by
    by_contra h_ne
    exact h_poly ⟨h_ne, h_num⟩
  rw [hs, h_num0, map_zero, zero_div]

/-- **Completeness bridge.** A symbolic zero is a pointwise one at a good challenge, and the
challenge is not bad. -/
theorem evalAt_eq_zero (e : RExpr F k) {α : F} (h_nz : NZ x e) (h_sym : sym x e = 0)
    (h_good : Good x α e) : evalAt x α e = 0 ∧ ¬Bad x e α := by
  obtain ⟨hd, hs⟩ := sym_eq x e h_nz
  have h_num0 : (frac x e).1 = 0 := by
    rw [hs, div_eq_zero_iff] at h_sym
    exact RatFunc.algebraMap_injective F (h_sym.resolve_right (RatFunc.algebraMap_ne_zero hd) |>.trans (map_zero _).symm)
  obtain ⟨hdα, hα⟩ := evalAt_eq x e α h_good
  refine ⟨by rw [hα, h_num0, eval_zero, zero_div], ?_⟩
  rintro ⟨-, h | ⟨h_ne, -⟩⟩
  · exact h h_good
  · exact h_ne h_num0

end RExpr
end Clean2
