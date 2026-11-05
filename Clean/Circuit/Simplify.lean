/-
Certified constraint simplification on flat circuit operations.

This is the backend-independent core of a simplifier: it works on `List (FlatOperation F)`
and Clean's own constraint semantics `ConstraintsHoldFlat`, not on any backend's
constraint type. `FormalCircuit.simplify` (SimplifyFormal.lean) packages it as a
transformation of formal circuits that preserves their `Spec`.

## What the pass does

Asserts are processed in order. Each assert is first rewritten with the substitutions
found so far (`Expression.subst`). If the result is *linear* (`toLinear?`), it is
normalized to `k + Σ cᵢ·vᵢ = 0` and classified:

* `0 = 0` is dropped;
* if the form is small enough (at most `maxVars + 1` variables) and contains a variable
  that is not forbidden, that variable `x` is solved for, `x ↦ r`, and the assert
  disappears; `x` is substituted in all later asserts, and in the right-hand sides found so
  far, so the substitution map stays *non-overlapping* (no eliminated variable occurs in
  any right-hand side);
* everything else, including constant contradictions like `-2 = 0` and non-linear asserts,
  is kept (rewritten).

Witness, lookup and interaction operations pass through untouched, in their original
positions. So the witness generators, the variable numbering, `localLength` and the
lookups/interactions of the operations are unchanged; only the asserts change.

The choice `maxVars = 1` is simple substitution (`x = y`, `x = k`); larger values allow
Gaussian-elimination-style substitution of longer linear constraints.

## What is proved

With `fb` marking the forbidden variables (never eliminated),

* `simplifyFlat_complete`: an environment satisfying the original constraints satisfies the
  simplified ones (the same environment: the eliminated variables keep their values);
* `simplifyFlat_sound`: an environment satisfying the simplified constraints extends, by
  recomputing eliminated variables from their right-hand sides (`Environment.substExtend`)
  and hence agreeing with it on all forbidden variables, to one satisfying the original.

Together, for any property of the forbidden variables (such as a circuit's `Spec` on its
input and output), the two operation lists are interchangeable.
-/
module

public import Clean.Circuit.Operations
public import Mathlib.Tactic.LinearCombination

@[expose] public section

variable {F : Type} [FiniteField F]

/-! ## Variables and substitution in expressions -/

namespace Expression

/-- Variables occurring in an expression. -/
def vars : Expression F → List ℕ
  | .var v => [v.index]
  | .const _ => []
  | .add a b => vars a ++ vars b
  | .mul a b => vars a ++ vars b

/-- Evaluation only depends on the variables that occur. -/
theorem eval_congr {env env' : Environment F} : ∀ {e : Expression F},
    (∀ v ∈ e.vars, env.get v = env'.get v) → eval env e = eval env' e
  | .var v, h => h v.index (by simp [vars])
  | .const _, _ => rfl
  | .add a b, h => by
    simp only [eval]
    rw [eval_congr (fun v hv => h v (by simp [vars, hv])),
      eval_congr (fun v hv => h v (by simp [vars, hv]))]
  | .mul a b, h => by
    simp only [eval]
    rw [eval_congr (fun v hv => h v (by simp [vars, hv])),
      eval_congr (fun v hv => h v (by simp [vars, hv]))]

/-- A substitution: a partial map from (eliminated) variables to expressions. -/
abbrev Subst (F : Type) := ℕ → Option (Expression F)

/-- Replace every occurrence of an eliminated variable by its right-hand side. -/
def subst (s : Subst F) : Expression F → Expression F
  | .var v => match s v.index with
    | some r => r
    | none => .var v
  | .const c => .const c
  | .add a b => .add (subst s a) (subst s b)
  | .mul a b => .mul (subst s a) (subst s b)

/-- `env` respects `s` if every eliminated variable equals its right-hand side under `env`. -/
def Respects (env : Environment F) (s : Subst F) : Prop :=
  ∀ x r, s x = some r → env.get x = eval env r

/-- Substituting an expression with a substitution that is respected by the environment does not change its evaluation. -/
theorem eval_subst {env : Environment F} {s : Subst F} (hs : Respects env s) :
    ∀ e : Expression F, eval env (subst s e) = eval env e
  | .var v => by
    simp only [subst]
    cases h : s v.index with
    | none => rfl
    | some r => simp [eval, hs _ _ h]
  | .const _ => rfl
  | .add a b => by simp only [subst, eval, eval_subst hs a, eval_subst hs b]
  | .mul a b => by simp only [subst, eval, eval_subst hs a, eval_subst hs b]

/-- No variable of `e` is eliminated by `s`. -/
def KeyFree (s : Subst F) (e : Expression F) : Prop :=
  ∀ v ∈ e.vars, s v = none

/-- No eliminated variable occurs in any right-hand side. -/
def NonOverlapping (s : Subst F) : Prop :=
  ∀ x r, s x = some r → KeyFree s r

omit [FiniteField F] in
theorem mem_vars_subst {s : Subst F} {v : ℕ} : ∀ {e : Expression F}, v ∈ (subst s e).vars →
    (v ∈ e.vars ∧ s v = none) ∨ ∃ x r, s x = some r ∧ v ∈ r.vars
  | .var w, h => by
    simp only [subst] at h
    cases hw : s w.index with
    | none =>
      rw [hw] at h
      simp only [vars, List.mem_singleton] at h
      subst h
      exact .inl ⟨by simp [vars], hw⟩
    | some r =>
      rw [hw] at h
      exact .inr ⟨w.index, r, hw, h⟩
  | .const _, h => by simp [subst, vars] at h
  | .add a b, h => by
    simp only [subst, vars, List.mem_append] at h
    rcases h with h | h
    · rcases mem_vars_subst h with ⟨h1, h2⟩ | h
      · exact .inl ⟨by simp [vars, h1], h2⟩
      · exact .inr h
    · rcases mem_vars_subst h with ⟨h1, h2⟩ | h
      · exact .inl ⟨by simp [vars, h1], h2⟩
      · exact .inr h
  | .mul a b, h => by
    simp only [subst, vars, List.mem_append] at h
    rcases h with h | h
    · rcases mem_vars_subst h with ⟨h1, h2⟩ | h
      · exact .inl ⟨by simp [vars, h1], h2⟩
      · exact .inr h
    · rcases mem_vars_subst h with ⟨h1, h2⟩ | h
      · exact .inl ⟨by simp [vars, h1], h2⟩
      · exact .inr h

omit [FiniteField F] in
/-- Substituting with `s` yields an expression free of `t`, provided the untouched variables
are free of `t` and every right-hand side of `s` is. -/
theorem keyFree_subst_of {s t : Subst F} {e : Expression F}
    (h1 : ∀ v ∈ e.vars, s v = none → t v = none)
    (h2 : ∀ x r, s x = some r → KeyFree t r) : KeyFree t (subst s e) := by
  intro v hv
  rcases mem_vars_subst hv with ⟨hv, hs⟩ | ⟨x, r, hx, hr⟩
  · exact h1 v hv hs
  · exact h2 x r hx v hr

omit [FiniteField F] in
theorem keyFree_subst {s : Subst F} (hNO : NonOverlapping s) (e : Expression F) :
    KeyFree s (subst s e) :=
  keyFree_subst_of (fun _ _ h => h) hNO

end Expression

/-! ## Witness extension -/

namespace Environment

/-- Recompute the eliminated variables from their right-hand sides. -/
def substExtend (s : Expression.Subst F) (env : Environment F) : Environment F where
  get v := match s v with
    | some r => Expression.eval env r
    | none => env.get v
  data := env.data

theorem substExtend_get_of_none {s : Expression.Subst F} {env : Environment F} {v : ℕ}
    (h : s v = none) : (env.substExtend s).get v = env.get v := by
  simp [substExtend, h]

theorem substExtend_data (s : Expression.Subst F) (env : Environment F) :
    (env.substExtend s).data = env.data := rfl

theorem eval_substExtend_of_keyFree {s : Expression.Subst F} {env : Environment F}
    {e : Expression F} (h : Expression.KeyFree s e) :
    Expression.eval (env.substExtend s) e = Expression.eval env e :=
  Expression.eval_congr fun v hv => substExtend_get_of_none (h v hv)

theorem respects_substExtend {s : Expression.Subst F} (hNO : Expression.NonOverlapping s)
    (env : Environment F) : Expression.Respects (env.substExtend s) s := by
  intro x r hx
  have h1 : (env.substExtend s).get x = Expression.eval env r := by simp [substExtend, hx]
  rw [h1, eval_substExtend_of_keyFree (hNO x r hx)]

end Environment

/-! ## Linear forms -/

namespace Circuit.Simplify

/-- A linear form `k + Σ cᵢ·vᵢ`: the constant and the terms. -/
abbrev Lin (F : Type) := F × List (ℕ × F)

/-- Evaluate a list of terms in an environment. -/
def evalTerms (env : Environment F) (lc : List (ℕ × F)) : F :=
  (lc.map fun (v, c) => c * env.get v).sum

def evalLin (env : Environment F) (l : Lin F) : F := l.1 + evalTerms env l.2

@[simp] theorem evalTerms_nil (env : Environment F) : evalTerms env [] = 0 := rfl

@[simp] theorem evalTerms_cons (env : Environment F) (v : ℕ) (c : F) (lc : List (ℕ × F)) :
    evalTerms env ((v, c) :: lc) = c * env.get v + evalTerms env lc := by
  simp [evalTerms]

theorem evalTerms_append (env : Environment F) (a b : List (ℕ × F)) :
    evalTerms env (a ++ b) = evalTerms env a + evalTerms env b := by
  simp [evalTerms]

def scaleTerms (k : F) (lc : List (ℕ × F)) : List (ℕ × F) :=
  lc.map fun (v, c) => (v, k * c)

/-- The evaluation of scaled terms is the scale of the evaluation. -/
theorem evalTerms_scaleTerms (env : Environment F) (k : F) (lc : List (ℕ × F)) :
    evalTerms env (scaleTerms k lc) = k * evalTerms env lc := by
  induction lc with
  | nil => simp [scaleTerms]
  | cons hd tl ih =>
    obtain ⟨v, c⟩ := hd
    have h : scaleTerms k ((v, c) :: tl) = (v, k * c) :: scaleTerms k tl := rfl
    rw [h, evalTerms_cons, evalTerms_cons, ih]
    ring

theorem evalTerms_perm (env : Environment F) {a b : List (ℕ × F)} (h : a.Perm b) :
    evalTerms env a = evalTerms env b :=
  (h.map _).sum_eq

/-- The keys (variables) of a term list. -/
def keys (lc : List (ℕ × F)) : List ℕ := lc.map (·.1)

omit [FiniteField F] in
theorem mem_keys {lc : List (ℕ × F)} {v : ℕ} : v ∈ keys lc ↔ ∃ c, (v, c) ∈ lc := by
  simp [keys]

/-- Linearize an expression, if it is linear: products need one constant factor. -/
def toLinear? : Expression F → Option (Lin F)
  | .var v => some (0, [(v.index, 1)])
  | .const c => some (c, [])
  | .add a b =>
    match toLinear? a, toLinear? b with
    | some (ka, la), some (kb, lb) => some (ka + kb, la ++ lb)
    | _, _ => none
  | .mul a b =>
    match toLinear? a, toLinear? b with
    | some (ka, la), some (kb, lb) =>
      if la = [] then some (ka * kb, scaleTerms ka lb)
      else if lb = [] then some (ka * kb, scaleTerms kb la)
      else none
    | _, _ => none

/-- If an expression can be linearized, its evaluation equals the evaluation of the resulting linear form. -/
theorem eval_of_toLinear (env : Environment F) :
    ∀ {e : Expression F} {l : Lin F}, toLinear? e = some l → Expression.eval env e = evalLin env l
  | .var v, l, h => by
    simp only [toLinear?, Option.some.injEq] at h
    subst h
    simp [Expression.eval, evalLin]
  | .const c, l, h => by
    simp only [toLinear?, Option.some.injEq] at h
    subst h
    simp [Expression.eval, evalLin]
  | .add a b, l, h => by
    simp only [toLinear?] at h
    cases ha : toLinear? a with
    | none => simp [ha] at h
    | some la =>
      cases hb : toLinear? b with
      | none => simp [ha, hb] at h
      | some lb =>
        obtain ⟨ka, la⟩ := la
        obtain ⟨kb, lb⟩ := lb
        simp only [ha, hb, Option.some.injEq] at h
        subst h
        simp only [Expression.eval, eval_of_toLinear env ha, eval_of_toLinear env hb, evalLin,
          evalTerms_append]
        ring
  | .mul a b, l, h => by
    simp only [toLinear?] at h
    cases ha : toLinear? a with
    | none => simp [ha] at h
    | some la =>
      cases hb : toLinear? b with
      | none => simp [ha, hb] at h
      | some lb =>
        obtain ⟨ka, la⟩ := la
        obtain ⟨kb, lb⟩ := lb
        simp only [ha, hb] at h
        have hea := eval_of_toLinear env ha
        have heb := eval_of_toLinear env hb
        split_ifs at h with h1 h2
        · simp only [Option.some.injEq] at h
          subst h
          subst h1
          simp only [Expression.eval, hea, heb, evalLin, evalTerms_scaleTerms, evalTerms_nil,
            add_zero]
          ring
        · simp only [Option.some.injEq] at h
          subst h
          subst h2
          simp only [Expression.eval, hea, heb, evalLin, evalTerms_scaleTerms, evalTerms_nil,
            add_zero]
          ring

/-- If an expression can be linearized, all the variables in the resulting linear form are also in the expression. -/
theorem keys_of_toLinear : ∀ {e : Expression F} {l : Lin F}, toLinear? e = some l →
    ∀ v ∈ keys l.2, v ∈ e.vars
  | .var w, l, h, v, hv => by
    simp only [toLinear?, Option.some.injEq] at h
    subst h
    simp [keys, Expression.vars] at hv ⊢
    exact hv
  | .const _, l, h, v, hv => by
    simp only [toLinear?, Option.some.injEq] at h
    subst h
    simp [keys] at hv
  | .add a b, l, h, v, hv => by
    simp only [toLinear?] at h
    cases ha : toLinear? a with
    | none => simp [ha] at h
    | some la =>
      cases hb : toLinear? b with
      | none => simp [ha, hb] at h
      | some lb =>
        obtain ⟨ka, la⟩ := la
        obtain ⟨kb, lb⟩ := lb
        simp only [ha, hb, Option.some.injEq] at h
        subst h
        simp only [keys, List.map_append, List.mem_append] at hv
        simp only [Expression.vars, List.mem_append]
        rcases hv with hv | hv
        · exact .inl (keys_of_toLinear ha v hv)
        · exact .inr (keys_of_toLinear hb v hv)
  | .mul a b, l, h, v, hv => by
    simp only [toLinear?] at h
    cases ha : toLinear? a with
    | none => simp [ha] at h
    | some la =>
      cases hb : toLinear? b with
      | none => simp [ha, hb] at h
      | some lb =>
        obtain ⟨ka, la⟩ := la
        obtain ⟨kb, lb⟩ := lb
        simp only [ha, hb] at h
        simp only [Expression.vars, List.mem_append]
        split_ifs at h with h1 h2
        · simp only [Option.some.injEq] at h
          subst h
          simp only [keys, scaleTerms, List.map_map] at hv
          exact .inr (keys_of_toLinear hb v (by simpa [keys] using hv))
        · simp only [Option.some.injEq] at h
          subst h
          simp only [keys, scaleTerms, List.map_map] at hv
          exact .inl (keys_of_toLinear ha v (by simpa [keys] using hv))

/-! ### Normalization: merge duplicate variables, drop zero coefficients -/

def insertTerm (v : ℕ) (c : F) : List (ℕ × F) → List (ℕ × F)
  | [] => if c = 0 then [] else [(v, c)]
  | (w, d) :: rest =>
    if v = w then (if c + d = 0 then rest else (w, c + d) :: rest)
    else (w, d) :: insertTerm v c rest

def normalize : List (ℕ × F) → List (ℕ × F)
  | [] => []
  | (v, c) :: rest => insertTerm v c (normalize rest)

/-- Evaluation of a list of terms after inserting a new term. -/
theorem evalTerms_insertTerm (env : Environment F) (v : ℕ) (c : F) :
    ∀ lc : List (ℕ × F), evalTerms env (insertTerm v c lc) = c * env.get v + evalTerms env lc
  | [] => by
    simp only [insertTerm]
    split_ifs with h
    · simp [h]
    · simp
  | (w, d) :: rest => by
    simp only [insertTerm]
    split_ifs with h1 h2
    · subst h1
      rw [evalTerms_cons]
      linear_combination -(env.get v) * h2
    · subst h1
      simp only [evalTerms_cons]
      ring
    · rw [evalTerms_cons, evalTerms_insertTerm env v c rest, evalTerms_cons]
      ring

/-- Evaluation of a normalized list of terms equals the evaluation of the original list. -/
theorem evalTerms_normalize (env : Environment F) :
    ∀ lc : List (ℕ × F), evalTerms env (normalize lc) = evalTerms env lc
  | [] => rfl
  | (v, c) :: rest => by
    simp only [normalize]
    rw [evalTerms_insertTerm, evalTerms_normalize env rest, evalTerms_cons]

/-- All the keys of a list of terms after inserting a new term are either the inserted variable or from the original list. -/
theorem keys_insertTerm_subset (v : ℕ) (c : F) :
    ∀ lc : List (ℕ × F), ∀ w ∈ keys (insertTerm v c lc), w = v ∨ w ∈ keys lc
  | [], w, hw => by
    simp only [insertTerm] at hw
    split_ifs at hw with h
    · simp [keys] at hw
    · simp [keys] at hw
      exact .inl hw
  | (u, d) :: rest, w, hw => by
    simp only [insertTerm] at hw
    split_ifs at hw with h1 h2
    · subst h1
      exact .inr (by simp [keys] at hw ⊢; exact .inr hw)
    · subst h1
      simp only [keys, List.map_cons, List.mem_cons] at hw ⊢
      rcases hw with hw | hw
      · exact .inl hw
      · exact .inr (.inr hw)
    · simp only [keys, List.map_cons, List.mem_cons] at hw ⊢
      rcases hw with hw | hw
      · exact .inr (.inl hw)
      · rcases keys_insertTerm_subset v c rest w hw with hw | hw
        · exact .inl hw
        · exact .inr (.inr hw)

theorem keys_normalize_subset : ∀ lc : List (ℕ × F), ∀ w ∈ keys (normalize lc), w ∈ keys lc
  | [], w, hw => by simp [normalize, keys] at hw
  | (v, c) :: rest, w, hw => by
    simp only [normalize] at hw
    simp only [keys, List.map_cons, List.mem_cons]
    rcases keys_insertTerm_subset v c _ w hw with hw | hw
    · exact .inl hw
    · exact .inr (keys_normalize_subset rest w hw)

theorem nodup_keys_insertTerm (v : ℕ) (c : F) :
    ∀ lc : List (ℕ × F), (keys lc).Nodup → (keys (insertTerm v c lc)).Nodup
  | [], _ => by
    simp only [insertTerm]
    split_ifs <;> simp [keys]
  | (u, d) :: rest, h => by
    simp only [keys, List.map_cons, List.nodup_cons] at h
    obtain ⟨hu, hrest⟩ := h
    simp only [insertTerm]
    split_ifs with h1 h2
    · exact hrest
    · simp only [keys, List.map_cons, List.nodup_cons]
      exact ⟨hu, hrest⟩
    · simp only [keys, List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_keys_insertTerm v c rest hrest⟩
      intro hu'
      rcases keys_insertTerm_subset v c rest u hu' with hu' | hu'
      · exact h1 hu'.symm
      · exact hu hu'

theorem nodup_keys_normalize : ∀ lc : List (ℕ × F), (keys (normalize lc)).Nodup
  | [] => List.nodup_nil
  | (v, c) :: rest => nodup_keys_insertTerm v c _ (nodup_keys_normalize rest)

theorem nonzero_insertTerm (v : ℕ) (c : F) :
    ∀ lc : List (ℕ × F), (∀ w d, (w, d) ∈ lc → d ≠ 0) →
      ∀ w d, (w, d) ∈ insertTerm v c lc → d ≠ 0
  | [], _, w, d, hw => by
    simp only [insertTerm] at hw
    split_ifs at hw with h
    · simp at hw
    · simp only [List.mem_singleton, Prod.mk.injEq] at hw
      rw [hw.2]
      exact h
  | (u, e) :: rest, h, w, d, hw => by
    simp only [insertTerm] at hw
    split_ifs at hw with h1 h2
    · exact h w d (List.mem_cons_of_mem _ hw)
    · simp only [List.mem_cons, Prod.mk.injEq] at hw
      rcases hw with ⟨_, rfl⟩ | hw
      · exact h2
      · exact h w d (List.mem_cons_of_mem _ hw)
    · simp only [List.mem_cons, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | hw
      · exact h _ _ (List.mem_cons_self ..)
      · exact nonzero_insertTerm v c rest (fun w d hw => h w d (List.mem_cons_of_mem _ hw)) w d hw

theorem nonzero_normalize : ∀ lc : List (ℕ × F), ∀ w d, (w, d) ∈ normalize lc → d ≠ 0
  | [], _, _, hw => by simp [normalize] at hw
  | (v, c) :: rest, w, d, hw => nonzero_insertTerm v c _ (nonzero_normalize rest) w d hw

/-! ### Choosing the variable to eliminate -/

/-- Pick a non-forbidden variable to eliminate (the largest index), returning
its coefficient and the remaining terms. -/
def pickCons (fb : ℕ → Bool) (v : ℕ) (c : F) (rest : List (ℕ × F)) :
    Option (ℕ × F × List (ℕ × F)) → Option (ℕ × F × List (ℕ × F))
  | some (x, cx, others) =>
    if fb v = false ∧ x < v then some (v, c, (x, cx) :: others)
    else some (x, cx, (v, c) :: others)
  | none => if fb v = false then some (v, c, rest) else none

def pickVar (fb : ℕ → Bool) : List (ℕ × F) → Option (ℕ × F × List (ℕ × F))
  | [] => none
  | (v, c) :: rest => pickCons fb v c rest (pickVar fb rest)

omit [FiniteField F] in
theorem pickVar_spec (fb : ℕ → Bool) : ∀ {lc : List (ℕ × F)} {x : ℕ} {cx : F} {others : List (ℕ × F)},
    pickVar fb lc = some (x, cx, others) → fb x = false ∧ lc.Perm ((x, cx) :: others)
  | [], _, _, _, h => by simp [pickVar] at h
  | (v, c) :: rest, x, cx, others, h => by
    simp only [pickVar] at h
    cases hp : pickVar fb rest with
    | none =>
      rw [hp] at h
      simp only [pickCons] at h
      by_cases hv : fb v = false
      · rw [if_pos hv] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hv, List.Perm.refl _⟩
      · rw [if_neg hv] at h
        cases h
    | some p =>
      obtain ⟨y, cy, ys⟩ := p
      obtain ⟨hy, hperm⟩ := pickVar_spec fb hp
      rw [hp] at h
      simp only [pickCons] at h
      by_cases hv : fb v = false ∧ y < v
      · rw [if_pos hv] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hv.1, hperm.cons _⟩
      · rw [if_neg hv] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hy, (hperm.cons _).trans (List.Perm.swap _ _ _)⟩

/-- A linear form as an expression. -/
def linToExpr (l : Lin F) : Expression F :=
  l.2.foldr (fun (v, c) acc => .add (.mul (.const c) (.var ⟨v⟩)) acc) (.const l.1)

theorem eval_linToExpr (env : Environment F) (k : F) :
    ∀ lc : List (ℕ × F), Expression.eval env (linToExpr (k, lc)) = evalLin env (k, lc)
  | [] => by simp [linToExpr, Expression.eval, evalLin]
  | (v, c) :: rest => by
    have h : linToExpr (k, (v, c) :: rest) =
        .add (.mul (.const c) (.var ⟨v⟩)) (linToExpr (k, rest)) := rfl
    rw [h]
    simp only [Expression.eval, eval_linToExpr env k rest, evalLin, evalTerms_cons]
    ring

omit [FiniteField F] in
theorem vars_linToExpr (k : F) : ∀ (lc : List (ℕ × F)) (v : ℕ),
    v ∈ (linToExpr (k, lc)).vars → v ∈ keys lc
  | [], v, hv => by simp [linToExpr, Expression.vars] at hv
  | (w, c) :: rest, v, hv => by
    have h : linToExpr (k, (w, c) :: rest) =
        .add (.mul (.const c) (.var ⟨w⟩)) (linToExpr (k, rest)) := rfl
    rw [h] at hv
    simp only [Expression.vars, List.mem_append, List.mem_singleton, List.nil_append] at hv
    simp only [keys, List.map_cons, List.mem_cons]
    rcases hv with rfl | hv
    · exact .inl rfl
    · exact .inr (vars_linToExpr k rest v hv)

/-! ### Classification -/

inductive Action (F : Type) where
  | drop
  | subst (x : ℕ) (r : Expression F)
  | keep

/-- Classify a linear assert `k + Σ cᵢ·vᵢ = 0`: drop it if trivial, turn it into a
substitution if it has at most `maxVars + 1` variables and one of them is not forbidden,
keep it otherwise (in particular, keep contradictions `k = 0` with `k ≠ 0`). -/
def classify (fb : ℕ → Bool) (maxVars : ℕ) (l : Lin F) : Action F :=
  let lc := normalize l.2
  if lc = [] then (if l.1 = 0 then .drop else .keep)
  else if lc.length ≤ maxVars + 1 then
    match pickVar fb lc with
    | some (x, cx, others) => .subst x (linToExpr (-(l.1 / cx), scaleTerms (-(1 / cx)) others))
    | none => .keep
  else .keep

/-- If `classify` returns `.drop`, the linear form is trivially zero. -/
theorem classify_drop {fb : ℕ → Bool} {m : ℕ} {l : Lin F} (h : classify fb m l = .drop)
    (env : Environment F) : evalLin env l = 0 := by
  unfold classify at h
  by_cases h0 : normalize l.2 = []
  · rw [if_pos h0] at h
    by_cases hk : l.1 = 0
    · have := evalTerms_normalize env l.2
      rw [h0] at this
      simp only [evalTerms_nil] at this
      simp [evalLin, ← this, hk]
    · rw [if_neg hk] at h
      cases h
  · rw [if_neg h0] at h
    by_cases hlen : (normalize l.2).length ≤ m + 1
    · rw [if_pos hlen] at h
      cases hp : pickVar fb (normalize l.2) with
      | none => rw [hp] at h; cases h
      | some p =>
        obtain ⟨y, cy, others⟩ := p
        rw [hp] at h
        cases h
    · rw [if_neg hlen] at h
      cases h

/-- Specification of a substitution produced by `classify`: it eliminates a non-forbidden
variable of the form, its right-hand side only mentions other variables of the form, and
it is equivalent to the assert. -/
theorem classify_subst {fb : ℕ → Bool} {m : ℕ} {l : Lin F} {x : ℕ} {r : Expression F}
    (h : classify fb m l = .subst x r) :
    fb x = false ∧ x ∉ r.vars ∧ x ∈ keys l.2 ∧ (∀ v ∈ r.vars, v ∈ keys l.2) ∧
    (∀ env : Environment F, evalLin env l = 0 ↔ env.get x = Expression.eval env r) := by
  unfold classify at h
  by_cases h0 : normalize l.2 = []
  · rw [if_pos h0] at h
    by_cases hk : l.1 = 0
    · rw [if_pos hk] at h; cases h
    · rw [if_neg hk] at h; cases h
  · rw [if_neg h0] at h
    by_cases hlen : (normalize l.2).length ≤ m + 1
    · rw [if_pos hlen] at h
      cases hp : pickVar fb (normalize l.2) with
      | none => rw [hp] at h; cases h
      | some p =>
        obtain ⟨y, cy, others⟩ := p
        rw [hp] at h
        simp only [Action.subst.injEq] at h
        obtain ⟨hx, hr⟩ := h
        rw [← hx, ← hr]
        obtain ⟨hfb, hperm⟩ := pickVar_spec fb hp
        have hnodup : (keys ((y, cy) :: others)).Nodup :=
          (hperm.map _).nodup_iff.mp (nodup_keys_normalize l.2)
        have hy_others : y ∉ keys others := by
          simp only [keys, List.map_cons, List.nodup_cons] at hnodup
          exact hnodup.1
        have hcy : cy ≠ 0 :=
          nonzero_normalize l.2 y cy (hperm.mem_iff.mpr (List.mem_cons_self ..))
        have hkeys : ∀ v ∈ keys others, v ∈ keys l.2 := fun v hv =>
          keys_normalize_subset l.2 v ((hperm.map _).mem_iff.mpr (List.mem_cons_of_mem _ hv))
        refine ⟨hfb, ?_, ?_, ?_, ?_⟩
        · intro hy
          have := vars_linToExpr _ _ y hy
          simp only [keys, scaleTerms, List.map_map] at this
          exact hy_others (by simpa [keys] using this)
        · exact keys_normalize_subset l.2 y ((hperm.map _).mem_iff.mpr (by simp))
        · intro v hv
          have := vars_linToExpr _ _ v hv
          simp only [keys, scaleTerms, List.map_map] at this
          exact hkeys v (by simpa [keys] using this)
        · intro env
          rw [eval_linToExpr]
          simp only [evalLin, evalTerms_scaleTerms]
          have hsum : evalTerms env l.2 = cy * env.get y + evalTerms env others := by
            rw [← evalTerms_normalize, evalTerms_perm env hperm, evalTerms_cons]
          rw [hsum]
          constructor
          · intro h
            linear_combination cy⁻¹ * h - (env.get y) * (mul_inv_cancel₀ hcy)
          · intro h
            rw [h]
            linear_combination -(l.1 + evalTerms env others) * (mul_inv_cancel₀ hcy)
    · rw [if_neg hlen] at h
      cases h

/-! ## The pass -/

/-- The substitution entries: `(x, r)` means `x` was eliminated and equals `r`. -/
abbrev SubstEntries (F : Type) := List (ℕ × Expression F)

def lookupVar : SubstEntries F → ℕ → Option (Expression F)
  | [], _ => none
  | (y, r) :: rest, v => if v = y then some r else lookupVar rest v

/-- The single substitution `x ↦ r`. -/
def single (x : ℕ) (r : Expression F) : Expression.Subst F :=
  fun v => if v = x then some r else none

/-- Add `x ↦ r`, substituting `x` in all existing right-hand sides, so the map stays
non-overlapping. -/
def addEntry (es : SubstEntries F) (x : ℕ) (r : Expression F) : SubstEntries F :=
  (x, r) :: es.map fun (y, ry) => (y, Expression.subst (single x r) ry)

/-- Apply a substitution to an operation: only asserts change. -/
def substOp (s : Expression.Subst F) : FlatOperation F → FlatOperation F
  | .assert e => .assert (Expression.subst s e)
  | op => op

structure State (F : Type) [FiniteField F] where
  subst : SubstEntries F := []
  /-- Kept operations, most recent first. -/
  kept : List (FlatOperation F) := []

/-- Process one operation. -/
def step (fb : ℕ → Bool) (maxVars : ℕ) (st : State F) : FlatOperation F → State F
  | .assert e =>
    let e' := Expression.subst (lookupVar st.subst) e
    match toLinear? e' with
    | some l =>
      match classify fb maxVars l with
      | .drop => st
      | .subst x r => { st with subst := addEntry st.subst x r }
      | .keep => { st with kept := .assert e' :: st.kept }
    | none => { st with kept := .assert e' :: st.kept }
  | op => { st with kept := op :: st.kept }

/-- The certified simplification pass on flat operations. `fb` marks the forbidden
variables (never eliminated); `maxVars` bounds the number of variables of a linear assert
that may be turned into a substitution. Returns the simplified operations and the substitution
map. -/
def simplifyFlat (fb : ℕ → Bool) (maxVars : ℕ) (ops : List (FlatOperation F)) :
    List (FlatOperation F) × SubstEntries F :=
  let st := ops.foldl (step fb maxVars) {}
  (st.kept.reverse.map (substOp (lookupVar st.subst)), st.subst)

/-! ## Correctness -/

omit [FiniteField F] in
theorem lookupVar_map_subst (es : SubstEntries F) (t : Expression.Subst F) (v : ℕ) :
    lookupVar (es.map fun (y, ry) => (y, Expression.subst t ry)) v =
      (lookupVar es v).map (Expression.subst t) := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨y, ry⟩ := hd
    simp only [List.map_cons, lookupVar]
    split_ifs <;> simp [ih]

omit [FiniteField F] in
theorem lookupVar_addEntry (es : SubstEntries F) (x : ℕ) (r : Expression F) (v : ℕ) :
    lookupVar (addEntry es x r) v =
      if v = x then some r else (lookupVar es v).map (Expression.subst (single x r)) := by
  simp only [addEntry, lookupVar]
  split_ifs with h
  · rfl
  · exact lookupVar_map_subst es _ v

omit [FiniteField F] in
theorem lookupVar_addEntry_of_ne {es : SubstEntries F} {x v : ℕ} {r : Expression F}
    (hvx : v ≠ x) (hv : lookupVar es v = none) : lookupVar (addEntry es x r) v = none := by
  rw [lookupVar_addEntry, if_neg hvx, hv]; rfl

theorem respects_single {env : Environment F} {x : ℕ} {r : Expression F} :
    Expression.Respects env (single x r) ↔ env.get x = Expression.eval env r := by
  constructor
  · intro h
    exact h x r (by simp [single])
  · intro h v r' hv
    by_cases hvx : v = x
    · subst hvx
      simp [single] at hv
      subst hv
      exact h
    · simp [single, hvx] at hv

theorem respects_addEntry {env : Environment F} {es : SubstEntries F} {x : ℕ} {r : Expression F}
    (hx : lookupVar es x = none) :
    Expression.Respects env (lookupVar (addEntry es x r)) ↔
      env.get x = Expression.eval env r ∧ Expression.Respects env (lookupVar es) := by
  constructor
  · intro h
    have hxr : env.get x = Expression.eval env r := h x r (by rw [lookupVar_addEntry]; simp)
    refine ⟨hxr, fun v rv hv => ?_⟩
    have hvx : v ≠ x := by
      rintro rfl
      rw [hx] at hv
      cases hv
    have h' := h v (Expression.subst (single x r) rv)
      (by rw [lookupVar_addEntry, if_neg hvx, hv]; rfl)
    rw [h', Expression.eval_subst (respects_single.mpr hxr)]
  · rintro ⟨hxr, hres⟩ v rv hv
    rw [lookupVar_addEntry] at hv
    split_ifs at hv with hvx
    · subst hvx
      rw [← Option.some.inj hv]
      exact hxr
    · cases hlv : lookupVar es v with
      | none => simp [hlv] at hv
      | some rv' =>
        simp only [hlv, Option.map_some, Option.some.injEq] at hv
        subst hv
        rw [Expression.eval_subst (respects_single.mpr hxr)]
        exact hres v rv' hlv

omit [FiniteField F] in
theorem nonOverlapping_addEntry {es : SubstEntries F} {x : ℕ} {r : Expression F}
    (hNO : Expression.NonOverlapping (lookupVar es))
    (hr : Expression.KeyFree (lookupVar es) r) (hxr : x ∉ r.vars) :
    Expression.NonOverlapping (lookupVar (addEntry es x r)) := by
  have hnone : ∀ v, v ≠ x → lookupVar es v = none → lookupVar (addEntry es x r) v = none :=
    fun v hv hvn => lookupVar_addEntry_of_ne hv hvn
  have hrfree : Expression.KeyFree (lookupVar (addEntry es x r)) r := by
    intro v hv
    exact hnone v (fun h => hxr (h ▸ hv)) (hr v hv)
  intro y ry hy
  rw [lookupVar_addEntry] at hy
  split_ifs at hy with hyx
  · rw [← Option.some.inj hy]
    exact hrfree
  · cases hly : lookupVar es y with
    | none => simp [hly] at hy
    | some ry' =>
      simp only [hly, Option.map_some, Option.some.injEq] at hy
      subst hy
      refine Expression.keyFree_subst_of ?_ ?_
      · intro v hv hsv
        have hvx : v ≠ x := by
          intro h
          simp [single, h] at hsv
        exact hnone v hvx (hNO y ry' hly v hv)
      · intro v rv hv
        by_cases hvx : v = x
        · simp [single, hvx] at hv
          subst hv
          exact hrfree
        · simp [single, hvx] at hv

/-- Operations with the asserts removed: the part of a list the pass never changes. -/
def dropAsserts : List (FlatOperation F) → List (FlatOperation F)
  | [] => []
  | .assert _ :: ops => dropAsserts ops
  | op :: ops => op :: dropAsserts ops

omit [FiniteField F] in
theorem dropAsserts_append : ∀ (a b : List (FlatOperation F)),
    dropAsserts (a ++ b) = dropAsserts a ++ dropAsserts b
  | [], _ => rfl
  | .assert _ :: a, b => dropAsserts_append a b
  | .witness _ _ :: a, b => by simp [dropAsserts, dropAsserts_append a b]
  | .lookup _ :: a, b => by simp [dropAsserts, dropAsserts_append a b]
  | .interact _ :: a, b => by simp [dropAsserts, dropAsserts_append a b]

omit [FiniteField F] in
theorem dropAsserts_map_substOp (s : Expression.Subst F) :
    ∀ ops : List (FlatOperation F), dropAsserts (ops.map (substOp s)) = dropAsserts ops
  | [] => rfl
  | .assert _ :: ops => by simp [substOp, dropAsserts, dropAsserts_map_substOp s ops]
  | .witness _ _ :: ops => by simp [substOp, dropAsserts, dropAsserts_map_substOp s ops]
  | .lookup _ :: ops => by simp [substOp, dropAsserts, dropAsserts_map_substOp s ops]
  | .interact _ :: ops => by simp [substOp, dropAsserts, dropAsserts_map_substOp s ops]

omit [FiniteField F] in
theorem lookups_dropAsserts : ∀ ops : List (FlatOperation F),
    FlatOperation.lookups (dropAsserts ops) = FlatOperation.lookups ops
  | [] => rfl
  | .assert _ :: ops => by simp [dropAsserts, FlatOperation.lookups, lookups_dropAsserts ops]
  | .witness _ _ :: ops => by simp [dropAsserts, FlatOperation.lookups, lookups_dropAsserts ops]
  | .lookup _ :: ops => by simp [dropAsserts, FlatOperation.lookups, lookups_dropAsserts ops]
  | .interact _ :: ops => by simp [dropAsserts, FlatOperation.lookups, lookups_dropAsserts ops]

omit [FiniteField F] in
theorem constraints_map_substOp (s : Expression.Subst F) :
    ∀ ops : List (FlatOperation F),
      FlatOperation.constraints (ops.map (substOp s)) =
        (FlatOperation.constraints ops).map (Expression.subst s)
  | [] => rfl
  | .assert _ :: ops => by simp [substOp, FlatOperation.constraints, constraints_map_substOp s ops]
  | .witness _ _ :: ops => by simp [substOp, FlatOperation.constraints, constraints_map_substOp s ops]
  | .lookup _ :: ops => by simp [substOp, FlatOperation.constraints, constraints_map_substOp s ops]
  | .interact _ :: ops => by simp [substOp, FlatOperation.constraints, constraints_map_substOp s ops]

omit [FiniteField F] in
theorem constraints_reverse (ops : List (FlatOperation F)) :
    FlatOperation.constraints ops.reverse = (FlatOperation.constraints ops).reverse := by
  induction ops using FlatOperation.induct <;>
    simp_all [FlatOperation.constraints, FlatOperation.constraints_append]

/-- The fold invariant: the substitution map is non-overlapping and never eliminates a
forbidden variable, the non-assert operations are kept verbatim, and `(subst, kept)` is
equivalent to the processed prefix `pre`. -/
structure Inv (fb : ℕ → Bool) (pre : List (FlatOperation F)) (st : State F) : Prop where
  nonOverlapping : Expression.NonOverlapping (lookupVar st.subst)
  forbidden : ∀ v, fb v = true → lookupVar st.subst v = none
  shape : dropAsserts st.kept.reverse = dropAsserts pre
  fwd : ∀ env : Environment F, (∀ e ∈ FlatOperation.constraints pre, Expression.eval env e = 0) →
    Expression.Respects env (lookupVar st.subst) ∧
    ∀ e ∈ FlatOperation.constraints st.kept, Expression.eval env e = 0
  bwd : ∀ env : Environment F, Expression.Respects env (lookupVar st.subst) →
    (∀ e ∈ FlatOperation.constraints st.kept, Expression.eval env e = 0) →
    ∀ e ∈ FlatOperation.constraints pre, Expression.eval env e = 0

/-- The initial invariant holds for an empty list of operations and an empty state. -/
theorem inv_init (fb : ℕ → Bool) : Inv fb [] ({} : State F) where
  nonOverlapping := fun _ _ h => by simp [lookupVar] at h
  forbidden := fun _ _ => rfl
  shape := rfl
  fwd := fun _ _ => ⟨fun _ _ h => by simp [lookupVar] at h, fun _ h => by simp [FlatOperation.constraints] at h⟩
  bwd := fun _ _ _ _ h => by simp [FlatOperation.constraints] at h

omit [FiniteField F] in
theorem constraints_append_singleton_assert (pre : List (FlatOperation F)) (e : Expression F) :
    FlatOperation.constraints (pre ++ [.assert e]) = FlatOperation.constraints pre ++ [e] := by
  rw [FlatOperation.constraints_append]; rfl

omit [FiniteField F] in
theorem constraints_append_singleton_other (pre : List (FlatOperation F)) (op : FlatOperation F)
    (h : ∀ e, op ≠ .assert e) :
    FlatOperation.constraints (pre ++ [op]) = FlatOperation.constraints pre := by
  rw [FlatOperation.constraints_append]
  cases op with
  | assert e => exact absurd rfl (h e)
  | witness _ _ => simp [FlatOperation.constraints]
  | lookup _ => simp [FlatOperation.constraints]
  | interact _ => simp [FlatOperation.constraints]

theorem step_inv_other {fb : ℕ → Bool} {pre : List (FlatOperation F)} {st : State F}
    (hinv : Inv fb pre st) (op : FlatOperation F) (h : ∀ e, op ≠ .assert e) :
    Inv fb (pre ++ [op]) { st with kept := op :: st.kept } := by
  obtain ⟨hNO, hforb, hstr, hfwd, hbwd⟩ := hinv
  have hc : FlatOperation.constraints (op :: st.kept) = FlatOperation.constraints st.kept := by
    cases op with
    | assert e => exact absurd rfl (h e)
    | witness _ _ => rfl
    | lookup _ => rfl
    | interact _ => rfl
  refine ⟨hNO, hforb, ?_, ?_, ?_⟩
  · show dropAsserts (op :: st.kept).reverse = dropAsserts (pre ++ [op])
    rw [List.reverse_cons, dropAsserts_append, dropAsserts_append, hstr]
  · intro env henv
    rw [constraints_append_singleton_other pre op h] at henv
    rw [hc]
    exact hfwd env henv
  · intro env hr hk
    rw [hc] at hk
    rw [constraints_append_singleton_other pre op h]
    exact hbwd env hr hk

theorem step_inv_assert {fb : ℕ → Bool} {m : ℕ} {pre : List (FlatOperation F)} {st : State F}
    (hinv : Inv fb pre st) (e : Expression F) :
    Inv fb (pre ++ [.assert e]) (step fb m st (.assert e)) := by
  obtain ⟨hNO, hforb, hstr, hfwd, hbwd⟩ := hinv
  -- the substituted assert
  have hkf : Expression.KeyFree (lookupVar st.subst) (Expression.subst (lookupVar st.subst) e) :=
    Expression.keyFree_subst hNO e
  have hiff : ∀ env : Environment F, Expression.Respects env (lookupVar st.subst) →
      (Expression.eval env (Expression.subst (lookupVar st.subst) e) = 0 ↔ Expression.eval env e = 0) :=
    fun env hr => by rw [Expression.eval_subst hr]
  simp only [step]
  cases hlin : toLinear? (Expression.subst (lookupVar st.subst) e) with
  | none =>
    dsimp only
    refine ⟨hNO, hforb, ?_, ?_, ?_⟩
    · show dropAsserts (FlatOperation.assert _ :: st.kept).reverse = dropAsserts (pre ++ [.assert e])
      rw [List.reverse_cons, dropAsserts_append, dropAsserts_append, hstr]; rfl
    · intro env henv
      rw [constraints_append_singleton_assert] at henv
      obtain ⟨hr, hk⟩ := hfwd env (fun e' he' => henv e' (List.mem_append_left _ he'))
      refine ⟨hr, fun e' he' => ?_⟩
      simp only [FlatOperation.constraints, List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact (hiff env hr).mpr (henv e (List.mem_append_right _ (List.mem_singleton_self _)))
      · exact hk e' he'
    · intro env hr hk
      rw [constraints_append_singleton_assert]
      intro e' he'
      rcases List.mem_append.mp he' with he' | he'
      · exact hbwd env hr (fun e'' he'' => hk e'' (List.mem_cons_of_mem _ he'')) e' he'
      · rw [List.mem_singleton.mp he']
        exact (hiff env hr).mp (hk _ (List.mem_cons_self ..))
  | some l =>
    dsimp only
    have hl : ∀ env : Environment F, Expression.eval env (Expression.subst (lookupVar st.subst) e) = evalLin env l :=
      fun env => eval_of_toLinear env hlin
    cases hcl : classify fb m l with
    | drop =>
      dsimp only
      refine ⟨hNO, hforb, ?_, ?_, ?_⟩
      · show dropAsserts st.kept.reverse = dropAsserts (pre ++ [.assert e])
        rw [dropAsserts_append, hstr]; simp [dropAsserts]
      · intro env henv
        rw [constraints_append_singleton_assert] at henv
        exact hfwd env (fun e' he' => henv e' (List.mem_append_left _ he'))
      · intro env hr hk
        rw [constraints_append_singleton_assert]
        intro e' he'
        rcases List.mem_append.mp he' with he' | he'
        · exact hbwd env hr hk e' he'
        · rw [List.mem_singleton.mp he']
          rw [← hiff env hr, hl]
          exact classify_drop hcl env
    | subst x r =>
      dsimp only
      obtain ⟨hfx, hxr, hxkeys, hrkeys, hcx⟩ := classify_subst hcl
      have hxvars : x ∈ (Expression.subst (lookupVar st.subst) e).vars :=
        keys_of_toLinear hlin x hxkeys
      have hx : lookupVar st.subst x = none := hkf x hxvars
      have hr : Expression.KeyFree (lookupVar st.subst) r :=
        fun v hv => hkf v (keys_of_toLinear hlin v (hrkeys v hv))
      refine ⟨nonOverlapping_addEntry hNO hr hxr, ?_, ?_, ?_, ?_⟩
      · intro v hv
        refine lookupVar_addEntry_of_ne ?_ (hforb v hv)
        intro hvx
        subst hvx
        rw [hv] at hfx
        exact Bool.noConfusion hfx
      · show dropAsserts st.kept.reverse = dropAsserts (pre ++ [.assert e])
        rw [dropAsserts_append, hstr]; simp [dropAsserts]
      · intro env henv
        rw [constraints_append_singleton_assert] at henv
        obtain ⟨hr', hk⟩ := hfwd env (fun e' he' => henv e' (List.mem_append_left _ he'))
        have he : Expression.eval env e = 0 := henv e (List.mem_append_right _ (List.mem_singleton_self _))
        refine ⟨(respects_addEntry hx).mpr ⟨?_, hr'⟩, hk⟩
        exact (hcx env).mp (by rw [← hl, hiff env hr']; exact he)
      · intro env hr' hk
        obtain ⟨hxr', hr''⟩ := (respects_addEntry hx).mp hr'
        rw [constraints_append_singleton_assert]
        intro e' he'
        rcases List.mem_append.mp he' with he' | he'
        · exact hbwd env hr'' hk e' he'
        · rw [List.mem_singleton.mp he']
          rw [← hiff env hr'', hl]
          exact (hcx env).mpr hxr'
    | keep =>
      dsimp only
      refine ⟨hNO, hforb, ?_, ?_, ?_⟩
      · show dropAsserts (FlatOperation.assert _ :: st.kept).reverse = dropAsserts (pre ++ [.assert e])
        rw [List.reverse_cons, dropAsserts_append, dropAsserts_append, hstr]; rfl
      · intro env henv
        rw [constraints_append_singleton_assert] at henv
        obtain ⟨hr, hk⟩ := hfwd env (fun e' he' => henv e' (List.mem_append_left _ he'))
        refine ⟨hr, fun e' he' => ?_⟩
        simp only [FlatOperation.constraints, List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact (hiff env hr).mpr (henv e (List.mem_append_right _ (List.mem_singleton_self _)))
        · exact hk e' he'
      · intro env hr hk
        rw [constraints_append_singleton_assert]
        intro e' he'
        rcases List.mem_append.mp he' with he' | he'
        · exact hbwd env hr (fun e'' he'' => hk e'' (List.mem_cons_of_mem _ he'')) e' he'
        · rw [List.mem_singleton.mp he']
          exact (hiff env hr).mp (hk _ (List.mem_cons_self ..))

/-- The invariant is preserved by a single step of the simplification pass. -/
theorem step_inv {fb : ℕ → Bool} {m : ℕ} {pre : List (FlatOperation F)} {st : State F}
    (hinv : Inv fb pre st) (op : FlatOperation F) : Inv fb (pre ++ [op]) (step fb m st op) := by
  cases op with
  | assert e => exact step_inv_assert hinv e
  | witness n c => exact step_inv_other hinv (.witness n c) (fun _ h => by cases h)
  | lookup l => exact step_inv_other hinv (.lookup l) (fun _ h => by cases h)
  | interact i => exact step_inv_other hinv (.interact i) (fun _ h => by cases h)

/-- The invariant is preserved by folding the simplification pass over a list of operations. -/
theorem foldl_inv {fb : ℕ → Bool} {m : ℕ} :
    ∀ (ops pre : List (FlatOperation F)) (st : State F),
      Inv fb pre st → Inv fb (pre ++ ops) (ops.foldl (step fb m) st)
  | [], pre, st, h => by rw [List.append_nil]; exact h
  | op :: ops, pre, st, h => by
    rw [List.foldl_cons, ← List.singleton_append, ← List.append_assoc]
    exact foldl_inv ops (pre ++ [op]) (step fb m st op) (step_inv h op)

/-- The non-assert operations are unchanged by the pass. -/
theorem dropAsserts_simplifyFlat (fb : ℕ → Bool) (m : ℕ) (ops : List (FlatOperation F)) :
    dropAsserts (simplifyFlat fb m ops).1 = dropAsserts ops := by
  have hinv := foldl_inv (fb := fb) (m := m) ops [] {} (inv_init fb)
  rw [List.nil_append] at hinv
  show dropAsserts (List.map (substOp _) _) = dropAsserts ops
  rw [dropAsserts_map_substOp]
  exact hinv.shape

/-- Variables occurring in a lookup's entry. -/
def lookupVars (l : Lookup F) : List ℕ := l.entry.toList.flatMap Expression.vars

theorem Lookup.contains_congr {l : Lookup F} {env env' : Environment F}
    (hdata : env.data = env'.data) (h : ∀ v ∈ lookupVars l, env.get v = env'.get v) :
    l.Contains env ↔ l.Contains env' := by
  have hmap : l.entry.map env = l.entry.map env' := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    apply Expression.eval_congr
    intro v hv
    apply h
    simp only [lookupVars, List.mem_flatMap]
    exact ⟨l.entry[i], by simp, hv⟩
  simp only [Lookup.Contains, hmap, hdata]

/-- **Completeness of the pass**: the same environment satisfies the simplified operations. -/
theorem simplifyFlat_complete (fb : ℕ → Bool) (m : ℕ) (ops : List (FlatOperation F))
    (env : Environment F) (h : ConstraintsHoldFlat env ops) :
    ConstraintsHoldFlat env (simplifyFlat fb m ops).1 := by
  have hinv := foldl_inv (fb := fb) (m := m) ops [] {} (inv_init fb)
  rw [List.nil_append] at hinv
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem] at h ⊢
  obtain ⟨hasserts, hlookups⟩ := h
  obtain ⟨hr, hk⟩ := hinv.fwd env hasserts
  refine ⟨?_, ?_⟩
  · intro e he
    show Expression.eval env e = 0
    simp only [simplifyFlat] at he
    rw [constraints_map_substOp, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    rw [constraints_reverse, List.mem_reverse] at he'
    rw [Expression.eval_subst hr]
    exact hk e' he'
  · intro l hl
    apply hlookups
    rw [← lookups_dropAsserts, ← dropAsserts_simplifyFlat fb m ops, lookups_dropAsserts]
    exact hl

/-- **Soundness of the pass**: an environment satisfying the simplified operations extends,
agreeing on the forbidden variables (and on the data), to one satisfying the original
operations. The lookups' variables must be forbidden. -/
theorem simplifyFlat_sound (fb : ℕ → Bool) (m : ℕ) (ops : List (FlatOperation F))
    (hlv : ∀ l ∈ FlatOperation.lookups ops, ∀ v ∈ lookupVars l, fb v = true)
    (env : Environment F) (h : ConstraintsHoldFlat env (simplifyFlat fb m ops).1) :
    ∃ env' : Environment F, (∀ v, fb v = true → env'.get v = env.get v) ∧ env'.data = env.data ∧
      ConstraintsHoldFlat env' ops := by
  have hinv := foldl_inv (fb := fb) (m := m) ops [] {} (inv_init fb)
  rw [List.nil_append] at hinv
  obtain ⟨hNO, hforb, _, _, hbwd⟩ := hinv
  set s := lookupVar (ops.foldl (step fb m) {}).subst with hs
  refine ⟨env.substExtend s, fun v hv => Environment.substExtend_get_of_none (hforb v hv),
    Environment.substExtend_data s env, ?_⟩
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem] at h ⊢
  obtain ⟨hasserts, hlookups⟩ := h
  have hr : Expression.Respects (env.substExtend s) s := Environment.respects_substExtend hNO env
  refine ⟨hbwd _ hr ?_, ?_⟩
  · intro e he
    -- `e` is a kept assert; its final version holds under `env`
    have hmem : Expression.subst s e ∈ FlatOperation.constraints (simplifyFlat fb m ops).1 := by
      simp only [simplifyFlat]
      rw [constraints_map_substOp, List.mem_map]
      exact ⟨e, by rw [constraints_reverse, List.mem_reverse]; exact he, rfl⟩
    have h1 : Expression.eval env (Expression.subst s e) = 0 := hasserts _ hmem
    have h2 : Expression.eval (env.substExtend s) (Expression.subst s e) = 0 := by
      rw [Environment.eval_substExtend_of_keyFree (Expression.keyFree_subst hNO e)]
      exact h1
    rw [Expression.eval_subst hr] at h2
    exact h2
  · intro l hl
    have hl' : l ∈ FlatOperation.lookups (simplifyFlat fb m ops).1 := by
      rw [← lookups_dropAsserts, dropAsserts_simplifyFlat fb m ops, lookups_dropAsserts]
      exact hl
    rw [Lookup.contains_congr (Environment.substExtend_data s env)
      (fun v hv => Environment.substExtend_get_of_none (hforb v (hlv l hl v hv)))]
    exact hlookups l hl'

end Circuit.Simplify
