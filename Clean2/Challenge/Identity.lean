/-
Symbolic identities, checked at a challenge: the functionality behind challenges in user circuits.

`Identity.interface e` takes `k` committed values `x` and a challenge `α`, and its spec is the
*symbolic* identity `sym x e = 0`, an equation between rational functions. The challenge does not
appear in the spec: users reason about `e` as if the challenge were the indeterminate `X`.

`Identity.impl` implements it on any backend with `Arith`: it evaluates `e` at `α` (a witness and a
`mulEq` per division), asserts that the value is zero, and assumes the rare event `Bad e x α`, at
no more than `e.bound` challenges. Its error bound is `e.bound` (`errorBound`), and completeness
needs the challenge to avoid the zeros of the divisors (`Good`), which is the honest prover's own
error.
-/
module

public import Clean2.Challenge.RExpr
public import Clean2.Functionalities.Arith

@[expose] public section

namespace Clean2
open Polynomial

namespace Identity
variable {Native : Type} [Field Native]

/-- The identity `e = 0`, in `k` committed values. The input is the committed values and the
challenge; the spec is symbolic. -/
@[reducible]
def interface {k : ℕ} (e : RExpr Native k) : Interface Native where
  input := Vector Native k × Native
  inputCType := .natives k ×ᵗ .native
  output := Unit
  outputCType := .unit
  Assumptions := fun (x, _) => e.NZ (fun i => x[i])
  Spec := fun (x, _) _ => e.sym (fun i => x[i]) = 0
  ProverAssumptions := fun (x, α) =>
    e.NZ (fun i => x[i]) ∧ e.sym (fun i => x[i]) = 0 ∧ e.Good (fun i => x[i]) α

variable {B : Backend} [Field B.Native]

/-- The rare event of checking `e` at the challenge `α`. -/
def event {k : ℕ} (e : RExpr B.Native k) (x : Vector B.Var k) (α : B.Var) : RareEvent B where
  committed := x
  challenge := α
  Bad := fun v a => e.Bad (fun i => v[i]) a
  bound := e.bound
  encard_bad_le := fun v => e.encard_bad_le _

variable (arith : ∀ n, Impl B (Arith.interface n))

/-- Evaluate `e` at `α`: arithmetic, and a witness and a `mulEq` per division. -/
@[circuit_norm]
def evalCircuit {k : ℕ} (x : Fin k → B.Var) (α : B.Var) : RExpr B.Native k → Circuit B B.Var
  | .leaf i => pure (x i)
  | .const c => arith (.const c) ()
  | .X => pure α
  | .add a b => do
    let u ← evalCircuit x α a
    let v ← evalCircuit x α b
    arith .add (u, v)
  | .sub a b => do
    let u ← evalCircuit x α a
    let v ← evalCircuit x α b
    arith .sub (u, v)
  | .mul a b => do
    let u ← evalCircuit x α a
    let v ← evalCircuit x α b
    arith .mul (u, v)
  | .div a b => do
    let u ← evalCircuit x α a
    let v ← evalCircuit x α b
    let w ← arith (.witness nativePair fun (p : B.Native × B.Native) => p.1 / p.2) (u, v)
    arith .mulEq (w, v, u)
    return w

section Eval
variable {k : ℕ} (x : Fin k → B.Var) (α : B.Var)

theorem evalCircuit_consistent (e : RExpr B.Native k) (s : B.State) :
    ((evalCircuit arith x α e).operations s).Consistent s := by
  induction e generalizing s with
  | leaf | const | X => simp only [circuit_norm]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb =>
    simp only [circuit_norm]
    exact ⟨iha s, ihb _⟩

theorem evalCircuit_sound (e : RExpr B.Native k) (s : B.State) (env : B.Cell → B.Native)
    (h : ((evalCircuit arith x α e).operations s).SoundnessHold env s)
    (h_good : e.Good (fun i => B.eval env (x i)) (B.eval env α)) :
    B.eval env ((evalCircuit arith x α e).output s) = e.evalAt (fun i => B.eval env (x i)) (B.eval env α) := by
  induction e generalizing s with
  | leaf i => simp only [circuit_norm, RExpr.evalAt]
  | const c => simp only [circuit_norm, RExpr.evalAt] at h ⊢; exact h
  | X => simp only [circuit_norm, RExpr.evalAt]
  | add a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_out⟩ := h
    rw [h_out, iha s ha h_good.1, ihb _ hb h_good.2]; rfl
  | sub a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_out⟩ := h
    rw [h_out, iha s ha h_good.1, ihb _ hb h_good.2]; rfl
  | mul a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_out⟩ := h
    rw [h_out, iha s ha h_good.1, ihb _ hb h_good.2]; rfl
  | div a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_mul⟩ := h
    rw [iha s ha h_good.1, ihb _ hb h_good.2.1] at h_mul
    exact eq_div_of_mul_eq h_good.2.2 h_mul

theorem evalCircuit_complete (e : RExpr B.Native k) (s : B.State) (env : B.Cell → B.Native)
    (h : ((evalCircuit arith x α e).operations s).HonestCompleteness env s)
    (h_good : e.Good (fun i => B.eval env (x i)) (B.eval env α)) :
    ((evalCircuit arith x α e).operations s).CompletenessHold env s ∧
      B.eval env ((evalCircuit arith x α e).output s) = e.evalAt (fun i => B.eval env (x i)) (B.eval env α) := by
  induction e generalizing s with
  | leaf i => simp only [circuit_norm, RExpr.evalAt, and_self]
  | const c => simp only [circuit_norm, RExpr.evalAt] at h ⊢; exact h
  | X => simp only [circuit_norm, RExpr.evalAt, and_self]
  | add a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_out⟩ := h
    obtain ⟨ha', hva⟩ := iha s ha h_good.1
    obtain ⟨hb', hvb⟩ := ihb _ hb h_good.2
    exact ⟨⟨ha', hb'⟩, by rw [h_out, hva, hvb]; rfl⟩
  | sub a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_out⟩ := h
    obtain ⟨ha', hva⟩ := iha s ha h_good.1
    obtain ⟨hb', hvb⟩ := ihb _ hb h_good.2
    exact ⟨⟨ha', hb'⟩, by rw [h_out, hva, hvb]; rfl⟩
  | mul a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_out⟩ := h
    obtain ⟨ha', hva⟩ := iha s ha h_good.1
    obtain ⟨hb', hvb⟩ := ihb _ hb h_good.2
    exact ⟨⟨ha', hb'⟩, by rw [h_out, hva, hvb]; rfl⟩
  | div a b iha ihb =>
    simp only [circuit_norm] at h ⊢
    obtain ⟨ha, hb, h_w⟩ := h
    obtain ⟨ha', hva⟩ := iha s ha h_good.1
    obtain ⟨hb', hvb⟩ := ihb _ hb h_good.2.1
    have h_ne := h_good.2.2
    rw [← hvb] at h_ne
    refine ⟨⟨ha', hb', ?_⟩, ?_⟩
    · rw [h_w]; exact div_mul_cancel₀ _ h_ne
    · rw [h_w, hva, hvb]; rfl

theorem evalCircuit_local (e : RExpr B.Native k) (s : B.State) (K : B.State → Prop)
    (h_x : ∀ i, B.footprint (x i) ⊆ B.Alloc s) (h_α : B.footprint α ⊆ B.Alloc s)
    (h_K : B.footprint ((evalCircuit arith x α e).output s) ⊆
        B.Alloc (((evalCircuit arith x α e).operations s).advance s) →
      K (((evalCircuit arith x α e).operations s).advance s)) :
    ((evalCircuit arith x α e).operations s).LocalHold s K := by
  induction e generalizing s K with
  | leaf i => simp only [circuit_norm] at h_K ⊢; exact h_K (h_x i)
  | X => simp only [circuit_norm] at h_K ⊢; exact h_K h_α
  | const c =>
    simp only [circuit_norm, Set.empty_subset] at h_K ⊢
    spatial_split
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb =>
    have hca := evalCircuit_consistent arith x α a s
    have hmono := Ops.alloc_mono hca
    simp only [circuit_norm] at h_K hca hmono ⊢
    rw [Ops.localHold_append_of_consistent hca]
    refine iha s _ h_x h_α fun h_u => ?_
    have hcb := evalCircuit_consistent arith x α b ((evalCircuit arith x α a).operations s |>.advance s)
    have hmono2 := Ops.alloc_mono hcb
    simp only [circuit_norm] at hcb hmono2
    rw [Ops.localHold_append_of_consistent hcb]
    refine ihb _ _ (fun i => (h_x i).trans hmono) (h_α.trans hmono) fun h_v => ?_
    simp only [circuit_norm, Set.union_subset_iff, Set.empty_subset]
    spatial_split

end Eval

/-- Check `e = 0` at the challenge: evaluate, assert zero, assume the rare event. -/
def impl {k : ℕ} (e : RExpr B.Native k) : Impl B (interface e) where
  main | (x, α) => do
    let v ← evalCircuit arith (fun i => x[i]) α e
    arith .assertZero v
    Circuit.assumeRare (event e x α)
  consistent := by
    intro (x, α) s
    simp only [circuit_norm]
    exact evalCircuit_consistent arith _ _ e s
  spatial := by
    intro (x, α) s h
    obtain ⟨h_x, h_α⟩ := Backend.footprintT_ctypeProd_subset.mp h
    have h_x : ∀ i : Fin k, B.footprint x[i] ⊆ B.Alloc s := fun i => Backend.footprint_getElem_subset h_x i i.isLt
    have hc := evalCircuit_consistent arith (fun i => x[i]) α e s
    have hmono := Ops.alloc_mono hc
    simp only [circuit_norm] at h_α hc hmono ⊢
    rw [Ops.localHold_append_of_consistent hc]
    refine evalCircuit_local arith _ _ e s _ h_x h_α fun h_v => ?_
    simp only [circuit_norm, Set.empty_subset]
    spatial_split
  soundness := by
    intro s env (x, α) h_assumptions h
    simp only [circuit_norm, event] at h_assumptions h ⊢
    have hx : (fun i : Fin k => (Vector.map (B.eval env) x)[i]) = fun i => B.eval env x[i] :=
      funext fun i => by simp
    obtain ⟨h_eval, h_zero, h_rare⟩ := h
    rw [hx] at h_assumptions h_rare ⊢
    have h_good : e.Good (fun i => B.eval env x[i]) (B.eval env α) := by
      by_contra hg
      exact h_rare ⟨h_assumptions, .inl hg⟩
    rw [evalCircuit_sound arith _ α e s env h_eval h_good] at h_zero
    exact RExpr.sym_eq_zero _ e h_assumptions h_rare h_zero
  completeness := by
    intro s env (x, α) h h_prover
    simp only [circuit_norm, event] at h h_prover ⊢
    have hx : (fun i : Fin k => (Vector.map (B.eval env) x)[i]) = fun i => B.eval env x[i] :=
      funext fun i => by simp
    obtain ⟨h_nz, h_sym, h_good⟩ := h_prover
    rw [hx] at h_nz h_sym h_good ⊢
    obtain ⟨h_holds, h_val⟩ := evalCircuit_complete arith _ α e s env h h_good
    obtain ⟨h_zero, h_not_bad⟩ := RExpr.evalAt_eq_zero _ e h_nz h_sym h_good
    exact ⟨h_holds, h_val.trans h_zero, h_not_bad⟩

/-- Evaluating an expression uses no challenge, if the arithmetic does not. -/
theorem errorBound_evalCircuit
    (h0 : ∀ n input s, errorBound.ofOps (((arith n).main input).operations s) = 0)
    {k : ℕ} (x : Fin k → B.Var) (α : B.Var) (e : RExpr B.Native k) (s : B.State) :
    errorBound.ofOps ((evalCircuit arith x α e).operations s) = 0 := by
  induction e generalizing s with
  | leaf | X => rfl
  | const c =>
    simp only [circuit_norm, Backend.Measure.ofOps, measure_call errorBound, h0, add_zero]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb =>
    simp only [circuit_norm, Backend.Measure.ofOps, measure_call errorBound, h0, iha, ihb, add_zero]

/-- **The error of an identity check** is the bound of its expression, if the arithmetic it uses
has no rare events of its own. -/
theorem errorBound_impl
    (h0 : ∀ n input s, errorBound.ofOps (((arith n).main input).operations s) = 0)
    {k : ℕ} (e : RExpr B.Native k) (input : (interface e).Input B.Var) (s : B.State) :
    errorBound.ofOps (((impl arith e).main input).operations s) = e.bound := by
  obtain ⟨x, α⟩ := input
  simp only [impl, circuit_norm, Backend.Measure.ofOps, measure_call errorBound, h0, errorBound_evalCircuit arith h0,
    errorBound_rare, event, zero_add, add_zero]

omit [Field B.Native] in
/-- What a concatenation of committed values reads. For the spatial obligation of a call. -/
theorem footprintT_append_subset {n m : ℕ} {a : Vector B.Var n} {b : Vector B.Var m} {S : Set B.Cell}
    (ha : B.footprintT (M := natives n) a ⊆ S) (hb : B.footprintT (M := natives m) b ⊆ S) :
    B.footprintT (M := natives (n + m)) (a ++ b) ⊆ S := by
  rw [Backend.footprintT_natives] at ha hb ⊢
  refine Set.iUnion_subset fun i => ?_
  rw [Fin.getElem_fin, Vector.getElem_append]
  split
  · exact (Set.subset_iUnion (fun j : Fin n => B.footprint a[j]) ⟨i, by omega⟩).trans ha
  · exact (Set.subset_iUnion (fun j : Fin m => B.footprint b[j]) ⟨i - n, by omega⟩).trans hb

end Identity
end Clean2
