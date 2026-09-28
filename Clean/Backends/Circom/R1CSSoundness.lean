/-
Soundness of the R1CS export.

`exportConstraints` (R1CS.lean) turns a circuit's operations into R1CS constraints over
*signals*: signal `0` is the constant `1`, circuit variables are placed by `signalOfVar`
(outputs first), and every non-linear product gets a fresh intermediate signal. The
constraints' meaning (`Sat`) lives in `R1CSSemantics.lean`; the circuit's meaning
(`ConstraintsHoldFlat`) lives in `Clean.Circuit.Operations`. This module relates them.

The main results:

* `exportConstraints_sound`: a satisfying assignment `w` of the exported constraints
  yields the environment `envOfWitness vm w`, reading each variable from its signal, under
  which the circuit's constraints hold.
* `FormalCircuit.r1cs_soundness`: for any `FormalCircuit`, a satisfying assignment of the
  exported constraints implies the circuit's `Spec` on the inputs and outputs read from
  the signals.
-/
module

public import Clean.Backends.Circom.R1CS
public import Clean.Backends.Circom.R1CSSemantics
public import Clean.Circuit.Theorems
public import Clean.Circuit.Subcircuit

@[expose] public section

namespace Backends.Circom

open Expression (var const add mul)

variable {F : Type} [FiniteField F]

/-- The circuit environment a signal assignment induces: variable `v` reads the signal
`signalOfVar vm v`. -/
def envOfWitness (vm : VarMap) (w : ℕ → F) : Environment F :=
  { get := fun v => w (signalOfVar vm v), data := fun _ _ => #[] }

omit [FiniteField F] in
@[simp] theorem envOfWitness_get (vm : VarMap) (w : ℕ → F) (v : ℕ) :
    (envOfWitness vm w).get v = w (signalOfVar vm v) := rfl

/-! ## Equations of `flattenExpr` -/

theorem flattenExpr_var (vm : VarMap) (i : Variable F) (st : FlattenState F) :
    flattenExpr vm (var i) st = ([(signalOfVar vm i.index, (1 : F))], st) := rfl

theorem flattenExpr_const (vm : VarMap) (k : F) (st : FlattenState F) :
    flattenExpr vm (const k) st = ([(0, k)], st) := rfl

theorem flattenExpr_add (vm : VarMap) (a b : Expression F) (st : FlattenState F) :
    flattenExpr vm (add a b) st =
      (addLinCombs (flattenExpr vm a st).1 (flattenExpr vm b (flattenExpr vm a st).2).1,
        (flattenExpr vm b (flattenExpr vm a st).2).2) := rfl

theorem flattenExpr_mul (vm : VarMap) (a b : Expression F) (st : FlattenState F) :
    flattenExpr vm (mul a b) st =
      let la := (flattenExpr vm a st).1
      let st1 := (flattenExpr vm a st).2
      let lb := (flattenExpr vm b st1).1
      let st2 := (flattenExpr vm b st1).2
      if isConstant la then (scaleLinComb ((la.head?.getD (0, 0)).2) lb, st2)
      else if isConstant lb then (scaleLinComb ((lb.head?.getD (0, 0)).2) la, st2)
      else ([(st2.nextSignal, (1 : F))],
        { nextSignal := st2.nextSignal + 1,
          constraints := (la, lb, [(st2.nextSignal, (1 : F))]) :: st2.constraints }) := rfl

omit [FiniteField F] in
theorem isConstant_eq_true {lc : List (ℕ × F)} (h : isConstant lc = true) : ∃ c, lc = [(0, c)] := by
  match lc, h with
  | [(0, c)], _ => exact ⟨c, rfl⟩
  | [], h => simp [isConstant] at h
  | [(n + 1, _)], h => simp [isConstant] at h
  | _ :: _ :: _, h => simp [isConstant] at h

/-! ## Flattening only adds constraints -/

theorem flattenExpr_constraints_mono (vm : VarMap) :
    ∀ (e : Expression F) (st : FlattenState F), ∀ c ∈ st.constraints,
      c ∈ (flattenExpr vm e st).2.constraints
  | var _, _, _, hc => hc
  | Expression.const _, _, _, hc => hc
  | add a b, st, c, hc => by
    rw [flattenExpr_add]
    exact flattenExpr_constraints_mono vm b _ c (flattenExpr_constraints_mono vm a st c hc)
  | mul a b, st, c, hc => by
    rw [flattenExpr_mul]
    have h1 := flattenExpr_constraints_mono vm b _ c (flattenExpr_constraints_mono vm a st c hc)
    dsimp only
    split_ifs
    · exact h1
    · exact h1
    · exact List.mem_cons_of_mem _ h1

/-! ## Flattening preserves evaluation -/

/-- If the constraints produced while flattening `e` hold under `w`, the resulting linear
combination evaluates to `e` under the induced environment. -/
theorem flattenExpr_eval (vm : VarMap) {w : ℕ → F} (h0 : w 0 = 1) :
    ∀ (e : Expression F) (st : FlattenState F),
      (∀ c ∈ (flattenExpr vm e st).2.constraints, Constraint.Holds w c) →
      evalLC w (flattenExpr vm e st).1 = Expression.eval (envOfWitness vm w) e
  | var i, st, _ => by
    rw [flattenExpr_var]
    simp [Expression.eval]
  | Expression.const k, st, _ => by
    rw [flattenExpr_const]
    simp [Expression.eval, h0]
  | add a b, st, hh => by
    rw [flattenExpr_add] at hh ⊢
    dsimp only at hh ⊢
    have ha := flattenExpr_eval vm h0 a st
      (fun c hc => hh c (flattenExpr_constraints_mono vm b _ c hc))
    have hb := flattenExpr_eval vm h0 b (flattenExpr vm a st).2 hh
    rw [evalLC_addLinCombs, ha, hb]
    rfl
  | mul a b, st, hh => by
    rw [flattenExpr_mul] at hh ⊢
    dsimp only at hh ⊢
    have hmono := flattenExpr_constraints_mono vm b (flattenExpr vm a st).2
    split_ifs at hh ⊢ with hca hcb
    · have ha := flattenExpr_eval vm h0 a st (fun c hc => hh c (hmono c hc))
      have hb := flattenExpr_eval vm h0 b (flattenExpr vm a st).2 hh
      obtain ⟨k, hk⟩ := isConstant_eq_true hca
      rw [evalLC_scaleLinComb, hb, hk]
      rw [hk] at ha
      simp only [evalLC_cons, evalLC_nil, h0, mul_one, add_zero] at ha
      simp [Expression.eval, ← ha]
    · have ha := flattenExpr_eval vm h0 a st (fun c hc => hh c (hmono c hc))
      have hb := flattenExpr_eval vm h0 b (flattenExpr vm a st).2 hh
      obtain ⟨k, hk⟩ := isConstant_eq_true hcb
      rw [evalLC_scaleLinComb, ha, hk]
      rw [hk] at hb
      simp only [evalLC_cons, evalLC_nil, h0, mul_one, add_zero] at hb
      simp [Expression.eval, ← hb, mul_comm]
    · have hrow := hh _ (List.mem_cons_self ..)
      have hrest : ∀ c ∈ (flattenExpr vm b (flattenExpr vm a st).2).2.constraints,
          Constraint.Holds w c := fun c hc => hh c (List.mem_cons_of_mem _ hc)
      have ha := flattenExpr_eval vm h0 a st (fun c hc => hrest c (hmono c hc))
      have hb := flattenExpr_eval vm h0 b (flattenExpr vm a st).2 hrest
      simp only [Constraint.Holds, evalLC_cons, evalLC_nil, one_mul, add_zero] at hrow
      simp only [evalLC_cons, evalLC_nil, one_mul, add_zero, Expression.eval]
      rw [← hrow, ha, hb]

/-! ## Lowering the operations -/

theorem processOps_ok_mono (vm : VarMap) :
    ∀ (ops : List (FlatOperation F)) (st st' : FlattenState F), processOps vm ops st = .ok st' →
      ∀ c ∈ st.constraints, c ∈ st'.constraints
  | [], st, st', h, c, hc => by
    simp only [processOps, Except.ok.injEq] at h
    rw [← h]
    exact hc
  | .witness _ _ :: rest, st, st', h, c, hc => processOps_ok_mono vm rest st st' h c hc
  | .assert e :: rest, st, st', h, c, hc =>
    processOps_ok_mono vm rest _ st' h c
      (List.mem_cons_of_mem _ (flattenExpr_constraints_mono vm e st c hc))
  | .lookup _ :: _, _, _, h, _, _ => by simp [processOps] at h
  | .interact _ :: _, _, _, h, _, _ => by simp [processOps] at h

/-- If the lowered constraints hold under `w`, every assert evaluates to `0` under the
induced environment; and the operations contain no lookups or interactions. -/
theorem processOps_sound (vm : VarMap) {w : ℕ → F} (h0 : w 0 = 1) :
    ∀ (ops : List (FlatOperation F)) (st st' : FlattenState F), processOps vm ops st = .ok st' →
      (∀ c ∈ st'.constraints, Constraint.Holds w c) →
      (∀ e ∈ FlatOperation.constraints ops, Expression.eval (envOfWitness vm w) e = 0) ∧
      FlatOperation.lookups ops = [] ∧ FlatOperation.interactions ops = []
  | [], _, _, _, _ => ⟨fun e he => by simp [FlatOperation.constraints] at he, rfl, rfl⟩
  | .witness _ _ :: rest, st, st', h, hh => by
    have ih := processOps_sound vm h0 rest st st' h hh
    simp only [FlatOperation.constraints, FlatOperation.lookups, FlatOperation.interactions]
    exact ih
  | .assert e :: rest, st, st', h, hh => by
    have ih := processOps_sound vm h0 rest _ st' h hh
    refine ⟨fun e' he' => ?_, ?_, ?_⟩
    · simp only [FlatOperation.constraints, List.mem_cons] at he'
      rcases he' with rfl | he'
      · have hrow : Constraint.Holds w ((flattenExpr vm e' st).1, [(0, (1 : F))], []) :=
          hh _ (processOps_ok_mono vm rest _ st' h _ (List.mem_cons_self ..))
        have hsub : ∀ c ∈ (flattenExpr vm e' st).2.constraints, Constraint.Holds w c :=
          fun c hc => hh c (processOps_ok_mono vm rest _ st' h c (List.mem_cons_of_mem _ hc))
        rw [← flattenExpr_eval vm h0 e' st hsub]
        simp only [Constraint.Holds, evalLC_cons, evalLC_nil, h0, mul_one, add_zero] at hrow
        exact hrow
      · exact ih.1 e' he'
    · simp only [FlatOperation.lookups]
      exact ih.2.1
    · simp only [FlatOperation.interactions]
      exact ih.2.2
  | .lookup _ :: _, _, _, h, _ => by simp [processOps] at h
  | .interact _ :: _, _, _, h, _ => by simp [processOps] at h

/-! ## The export -/

theorem exportConstraints_ok {fieldPrime numInputs numWords : ℕ} {inputNames : List String}
    {outputVarIdx : List ℕ} {ops : List (Operation F)} {cs : List (Constraint F)} {n : ℕ} {vm : VarMap}
    (h : exportConstraints fieldPrime numInputs inputNames outputVarIdx ops numWords = .ok (cs, n, vm)) :
    ∃ numVars st, processOps vm (Operations.toFlat ops) { nextSignal := 1 + numVars } = .ok st ∧
      cs = st.constraints.reverse := by
  unfold exportConstraints at h
  cases hv : validateExport fieldPrime numInputs inputNames outputVarIdx ops numWords with
  | error e => simp [hv] at h
  | ok p =>
    obtain ⟨vm', numVars⟩ := p
    simp only [hv] at h
    cases hp : processOps vm' (Operations.toFlat ops) { nextSignal := 1 + numVars } with
    | error e => simp [hp] at h
    | ok st =>
      simp only [hp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨numVars, st, hp, rfl⟩

/-- **Soundness of the export.** A satisfying assignment of the exported constraints makes
the circuit's constraints hold under the induced environment. -/
theorem exportConstraints_sound {fieldPrime numInputs numWords : ℕ} {inputNames : List String}
    {outputVarIdx : List ℕ} {ops : List (Operation F)} {cs : List (Constraint F)} {n : ℕ} {vm : VarMap}
    (h : exportConstraints fieldPrime numInputs inputNames outputVarIdx ops numWords = .ok (cs, n, vm))
    {w : ℕ → F} (hw : Sat w cs) :
    ConstraintsHoldFlat (envOfWitness vm w) (Operations.toFlat ops) ∧
      FlatOperation.interactions (Operations.toFlat ops) = [] := by
  obtain ⟨numVars, st, hp, rfl⟩ := exportConstraints_ok h
  obtain ⟨hc, hl, hi⟩ := processOps_sound vm hw.1 _ _ st hp
    (fun c hc => hw.2 c (List.mem_reverse.mpr hc))
  refine ⟨?_, hi⟩
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  exact ⟨hc, by rw [hl]; simp⟩

/-! ## Formal circuits -/

section
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- **R1CS soundness of a formal circuit.** A satisfying assignment `w` of the constraints
exported from `circuit.main input_var` yields the circuit's `Spec` on the input and output
read from the signals. -/
theorem _root_.FormalCircuit.r1cs_soundness (circuit : FormalCircuit F Input Output)
    (input_var : Var Input F) (offset : ℕ)
    {fieldPrime numInputs numWords : ℕ} {inputNames : List String} {outputVarIdx : List ℕ}
    {cs : List (Constraint F)} {n : ℕ} {vm : VarMap}
    (h : exportConstraints fieldPrime numInputs inputNames outputVarIdx
      ((circuit.main input_var).operations offset) numWords = .ok (cs, n, vm))
    {w : ℕ → F} (hw : Sat w cs)
    (hA : circuit.Assumptions (eval (envOfWitness vm w) input_var)) :
    circuit.Spec (eval (envOfWitness vm w) input_var)
      (eval (envOfWitness vm w) (circuit.output input_var offset)) := by
  obtain ⟨hflat, hint⟩ := exportConstraints_sound h hw
  have hhold := Circuit.constraintsHold_toFlat_iff.mp hflat
  have hg : ((circuit.main input_var).operations offset).FullGuarantees (envOfWitness vm w) := by
    rw [← FlatOperation.guarantees_toFlat, FlatOperation.guarantees_iff_forall_mem, hint]
    simp
  exact (circuit.soundness offset (envOfWitness vm w) input_var _ rfl hA
    (Circuit.can_replace_soundness hhold hg)).1

end

end Backends.Circom
