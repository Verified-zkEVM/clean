/-
Certified simplification of formal circuits.

`FormalCircuit.simplify` turns a formal circuit into another formal circuit with the same
`Assumptions` and `Spec` and fewer constraints: the operations are flattened and the
asserts are simplified by the certified pass of `Clean.Circuit.Simplify`. The soundness
and completeness proofs of the result are derived from those of the original.

## Scope

The pass only rewrites asserts, and the packaging currently applies it when the
flattened operations contain no lookups and no interactions. Otherwise the circuit's
operations are left unchanged, so `FormalCircuit.simplify` is total and needs no hypotheses.

Lookups inside subcircuits are the obstacle: a flat circuit's soundness obligation only
grants `Lookup.Soundness` for its lookups, while a subcircuit's own soundness theorem
needs `Lookup.Contains`. Lifting this restriction is future work.

## What is preserved

Witness operations are untouched, so the witness generators, the variable numbering and
the local length are unchanged; only asserts are removed or rewritten. The forbidden
variables, never eliminated, are those occurring in the circuit's input and output, which
is exactly what the `Spec` talks about.
-/
module

public import Clean.Circuit.Simplify
public import Clean.Circuit.Formal
public import Clean.Circuit.Theorems
public import Clean.Circuit.Subcircuit

@[expose] public section

variable {F : Type} [FiniteField F]

namespace Circuit.Simplify

/-! ## Flat operations as subcircuit-free operations -/

def ofFlat : List (FlatOperation F) → Operations F
  | [] => []
  | .witness m c :: ops => .witness m c :: ofFlat ops
  | .assert e :: ops => .assert e :: ofFlat ops
  | .lookup l :: ops => .lookup l :: ofFlat ops
  | .interact i :: ops => .interact i :: ofFlat ops

theorem toFlat_ofFlat : ∀ l : List (FlatOperation F), (ofFlat l).toFlat = l
  | [] => rfl
  | .witness _ _ :: ops => by simp [ofFlat, Operations.toFlat, toFlat_ofFlat ops]
  | .assert _ :: ops => by simp [ofFlat, Operations.toFlat, toFlat_ofFlat ops]
  | .lookup _ :: ops => by simp [ofFlat, Operations.toFlat, toFlat_ofFlat ops]
  | .interact _ :: ops => by simp [ofFlat, Operations.toFlat, toFlat_ofFlat ops]

theorem localLength_ofFlat : ∀ l : List (FlatOperation F),
    Operations.localLength (ofFlat l) = FlatOperation.localLength l
  | [] => rfl
  | .witness _ _ :: ops => by
    simp [ofFlat, Operations.localLength, FlatOperation.localLength, localLength_ofFlat ops]
  | .assert _ :: ops => by
    simp [ofFlat, Operations.localLength, FlatOperation.localLength, localLength_ofFlat ops]
  | .lookup _ :: ops => by
    simp [ofFlat, Operations.localLength, FlatOperation.localLength, localLength_ofFlat ops]
  | .interact _ :: ops => by
    simp [ofFlat, Operations.localLength, FlatOperation.localLength, localLength_ofFlat ops]

theorem interactions_ofFlat : ∀ l : List (FlatOperation F),
    Operations.interactions (ofFlat l) = FlatOperation.interactions l
  | [] => rfl
  | .witness _ _ :: ops => by
    simp [ofFlat, Operations.interactions, FlatOperation.interactions, interactions_ofFlat ops]
  | .assert _ :: ops => by
    simp [ofFlat, Operations.interactions, FlatOperation.interactions, interactions_ofFlat ops]
  | .lookup _ :: ops => by
    simp [ofFlat, Operations.interactions, FlatOperation.interactions, interactions_ofFlat ops]
  | .interact _ :: ops => by
    simp [ofFlat, Operations.interactions, FlatOperation.interactions, interactions_ofFlat ops]

theorem subcircuits_ofFlat : ∀ l : List (FlatOperation F), Operations.subcircuits (ofFlat l) = []
  | [] => rfl
  | .witness _ _ :: ops => by simp [ofFlat, Operations.subcircuits, subcircuits_ofFlat ops]
  | .assert _ :: ops => by simp [ofFlat, Operations.subcircuits, subcircuits_ofFlat ops]
  | .lookup _ :: ops => by simp [ofFlat, Operations.subcircuits, subcircuits_ofFlat ops]
  | .interact _ :: ops => by simp [ofFlat, Operations.subcircuits, subcircuits_ofFlat ops]

theorem subcircuitChannelsWithGuarantees_ofFlat (l : List (FlatOperation F)) :
    Operations.subcircuitChannelsWithGuarantees (ofFlat l) = [] := by
  induction l with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [ofFlat, Operations.subcircuitChannelsWithGuarantees] at ih ⊢ <;> exact ih

theorem subcircuitChannelsWithRequirements_ofFlat (l : List (FlatOperation F)) :
    Operations.subcircuitChannelsWithRequirements (ofFlat l) = [] := by
  induction l with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [ofFlat, Operations.subcircuitChannelsWithRequirements] at ih ⊢ <;> exact ih

theorem shallowChannels_ofFlat (l : List (FlatOperation F))
    (h : FlatOperation.interactions l = []) : Operations.shallowChannels (ofFlat l) = [] := by
  induction l with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | interact i => simp [FlatOperation.interactions] at h
    | witness m c =>
      simp only [FlatOperation.interactions] at h
      simp [ofFlat, Operations.shallowChannels] at ih ⊢
      exact ih h
    | assert e =>
      simp only [FlatOperation.interactions] at h
      simp [ofFlat, Operations.shallowChannels] at ih ⊢
      exact ih h
    | lookup l =>
      simp only [FlatOperation.interactions] at h
      simp [ofFlat, Operations.shallowChannels] at ih ⊢
      exact ih h

theorem shallowConstraints_ofFlat (l : List (FlatOperation F)) :
    Operations.shallowConstraints (ofFlat l) = FlatOperation.constraints l := by
  induction l with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [ofFlat, Operations.shallowConstraints, FlatOperation.constraints] at ih ⊢ <;> exact ih

theorem shallowLookups_ofFlat (l : List (FlatOperation F)) :
    Operations.shallowLookups (ofFlat l) = FlatOperation.lookups l := by
  induction l with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [ofFlat, Operations.shallowLookups, FlatOperation.lookups] at ih ⊢ <;> exact ih

theorem shallowInteractions_ofFlat (l : List (FlatOperation F)) :
    Operations.shallowInteractions (ofFlat l) = FlatOperation.interactions l := by
  induction l with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [ofFlat, Operations.shallowInteractions, FlatOperation.interactions] at ih ⊢ <;> exact ih

theorem shallowWitnessOperations_ofFlat (l : List (FlatOperation F)) :
    Operations.shallowWitnessOperations (ofFlat l) = FlatOperation.witnessOperations l := by
  induction l with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [ofFlat, Operations.shallowWitnessOperations, FlatOperation.witnessOperations] at ih ⊢ <;> exact ih

/-- `forAllNoOffset` on subcircuit-free operations is `forAllNoOffset` on the flat ones. -/
theorem forAllNoOffset_ofFlat (cond : ConditionNoOffset F) (l : List (FlatOperation F)) :
    Operations.forAllNoOffset cond (ofFlat l) ↔
      FlatOperation.forAllNoOffset
        { witness := cond.witness, assert := cond.assert, lookup := cond.lookup,
          interact := cond.interact } l := by
  rw [Operations.forAllNoOffset_iff_forall_mem, FlatOperation.forAllNoOffset_iff_forall_mem,
    shallowConstraints_ofFlat, shallowLookups_ofFlat, shallowInteractions_ofFlat,
    shallowWitnessOperations_ofFlat, subcircuits_ofFlat]
  simp

/-- With no lookups and no interactions, only the assert condition matters. -/
theorem forAllNoOffset_ofFlat_of_noChannels (cond : ConditionNoOffset F)
    {l : List (FlatOperation F)} (hl : FlatOperation.lookups l = [])
    (hi : FlatOperation.interactions l = []) (hw : ∀ m c, cond.witness m c) :
    Operations.forAllNoOffset cond (ofFlat l) ↔ ∀ e ∈ FlatOperation.constraints l, cond.assert e := by
  rw [forAllNoOffset_ofFlat, FlatOperation.forAllNoOffset_iff_forall_mem, hl, hi]
  simp [hw]

theorem forAll_ofFlat_trivial (cond : Condition F) (hw : ∀ n m c, cond.witness n m c)
    (ha : ∀ n e, cond.assert n e) (hl : ∀ n l, cond.lookup n l) (hi : ∀ n i, cond.interact n i) :
    ∀ (n : ℕ) (l : List (FlatOperation F)), Operations.forAll n cond (ofFlat l)
  | _, [] => trivial
  | _, .witness _ _ :: ops => ⟨hw _ _ _, forAll_ofFlat_trivial cond hw ha hl hi _ ops⟩
  | _, .assert _ :: ops => ⟨ha _ _, forAll_ofFlat_trivial cond hw ha hl hi _ ops⟩
  | _, .lookup _ :: ops => ⟨hl _ _, forAll_ofFlat_trivial cond hw ha hl hi _ ops⟩
  | _, .interact _ :: ops => ⟨hi _ _, forAll_ofFlat_trivial cond hw ha hl hi _ ops⟩

theorem subcircuitsConsistent_ofFlat (n : ℕ) (l : List (FlatOperation F)) :
    Operations.SubcircuitsConsistent n (ofFlat l) :=
  forAll_ofFlat_trivial _ (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) n l

theorem usesLocalWitnessesCompleteness_ofFlat (env : ProverEnvironment F) :
    ∀ (n : ℕ) (l : List (FlatOperation F)),
      env.UsesLocalWitnessesCompleteness n (ofFlat l) ↔ env.UsesLocalWitnessesFlat n l
  | n, [] => by simp [ofFlat, ProverEnvironment.UsesLocalWitnessesCompleteness,
      ProverEnvironment.UsesLocalWitnessesFlat, FlatOperation.forAll]
  | n, .witness m c :: ops => by
    simp only [ofFlat, ProverEnvironment.UsesLocalWitnessesCompleteness,
      ProverEnvironment.UsesLocalWitnessesFlat, FlatOperation.forAll]
    rw [← ProverEnvironment.UsesLocalWitnessesFlat, usesLocalWitnessesCompleteness_ofFlat env, Nat.add_comm]
  | n, .assert _ :: ops => by
    simp only [ofFlat, ProverEnvironment.UsesLocalWitnessesCompleteness,
      ProverEnvironment.UsesLocalWitnessesFlat, FlatOperation.forAll]
    rw [← ProverEnvironment.UsesLocalWitnessesFlat, usesLocalWitnessesCompleteness_ofFlat env]
    simp
  | n, .lookup _ :: ops => by
    simp only [ofFlat, ProverEnvironment.UsesLocalWitnessesCompleteness,
      ProverEnvironment.UsesLocalWitnessesFlat, FlatOperation.forAll]
    rw [← ProverEnvironment.UsesLocalWitnessesFlat, usesLocalWitnessesCompleteness_ofFlat env]
    simp
  | n, .interact _ :: ops => by
    simp only [ofFlat, ProverEnvironment.UsesLocalWitnessesCompleteness,
      ProverEnvironment.UsesLocalWitnessesFlat, FlatOperation.forAll]
    rw [← ProverEnvironment.UsesLocalWitnessesFlat, usesLocalWitnessesCompleteness_ofFlat env]
    simp

/-! ## Facts about the pass that the packaging needs -/

omit [FiniteField F] in
theorem interactions_dropAsserts : ∀ ops : List (FlatOperation F),
    FlatOperation.interactions (dropAsserts ops) = FlatOperation.interactions ops
  | [] => rfl
  | .assert _ :: ops => by simp [dropAsserts, FlatOperation.interactions, interactions_dropAsserts ops]
  | .witness _ _ :: ops => by simp [dropAsserts, FlatOperation.interactions, interactions_dropAsserts ops]
  | .lookup _ :: ops => by simp [dropAsserts, FlatOperation.interactions, interactions_dropAsserts ops]
  | .interact _ :: ops => by simp [dropAsserts, FlatOperation.interactions, interactions_dropAsserts ops]

omit [FiniteField F] in
theorem localLength_dropAsserts : ∀ ops : List (FlatOperation F),
    FlatOperation.localLength (dropAsserts ops) = FlatOperation.localLength ops
  | [] => rfl
  | .assert _ :: ops => by simp [dropAsserts, FlatOperation.localLength, localLength_dropAsserts ops]
  | .witness _ _ :: ops => by simp [dropAsserts, FlatOperation.localLength, localLength_dropAsserts ops]
  | .lookup _ :: ops => by simp [dropAsserts, FlatOperation.localLength, localLength_dropAsserts ops]
  | .interact _ :: ops => by simp [dropAsserts, FlatOperation.localLength, localLength_dropAsserts ops]

theorem forAll_dropAsserts (cond : Condition F) (ha : ∀ n e, cond.assert n e) :
    ∀ (n : ℕ) (ops : List (FlatOperation F)),
      FlatOperation.forAll n cond (dropAsserts ops) ↔ FlatOperation.forAll n cond ops
  | _, [] => Iff.rfl
  | n, .assert e :: ops => by
    simp only [dropAsserts, FlatOperation.forAll, forAll_dropAsserts cond ha n ops, ha n e, true_and]
  | n, .witness _ _ :: ops => by
    simp only [dropAsserts, FlatOperation.forAll, forAll_dropAsserts cond ha _ ops]
  | n, .lookup _ :: ops => by
    simp only [dropAsserts, FlatOperation.forAll, forAll_dropAsserts cond ha _ ops]
  | n, .interact _ :: ops => by
    simp only [dropAsserts, FlatOperation.forAll, forAll_dropAsserts cond ha _ ops]

theorem localLength_simplifyFlat (fb : ℕ → Bool) (m : ℕ) (ops : List (FlatOperation F)) :
    FlatOperation.localLength (simplifyFlat fb m ops).1 = FlatOperation.localLength ops := by
  rw [← localLength_dropAsserts, dropAsserts_simplifyFlat, localLength_dropAsserts]

theorem lookups_simplifyFlat (fb : ℕ → Bool) (m : ℕ) (ops : List (FlatOperation F)) :
    FlatOperation.lookups (simplifyFlat fb m ops).1 = FlatOperation.lookups ops := by
  rw [← lookups_dropAsserts, dropAsserts_simplifyFlat, lookups_dropAsserts]

theorem interactions_simplifyFlat (fb : ℕ → Bool) (m : ℕ) (ops : List (FlatOperation F)) :
    FlatOperation.interactions (simplifyFlat fb m ops).1 = FlatOperation.interactions ops := by
  rw [← interactions_dropAsserts, dropAsserts_simplifyFlat, interactions_dropAsserts]

theorem usesLocalWitnessesFlat_simplifyFlat (env : ProverEnvironment F) (fb : ℕ → Bool) (m : ℕ)
    (n : ℕ) (ops : List (FlatOperation F)) :
    env.UsesLocalWitnessesFlat n (simplifyFlat fb m ops).1 ↔ env.UsesLocalWitnessesFlat n ops := by
  simp only [ProverEnvironment.UsesLocalWitnessesFlat]
  rw [← forAll_dropAsserts _ (fun _ _ => trivial) n (simplifyFlat fb m ops).1,
    dropAsserts_simplifyFlat, forAll_dropAsserts _ (fun _ _ => trivial)]

/-! ## Variables of circuit values -/

section
variable {M : TypeMap} [ProvableType M]

/-- Variables occurring in a circuit value made of expressions. -/
def varsOf (x : M (Expression F)) : List ℕ :=
  (toElements x).toList.flatMap Expression.vars

/-- Evaluation of a circuit value only depends on the variables that occur in it. -/
theorem eval_congr_of_vars {env env' : Environment F} {x : M (Expression F)}
    (h : ∀ v ∈ varsOf x, env.get v = env'.get v) :
    (Eval.eval env x : M F) = Eval.eval env' x := by
  rw [← ProvableType.fromElements_eval_toElements, ← ProvableType.fromElements_eval_toElements]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  apply Expression.eval_congr
  intro v hv
  apply h
  simp only [varsOf, List.mem_flatMap]
  exact ⟨(toElements x)[i], by simp, hv⟩

end

section
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- The forbidden variables: those of the input and of the output. -/
def forbiddenOf (input : Var Input F) (out : Var Output F) : ℕ → Bool :=
  fun v => decide (v ∈ varsOf (M := Input) input ++ varsOf (M := Output) out)

omit [FiniteField F] in
theorem forbiddenOf_input {input : Var Input F} {out : Var Output F} {v : ℕ}
    (h : v ∈ varsOf (M := Input) input) : forbiddenOf input out v = true := by
  simp [forbiddenOf, h]

omit [FiniteField F] in
theorem forbiddenOf_output {input : Var Input F} {out : Var Output F} {v : ℕ}
    (h : v ∈ varsOf (M := Output) out) : forbiddenOf input out v = true := by
  simp [forbiddenOf, h]

/-- Whether flat operations are in the simplifier's scope: no lookups and no interactions. -/
def inScope (l : List (FlatOperation F)) : Bool :=
  (FlatOperation.lookups l).isEmpty && (FlatOperation.interactions l).isEmpty

omit [FiniteField F] in
theorem inScope_iff {l : List (FlatOperation F)} :
    inScope l = true ↔ FlatOperation.lookups l = [] ∧ FlatOperation.interactions l = [] := by
  simp [inScope, List.isEmpty_iff]

/-- Simplify one run of a circuit: flatten and simplify the asserts when in scope,
leave the operations unchanged otherwise. -/
def simplifyOps (input : Var Input F) (out : Var Output F) (maxVars : ℕ) (ops : Operations F) :
    Operations F :=
  if inScope ops.toFlat then ofFlat (simplifyFlat (forbiddenOf input out) maxVars ops.toFlat).1
  else ops

theorem localLength_simplifyOps (input : Var Input F) (out : Var Output F) (maxVars : ℕ)
    (ops : Operations F) : Operations.localLength (simplifyOps input out maxVars ops) = ops.localLength := by
  unfold simplifyOps
  by_cases h : inScope ops.toFlat = true
  · rw [if_pos h, localLength_ofFlat, localLength_simplifyFlat, FlatOperation.localLength_toFlat]
  · rw [if_neg h]

/-- The main function of the simplified circuit. -/
def simplifyMain (c : FormalCircuit F Input Output) (maxVars : ℕ) :
    Var Input F → Circuit F (Var Output F) :=
  fun input offset =>
    ((c.main input offset).1, simplifyOps input (c.output input offset) maxVars (c.main input offset).2)

theorem simplifyMain_operations (c : FormalCircuit F Input Output) (maxVars : ℕ)
    (input : Var Input F) (offset : ℕ) :
    (simplifyMain c maxVars input).operations offset =
      simplifyOps input (c.output input offset) maxVars ((c.main input).operations offset) := rfl

theorem simplifyMain_output (c : FormalCircuit F Input Output) (maxVars : ℕ)
    (input : Var Input F) (offset : ℕ) :
    (simplifyMain c maxVars input).output offset = c.output input offset :=
  c.elaborated.output_eq input offset

/-! ## The simplified formal circuit -/

/-- **Certified simplification of a formal circuit.** Same input and output types, same
`Assumptions` and `Spec`; the operations are flattened and their asserts simplified (when
in scope). -/
def _root_.FormalCircuit.simplify (c : FormalCircuit F Input Output) (maxVars : ℕ := 1) :
    FormalCircuit F Input Output where
  name := c.name ++ " (simplified)"
  main := simplifyMain c maxVars
  elaborated := {
    localLength := c.elaborated.localLength
    localLength_eq := fun input offset => by
      show Operations.localLength ((simplifyMain c maxVars input).operations offset) = _
      rw [simplifyMain_operations, localLength_simplifyOps]
      exact c.elaborated.localLength_eq input offset
    output := c.elaborated.output
    output_eq := fun input offset => simplifyMain_output c maxVars input offset
    subcircuitsConsistent := fun input offset => by
      rw [simplifyMain_operations]
      unfold simplifyOps
      by_cases h : inScope ((c.main input).operations offset).toFlat = true
      · rw [if_pos h]
        exact subcircuitsConsistent_ofFlat _ _
      · rw [if_neg h]
        exact c.elaborated.subcircuitsConsistent input offset
    channelsWithGuarantees := c.elaborated.channelsWithGuarantees
    channelsLawful := fun input offset => by
      rw [simplifyMain_operations]
      unfold simplifyOps
      by_cases h : inScope ((c.main input).operations offset).toFlat = true
      · rw [if_pos h]
        obtain ⟨_, hi⟩ := inScope_iff.mp h
        have hi' : FlatOperation.interactions (simplifyFlat (forbiddenOf input (c.output input offset)) maxVars ((c.main input).operations offset).toFlat).1 = [] := by
          rw [interactions_simplifyFlat]; exact hi
        unfold Operations.ChannelsLawful
        refine ⟨by simp [subcircuitChannelsWithGuarantees_ofFlat], fun env => ?_, ?_⟩
        · rw [Operations.InChannelsOrGuarantees, forAllNoOffset_ofFlat,
            FlatOperation.forAllNoOffset_iff_forall_mem, hi']
          simp
        · simp [Operations.SubcircuitChannelsLawful, subcircuits_ofFlat]
      · rw [if_neg h]
        exact c.elaborated.channelsLawful input offset
  }
  exposedChannels := c.exposedChannels
  exposedChannels_eq := fun input offset => by
    rw [simplifyMain_operations]
    unfold simplifyOps
    by_cases h : inScope ((c.main input).operations offset).toFlat = true
    · rw [if_pos h]
      intro exposed hexp
      have horig := c.exposedChannels_eq input offset exposed hexp
      rw [← horig]
      simp only [Operations.interactionsWith, interactions_ofFlat, interactions_simplifyFlat,
        Operations.interactions_toFlat]
    · rw [if_neg h]
      exact c.exposedChannels_eq input offset
  channelsWithRequirements := c.channelsWithRequirements
  requirementsChannelsLawful := fun input offset => by
    rw [simplifyMain_operations]
    unfold simplifyOps
    by_cases h : inScope ((c.main input).operations offset).toFlat = true
    · rw [if_pos h]
      obtain ⟨_, hi⟩ := inScope_iff.mp h
      have hi' : FlatOperation.interactions (simplifyFlat (forbiddenOf input (c.output input offset)) maxVars ((c.main input).operations offset).toFlat).1 = [] := by
        rw [interactions_simplifyFlat]; exact hi
      unfold Operations.RequirementsChannelsLawful
      refine ⟨by simp [subcircuitChannelsWithRequirements_ofFlat], ?_, fun env _ => ?_⟩
      · rw [shallowChannels_ofFlat _ hi']
        simp
      · rw [Operations.InChannelsOrRequirements, forAllNoOffset_ofFlat,
          FlatOperation.forAllNoOffset_iff_forall_mem, hi']
        simp
    · rw [if_neg h]
      exact c.requirementsChannelsLawful input offset
  Assumptions := c.Assumptions
  Spec := c.Spec
  soundness := by
    intro offset env input_var input hinput hA hholds
    rw [simplifyMain_operations] at hholds ⊢
    unfold simplifyOps at hholds ⊢
    by_cases h : inScope ((c.main input_var).operations offset).toFlat = true
    · rw [if_pos h] at hholds ⊢
      obtain ⟨hl, hi⟩ := inScope_iff.mp h
      have hl' : FlatOperation.lookups (simplifyFlat (forbiddenOf input_var (c.output input_var offset)) maxVars ((c.main input_var).operations offset).toFlat).1 = [] := by
        rw [lookups_simplifyFlat]; exact hl
      have hi' : FlatOperation.interactions (simplifyFlat (forbiddenOf input_var (c.output input_var offset)) maxVars ((c.main input_var).operations offset).toFlat).1 = [] := by
        rw [interactions_simplifyFlat]; exact hi
      -- the simplified asserts hold under `env`
      have hasserts := (forAllNoOffset_ofFlat_of_noChannels _ hl' hi' (fun _ _ => trivial)).mp hholds
      have hflat' : ConstraintsHoldFlat env (simplifyFlat (forbiddenOf input_var (c.output input_var offset)) maxVars ((c.main input_var).operations offset).toFlat).1 := by
        rw [FlatOperation.constraintsHoldFlat_iff_forall_mem, hl']
        exact ⟨hasserts, by simp⟩
      -- so the original constraints hold under the extended environment
      obtain ⟨env', hagree, _, hflat⟩ := simplifyFlat_sound (forbiddenOf input_var (c.output input_var offset)) maxVars ((c.main input_var).operations offset).toFlat (by rw [hl]; simp) env hflat'
      have hhold := Circuit.constraintsHold_toFlat_iff.mp hflat
      have hg : ((c.main input_var).operations offset).FullGuarantees env' := by
        intro i hi''
        rw [← Operations.interactions_toFlat, hi] at hi''
        simp at hi''
      have hs := Circuit.can_replace_soundness hhold hg
      have hin : Eval.eval env' input_var = Eval.eval env input_var :=
        eval_congr_of_vars (M := Input) fun v hv => hagree v (forbiddenOf_input (out := c.output input_var offset) hv)
      have hout : Eval.eval env' (c.output input_var offset) = Eval.eval env (c.output input_var offset) :=
        eval_congr_of_vars (M := Output) fun v hv => hagree v (forbiddenOf_output (input := input_var) hv)
      have hspec := c.soundness offset env' input_var input (hin.trans hinput) hA hs
      refine ⟨?_, ?_⟩
      · show c.Spec input (Eval.eval env (c.output input_var offset))
        rw [← hout]
        exact hspec.1
      · rw [Operations.Requirements, forAllNoOffset_ofFlat, FlatOperation.forAllNoOffset_iff_forall_mem, hi']
        simp
    · rw [if_neg h] at hholds ⊢
      exact c.soundness offset env input_var input hinput hA hholds
  completeness := by
    intro offset env input_var henv input hinput hA
    rw [simplifyMain_operations] at henv ⊢
    unfold simplifyOps at henv ⊢
    by_cases h : inScope ((c.main input_var).operations offset).toFlat = true
    · rw [if_pos h] at henv ⊢
      obtain ⟨hl, hi⟩ := inScope_iff.mp h
      have hl' : FlatOperation.lookups (simplifyFlat (forbiddenOf input_var (c.output input_var offset)) maxVars ((c.main input_var).operations offset).toFlat).1 = [] := by
        rw [lookups_simplifyFlat]; exact hl
      have hi' : FlatOperation.interactions (simplifyFlat (forbiddenOf input_var (c.output input_var offset)) maxVars ((c.main input_var).operations offset).toFlat).1 = [] := by
        rw [interactions_simplifyFlat]; exact hi
      have hconsistent := c.subcircuitsConsistent input_var offset
      have hw : env.UsesLocalWitnesses offset ((c.main input_var).operations offset) := by
        rw [ProverEnvironment.usesLocalWitnesses_iff_flat, ← usesLocalWitnessesFlat_simplifyFlat env
          (forbiddenOf input_var (c.output input_var offset)) maxVars]
        exact (usesLocalWitnessesCompleteness_ofFlat env _ _).mp henv
      have hwc := env.can_replace_usesLocalWitnessesCompleteness hconsistent hw
      have hc := c.completeness offset env input_var hwc input hinput hA
      have hhold := Circuit.can_replace_completeness hconsistent hw hc
      have hflat := Circuit.constraintsHold_toFlat_iff.mpr hhold
      have hflat' := simplifyFlat_complete (forbiddenOf input_var (c.output input_var offset)) maxVars
        ((c.main input_var).operations offset).toFlat env.toEnvironment hflat
      rw [ConstraintsHold.Completeness, forAllNoOffset_ofFlat_of_noChannels _ hl' hi' (fun _ _ => trivial)]
      exact (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp hflat').1
    · rw [if_neg h] at henv ⊢
      exact c.completeness offset env input_var henv input hinput hA

end

end Circuit.Simplify
