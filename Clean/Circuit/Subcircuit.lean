import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F : Type} [Field F]

namespace FlatOperation
open Circuit (ConstraintsHold.Completeness ConstraintsHold)

lemma constraintsHold_cons : ∀ {op : FlatOperation F}, ∀ {ops : List (FlatOperation F)}, ∀ {env : Environment F},
    ConstraintsHoldFlat env (op :: ops) ↔ ConstraintsHoldFlat env [op] ∧ ConstraintsHoldFlat env ops := by
  intro op ops env
  constructor <;> (
    rintro h
    dsimp only [ConstraintsHoldFlat] at h
    split at h
    <;> simp_all only [ConstraintsHoldFlat, and_self])

lemma constraintsHold_append : ∀ {a b: List (FlatOperation F)}, ∀ {env : Environment F},
    ConstraintsHoldFlat env (a ++ b) ↔ ConstraintsHoldFlat env a ∧ ConstraintsHoldFlat env b := by
  intro a b env
  induction a with
  | nil => rw [List.nil_append]; tauto
  | cons op ops ih =>
    constructor
    · intro h
      rw [List.cons_append] at h
      obtain ⟨ h_op, h_rest ⟩ := constraintsHold_cons.mp h
      obtain ⟨ h_ops, h_b ⟩ := ih.mp h_rest
      exact ⟨ constraintsHold_cons.mpr ⟨ h_op, h_ops ⟩, h_b ⟩
    · rintro ⟨ h_a, h_b ⟩
      obtain ⟨ h_op, h_ops ⟩ := constraintsHold_cons.mp h_a
      have h_rest := ih.mpr ⟨ h_ops, h_b ⟩
      exact constraintsHold_cons.mpr ⟨ h_op, h_rest ⟩
end FlatOperation

@[circuit_norm]
lemma Operations.toNested_toFlat (ops : Operations F) {name : String} :
    (NestedOperations.nested ⟨ name, ops.toNested ⟩).toFlat = ops.toFlat := by
  induction ops using Operations.induct
  <;> simp_all [toNested, toFlat, NestedOperations.toFlat]

variable {α β: TypeMap} [ProvableType α] [ProvableType β]

section
open Circuit
open FlatOperation (constraintsHold_cons constraintsHold_append)

/--
Consistency theorem which proves that flattened constraints are equivalent to the
constraints created from the inductive `Operations` type, using flat constraints for subcircuits.
-/
theorem Circuit.constraintsHold_toFlat_iff : ∀ {ops : Operations F}, ∀ {env : Environment F},
    ConstraintsHoldFlat env ops.toFlat ↔ ConstraintsHold env ops := by
  intro ops env
  induction ops using Operations.induct with
  | empty => trivial
  -- we can handle all non-empty cases at once
  | witness | assert | lookup | subcircuit =>
    dsimp only [Operations.toFlat]
    try rw [constraintsHold_cons]
    try rw [constraintsHold_append]
    simp_all only [ConstraintsHold, ConstraintsHoldFlat, and_true, true_and]

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def FormalCircuit.toSubcircuit (circuit : FormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have soundness : ∀ env : Environment F,
    let input := eval env input_var
    let output := eval env (circuit.output input_var n)
    ConstraintsHoldFlat env nestedOps.toFlat → circuit.Assumptions input → circuit.Spec input output := by
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env input output h_holds (as : circuit.Assumptions input)
    rw [ops.toNested_toFlat] at h_holds
    show circuit.Spec input output

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: ConstraintsHold.Soundness env ops by
      exact circuit.soundness n env input_var input rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env ops.toFlat
    apply can_replace_soundness
    exact constraintsHold_toFlat_iff.mp h_holds

  have completeness : ∀ env : ProverEnvironment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.Assumptions (eval env input_var) → ConstraintsHoldFlat env nestedOps.toFlat := by
    -- we are given that the assumptions are true
    intro env h_env
    let input := eval env input_var
    intro (as : circuit.Assumptions input)
    rw [ops.toNested_toFlat] at h_env ⊢

    have h_env : env.UsesLocalWitnesses n ops := by
      guard_hyp h_env : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n
      rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
      exact h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env input_var h_env_completeness input rfl as

    -- so we just need to go from constraints to flattened constraints
    apply constraintsHold_toFlat_iff.mpr
    exact can_replace_completeness h_consistent h_env h_holds

  {
    ops := nestedOps,
    Spec env := circuit.Assumptions (eval env input_var) →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    ProverAssumptions env := circuit.Assumptions (eval env input_var),
    ProverSpec env := circuit.Assumptions (eval env input_var) →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    localLength := circuit.localLength input_var

    soundness
    completeness := by
      intro env h_env
      use completeness env h_env
      intro as
      -- by completeness, the constraints hold
      have h_holds := completeness env h_env as
      -- by soundness, this implies the spec
      simp only [circuit_norm] at as ⊢
      exact soundness env h_holds as

    localLength_eq := by
      rw [ops.toNested_toFlat, ←circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]
  }

/--
Theorem and implementation that allows us to take a formal assertion and use it as a subcircuit.
-/
def FormalAssertion.toSubcircuit (circuit : FormalAssertion F β)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  {
    ops := nestedOps,
    Spec env := circuit.Assumptions (eval env input_var) → circuit.Spec (eval env input_var),
    ProverAssumptions env := circuit.Assumptions (eval env input_var) ∧ circuit.Spec (eval env input_var),
    ProverSpec _ := True,
    localLength := circuit.localLength input_var

    soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env h_holds
      let input : β F := eval env input_var
      rintro (as : circuit.Assumptions input)
      show circuit.Spec input
      rw [ops.toNested_toFlat] at h_holds

      -- by soundness of the circuit, the spec is satisfied if only the constraints hold
      suffices h: ConstraintsHold.Soundness env ops by
        exact circuit.soundness n env input_var input rfl as h

      -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env ops.toFlat
      apply can_replace_soundness
      exact constraintsHold_toFlat_iff.mp h_holds

    completeness := by
      -- we are given that the assumptions and the spec are true
      intro env h_env
      simp only [and_true]
      intro assumptions

      let input := eval env input_var
      have as : circuit.Assumptions input ∧ circuit.Spec input := assumptions
      rw [ops.toNested_toFlat] at h_env ⊢

      have h_env : env.UsesLocalWitnesses n ops := by
        guard_hyp h_env : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n
        rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
        exact h_env
      have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds := circuit.completeness n env input_var h_env_completeness input rfl as.left as.right

      -- so we just need to go from constraints to flattened constraints
      apply constraintsHold_toFlat_iff.mpr
      exact can_replace_completeness h_consistent h_env h_holds

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]
  }

/--
Theorem and implementation that allows us to take a general formal circuit and use it as a subcircuit.
-/
def GeneralFormalCircuit.WithHint.toSubcircuit [CircuitType α] [CircuitType β]
    (circuit : GeneralFormalCircuit.WithHint F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have soundness : ∀ env : Environment F,
      let input := eval env input_var
      let output := eval env (circuit.output input_var n)
      ConstraintsHoldFlat env nestedOps.toFlat →
      circuit.Assumptions input env.data →
      circuit.Spec input output env.data := by
    intro env input output constraints assumptions
    rw [ops.toNested_toFlat] at constraints
    apply circuit.soundness n env input_var input rfl assumptions
    apply can_replace_soundness
    exact constraintsHold_toFlat_iff.mp constraints

  have implied_by_assumptions : ∀ env : ProverEnvironment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.ProverAssumptions (eval env input_var) env.data env.hint →
      ConstraintsHoldFlat env nestedOps.toFlat := by
    intro env h_env assumptions
    set input := eval env input_var
    rw [ops.toNested_toFlat] at h_env ⊢
    rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env
    rw [constraintsHold_toFlat_iff]
    apply can_replace_completeness h_consistent h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    apply (circuit.completeness n env input_var h_env_completeness input rfl assumptions).1

  {
    ops := nestedOps,

    Spec env := circuit.Assumptions (eval env input_var) env.data →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data,

    ProverAssumptions env := circuit.ProverAssumptions (eval env input_var) env.data env.hint,

    ProverSpec env :=
      circuit.ProverAssumptions (eval env input_var) env.data env.hint →
      (circuit.Assumptions (eval env.toEnvironment input_var) env.data →
        circuit.Spec (eval env.toEnvironment input_var)
          (eval env.toEnvironment (circuit.output input_var n)) env.data)
      ∧ circuit.ProverSpec (eval env input_var) (eval env (circuit.output input_var n)) env.hint,

    localLength := circuit.localLength input_var

    soundness
    completeness := by
      intro env h_env
      use implied_by_assumptions env h_env
      intro assumptions
      constructor
      · exact implied_by_assumptions env h_env assumptions |> soundness env
      · have h_env' := h_env
        rw [ops.toNested_toFlat] at h_env'
        rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env'
        have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env'
        exact (circuit.completeness n env input_var h_env_completeness _ rfl assumptions).2

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]
  }

/--
Theorem and implementation that allows us to take a pure general formal circuit
and use it as a subcircuit. The implementation delegates to the hint-aware
variant through the default `ProvableType.toCircuitType` instance.
-/
def GeneralFormalCircuit.toSubcircuit (circuit : GeneralFormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  circuit.toWithHint.toSubcircuit n input_var
end

/-- Include a subcircuit. -/
@[circuit_norm]
def subcircuit (circuit : FormalCircuit F β α) (b : Var β F) : Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

/-- Include an assertion subcircuit. -/
@[circuit_norm]
def assertion (circuit : FormalAssertion F β) (b : Var β F) : Circuit F Unit :=
  fun offset =>
    let subcircuit := circuit.toSubcircuit offset b
    ((), [.subcircuit subcircuit])

/-- Include a general subcircuit. -/
@[circuit_norm]
def subcircuitWithAssertion (circuit : GeneralFormalCircuit F β α) (b : Var β F) :
    Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

/-- Include a hint-aware general subcircuit. -/
@[circuit_norm]
def subcircuitWithHintAssertion [CircuitType α] [CircuitType β]
    (circuit : GeneralFormalCircuit.WithHint F β α) (b : Var β F) :
    Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

-- we'd like to use subcircuits like functions

instance : CoeFun (FormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuit circuit input

instance : CoeFun (FormalAssertion F β) (fun _ => Var β F → Circuit F Unit) where
  coe circuit input := assertion circuit input

instance :
    CoeFun (GeneralFormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuitWithAssertion circuit input

instance [CircuitType α] [CircuitType β] :
    CoeFun (GeneralFormalCircuit.WithHint F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuitWithHintAssertion circuit input

namespace Circuit
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

/-- The local length of a subcircuit is derived from the original formal circuit -/
lemma subcircuit_localLength_eq (circuit : FormalCircuit F β α) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma assertion_localLength_eq (circuit : FormalAssertion F β) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma subcircuitWithAssertion_localLength_eq
    (circuit : GeneralFormalCircuit F β α) (input : Var β F) (offset : ℕ) :
    (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

omit [ProvableType α] [ProvableType β] in
lemma subcircuitWithHintAssertion_localLength_eq [CircuitType α] [CircuitType β]
    (circuit : GeneralFormalCircuit.WithHint F β α) (input : Var β F) (offset : ℕ) :
    (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl
end Circuit

-- subcircuit composability for `ComputableWitnesses`

namespace ElaboratedCircuit
/--
For formal circuits, to prove `ComputableWitnesses`, we assume that the input
only contains variables below the current offset `n`.
 -/
def ComputableWitnesses' (circuit : ElaboratedCircuit F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F),
    ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input) →
      (circuit.main input).ComputableWitnesses n

/--
This reformulation of `ComputableWitnesses'` is easier to prove in a formal circuit,
because we have all necessary assumptions at each circuit operation step.
 -/
def ComputableWitnesses (circuit : ElaboratedCircuit F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F) (env env' : ProverEnvironment F),
  circuit.main input |>.operations n |>.forAllFlat n {
    witness n _ compute :=
      env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env' }

/--
`ComputableWitnesses` is stronger than `ComputableWitnesses'` (so it's fine to only prove the former).
-/
lemma computableWitnesses_implies {circuit : ElaboratedCircuit F β α} :
    circuit.ComputableWitnesses → circuit.ComputableWitnesses' := by
  simp only [ComputableWitnesses, ComputableWitnesses']
  intro h_computable n input input_only_accesses_n env env'
  specialize h_computable n input env env'
  specialize input_only_accesses_n env env'
  simp only [Operations.ComputableWitnesses, ←Operations.forAll_toFlat_iff] at *
  generalize ((circuit.main input).operations n).toFlat = ops at *
  revert h_computable
  apply FlatOperation.forAll_implies
  simp only [Condition.implies, Condition.ignoreSubcircuit, imp_self]
  induction ops using FlatOperation.induct generalizing n with
  | empty => trivial
  | assert | lookup => simp_all [FlatOperation.forAll]
  | witness m c ops ih =>
    simp_all only [FlatOperation.forAll, forall_const, implies_true, true_and]
    apply ih (m + n)
    intro h_agrees
    apply input_only_accesses_n
    exact ProverEnvironment.agreesBelow_of_le h_agrees (by linarith)

/--
Composability for `ComputableWitnesses`: If
- in the parent circuit, we prove that input variables are < `n`,
- and the child circuit provides `ElaboratedCircuit.ComputableWitnesses`,
then we can conclude that the subcircuit, evaluated at this particular input,
satisfies `ComputableWitnesses` in the original sense.
-/
theorem compose_computableWitnesses (circuit : ElaboratedCircuit F β α) (input : Var β F) (n : ℕ) :
  ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input) ∧ circuit.ComputableWitnesses →
    (circuit.main input).ComputableWitnesses n := by
  intro ⟨ h_input, h_computable ⟩
  apply ElaboratedCircuit.computableWitnesses_implies h_computable
  exact h_input
end ElaboratedCircuit

theorem Circuit.subcircuit_computableWitnesses (circuit : FormalCircuit F β α)
    (input : Var β F) (n : ℕ) :
  ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input) ∧ circuit.ComputableWitnesses →
    (subcircuit circuit input).ComputableWitnesses n := by
  intro h env env'
  simp only [circuit_norm, FormalCircuit.toSubcircuit, Operations.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact circuit.compose_computableWitnesses input n h env env'

-- to reduce offsets, `circuit_norm` will use these theorems to unfold subcircuits
attribute [circuit_norm] Circuit.subcircuit_localLength_eq Circuit.assertion_localLength_eq
  Circuit.subcircuitWithAssertion_localLength_eq Circuit.subcircuitWithHintAssertion_localLength_eq

-- Simplification lemmas for toSubcircuit.UsesLocalWitnesses

/--
Simplifies UsesLocalWitnesses for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverSpec env =
    (circuit.Assumptions (eval env input_var) → circuit.Spec (eval env input_var) (eval env (circuit.output input_var n))) := by
  rfl

/--
Simplifies UsesLocalWitnesses for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverSpec env =
    (circuit.ProverAssumptions (eval env input_var) env.data env.hint →
      (circuit.Assumptions (eval env.toEnvironment input_var) env.data →
        circuit.Spec (eval env.toEnvironment input_var)
          (eval env.toEnvironment (circuit.output input_var n)) env.data)
      ∧ circuit.ProverSpec (eval env input_var) (eval env (circuit.output input_var n)) env.hint) := by
  rfl

/--
Simplifies UsesLocalWitnesses for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverSpec env =
    (circuit.ProverAssumptions (eval env input_var) env.data env.hint →
      (circuit.Assumptions (eval env input_var) env.data →
        circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data)
      ∧ circuit.ProverSpec (eval env input_var) (eval env (circuit.output input_var n)) env.hint) := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit_usesLocalWitnesses,
    CircuitType.eval_var_prover_to_verifier]

/--
Simplifies UsesLocalWitnesses for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverSpec env = True := by
  rfl

-- Simplification lemmas for toSubcircuit.localLength

/--
Simplifies localLength for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_localLength
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

/--
Simplifies localLength for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_localLength
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

/--
Simplifies localLength for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_localLength
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

/--
Simplifies localLength for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_localLength
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

-- Simplification lemmas for toSubcircuit.Soundness

/--
Simplifies Soundness for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_soundness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) :
    (circuit.toSubcircuit n input_var).Spec env =
    (circuit.Assumptions (eval env input_var) → circuit.Spec (eval env input_var) (eval env (circuit.output input_var n))) := by
  rfl

/--
Simplifies Soundness for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_soundness
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) (env : Environment F) :
    (circuit.toSubcircuit n input_var).Spec env =
    (circuit.Assumptions (eval env input_var) env.data →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data) := by
  rfl

/--
Simplifies Soundness for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_soundness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) :
    (circuit.toSubcircuit n input_var).Spec env =
    (circuit.Assumptions (eval env input_var) env.data →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data) := by
  rfl

/--
Simplifies Soundness for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_soundness
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input_var : Var Input F) (env : Environment F) :
    (circuit.toSubcircuit n input_var).Spec env =
    (circuit.Assumptions (eval env input_var) → circuit.Spec (eval env input_var)) := by
  rfl

-- Simplification lemmas for toSubcircuit.Completeness

/--
Simplifies Completeness for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverAssumptions env =
    circuit.Assumptions (eval env input_var) := by
  rfl

/--
Simplifies Completeness for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverAssumptions env =
    circuit.ProverAssumptions (eval env input_var) env.data env.hint := by
  rfl

/--
Simplifies Completeness for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverAssumptions env =
    circuit.ProverAssumptions (eval env input_var) env.data env.hint := by
  rfl

/--
Simplifies Completeness for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_completeness
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverAssumptions env =
    (circuit.Assumptions (eval env input_var) ∧ circuit.Spec (eval env input_var)) := by
  rfl
