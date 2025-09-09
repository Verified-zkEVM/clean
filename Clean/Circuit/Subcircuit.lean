import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F : Type} [Field F]

namespace FlatOperation
open Circuit (ConstraintsHold.Completeness ConstraintsHold)

lemma constraintsHold_cons : ∀ {sentences : PropertySet F} {op : FlatOperation sentences}, ∀ {ops : List (FlatOperation sentences)}, ∀ {env : Environment F} {yields : YieldContext sentences} {checked : CheckedYields sentences},
    ConstraintsHoldFlat env yields checked (op :: ops) ↔ ConstraintsHoldFlat env yields checked [op] ∧ ConstraintsHoldFlat env yields checked ops := by
  intro op ops env sentences yields checked
  constructor <;> (
    rintro h
    dsimp only [ConstraintsHoldFlat] at h
    split at h
    <;> simp_all only [ConstraintsHoldFlat, and_self])

lemma constraintsHold_append : ∀ {sentences : PropertySet F} {a b: List (FlatOperation sentences)}, ∀ {env : Environment F} {yields : YieldContext sentences} {checked : CheckedYields sentences},
    ConstraintsHoldFlat env yields checked (a ++ b) ↔ ConstraintsHoldFlat env yields checked a ∧ ConstraintsHoldFlat env yields checked b := by
  intro sentences a b env yields checked
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

variable {α β: TypeMap} [ProvableType α] [ProvableType β]

section
open Circuit
open FlatOperation (constraintsHold_cons constraintsHold_append)

/--
Consistency theorem which proves that flattened constraints are equivalent to the
constraints created from the inductive `Operations` type, using flat constraints for subcircuits.
-/
theorem Circuit.constraintsHold_toFlat_iff : ∀ {sentences : PropertySet F} {ops : Operations sentences}, ∀ {env : Environment F} {yields : YieldContext sentences} {checked : CheckedYields sentences},
    ConstraintsHoldFlat env yields checked ops.toFlat ↔ ConstraintsHold env yields checked ops := by
  intro sentences ops env yields checked
  induction ops using Operations.induct with
  | empty => trivial
  -- we can handle all non-empty cases at once
  | witness | assert | lookup | yield | subcircuit =>
    dsimp only [Operations.toFlat]
    try rw [constraintsHold_cons]
    try rw [constraintsHold_append]
    simp_all only [ConstraintsHold, ConstraintsHoldFlat, and_true, true_and]

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def FormalCircuit.toSubcircuit {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : FormalCircuit order β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit sentences n :=
  let ops := circuit.main input_var |>.operations n
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have imply_soundness : ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
    let input := eval env input_var
    let output := eval env (circuit.output input_var n)
    ConstraintsHoldFlat env yields checked ops.toFlat → circuit.Assumptions input → circuit.Spec checked input output := by
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env yields checked input output h_holds (as : circuit.Assumptions input)
    show circuit.Spec checked input output

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: ConstraintsHold.Soundness env yields checked ops by
      exact circuit.soundness n env yields checked input_var input rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env yields checked ops.toFlat
    apply can_replace_soundness
    exact constraintsHold_toFlat_iff.mp h_holds

  have implied_by_completeness : ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
      env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n ∧ 
      FlatOperation.localYields env ops.toFlat ⊆ yields.yielded →
      circuit.Assumptions (eval env input_var) → ConstraintsHoldFlat env yields checked ops.toFlat := by
    -- we are given that the assumptions are true
    intro env yields checked h_env
    let input := eval env input_var
    intro (as : circuit.Assumptions input)

    have h_env : env.UsesLocalWitnessesAndYields yields n ops := by
      guard_hyp h_env : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n ∧ 
                         FlatOperation.localYields env ops.toFlat ⊆ yields.yielded
      rw [env.usesLocalWitnessesAndYields_iff_flat, env.usesLocalWitnessesAndYieldsFlat_iff_extends]
      exact h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env yields input_var h_env_completeness input rfl as

    -- so we just need to go from constraints to flattened constraints
    apply constraintsHold_toFlat_iff.mpr
    exact can_replace_completeness yields checked h_consistent h_env h_holds

  {
    ops := ops.toFlat,
    Soundness env yields checked := circuit.Assumptions (eval env input_var) →
      circuit.Spec checked (eval env input_var) (eval env (circuit.output input_var n)),
    Completeness env yields := circuit.Assumptions (eval env input_var),
    UsesLocalWitnessesAndYields env yields := circuit.Assumptions (eval env input_var) →
      circuit.Spec Set.univ (eval env input_var) (eval env (circuit.output input_var n)),
    localLength := circuit.localLength input_var

    imply_soundness
    implied_by_completeness
    imply_usesLocalWitnessesAndYields := by
      intro env yields h_env as
      -- by completeness, the constraints hold
      have h_holds := implied_by_completeness env yields Set.univ h_env as
      -- by soundness, this implies the spec
      exact imply_soundness env yields Set.univ h_holds as

    localLength_eq := by
      rw [← circuit.localLength_eq input_var n, FlatOperation.localLength_toFlat]
  }

/--
Theorem and implementation that allows us to take a formal assertion and use it as a subcircuit.
-/
def FormalAssertion.toSubcircuit {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : FormalAssertion order β)
    (n : ℕ) (input_var : Var β F) : Subcircuit sentences n :=
  let ops := circuit.main input_var |>.operations n
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  {
    ops := ops.toFlat,
    Soundness env yields checked := circuit.Assumptions (eval env input_var) → circuit.Spec checked (eval env input_var),
    Completeness env yields := circuit.Assumptions (eval env input_var) ∧ circuit.Spec Set.univ (eval env input_var),
    UsesLocalWitnessesAndYields env yields := True,
    localLength := circuit.localLength input_var

    imply_soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env yields checked h_holds
      let input : β F := eval env input_var
      rintro (as : circuit.Assumptions input)
      show circuit.Spec checked input

      -- by soundness of the circuit, the spec is satisfied if only the constraints hold
      suffices h: ConstraintsHold.Soundness env yields checked ops by
        exact circuit.soundness n env yields checked input_var input rfl as h

      -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env yields checked ops.toFlat
      apply can_replace_soundness yields checked
      exact constraintsHold_toFlat_iff.mp h_holds

    implied_by_completeness := by
      -- we are given that the assumptions and the spec are true
      intro env yields checked h_env h_completeness

      let input := eval env input_var
      have as : circuit.Assumptions input ∧ circuit.Spec Set.univ input := h_completeness

      have h_env : env.UsesLocalWitnessesAndYields yields n ops := by
        guard_hyp h_env : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n ∧ 
                           FlatOperation.localYields env ops.toFlat ⊆ yields.yielded
        rw [env.usesLocalWitnessesAndYields_iff_flat, env.usesLocalWitnessesAndYieldsFlat_iff_extends]
        exact h_env
      have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds := circuit.completeness n env yields input_var h_env_completeness input rfl as.left as.right

      -- so we just need to go from constraints to flattened constraints
      apply constraintsHold_toFlat_iff.mpr
      exact can_replace_completeness yields checked h_consistent h_env h_holds

    imply_usesLocalWitnessesAndYields := by intros; exact trivial

    localLength_eq := by
      rw [← circuit.localLength_eq input_var n, FlatOperation.localLength_toFlat]
  }

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def GeneralFormalCircuit.toSubcircuit {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : GeneralFormalCircuit order β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit sentences n :=
  let ops := circuit.main input_var |>.operations n
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have imply_soundness : ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
      let input := eval env input_var
      let output := eval env (circuit.output input_var n)
      ConstraintsHoldFlat env yields checked ops.toFlat → circuit.Spec checked input output := by
    intro env yields checked input output h_holds
    apply circuit.soundness n env yields checked input_var input rfl
    apply can_replace_soundness yields checked
    exact constraintsHold_toFlat_iff.mp h_holds

  have implied_by_completeness : ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
      env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n ∧ 
      FlatOperation.localYields env ops.toFlat ⊆ yields.yielded →
      circuit.Assumptions (eval env input_var) → ConstraintsHoldFlat env yields checked ops.toFlat := by
    intro env yields checked h_env assumptions
    set input := eval env input_var
    rw [←env.usesLocalWitnessesAndYieldsFlat_iff_extends, ←env.usesLocalWitnessesAndYields_iff_flat] at h_env
    rw [constraintsHold_toFlat_iff]
    apply can_replace_completeness yields checked h_consistent h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    apply circuit.completeness n env yields input_var h_env_completeness input rfl assumptions

  {
    ops := ops.toFlat,
    Soundness env yields checked := circuit.Spec checked (eval env input_var) (eval env (circuit.output input_var n)),
    Completeness env yields := circuit.Assumptions (eval env input_var),
    UsesLocalWitnessesAndYields env yields := circuit.Assumptions (eval env input_var) →
      circuit.Spec Set.univ (eval env input_var) (eval env (circuit.output input_var n)),
    localLength := circuit.localLength input_var

    imply_soundness
    implied_by_completeness
    imply_usesLocalWitnessesAndYields env yields h_env assumptions :=
      -- constraints hold by completeness, which implies the spec by soundness
      implied_by_completeness env yields Set.univ h_env assumptions |> imply_soundness env yields Set.univ

    localLength_eq := by
      rw [← circuit.localLength_eq input_var n, FlatOperation.localLength_toFlat]
  }
end

/-- Include a subcircuit. -/
@[circuit_norm]
def subcircuit {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : FormalCircuit order β α) (b : Var β F) : Circuit sentences (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

/-- Include an assertion subcircuit. -/
@[circuit_norm]
def assertion {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : FormalAssertion order β) (b : Var β F) : Circuit sentences Unit :=
  fun offset =>
    let subcircuit := circuit.toSubcircuit offset b
    ((), [.subcircuit subcircuit])

/-- Include a general subcircuit. -/
@[circuit_norm]
def subcircuitWithAssertion {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : GeneralFormalCircuit order β α) (b : Var β F) : Circuit sentences (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

-- we'd like to use subcircuits like functions

instance {sentences : PropertySet F} {order : SentenceOrder sentences} : CoeFun (FormalCircuit order β α) (fun _ => Var β F → Circuit sentences (Var α F)) where
  coe circuit input := subcircuit circuit input

instance {sentences : PropertySet F} {order : SentenceOrder sentences} : CoeFun (FormalAssertion order β) (fun _ => Var β F → Circuit sentences Unit) where
  coe circuit input := assertion circuit input

instance {sentences : PropertySet F} {order : SentenceOrder sentences} : CoeFun (GeneralFormalCircuit order β α) (fun _ => Var β F → Circuit sentences (Var α F)) where
  coe circuit input := subcircuitWithAssertion circuit input

namespace Circuit
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

/-- The local length of a subcircuit is derived from the original formal circuit -/
lemma subcircuit_localLength_eq {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : FormalCircuit order β α) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma assertion_localLength_eq {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : FormalAssertion order β) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma subcircuitWithAssertion_localLength_eq {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : GeneralFormalCircuit order β α) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl
end Circuit

-- subcircuit composability for `ComputableWitnesses`

namespace ElaboratedCircuit
/--
For formal circuits, to prove `ComputableWitnesses`, we assume that the input
only contains variables below the current offset `n`.
 -/
def ComputableWitnesses' {sentences : PropertySet F} (circuit : ElaboratedCircuit F sentences β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F),
    Environment.OnlyAccessedBelow n (eval · input) →
      (circuit.main input).ComputableWitnesses n

/--
This reformulation of `ComputableWitnesses'` is easier to prove in a formal circuit,
because we have all necessary assumptions at each circuit operation step.
 -/
def ComputableWitnesses {sentences : PropertySet F} (circuit : ElaboratedCircuit F sentences β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F) env env',
  circuit.main input |>.operations n |>.forAllFlat n {
    witness n _ compute :=
      env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env' }

/--
`ComputableWitnesses` is stronger than `ComputableWitnesses'` (so it's fine to only prove the former).
-/
lemma computableWitnesses_implies {sentences : PropertySet F} {circuit : ElaboratedCircuit F sentences β α} :
    circuit.ComputableWitnesses → circuit.ComputableWitnesses' := by
  simp only [ComputableWitnesses, ComputableWitnesses']
  intro h_computable n input input_only_accesses_n
  intro env env'
  specialize h_computable n input env env'
  specialize input_only_accesses_n env env'
  simp only [Operations.ComputableWitnesses, ←Operations.forAll_toFlat_iff] at *
  generalize ((circuit.main input).operations n).toFlat = ops at *
  revert h_computable
  apply FlatOperation.forAll_implies
  simp only [Condition.implies, Condition.ignoreSubcircuit, imp_self]
  induction ops using FlatOperation.induct generalizing n with
  | empty => trivial
  | assert | lookup | yield => simp_all [FlatOperation.forAll]
  | witness m c ops ih =>
    simp_all only [FlatOperation.forAll, forall_const, implies_true, true_and]
    apply ih (m + n)
    intro h_agrees
    apply input_only_accesses_n
    exact Environment.agreesBelow_of_le h_agrees (by linarith)

/--
Composability for `ComputableWitnesses`: If
- in the parent circuit, we prove that input variables are < `n`,
- and the child circuit provides `ElaboratedCircuit.ComputableWitnesses`,
then we can conclude that the subcircuit, evaluated at this particular input,
satisfies `ComputableWitnesses` in the original sense.
-/
theorem compose_computableWitnesses {sentences : PropertySet F} (circuit : ElaboratedCircuit F sentences β α) (input : Var β F) (n : ℕ) :
  Environment.OnlyAccessedBelow n (eval · input) ∧ circuit.ComputableWitnesses →
    (circuit.main input).ComputableWitnesses n := by
  intro ⟨ h_input, h_computable ⟩
  apply ElaboratedCircuit.computableWitnesses_implies h_computable
  exact h_input
end ElaboratedCircuit

theorem Circuit.subcircuit_computableWitnesses {sentences : PropertySet F} {order : SentenceOrder sentences} (circuit : FormalCircuit order β α) (input : Var β F) (n : ℕ) :
  Environment.OnlyAccessedBelow n (eval · input) ∧ circuit.ComputableWitnesses →
    (subcircuit circuit input).ComputableWitnesses n := by
  intro h env env'
  simp only [circuit_norm, FormalCircuit.toSubcircuit, Operations.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact circuit.compose_computableWitnesses input n h env env'

-- to reduce offsets, `circuit_norm` will use these theorems to unfold subcircuits
attribute [circuit_norm] Circuit.subcircuit_localLength_eq Circuit.assertion_localLength_eq
  Circuit.subcircuitWithAssertion_localLength_eq

-- Simplification lemmas for toSubcircuit.UsesLocalWitnesses

/--
Simplifies UsesLocalWitnesses for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_usesLocalWitnessesAndYields
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) :
    (circuit.toSubcircuit n input_var).UsesLocalWitnessesAndYields env yields =
    (circuit.Assumptions (eval env input_var) → circuit.Spec Set.univ (eval env input_var) (eval env (circuit.output input_var n))) := by
  rfl

/--
Simplifies UsesLocalWitnesses for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_usesLocalWitnessesAndYields
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : GeneralFormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) :
    (circuit.toSubcircuit n input_var).UsesLocalWitnessesAndYields env yields =
    (circuit.Assumptions (eval env input_var) → circuit.Spec Set.univ (eval env input_var) (eval env (circuit.output input_var n))) := by
  rfl

/--
Simplifies UsesLocalWitnesses for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_usesLocalWitnessesAndYields
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalAssertion order Input) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) :
    (circuit.toSubcircuit n input_var).UsesLocalWitnessesAndYields env yields = True := by
  rfl

-- Simplification lemmas for toSubcircuit.localLength

/--
Simplifies localLength for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_localLength
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

/--
Simplifies localLength for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_localLength
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : GeneralFormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

/--
Simplifies localLength for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_localLength
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalAssertion order Input) (n : ℕ) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

-- Simplification lemmas for toSubcircuit.Soundness

/--
Simplifies Soundness for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_soundness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences) :
    (circuit.toSubcircuit n input_var).Soundness env yields checked =
    (circuit.Assumptions (eval env input_var) → circuit.Spec checked (eval env input_var) (eval env (circuit.output input_var n))) := by
  rfl

/--
Simplifies Soundness for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_soundness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : GeneralFormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences) :
    (circuit.toSubcircuit n input_var).Soundness env yields checked =
    circuit.Spec checked (eval env input_var) (eval env (circuit.output input_var n)) := by
  rfl

/--
Simplifies Soundness for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_soundness
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalAssertion order Input) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences) :
    (circuit.toSubcircuit n input_var).Soundness env yields checked =
    (circuit.Assumptions (eval env input_var) → circuit.Spec checked (eval env input_var)) := by
  rfl

-- Simplification lemmas for toSubcircuit.Completeness

/--
Simplifies Completeness for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) :
    (circuit.toSubcircuit n input_var).Completeness env yields =
    circuit.Assumptions (eval env input_var) := by
  rfl

/--
Simplifies Completeness for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : GeneralFormalCircuit order Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) :
    (circuit.toSubcircuit n input_var).Completeness env yields =
    circuit.Assumptions (eval env input_var) := by
  rfl

/--
Simplifies Completeness for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_completeness
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    {sentences : PropertySet F} {order : SentenceOrder sentences}
    (circuit : FormalAssertion order Input) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yields : YieldContext sentences) :
    (circuit.toSubcircuit n input_var).Completeness env yields =
    (circuit.Assumptions (eval env input_var) ∧ circuit.Spec Set.univ (eval env input_var)) := by
  rfl
