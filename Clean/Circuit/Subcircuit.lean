import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F : Type} [Field F]

namespace FlatOperation
open Circuit (ConstraintsHold.Completeness ConstraintsHold)

lemma constraintsHold_cons : ∀ {op : FlatOperation F}, ∀ {ops : List (FlatOperation F)}, ∀ {env : Environment F}, ∀ {yielded : Set (NamedList F)},
    ConstraintsHoldFlat env yielded (op :: ops) ↔ ConstraintsHoldFlat env yielded [op] ∧ ConstraintsHoldFlat env yielded ops := by
  intro op ops env yielded
  constructor <;> (
    rintro h
    dsimp only [ConstraintsHoldFlat] at h
    split at h
    <;> simp_all only [ConstraintsHoldFlat, and_self, and_true]
    ; grind)

lemma constraintsHold_append : ∀ {a b: List (FlatOperation F)}, ∀ {env : Environment F}, ∀ {yielded : Set (NamedList F)},
    ConstraintsHoldFlat env yielded (a ++ b) ↔ ConstraintsHoldFlat env yielded a ∧ ConstraintsHoldFlat env yielded b := by
  intro a b env yielded
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
theorem Circuit.constraintsHold_toFlat_iff : ∀ {ops : Operations F}, ∀ {env : Environment F}, ∀ {yielded : Set (NamedList F)},
    ConstraintsHoldFlat env yielded ops.toFlat ↔ ConstraintsHold env yielded ops := by
  intro ops env yielded
  induction ops using Operations.induct with
  | empty => trivial
  -- we can handle all non-empty cases at once
  | witness | assert | lookup | subcircuit | yield | use =>
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
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have imply_soundness : ∀ env : Environment F, ∀ yielded : Set (NamedList F),
    let input := eval env input_var
    let output := eval env (circuit.output input_var n)
    let localYields := circuit.yields input_var env n
    ConstraintsHoldFlat env yielded ops.toFlat → circuit.Assumptions input yielded → circuit.Spec input output localYields := by
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env yielded input output localYields h_holds (as : circuit.Assumptions input yielded)
    show circuit.Spec input output localYields

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: ConstraintsHold.Soundness env yielded ops by
      exact circuit.soundness n env yielded input_var input rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env yielded ops.toFlat
    apply can_replace_soundness
    exact constraintsHold_toFlat_iff.mp h_holds

  have implied_by_completeness : ∀ env : Environment F, ∀ yielded : Set (NamedList F),
      env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n →
      FlatOperation.localYields env ops.toFlat ⊆ yielded →
      circuit.Assumptions (eval env input_var) yielded → ConstraintsHoldFlat env yielded ops.toFlat := by
    -- we are given that the assumptions are true
    intro env yielded h_ext h_subset
    let input := eval env input_var
    intro (as : circuit.Assumptions input yielded)

    have h_env : env.UsesLocalWitnesses yielded n ops := by
      guard_hyp h_ext : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n
      rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
      exact ⟨h_ext, h_subset⟩
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env yielded input_var h_env_completeness input rfl as

    -- so we just need to go from constraints to flattened constraints
    apply constraintsHold_toFlat_iff.mpr
    exact can_replace_completeness h_consistent h_env h_holds

  {
    ops := ops.toFlat,
    Soundness env yielded := circuit.Assumptions (eval env input_var) yielded →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) (circuit.yields input_var env n),
    Completeness env yielded := circuit.Assumptions (eval env input_var) yielded,
    UsesLocalWitnesses env yielded := circuit.Assumptions (eval env input_var) yielded →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) (circuit.yields input_var env n),
    localLength := circuit.localLength input_var

    imply_soundness
    implied_by_completeness
    imply_usesLocalWitnesses := by
      intro env yielded h_ext h_subset as
      -- by completeness, the constraints hold
      have h_holds := implied_by_completeness env yielded h_ext h_subset as
      -- by soundness, this implies the spec
      exact imply_soundness env yielded h_holds as

    localLength_eq := by
      rw [← circuit.localLength_eq input_var n, FlatOperation.localLength_toFlat]
  }

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_yields (circuit : FormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) (env : Environment F) :
    FlatOperation.localYields env (circuit.toSubcircuit n input_var).ops =
    circuit.yields input_var env n := by
  simp only [toSubcircuit, FlatOperation.localYields_toFlat, circuit.yields_eq]

/--
Theorem and implementation that allows us to take a formal assertion and use it as a subcircuit.
-/
def FormalAssertion.toSubcircuit (circuit : FormalAssertion F β)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  {
    ops := ops.toFlat,
    Soundness env yielded := circuit.Assumptions (eval env input_var) yielded → circuit.Spec (eval env input_var),
    Completeness env yielded := circuit.Assumptions (eval env input_var) yielded ∧ circuit.Spec (eval env input_var),
    UsesLocalWitnesses _ _ := True,
    localLength := circuit.localLength input_var

    imply_soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env yielded h_holds
      let input : β F := eval env input_var
      rintro (as : circuit.Assumptions input yielded)
      show circuit.Spec input

      -- by soundness of the circuit, the spec is satisfied if only the constraints hold
      suffices h: ConstraintsHold.Soundness env yielded ops by
        exact circuit.soundness n env yielded input_var input rfl as h

      -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env yielded ops.toFlat
      apply can_replace_soundness
      exact constraintsHold_toFlat_iff.mp h_holds

    implied_by_completeness := by
      -- we are given that the assumptions and the spec are true
      intro env yielded h_ext h_subset h_completeness

      let input := eval env input_var
      have as : circuit.Assumptions input yielded ∧ circuit.Spec input := h_completeness

      have h_env : env.UsesLocalWitnesses yielded n ops := by
        guard_hyp h_ext : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n
        rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
        exact ⟨h_ext, h_subset⟩
      have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds := circuit.completeness n env yielded input_var h_env_completeness input rfl as.left as.right

      -- so we just need to go from constraints to flattened constraints
      apply constraintsHold_toFlat_iff.mpr
      exact can_replace_completeness h_consistent h_env h_holds

    imply_usesLocalWitnesses := by intros; exact trivial

    localLength_eq := by
      rw [← circuit.localLength_eq input_var n, FlatOperation.localLength_toFlat]
  }

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_yields (circuit : FormalAssertion F β)
    (n : ℕ) (input_var : Var β F) (env : Environment F) :
    FlatOperation.localYields env (circuit.toSubcircuit n input_var).ops =
    circuit.yields input_var env n := by
  simp only [toSubcircuit, FlatOperation.localYields_toFlat, circuit.yields_eq]

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def GeneralFormalCircuit.toSubcircuit (circuit : GeneralFormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have imply_soundness : ∀ env : Environment F, ∀ yielded : Set (NamedList F),
      let input := eval env input_var
      let output := eval env (circuit.output input_var n)
      let localYields := circuit.yields input_var env n
      ConstraintsHoldFlat env yielded ops.toFlat → circuit.Spec input yielded output localYields := by
    intro env yielded input output localYields h_holds
    apply circuit.soundness n env yielded input_var input rfl
    apply can_replace_soundness
    exact constraintsHold_toFlat_iff.mp h_holds

  have implied_by_completeness : ∀ env : Environment F, ∀ yielded : Set (NamedList F),
      env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n →
      FlatOperation.localYields env ops.toFlat ⊆ yielded →
      circuit.Assumptions (eval env input_var) yielded → ConstraintsHoldFlat env yielded ops.toFlat := by
    intro env yielded h_ext h_subset assumptions
    set input := eval env input_var
    have h_env : env.UsesLocalWitnesses yielded n ops := by
      rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
      exact ⟨h_ext, h_subset⟩
    rw [constraintsHold_toFlat_iff]
    apply can_replace_completeness h_consistent h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    apply circuit.completeness n env yielded input_var h_env_completeness input rfl assumptions
    calc circuit.yields input_var env n
      = Operations.localYields env ops := (circuit.yields_eq input_var env n).symm
      _ = FlatOperation.localYields env ops.toFlat := FlatOperation.localYields_toFlat.symm
      _ ⊆ yielded := h_subset

  {
    ops := ops.toFlat,
    Soundness env yielded := circuit.Spec (eval env input_var) yielded (eval env (circuit.output input_var n)) (circuit.yields input_var env n),
    Completeness env yielded := circuit.Assumptions (eval env input_var) yielded,
    UsesLocalWitnesses env yielded := circuit.Assumptions (eval env input_var) yielded →
      circuit.Spec (eval env input_var) yielded (eval env (circuit.output input_var n)) (circuit.yields input_var env n),
    localLength := circuit.localLength input_var

    imply_soundness
    implied_by_completeness
    imply_usesLocalWitnesses env yielded h_ext h_subset assumptions :=
      -- constraints hold by completeness, which implies the spec by soundness
      implied_by_completeness env yielded h_ext h_subset assumptions |> imply_soundness env yielded

    localLength_eq := by
      rw [← circuit.localLength_eq input_var n, FlatOperation.localLength_toFlat]
  }

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_yields (circuit : GeneralFormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) (env : Environment F) :
    FlatOperation.localYields env (circuit.toSubcircuit n input_var).ops =
    circuit.yields input_var env n := by
  simp only [toSubcircuit, FlatOperation.localYields_toFlat, circuit.yields_eq]
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
def subcircuitWithAssertion (circuit : GeneralFormalCircuit F β α) (b : Var β F) : Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

-- we'd like to use subcircuits like functions

instance : CoeFun (FormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuit circuit input

instance : CoeFun (FormalAssertion F β) (fun _ => Var β F → Circuit F Unit) where
  coe circuit input := assertion circuit input

instance : CoeFun (GeneralFormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuitWithAssertion circuit input

namespace Circuit
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

/-- The local length of a subcircuit is derived from the original formal circuit -/
lemma subcircuit_localLength_eq (circuit : FormalCircuit F β α) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma assertion_localLength_eq (circuit : FormalAssertion F β) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma subcircuitWithAssertion_localLength_eq (circuit : GeneralFormalCircuit F β α) (input : Var β F) (offset : ℕ) :
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
    Environment.OnlyAccessedBelow n (eval · input) →
      (circuit.main input).ComputableWitnesses n

/--
This reformulation of `ComputableWitnesses'` is easier to prove in a formal circuit,
because we have all necessary assumptions at each circuit operation step.
 -/
def ComputableWitnesses (circuit : ElaboratedCircuit F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F) env env',
  circuit.main input |>.operations n |>.forAllFlat n {
    witness n _ compute :=
      env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env' }

/--
`ComputableWitnesses` is stronger than `ComputableWitnesses'` (so it's fine to only prove the former).
-/
lemma computableWitnesses_implies {circuit : ElaboratedCircuit F β α} :
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
  | assert | lookup | yield | use => simp_all [FlatOperation.forAll]
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
theorem compose_computableWitnesses (circuit : ElaboratedCircuit F β α) (input : Var β F) (n : ℕ) :
  Environment.OnlyAccessedBelow n (eval · input) ∧ circuit.ComputableWitnesses →
    (circuit.main input).ComputableWitnesses n := by
  intro ⟨ h_input, h_computable ⟩
  apply ElaboratedCircuit.computableWitnesses_implies h_computable
  exact h_input
end ElaboratedCircuit

theorem Circuit.subcircuit_computableWitnesses (circuit : FormalCircuit F β α) (input : Var β F) (n : ℕ) :
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
theorem FormalCircuit.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).UsesLocalWitnesses env yielded =
    (circuit.Assumptions (eval env input_var) yielded → circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) (circuit.yields input_var env n)) := by
  rfl

/--
Simplifies UsesLocalWitnesses for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).UsesLocalWitnesses env yielded =
    (circuit.Assumptions (eval env input_var) yielded → circuit.Spec (eval env input_var) yielded (eval env (circuit.output input_var n)) (circuit.yields input_var env n)) := by
  rfl

/--
Simplifies UsesLocalWitnesses for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).UsesLocalWitnesses env yielded = True := by
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
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).Soundness env yielded =
    (circuit.Assumptions (eval env input_var) yielded → circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) (circuit.yields input_var env n)) := by
  rfl

/--
Simplifies Soundness for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_soundness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).Soundness env yielded =
    circuit.Spec (eval env input_var) yielded (eval env (circuit.output input_var n)) (circuit.yields input_var env n) := by
  rfl

/--
Simplifies Soundness for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_soundness
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).Soundness env yielded =
    (circuit.Assumptions (eval env input_var) yielded → circuit.Spec (eval env input_var)) := by
  rfl

-- Simplification lemmas for toSubcircuit.Completeness

/--
Simplifies Completeness for FormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalCircuit.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).Completeness env yielded =
    circuit.Assumptions (eval env input_var) yielded := by
  rfl

/--
Simplifies Completeness for GeneralFormalCircuit.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).Completeness env yielded =
    circuit.Assumptions (eval env input_var) yielded := by
  rfl

/--
Simplifies Completeness for FormalAssertion.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem FormalAssertion.toSubcircuit_completeness
    {F : Type} [Field F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input_var : Var Input F) (env : Environment F) (yielded : Set (NamedList F)) :
    (circuit.toSubcircuit n input_var).Completeness env yielded =
    (circuit.Assumptions (eval env input_var) yielded ∧ circuit.Spec (eval env input_var)) := by
  rfl
