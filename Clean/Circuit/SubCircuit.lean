import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F: Type} [Field F]

namespace FlatOperation
open Circuit (constraints_hold.completeness constraints_hold)

lemma constraints_hold_cons : ∀ {op : FlatOperation F}, ∀ {ops: List (FlatOperation F)}, ∀ {env : Environment F},
  constraints_hold_flat env (op :: ops) ↔ constraints_hold_flat env [op] ∧ constraints_hold_flat env ops := by
  intro op ops env
  constructor <;> (
    rintro h
    dsimp only [constraints_hold_flat] at h
    split at h
    <;> simp_all only [constraints_hold_flat, and_self])

lemma constraints_hold_append : ∀ {a b: List (FlatOperation F)}, ∀ {env : Environment F},
  constraints_hold_flat env (a ++ b) ↔ constraints_hold_flat env a ∧ constraints_hold_flat env b := by
  intro a b env
  induction a with
  | nil => rw [List.nil_append]; tauto
  | cons op ops ih =>
    constructor
    · intro h
      rw [List.cons_append] at h
      obtain ⟨ h_op, h_rest ⟩ := constraints_hold_cons.mp h
      obtain ⟨ h_ops, h_b ⟩ := ih.mp h_rest
      exact ⟨ constraints_hold_cons.mpr ⟨ h_op, h_ops ⟩, h_b ⟩
    · rintro ⟨ h_a, h_b ⟩
      obtain ⟨ h_op, h_ops ⟩ := constraints_hold_cons.mp h_a
      have h_rest := ih.mpr ⟨ h_ops, h_b ⟩
      exact constraints_hold_cons.mpr ⟨ h_op, h_rest ⟩
end FlatOperation

variable {α β: TypeMap} [ProvableType α] [ProvableType β]

section
open Circuit
open FlatOperation (constraints_hold_cons constraints_hold_append)

/--
Consistency theorem which proves that flattened constraints are equivalent to the
constraints created from the inductive `Operations` type, using flat constraints for subcircuits.
-/
theorem Circuit.can_replace_subcircuits : ∀ {ops : Operations F}, ∀ {env : Environment F},
  constraints_hold env ops ↔ constraints_hold_flat env ops.toFlat
:= by
  intro ops env
  induction ops using Operations.induct with
  | empty => trivial
  -- we can handle all non-empty cases at once
  | witness | assert | lookup | subcircuit =>
    dsimp only [Operations.toFlat]
    try rw [constraints_hold_cons]
    try rw [constraints_hold_append]
    simp_all only [constraints_hold, constraints_hold_flat, and_true, true_and]

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def FormalCircuit.to_subcircuit (circuit: FormalCircuit F β α)
    (n: ℕ) (b_var : Var β F) : SubCircuit F n :=
  let ops := circuit.main b_var |>.operations n
  let flat_ops := ops.toFlat
  have h_consistent : ops.subcircuits_consistent n := circuit.subcircuits_consistent b_var n

  have imply_soundness : ∀ env : Environment F,
      constraints_hold_flat env flat_ops → subcircuit_soundness circuit b_var n env := by
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show subcircuit_soundness circuit b_var n env

    let b : β F := eval env b_var
    let a : α F := eval env (circuit.output b_var n)
    rintro (as : circuit.assumptions b)
    show circuit.spec b a

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: constraints_hold.soundness env ops by
      exact circuit.soundness n env b_var b rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : FlatOperation.constraints_hold_flat env flat_ops
    apply can_replace_soundness
    exact can_replace_subcircuits.mpr h_holds

  have implied_by_completeness : ∀ env : Environment F,
      env.extends_vector (FlatOperation.local_witnesses env flat_ops) n →
      subcircuit_completeness circuit b_var env → constraints_hold_flat env flat_ops := by
    -- we are given that the assumptions are true
    intro env h_env
    let b := eval env b_var
    intro (as : circuit.assumptions b)

    have h_env : env.UsesLocalWitnesses n ops := by
      guard_hyp h_env : env.extends_vector (FlatOperation.local_witnesses env flat_ops) n
      rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
      exact h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env b_var h_env_completeness b rfl as

    -- so we just need to go from constraints to flattened constraints
    apply can_replace_subcircuits.mp
    exact can_replace_completeness h_consistent h_env h_holds

  {
    ops := flat_ops,
    soundness := subcircuit_soundness circuit b_var n,
    completeness := subcircuit_completeness circuit b_var,
    uses_local_witnesses := subcircuit_soundness circuit b_var n,
    local_length := circuit.local_length b_var

    imply_soundness
    implied_by_completeness
    implied_by_local_witnesses := by
      intro env h_env as
      -- by completeness, the constraints hold
      have h_holds := implied_by_completeness env h_env as
      -- by soundness, this implies the spec
      exact imply_soundness env h_holds as

    local_length_eq := by
      rw [← circuit.local_length_eq b_var n]
      exact FlatOperation.flat_witness_length_eq |>.symm
  }

/--
Theorem and implementation that allows us to take a formal assertion and use it as a subcircuit.
-/
def FormalAssertion.to_subcircuit (circuit: FormalAssertion F β)
    (n: ℕ) (b_var : Var β F) : SubCircuit F n :=
  let ops := circuit.main b_var |>.operations n
  let flat_ops := ops.toFlat
  have h_consistent : ops.subcircuits_consistent n := circuit.subcircuits_consistent b_var n

  {
    ops := flat_ops,
    soundness := subassertion_soundness circuit b_var,
    completeness := subassertion_completeness circuit b_var,
    uses_local_witnesses _ := True,
    local_length := circuit.local_length b_var

    imply_soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env h_holds
      show subassertion_soundness circuit b_var env

      let b : β F := eval env b_var
      rintro (as : circuit.assumptions b)
      show circuit.spec b

      -- by soundness of the circuit, the spec is satisfied if only the constraints hold
      suffices h: constraints_hold.soundness env ops by
        exact circuit.soundness n env b_var b rfl as h

      -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.constraints_hold_flat env flat_ops
      apply can_replace_soundness
      exact can_replace_subcircuits.mpr h_holds

    implied_by_completeness := by
      -- we are given that the assumptions and the spec are true
      intro env h_env h_completeness

      let b := eval env b_var
      have as : circuit.assumptions b ∧ circuit.spec b := h_completeness

      have h_env : env.UsesLocalWitnesses n ops := by
        guard_hyp h_env : env.extends_vector (FlatOperation.local_witnesses env flat_ops) n
        rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
        exact h_env
      have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds := circuit.completeness n env b_var h_env_completeness b rfl as.left as.right

      -- so we just need to go from constraints to flattened constraints
      apply can_replace_subcircuits.mp
      exact can_replace_completeness h_consistent h_env h_holds

    implied_by_local_witnesses := by intros; exact trivial

    local_length_eq := by
      rw [← circuit.local_length_eq b_var n]
      exact FlatOperation.flat_witness_length_eq |>.symm
  }
end

/-- Include a subcircuit. -/
@[circuit_norm]
def subcircuit (circuit: FormalCircuit F β α) (b: Var β F) : Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.to_subcircuit offset b
    (a, [.subcircuit subcircuit])

/-- Include an assertion subcircuit. -/
@[circuit_norm]
def assertion (circuit: FormalAssertion F β) (b: Var β F) : Circuit F Unit :=
  fun offset =>
    let subcircuit := circuit.to_subcircuit offset b
    ((), [.subcircuit subcircuit])

namespace Circuit
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

/-- The local length of a subcircuit is derived from the original formal circuit -/
lemma subcircuit_local_length_eq (circuit: FormalCircuit F β α) (input: Var β F) (offset: ℕ) :
  (circuit.to_subcircuit offset input).local_length = circuit.local_length input := by rfl

lemma assertion_local_length_eq (circuit: FormalAssertion F β) (input: Var β F) (offset: ℕ) :
  (circuit.to_subcircuit offset input).local_length = circuit.local_length input := by rfl
end Circuit

-- subcircuit composability for `computable_witnesses`

namespace ElaboratedCircuit
/--
For formal circuits, to prove `computableWitnesses`, we assume that the input
only contains variables below the current offset `n`.
 -/
def computableWitnesses' (circuit : ElaboratedCircuit F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F),
    Environment.onlyAccessedBelow n (eval · input) →
      (circuit.main input).computableWitnesses n

/--
This reformulation of `computableWitnesses'` is easier to prove in a formal circuit,
because we have all necessary assumptions at each circuit operation step.
 -/
def computableWitnesses (circuit : ElaboratedCircuit F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F) env env',
  circuit.main input |>.operations n |>.forAllFlat n {
    witness n _ compute :=
      env.agreesBelow n env' → eval env input = eval env' input → compute env = compute env' }

/--
`computableWitnesses` is stronger than `computableWitnesses'` (so it's fine to only prove the former).
-/
lemma computableWitnesses_implies {circuit : ElaboratedCircuit F β α} :
    circuit.computableWitnesses → circuit.computableWitnesses' := by
  simp only [computableWitnesses, computableWitnesses']
  intro h_computable n input input_only_accesses_n
  intro env env'
  specialize h_computable n input env env'
  specialize input_only_accesses_n env env'
  simp only [Operations.computableWitnesses, ←Operations.forAll_toFlat_iff] at *
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
    exact Environment.agreesBelow_of_le h_agrees (by linarith)

/--
Composability for `computableWitnesses`: If
- in the parent circuit, we prove that input variables are < `n`,
- and the child circuit provides `ElaboratedCircuit.computableWitnesses`,
then we can conclude that the subcircuit, evaluated at this particular input,
satisfies `computableWitnesses` in the original sense.
-/
theorem compose_computableWitnesses (circuit : ElaboratedCircuit F β α) (input: Var β F) (n : ℕ) :
  Environment.onlyAccessedBelow n (eval · input) ∧ circuit.computableWitnesses →
    (circuit.main input).computableWitnesses n := by
  intro ⟨ h_input, h_computable ⟩
  apply ElaboratedCircuit.computableWitnesses_implies h_computable
  exact h_input
end ElaboratedCircuit

theorem Circuit.subcircuit_computableWitnesses (circuit: FormalCircuit F β α) (input: Var β F) (n : ℕ) :
  Environment.onlyAccessedBelow n (eval · input) ∧ circuit.computableWitnesses →
    (subcircuit circuit input).computableWitnesses n := by
  intro h env env'
  simp only [circuit_norm, FormalCircuit.to_subcircuit, Operations.computableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact circuit.compose_computableWitnesses input n h env env'

-- simp set to unfold subcircuits
attribute [subcircuit_norm]
  FormalCircuit.to_subcircuit FormalAssertion.to_subcircuit
  Circuit.subcircuit_soundness Circuit.subcircuit_completeness
  Circuit.subassertion_soundness Circuit.subassertion_completeness

-- to just reduce offsets, it's much better to _not_ use `subcircuit_norm`
-- instead, `circuit_norm` will use these theorems to unfold subcircuits
attribute [circuit_norm]
  Circuit.subcircuit_local_length_eq Circuit.assertion_local_length_eq
