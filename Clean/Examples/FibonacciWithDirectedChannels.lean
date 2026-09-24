module

public import Clean.Air.VmWith
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci over directed channels

The Fibonacci VM of `Clean.Examples.FibonacciWithChannels`, rebuilt on a directed state channel
under the multiset balance model (`Clean.Air.VmWith`) so that it works over every field, binary
fields included. The state `(n, x, y)` carries the guarantee `(x, y) = (fib n, fib (n + 1))`, the
sum `x + y` is looked up on a second channel, and the verifier provides `(0, 0, 1)` and receives
the state at index `N`.

Ensemble soundness gives, over any field, that the output is a Fibonacci pair at an index
congruent to `N` modulo the characteristic. Over `F 2` with `N = 1`, both the one-step run and
the three-step run `0 → 1 → 0 → 1` are accepted, with different outputs; the output `(0, 0)` is
rejected over every field; and the legacy sign-based relation accepts no witness at all.
-/

@[expose] public section

namespace Examples.FibonacciWithDirectedChannels
open Air.Flat

/-- The state channel: `(n, x, y)` is reachable iff `(x, y) = (fib n, fib (n + 1))` for some
index `n : ℕ`, read into the field. -/
def FibChannel (F : Type) [FiniteField F] : DirectedChannel F fieldTriple where
  name := "fibonacci"
  Guarantees
  | (n, x, y), _ => ∃ k : ℕ, n = (k : F) ∧ x = (Nat.fib k : F) ∧ y = (Nat.fib (k + 1) : F)

/-- The addition lookup channel: a provider of `(x, y, z)` establishes `z = x + y`. -/
def AddChannel (F : Type) [FiniteField F] : DirectedChannel F fieldTriple where
  name := "add"
  Guarantees
  | (x, y, z), _ => z = x + y

/-- One row per sum the VM consumes. -/
def addProvider (F : Type) [FiniteField F] : GeneralFormalCircuit F fieldPair unit where
  main input := (AddChannel F).push (input.1, input.2, input.1 + input.2)
  Spec _ _ _ := True
  channelsWithRequirements := [(AddChannel F).toRaw]
  soundness := by circuit_proof_start [AddChannel]
  completeness := by circuit_proof_start [AddChannel]

structure FibRow (F : Type) where
  enabled : F
  n : F
  x : F
  y : F
  z : F
deriving ProvableStruct

/-- One step, gated by a boolean `enabled`: receive `(n, x, y)`, look up `z = x + y` and provide
`(n + 1, y, z)`. -/
def fibStep (F : Type) [FiniteField F] : GeneralFormalCircuit F FibRow unit where
  main row := do
    assertZero (row.enabled * (row.enabled - 1))
    (FibChannel F).pullIf row.enabled (row.n, row.x, row.y)
    (AddChannel F).pullIf row.enabled (row.x, row.y, row.z)
    (FibChannel F).pushIf row.enabled (row.n + 1, row.y, row.z)
  exposedChannels
  | { enabled, n, x, y, z }, _ =>
    (FibChannel F).expose [(FibChannel F).pulledIf enabled (n, x, y),
      (FibChannel F).pushedIf enabled (n + 1, y, z)]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, n, x, y, z⟩ := input
    simp only [circuit_norm, FibChannel, AddChannel]
  ProverAssumptions row _ _ :=
    row.enabled = 0 ∨
      (row.enabled = 1 ∧
        (∃ k : ℕ, row.n = (k : F) ∧ row.x = (Nat.fib k : F) ∧ row.y = (Nat.fib (k + 1) : F)) ∧
        row.z = row.x + row.y)
  Spec _ _ _ := True
  channelsWithRequirements := [(FibChannel F).toRaw]
  requirementsChannelsLawful input i₀ := by
    obtain ⟨enabled, n, x, y, z⟩ := input
    simp only [circuit_norm, FibChannel, AddChannel]
    intro env h
    rw [mul_eq_zero, sub_eq_zero] at h
    exact h
  soundness := by
    circuit_proof_start [FibChannel, AddChannel]
    obtain ⟨h_bool, h_state, h_add⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    refine ⟨h_bool, h_bool, h_bool, fun h_on => ?_⟩
    obtain ⟨k, rfl, rfl, rfl⟩ := h_state h_on
    exact ⟨k + 1, by simp, rfl, by simp [h_add h_on, Nat.fib_add_two]⟩
  completeness := by
    circuit_proof_start [FibChannel, AddChannel]
    rcases h_assumptions with rfl | ⟨rfl, h_state, h_add⟩
    · simp
    · simp [h_state, h_add]

/-- The verifier of the run to index `N`: it provides the initial state `(0, 0, 1)` and receives
the state at index `N`. Its spec is the state guarantee at `N`. -/
def fibVerifier (F : Type) [FiniteField F] (N : ℕ) : GeneralFormalCircuit F fieldPair unit where
  main output := do
    (FibChannel F).pull ((N : F), output.1, output.2)
    (FibChannel F).push (0, 0, 1)
  exposedChannels
  | (x, y), _ =>
    (FibChannel F).expose [(FibChannel F).pulled ((N : F), x, y), (FibChannel F).pushed (0, 0, 1)]
  ProverAssumptions
  | (x, y), _, _ => ∃ k : ℕ, (N : F) = (k : F) ∧ x = (Nat.fib k : F) ∧ y = (Nat.fib (k + 1) : F)
  Spec
  | (x, y), _, _ => ∃ k : ℕ, (N : F) = (k : F) ∧ x = (Nat.fib k : F) ∧ y = (Nat.fib (k + 1) : F)
  channelsWithRequirements := [(FibChannel F).toRaw]
  soundness := by
    circuit_proof_start [FibChannel]
    exact ⟨h_holds, 0, by simp⟩
  completeness := by
    circuit_proof_start [FibChannel]
    exact h_assumptions

/-- The Fibonacci VM: the state channel, the step table and the verifier. -/
def fibVm (F : Type) [FiniteField F] [DecidableEq F] (N : ℕ) : DirectedVmTables F fieldPair where
  channel := FibChannel F
  tables := [⟨ fibStep F ⟩]
  verifier := fibVerifier F N
  verifier_length_zero := by simp [circuit_norm, fibVerifier]
  tables_channel := by simp [circuit_norm, fibStep, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, fibVerifier]
  verifier_requirements env := by
    simp [circuit_norm, fibVerifier, FibChannel]
    exact ⟨0, by simp⟩

/-- The ensemble under the multiset model: the addition provider, the addition channel finished,
then the VM. -/
def fibEnsemble (F : Type) [FiniteField F] [DecidableEq F] (N : ℕ) :
    FormalEnsembleWith F (.multiset F) fieldPair :=
  SoundEnsembleWith.empty F (.multiset F) fieldPair
    |>.addTable ⟨ addProvider F ⟩
      (by simp [circuit_norm, addProvider]) (by simp [circuit_norm, addProvider])
    |>.addFinishedChannel (AddChannel F)
    |>.addVm (fibVm F N)
      (by simp +instances [circuit_norm, fibVm, addProvider, AddChannel, FibChannel])
      (by simp +instances [circuit_norm, fibVm, fibStep, fibVerifier])
      (by simp [circuit_norm, fibVm, fibStep, fibVerifier, AddChannel, FibChannel])
    |>.toFormal (fun _ _ => True)
      (by simp [circuit_norm, fibVm, fibStep, addProvider])

/-- Soundness over any field: the output is a Fibonacci pair `(fib k, fib (k + 1))` at an index
`k` with `(k : F) = N`. Over a field of characteristic `p` this fixes `k` only modulo `p`. -/
theorem fibEnsemble_soundness (F : Type) [FiniteField F] [DecidableEq F] (N : ℕ) (x y : F) :
    (fibEnsemble F N).ensemble.StatementWith (.multiset F) (x, y) →
      ∃ k : ℕ, (N : F) = (k : F) ∧ x = (Nat.fib k : F) ∧ y = (Nat.fib (k + 1) : F) := by
  intro statement
  have h := (fibEnsemble F N).soundness (x, y) ?_ statement
  · simp only [fibEnsemble, circuit_norm, fibVm, fibVerifier] at h
    obtain ⟨_, h⟩ := h
    exact h
  · simp [fibEnsemble, circuit_norm, fibVm, fibVerifier]

/-- Consecutive Fibonacci numbers are coprime, so no characteristic divides both: the output
`(0, 0)` is rejected over every field, for every `N`. -/
theorem fibEnsemble_rejects_zero (F : Type) [FiniteField F] [DecidableEq F] (N : ℕ) :
    ¬ (fibEnsemble F N).ensemble.StatementWith (.multiset F) (0, 0) := by
  intro h
  obtain ⟨k, -, hx, hy⟩ := fibEnsemble_soundness F N 0 0 h
  rw [eq_comm, ringChar.spec] at hx hy
  have h_dvd := Nat.dvd_gcd hx hy
  rw [(Nat.fib_coprime_fib_succ k).gcd_eq_one, Nat.dvd_one] at h_dvd
  exact CharP.ringChar_ne_one h_dvd

/-! ## Runs over `F 2` -/

/-- The one-step run: the row `(enabled, n, x, y, z) = (1, 0, 0, 1, 1)`. -/
def stepTable1 : Table (F 2) where
  component := ⟨ fibStep (F 2) ⟩
  width := 5
  table := [#[1, 0, 0, 1, 1]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- Its addition row `(0, 1)`. -/
def addTable1 : Table (F 2) where
  component := ⟨ addProvider (F 2) ⟩
  width := 2
  table := [#[0, 1]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The one-step witness, with output `(1, 1) = (fib 1, fib 2)`. -/
def witness1 : EnsembleWitness (fibEnsemble (F 2) 1).ensemble where
  tables := [stepTable1, addTable1]
  data := fun _ _ => #[]
  publicInput := (1, 1)
  same_length := rfl
  same_circuits := by
    intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
  same_data := by
    intro table ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> rfl

/-- Over `F 2` with `N = 1`, the one-step run is accepted: four interactions on the state channel
and two on the addition channel, balanced under the multiset model. -/
theorem fibEnsemble_one_step_over_F2 :
    (fibEnsemble (F 2) 1).ensemble.StatementWith (.multiset (F 2)) (1, 1) := by
  refine ⟨witness1, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    refine ⟨ ?_, ?_ ⟩
    · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
      simp [Ensemble.VerifierConstraints, circuit_norm, fibEnsemble, fibVm, fibVerifier]
    · simp [witness1, stepTable1, addTable1, Table.Constraints, Component.constraints_eq,
        Component.lookups_eq, circuit_norm, fibStep, addProvider, Table.environment,
        Environment.fromArray]
  · have hv : (fibEnsemble (F 2) 1).ensemble.verifier = fibVerifier (F 2) 1 := rfl
    intro channel h_channel
    simp only [fibEnsemble, fibVm, circuit_norm, List.mem_cons, List.not_mem_nil,
      or_false] at h_channel
    rw [BalanceModel.multiset_balanced_iff, EnsembleWitness.interactionsWith_allTablesWitness]
    simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
      Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
      EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
      Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
      Ensemble.verifierOperations, hv]
    simp only [witness1, stepTable1, addTable1, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Component.interactionsWith_eq]
    rcases h_channel with rfl | rfl <;>
      simp [circuit_norm, fibStep, addProvider, fibVerifier, FibChannel, AddChannel,
        DirectedChannel.eval_toRaw, Table.environment, Environment.fromArray,
        Environment.fromInput, Component.rowOperations, activePayloads]
    exact List.Perm.swap _ _ _

/-- The three-step run `0 → 1 → 0 → 1`: rows `(1, 0, 0, 1, 1)`, `(1, 1, 1, 1, 0)`,
`(1, 0, 1, 0, 1)`. -/
def stepTable3 : Table (F 2) where
  component := ⟨ fibStep (F 2) ⟩
  width := 5
  table := [#[1, 0, 0, 1, 1], #[1, 1, 1, 1, 0], #[1, 0, 1, 0, 1]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- Its addition rows `(0, 1)`, `(1, 1)`, `(1, 0)`. -/
def addTable3 : Table (F 2) where
  component := ⟨ addProvider (F 2) ⟩
  width := 2
  table := [#[0, 1], #[1, 1], #[1, 0]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The three-step witness, with output `(0, 1) = (fib 3, fib 4)` read into `F 2`. -/
def witness3 : EnsembleWitness (fibEnsemble (F 2) 1).ensemble where
  tables := [stepTable3, addTable3]
  data := fun _ _ => #[]
  publicInput := (0, 1)
  same_length := rfl
  same_circuits := by
    intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
  same_data := by
    intro table ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> rfl

/-- With the same `N = 1`, the three-step run is accepted too, with a different output: `N` fixes
the final index as a field element, and `(3 : F 2) = 1`. -/
theorem fibEnsemble_three_steps_over_F2 :
    (fibEnsemble (F 2) 1).ensemble.StatementWith (.multiset (F 2)) (0, 1) := by
  refine ⟨witness3, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    refine ⟨ ?_, ?_ ⟩
    · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
      simp [Ensemble.VerifierConstraints, circuit_norm, fibEnsemble, fibVm, fibVerifier]
    · simp [witness3, stepTable3, addTable3, Table.Constraints, Component.constraints_eq,
        Component.lookups_eq, circuit_norm, fibStep, addProvider, Table.environment,
        Environment.fromArray]
  · have hv : (fibEnsemble (F 2) 1).ensemble.verifier = fibVerifier (F 2) 1 := rfl
    intro channel h_channel
    simp only [fibEnsemble, fibVm, circuit_norm, List.mem_cons, List.not_mem_nil,
      or_false] at h_channel
    rw [BalanceModel.multiset_balanced_iff, EnsembleWitness.interactionsWith_allTablesWitness]
    simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
      Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
      EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
      Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
      Ensemble.verifierOperations, hv]
    simp only [witness3, stepTable3, addTable3, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Component.interactionsWith_eq]
    rcases h_channel with rfl | rfl <;>
      simp [circuit_norm, fibStep, addProvider, fibVerifier, FibChannel, AddChannel,
        DirectedChannel.eval_toRaw, Table.environment, Environment.fromArray,
        Environment.fromInput, Component.rowOperations, activePayloads] <;>
      simp [List.perm_iff_count, List.count_cons, explicit_provable_type,
        (by decide : (1 : F 2) + 1 = 0)]
    intro a
    ac_rfl

/-- The legacy sign-based relation accepts no witness of this ensemble over `F 2`, whatever `N`:
the verifier alone puts two interactions on the state channel, and the no-wrap guard
`length < ringChar (F 2)` admits at most one. -/
theorem legacy_rejects_every_run (N : ℕ)
    (witness : EnsembleWitness (fibEnsemble (F 2) N).ensemble) :
    ¬ BalancedInteractions
      (witness.allTablesWitness.interactionsWith (FibChannel (F 2)).toRaw) := by
  intro h
  have hlen := length_le_one_of_balancedInteractions_of_ringChar_eq_two (ZMod.ringChar_zmod_n 2) h
  have hv : (fibEnsemble (F 2) N).ensemble.verifier = fibVerifier (F 2) N := rfl
  rw [EnsembleWitness.interactionsWith_allTablesWitness] at hlen
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
    Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
    Ensemble.verifierOperations, hv, List.length_append, List.length_map] at hlen
  simp [circuit_norm, fibVerifier, FibChannel] at hlen
  omega

end Examples.FibonacciWithDirectedChannels
