module

public import Clean.Air.CounterChannel
public import Clean.Air.WitnessGeneration
public import Clean.Utils.BinaryField

@[expose] public section

/-!
# Fibonacci over GF(2^64)

A Fibonacci VM over the binary field `BF64`, proven sound under multiset balance, the balance check
of binary-field proof systems. Addition is `xor`, so the sequence starts `0, 1, 1, 0, 1, 1, ...`; the
point is the machinery, not the numbers.

A state `(counter, x, y)` counts its steps with a power of the primitive element `g`, since there is
no integer counter in characteristic 2: the state after `k` steps is `(g ^ k, fibonacci k)`. The
counter makes the state channel a closed counter channel, on which all guarantees hold: there are no
cycles of steps that fail them. The counter must be nonzero: at counter `0`, the states
`(0, 0, 1) → (0, 1, 1) → (0, 1, 0) → (0, 0, 1)` would form such a cycle.
-/

namespace BinaryFibonacci

open Air.Flat

/-- The primitive element whose powers count the steps. -/
abbrev g : BF64 := BF64.X

def fibonacci : ℕ → BF64 × BF64
  | 0 => (0, 1)
  | n + 1 =>
    let (x, y) := fibonacci n
    (y, x + y)

structure State (F : Type) where
  counter : F
  x : F
  y : F
deriving ProvableStruct

/-- A state reached after `k` steps. -/
def stateChannel : Channel BF64 State where
  name := "state"
  Guarantees state _ := ∃ k : ℕ, state.counter = g ^ k ∧ (state.x, state.y) = fibonacci k

structure StepInput (F : Type) where
  enabled : F
  counter : F
  x : F
  y : F
deriving ProvableStruct

/-- One Fibonacci step: pull a state and push the next one. -/
def step : GeneralFormalCircuit BF64 StepInput unit where
  name := "fibonacci"
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    -- the counter is nonzero
    let inverse ← witness input.counter⁻¹
    assertZero (input.enabled * (input.counter * inverse - 1))
    stateChannel.pullIf input.enabled { counter := input.counter, x := input.x, y := input.y }
    stateChannel.pushIf input.enabled
      { counter := input.counter * .const g, x := input.y, y := input.x + input.y }

  exposedChannels
  | { enabled, counter, x, y }, _ =>
    expose stateChannel [ pulledIf enabled { counter, x, y },
      pushedIf enabled { counter := counter * .const g, x := y, y := x + y } ]
  exposedChannels_eq input _ := by
    obtain ⟨enabled, counter, x, y⟩ := input
    simp only [circuit_norm, stateChannel]

  ProverAssumptions
  | { enabled, counter, x, y }, data, _ =>
    enabled = 0 ∨ enabled = 1 ∧ stateChannel.Guarantees { counter, x, y } data
  Spec _ _ _ := True

  channelsWithRequirements := [ stateChannel.toRaw ]
  requirementsChannelsLawful input_var _ := by
    obtain ⟨enabled, counter, x, y⟩ := input_var
    simp only [circuit_norm, stateChannel]

  soundness := by
    circuit_proof_start [stateChannel]
    obtain ⟨ h_bool, -, h_state ⟩ := h_holds
    rcases mul_eq_zero.mp h_bool with rfl | h_one
    · simp
    rw [sub_eq_zero] at h_one
    subst h_one
    obtain ⟨ k, h_counter, h_fib ⟩ := h_state rfl
    refine ⟨ fun _ h => absurd rfl h, fun _ => ⟨ k + 1, by rw [h_counter, pow_succ], ?_ ⟩ ⟩
    simp only [fibonacci, ← h_fib]
  completeness := by
    circuit_proof_start [stateChannel]
    rcases h_assumptions with rfl | ⟨ rfl, k, h_counter, h_fib ⟩
    · simp_all
    have h_ne : (g ^ k : BF64) ≠ 0 := pow_ne_zero _ (by decide)
    simp_all
    exact ⟨k, rfl, rfl⟩

/-- One row per state pushed to the state channel. Padding rows are disabled. -/
abbrev stepComponent : Component BF64 where
  circuit := step
  generation := .demand {
    trigger := .push
    channel := stateChannel
    input | { counter, x, y } => pure { enabled := 1, counter, x, y }
  }

/-- The public input is the claimed final state. The verifier pushes the initial state. -/
def verifier : Verifier.Program BF64 State where
  main final := do
    Verifier.pull stateChannel final
    Verifier.push stateChannel { counter := 1, x := 0, y := 1 }
  Spec final data := stateChannel.Guarantees final data
  soundness := by simp [circuit_norm]

/-- The state channel is closed by its counter: every step multiplies it by the primitive element
`g`, so the states that fail their guarantee can't form a cycle. -/
def stateCounterChannel : CounterChannel BF64 State where
  channel := stateChannel
  owners := [stepComponent]
  counter state := state.counter
  generator := g
  orderOf_generator := BF64.orderOf_X
  exists_step_of_constraintsHold := by
    simp only [List.mem_singleton, forall_eq]
    intro env h_constraints
    rw [Component.constraintsHold_iff] at h_constraints
    rw [Operations.interactionValuesWith_eq_map,
      Component.interactionsWith_of_exposedChannels (table := stepComponent)
        (List.mem_singleton_self _)]
    simp only [List.map_cons, List.map_nil, Channel.eval_toRaw_pulledIf,
      Channel.eval_toRaw_pushedIf]
    refine ⟨_, _, _, rfl, ?_⟩
    simp only [circuit_norm, stepComponent, step] at h_constraints
    simp [explicit_provable_type, circuit_norm, Vector.mapRange, Vector.cast, Vector.take,
      Vector.drop]
    obtain ⟨h_bool, h_inverse⟩ := h_constraints
    refine ⟨?_, fun h_one => ⟨?_, ?_⟩⟩
    · rcases mul_eq_zero.mp h_bool with h | h
      · exact .inl h
      · exact .inr (sub_eq_zero.mp h)
    · rw [h_one, one_mul, sub_eq_zero] at h_inverse
      exact left_ne_zero_of_mul_eq_one h_inverse
    · rintro ⟨k, h_counter, h_fib⟩
      simp only at h_counter h_fib ⊢
      refine ⟨k + 1, by rw [h_counter, pow_succ], ?_⟩
      simp only [fibonacci, ← h_fib]

/-- The public statement: the final state is reached after some number of steps. -/
def Spec (final : State BF64) : Prop :=
  ∃ k : ℕ, final.counter = g ^ k ∧ (final.x, final.y) = fibonacci k

/-- The ensemble, sound under multiset balance. -/
def formalEnsemble : FormalEnsemble BF64 State .multiset :=
  SoundEnsemble.empty BF64 State .multiset
  |>.addClosedChannel (stateCounterChannel.closedChannel .multiset)
    (by simp [circuit_norm, stateCounterChannel])
    (by simp [circuit_norm, stateCounterChannel, step])
    (by simp [circuit_norm, stateCounterChannel, step])
    (by simp [circuit_norm, stateCounterChannel, step])
  |>.setVerifier verifier
    (by simp [circuit_norm, verifier, stateCounterChannel])
    (by simp [circuit_norm, verifier, stateCounterChannel])
    (fun _ channel => by
      simp only [circuit_norm, verifier, stateChannel]
      exact fun _ => ⟨0, by simp, rfl⟩)
  |>.toFormal (fun _ => True) Spec
    (by simp [circuit_norm, stateCounterChannel])
    (fun _ h => h.1)

/-- End-to-end soundness: a valid proof for the public input `final` shows that it is the state
after some number of steps. -/
theorem soundness (final : State BF64) :
    formalEnsemble.ensemble.Statement .multiset final → Spec final :=
  formalEnsemble.soundness final trivial

/-- Generate a complete ensemble witness from the claimed final state. -/
def generate (final : State BF64) (fuel : ℕ) :
    Except WitnessGeneration.GenerationError (EnsembleWitness formalEnsemble.ensemble) :=
  WitnessGeneration.generate formalEnsemble.ensemble fuel final ()

end BinaryFibonacci
