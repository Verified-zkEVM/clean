module

public import Clean.Air.Vm
public import Clean.Air.WitnessGeneration
public import Clean.Utils.BinaryField

@[expose] public section

/-!
# Fibonacci over GF(2^64)

A Fibonacci VM over the binary field `BF64`, proven sound under multiset balance, the balance check
of binary-field proof systems. Addition is `xor`, so the sequence starts `0, 1, 1, 0, 1, 1, ...`; the
point is the machinery, not the numbers.

A state `(counter, x, y)` counts its steps with a power of the field element `g`, since there is no
integer counter in characteristic 2: the state after `k` steps is `(g ^ k, fibonacci k)`.
-/

namespace BinaryFibonacci

open Air.Flat

/-- The field element whose powers count the steps. -/
def g : BF64 := BF64.ofBitVec 2#64

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
    obtain ⟨ h_bool, h_state ⟩ := h_holds
    rcases mul_eq_zero.mp h_bool with rfl | h_one
    · simp
    rw [sub_eq_zero] at h_one
    subst h_one
    obtain ⟨ k, h_counter, h_fib ⟩ := h_state rfl
    refine ⟨ fun _ h => absurd rfl h, fun _ => ⟨ k + 1, by rw [h_counter, pow_succ], ?_ ⟩ ⟩
    simp only [fibonacci, ← h_fib]
  completeness := by
    circuit_proof_start [stateChannel]
    rcases h_assumptions with rfl | ⟨ rfl, h_state ⟩ <;> simp_all

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

def vm : VmTables BF64 State where
  channel := stateChannel
  tables := [stepComponent]
  unique_names := by simp
  verifier := verifier
  tables_channel := by simp [circuit_norm, step, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, verifier]
  verifier_requirements _ := by
    simp only [circuit_norm, verifier, stateChannel]
    exact ⟨ 0, by simp, rfl ⟩

/-- The public statement: the final state is reached after some number of steps. -/
def Spec (final : State BF64) : Prop :=
  ∃ k : ℕ, final.counter = g ^ k ∧ (final.x, final.y) = fibonacci k

/-- The ensemble, sound under multiset balance. -/
def formalEnsemble : FormalEnsemble BF64 State .multiset :=
  SoundEnsemble.empty BF64 State .multiset
  |>.addVm vm
    (by simp +instances [circuit_norm, vm, stateChannel])
    (by simp +instances [circuit_norm, vm, step, verifier])
    (by simp +instances [circuit_norm, vm, step, verifier, stateChannel])
    (by simp [circuit_norm, vm, step])
  |>.toFormal (fun _ => True) Spec
    (by simp [circuit_norm, vm])
    (fun _ _ h => h)

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
