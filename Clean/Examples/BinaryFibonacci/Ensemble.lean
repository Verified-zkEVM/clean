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

/-- The state reached after `k` steps. -/
def Reached (k : ℕ) (state : State BF64) : Prop :=
  state.counter = g ^ k ∧ (state.x, state.y) = fibonacci k

/-- The states of the VM, which `Reached` describes. -/
def stateChannel : Channel BF64 State where
  name := "state"
  Guarantees _ _ := True

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
  | { enabled, counter, x, y }, _, _ =>
    enabled = 0 ∨ enabled = 1 ∧ ∃ k, Reached k { counter, x, y }
  -- an enabled step takes the state after `k` steps to the state after `k + 1` steps
  Spec
  | { enabled, counter, x, y }, _, _ => enabled = 1 → ∀ k, Reached k { counter, x, y } →
    Reached (k + 1) { counter := counter * g, x := y, y := x + y }

  requirementsChannelsLawful input_var _ := by
    obtain ⟨enabled, counter, x, y⟩ := input_var
    simp only [circuit_norm, stateChannel]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]

  soundness := by
    circuit_proof_start [stateChannel, Reached]
    rw [mul_eq_zero, sub_eq_zero] at h_holds
    refine ⟨ ?_, h_holds ⟩
    rintro rfl k ⟨ h_counter, h_fib ⟩
    refine ⟨ by rw [h_counter, pow_succ], ?_ ⟩
    simp only [fibonacci, ← h_fib]
  completeness := by
    circuit_proof_start [stateChannel]
    rcases h_assumptions with rfl | ⟨ rfl, h_state ⟩ <;> simp_all

/-- One row per state pushed to the state channel. Padding rows are disabled. -/
abbrev stepComponent : Component BF64 where
  circuit := step
  generation := .demand {
    channel := stateChannel
    trigger := .push
    input | { counter, x, y } => pure { enabled := 1, counter, x, y }
  }

/-- The public input is the claimed final state. The verifier pushes the initial state. -/
def verifier : Verifier.Program BF64 State where
  main final := do
    Verifier.pull stateChannel final
    Verifier.push stateChannel { counter := 1, x := 0, y := 1 }

def vm : VmTables BF64 State where
  channel := stateChannel
  Reached k state _ := Reached k state
  guarantees_of_reached := by simp [stateChannel]
  tables := [stepComponent]
  unique_names := by simp
  verifier := verifier
  final := id
  tables_channel := by simp [circuit_norm, step, sub_eq_zero]
  verifier_channel := by
    simp [circuit_norm, verifier, Reached, fibonacci, ProverData.getPublicInput_eq_eval]

/-- The public statement: the final state is reached after some number of steps. -/
def Spec (final : State BF64) : Prop :=
  ∃ k : ℕ, Reached k final

/-- The ensemble, sound under multiset balance. -/
def formalEnsemble : FormalEnsemble BF64 State .multiset :=
  SoundEnsemble.empty BF64 State .multiset
  |>.addVm vm
    (by simp +instances [circuit_norm, vm, stateChannel])
    (by simp +instances [circuit_norm, vm, step, verifier])
    (by simp +instances [circuit_norm, vm, step, verifier, stateChannel])
    (by simp [circuit_norm, vm, step])
  |>.toFormal (fun _ _ => True) Spec
    (by simp [circuit_norm, vm])
    (by rintro witness - - ⟨ k, -, -, -, reached ⟩; exact ⟨ k, reached ⟩)

/-- End-to-end soundness: a valid proof for the public input `final` shows that it is the state
after some number of steps. -/
theorem soundness (final : State BF64) (heights : List ℕ) :
    formalEnsemble.ensemble.Statement .multiset final heights → Spec final :=
  formalEnsemble.soundness final heights trivial

/-- Generate a complete ensemble witness from the claimed final state. -/
def generate (final : State BF64) (fuel : ℕ) :
    Except WitnessGeneration.GenerationError (EnsembleWitness formalEnsemble.ensemble) :=
  WitnessGeneration.generate formalEnsemble.ensemble fuel final ()

end BinaryFibonacci
