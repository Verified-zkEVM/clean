module

public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Air.GenerationCompleteness

@[expose] public section

/-!
# Completeness of Fibonacci witness generation

From any public state `(n, x, y)` that is the `n`-th Fibonacci state, of a run short enough for the
field, witness generation returns a valid witness.
-/

open Air.Flat Air.Flat.WitnessGeneration

variable {p : ℕ} [Fact p.Prime] [pGt : Fact (p > 512)]

namespace FibonacciWitness

/-- The Fibonacci step on channel messages `(n, x, y)`. -/
def next (state : Array (F p)) : Array (F p) :=
  #[state[0]?.getD 0 + 1, state[2]?.getD 0,
    ((((state[1]?.getD 0).val + (state[2]?.getD 0).val) % 256 : ℕ) : F p)]

/-- A table height for a run of `steps` steps. -/
def height (steps : ℕ) : ℕ := 2 ^ Nat.clog 2 (max steps 32)

def vm : Vm (fibonacciEnsemble (p := p)) (plan (p := p)) where
  channel := FibonacciChannel.toRaw
  component := fib8Component
  mode := fibMode
  padding := { input := #[0, 0, 0, 0], minimumRows := 32 }
  mem := by simp [fibonacciEnsemble, FormalEnsemble.withProverInput, SoundVmEnsemble.toFormal,
    SoundEnsemble.addVm, Ensemble.addVm, fibonacciVm]
  planned := by simp [plan, fib8Component]
  mode_channel := rfl
  mode_direction := rfl
  mode_aggregation := rfl
  next
  initial _ := #[0, 0, 1]
  final | (n, x, y) => #[n, x, y]

def completePlan : CompletePlan (fibonacciEnsemble (p := p)) (plan (p := p)) where
  valid := sorry
  vm
  rowBound steps name := if name = "bytes" then 256 else height steps
  run := sorry
  vm_row := by
    intro state env hsize honest assumptions
    obtain ⟨hlocal, hinput⟩ := honest
    rcases state with ⟨_ | ⟨n, _ | ⟨x, _ | ⟨y, _ | _⟩⟩⟩⟩ <;>
      simp [vm, FibonacciChannel, circuit_norm] at hsize
    simp [vm, Vm.input, fibMode, InputTemplate.eval, InputCell.eval, fib8Component, fib8,
      interactionsIn, Component.rowOperations, Component.rowInput, inputOf, circuit_norm,
      explicit_provable_type] at hlocal hinput assumptions ⊢
    sorry
  verifier := sorry
  demand := sorry
  preallocated := sorry
  padding := sorry

end FibonacciWitness
