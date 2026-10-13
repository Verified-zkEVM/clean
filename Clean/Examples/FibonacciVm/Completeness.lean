module

public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Air.GenerationCompletenessProof

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
  declared := by
    simp [fibonacciEnsemble, FormalEnsemble.withProverInput, SoundVmEnsemble.toFormal,
      SoundEnsemble.addVm, Ensemble.addVm, fibonacciVm, SoundEnsemble.addFinishedChannel,
      SoundEnsemble.addTable, Ensemble.addTable, SoundEnsemble.empty]
  mem := by simp [fibonacciEnsemble, FormalEnsemble.withProverInput, SoundVmEnsemble.toFormal,
    SoundEnsemble.addVm, Ensemble.addVm, fibonacciVm]
  planned := by simp [plan, fib8Component]
  mode_channel := rfl
  mode_direction := rfl
  mode_aggregation := rfl
  no_pull_handler := sorry
  next
  initial _ := #[0, 0, 1]
  final | (n, x, y) => #[n, x, y]

example (e n' x' y' n x y : F p)
    (h : ({ enabled := e, n := n', x := x', y := y' } : Fib8Input (F p)) =
      fromElements (inputRow Fib8Input #[1, n, x, y])) : e = 1 ∧ n' = n ∧ x' = x ∧ y' = y := by
  simp [explicit_provable_type, circuit_norm] at h
  trace_state
  sorry

end FibonacciWitness
