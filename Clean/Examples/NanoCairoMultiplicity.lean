import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Utils.SourceSinkPath

/-!
# NanoCairoMultiplicity

A FemtoCairo-like VM example that uses the multiplicity-based approach from `SourceSinkPath.lean`
to prove execution correctness without timestamps.

## Key Insight

Instead of using `InductiveTable` with explicit step indices, we track VM execution using
global multiset operations:
- Each transition circuit emits `add` operations on a global multiset
- For each VM step from state `s1` to state `s2`:
  - Add entry `("state", [s1.pc, s1.ap, s1.fp])` with multiplicity -1 (remove source)
  - Add entry `("state", [s2.pc, s2.ap, s2.fp])` with multiplicity +1 (add destination)
- At boundaries: initial state +1, final state -1
- Net result: all intermediate states have net multiplicity 0

The `SourceSinkPath.exists_path_from_source_to_sink` theorem then proves: if net flow is +1 at
initial, -1 at final, and 0 elsewhere, a valid execution path exists.
-/

namespace Examples.NanoCairoMultiplicity
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

-- ============================================================================
-- Circuit Building Blocks
-- ============================================================================

/-- Emit an add operation to the global multiset -/
@[circuit_norm]
def emitAdd (name : String) (multiplicity : ℤ) (values : List (Expression (F p))) : Circuit (F p) Unit := fun _ =>
  ((), [.add multiplicity { name, values }])

/-- The step circuit that wraps FemtoCairo's step circuit and adds multiplicity tracking -/
def stepWithMultiplicity
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (state : Var State (F p)) : Circuit (F p) (Var State (F p)) := do
  -- Emit remove of current state (multiplicity -1)
  emitAdd "state" (-1) [state.pc, state.ap, state.fp]

  -- Perform the actual step using FemtoCairo's elaborated circuit
  let nextState ← (femtoCairoStepElaboratedCircuit program h_programSize memory h_memorySize).main state

  -- Emit add of next state (multiplicity +1)
  emitAdd "state" 1 [nextState.pc, nextState.ap, nextState.fp]

  return nextState

/-- Initial state boundary circuit: adds initial state with +1 -/
def initialBoundary (initialState : Var State (F p)) : Circuit (F p) Unit :=
  emitAdd "state" 1 [initialState.pc, initialState.ap, initialState.fp]

/-- Final state boundary circuit: removes final state with -1 -/
def finalBoundary (finalState : Var State (F p)) : Circuit (F p) Unit :=
  emitAdd "state" (-1) [finalState.pc, finalState.ap, finalState.fp]

-- ============================================================================
-- Connection to SourceSinkPath
-- ============================================================================

/-- Convert a State to a NamedList for comparison -/
def stateToNamedList (s : State (F p)) : NamedList (F p) :=
  { name := "state", values := [s.pc, s.ap, s.fp] }

/-- Check if a NamedList represents a given state -/
def isStateNL (nl : NamedList (F p)) (s : State (F p)) : Bool :=
  nl.name = "state" ∧ nl.values = [s.pc, s.ap, s.fp]

/-- Compute the net flow at a state from collected adds -/
def netFlowFromAdds (adds : List (NamedList (F p) × ℤ)) (state : State (F p)) : ℤ :=
  ∑ i : Fin adds.length, if isStateNL adds[i].1 state then adds[i].2 else 0

/-- A valid execution path: each consecutive pair is a valid transition -/
def validExecutionPath
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (path : List (State (F p))) : Prop :=
  ∀ i (h : i + 1 < path.length),
    femtoCairoMachineTransition program memory path[i] = some path[i + 1]

/-- Build a Run from the collected add operations.
    For each transition (src, dst), count how many times it appears. -/
def buildRun
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (adds : List (NamedList (F p) × ℤ)) : Utils.StateTransition.Run (State (F p)) :=
  -- For each possible transition, count occurrences
  fun (src, dst) =>
    -- A transition from src to dst is recorded when:
    -- - We see (src, -1) followed by (dst, +1) in the adds list
    -- - And the transition is valid according to the FemtoCairo machine
    if femtoCairoMachineTransition program memory src = some dst then
      -- Count pairs of consecutive adds that represent this transition
      (adds.zip adds.tail).countP fun ((nl1, m1), (nl2, m2)) =>
        isStateNL nl1 src ∧ m1 = -1 ∧ isStateNL nl2 dst ∧ m2 = 1
    else
      0

/-- Key lemma: The net flow from adds equals the net flow from the Run -/
theorem netFlow_from_run_eq
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (adds : List (NamedList (F p) × ℤ))
    (s : State (F p))
    (h_wellformed : ∀ (nl : NamedList (F p)) (m : ℤ), (nl, m) ∈ adds →
      nl.name = "state" → (m = 1 ∨ m = -1)) :
    netFlowFromAdds adds s =
      Utils.StateTransition.Run.netFlow (buildRun program memory adds) s := by
  sorry

/-- Main soundness theorem: valid circuit constraints imply valid execution path exists -/
theorem multiplicity_soundness
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (initialState finalState : State (F p))
    (collectedAdds : List (NamedList (F p) × ℤ))
    (h_initial : netFlowFromAdds collectedAdds initialState = 1)
    (h_final : netFlowFromAdds collectedAdds finalState = -1)
    (h_others : ∀ s, s ≠ initialState → s ≠ finalState → netFlowFromAdds collectedAdds s = 0)
    (h_transitions_valid : ∀ src dst,
      (buildRun program memory collectedAdds) (src, dst) > 0 →
      femtoCairoMachineTransition program memory src = some dst)
    : ∃ path : List (State (F p)),
        path.head? = some initialState ∧
        path.getLast? = some finalState ∧
        path ≠ [] ∧
        validExecutionPath program memory path := by
  -- The proof uses exists_path_from_source_to_sink from SourceSinkPath
  -- First, we convert our net flow conditions to the Run.netFlow format
  -- Then we apply the theorem to get a path
  -- Finally, we show each transition in the path is valid
  sorry

end Examples.NanoCairoMultiplicity
