import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Utils.SourceSinkPath
import Clean.Examples.PicoCairoMultiplicity.Types
import Clean.Examples.PicoCairoMultiplicity.Helpers
import Clean.Examples.PicoCairoMultiplicity.AddInstruction
import Clean.Examples.PicoCairoMultiplicity.MulInstruction
import Clean.Examples.PicoCairoMultiplicity.LoadStateInstruction
import Clean.Examples.PicoCairoMultiplicity.StoreStateInstruction
import Clean.Examples.PicoCairoMultiplicity.ExecutionBundle
import Clean.Examples.PicoCairoMultiplicity.TraceExecution

/-!
# PicoCairoMultiplicity

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

## Module Structure

- `Types`: Common type definitions (State, InstructionStepInput, etc.)
- `Helpers`: Helper circuits for fetching, decoding, memory access
- `AddInstruction`: ADD instruction circuit and bundle
- `MulInstruction`: MUL instruction circuit and bundle
- `LoadStateInstruction`: LOAD_STATE instruction circuit and bundle
- `StoreStateInstruction`: STORE_STATE instruction circuit and bundle
- `ExecutionBundle`: Combined execution circuit with initial/final state emissions
- `TraceExecution`: Theorem connecting ExecutionBundle.Spec to valid execution existence
-/
