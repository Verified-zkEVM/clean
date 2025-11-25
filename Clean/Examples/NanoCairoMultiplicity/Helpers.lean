import Clean.Circuit.Basic
import Clean.Examples.FemtoCairo.Types
import Clean.Examples.NanoCairoMultiplicity.Types

/-!
# NanoCairoMultiplicity Helpers

Shared circuit helper functions for the multiplicity-based VM execution tracking.
-/

namespace Examples.NanoCairoMultiplicity.Helpers
open Examples.FemtoCairo.Types
open Examples.NanoCairoMultiplicity.Types

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/-- Emit an add operation to the global multiset -/
@[circuit_norm]
def emitAdd (name : String) (multiplicity : Expression (F p)) (values : List (Expression (F p))) : Circuit (F p) Unit := fun _ =>
  ((), [.add multiplicity { name, values }])

/-- Emit a state with given multiplicity -/
@[circuit_norm]
def emitState (multiplicity : Expression (F p)) (state : Var State (F p)) : Circuit (F p) Unit :=
  emitAdd "state" multiplicity [state.pc, state.ap, state.fp]

/-- Emit a state conditionally: multiplicity is scaled by enabled.
    When enabled = 0, multiplicity becomes 0 (no effect).
    When enabled = 1, multiplicity is unchanged. -/
@[circuit_norm]
def emitStateWhen (enabled : Expression (F p)) (multiplicity : Expression (F p)) (state : Var State (F p)) : Circuit (F p) Unit :=
  emitAdd "state" (enabled * multiplicity) [state.pc, state.ap, state.fp]

end Examples.NanoCairoMultiplicity.Helpers
