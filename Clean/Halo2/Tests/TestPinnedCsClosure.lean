import Clean.Halo2.Keygen.PinnedCs
import Clean.Utils.Field

/-!
# Regression tests: synthesis-closed keygen constraint systems

A faithful circuit, whose synthesis enables only configure-registered entries, keeps
the configured gate/lookup lists exactly. A mismatched formal circuit is nevertheless
compiled to a constraint system containing every enabled gate and lookup, once and in
first-enable order, together with their query registrations.
-/

namespace Halo2.Tests.TestPinnedCsClosure

open Halo2

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev TestField := F 17

def configuredGate : Gate TestField :=
  Gate.withSelector "configured" ⟨0, true⟩
    [queryAdvice ⟨0⟩ 0] [("", queryAdvice ⟨0⟩ 0)]

def enabledGate : Gate TestField :=
  Gate.withSelector "enabled" ⟨1, true⟩
    [queryAdvice ⟨1⟩ 0] [("", queryAdvice ⟨1⟩ 0)]

def enabledLookup : LookupArgument TestField where
  inputs := [queryAdvice ⟨2⟩ 0]
  tables := [queryFixed ⟨0⟩]
  tablesFree := by simp [Expression.SelectorFree, queryFixed]
  arity := rfl

def rawConstraintSystem : ConstraintSystem TestField :=
  (createGate configuredGate {}).2

def faithfulOperations : Operations TestField :=
  [.region "faithful" [.enableGate configuredGate 0]]

def mismatchedOperations : Operations TestField :=
  [.region "mismatched"
    [.enableGate configuredGate 0,
     .enableGate enabledGate 1,
     .enableGate enabledGate 2,
     .enableLookup enabledLookup [⟨1, false⟩] 3,
     .enableLookup enabledLookup [⟨1, false⟩] 4]]

#guard (rawConstraintSystem.closeWithOperations faithfulOperations).gates =
  rawConstraintSystem.gates
#guard (rawConstraintSystem.closeWithOperations faithfulOperations).lookups =
  rawConstraintSystem.lookups

def closedConstraintSystem : ConstraintSystem TestField :=
  rawConstraintSystem.closeWithOperations mismatchedOperations

#guard closedConstraintSystem.gates = [configuredGate, enabledGate]
#guard closedConstraintSystem.lookups = [enabledLookup]
#guard closedConstraintSystem.adviceQueries =
  [(⟨0⟩, 0), (⟨1⟩, 0), (⟨2⟩, 0)]
#guard closedConstraintSystem.fixedQueries = [(⟨0⟩, 0)]

example : enabledGate ∈ closedConstraintSystem.gates :=
  ConstraintSystem.mem_gates_closeWithOperations_of_enabled
    rawConstraintSystem mismatchedOperations enabledGate (by decide)

example : enabledLookup ∈ closedConstraintSystem.lookups :=
  ConstraintSystem.mem_lookups_closeWithOperations_of_enabled
    rawConstraintSystem mismatchedOperations enabledLookup (by decide)

end Halo2.Tests.TestPinnedCsClosure
