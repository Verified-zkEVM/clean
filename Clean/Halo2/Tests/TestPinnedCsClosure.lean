import Clean.Halo2.Keygen.PinnedCs

/-!
# Regression tests: synthesis-closed keygen constraint systems

A faithful circuit, whose synthesis enables only configure-registered entries, keeps
the configured gate/lookup lists exactly. A mismatched formal circuit is nevertheless
compiled to a constraint system containing every enabled gate and lookup, once and in
first-enable order, together with their query registrations.
-/

namespace Halo2.Tests.TestPinnedCsClosure

open Halo2

def configuredGate : Gate Nat where
  name := "configured"
  selector := ⟨0, true⟩
  queriedCells := [queryAdvice ⟨0⟩ 0]
  constraints := [{ poly := querySelector ⟨0, true⟩ * queryAdvice ⟨0⟩ 0 }]

def enabledGate : Gate Nat where
  name := "enabled"
  selector := ⟨1, true⟩
  queriedCells := [queryAdvice ⟨1⟩ 0]
  constraints := [{ poly := querySelector ⟨1, true⟩ * queryAdvice ⟨1⟩ 0 }]

def enabledLookup : LookupArgument Nat where
  inputs := [queryAdvice ⟨2⟩ 0]
  tables := [queryFixed ⟨0⟩]

def rawConstraintSystem : ConstraintSystem Nat :=
  (createGate configuredGate {}).2

def faithfulOperations : Operations Nat :=
  [.region "faithful" [.enableGate configuredGate 0]]

def mismatchedOperations : Operations Nat :=
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

def closedConstraintSystem : ConstraintSystem Nat :=
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
