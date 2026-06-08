import Clean.Halo2.Orchard

namespace Halo2.Tests

/-- The new Halo2-like synthesis layer records selector activations for the
Orchard action skeleton. -/
theorem orchardActionSynthesis_hasSelectorActivations :
    let cols := (Halo2.Orchard.Action.configureActionColumns {}).1
    (Halo2.Orchard.ActionSynthesis.synthesize cols).selectorActivations.length > 0 := by
  native_decide

/-- Synthesis loads the 10-bit range-check table used by the Orchard circuit. -/
theorem orchardActionSynthesis_loadsRangeTable :
    let cols := (Halo2.Orchard.Action.configureActionColumns {}).1
    (Halo2.Orchard.ActionSynthesis.synthesize cols).fixedAssignments.length = 2^10 := by
  native_decide

end Halo2.Tests

namespace Halo2.Tests

/-- The Orchard action now has a single configured-circuit object combining CS
configuration and synthesis. -/
theorem orchardConfiguredCircuit_selectorMatrixRows :
    Halo2.Orchard.Action.selectorActivationMatrix.length =
      Halo2.Orchard.Action.configuredCircuit.cs.numSelectors := by
  native_decide

end Halo2.Tests
