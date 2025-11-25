/-
NanoCairoMultiplicity Helper Functions
Following PR 286 PicoCairo pattern but using multiplicities instead of timestamps.
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Provable
import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Examples.FemtoCairo.Spec
import Clean.Examples.NanoCairoMultiplicity.Types
import Clean.Gadgets.Conditional

namespace Examples.NanoCairoMultiplicity.Helpers

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.NanoCairoMultiplicity.Types

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/-!
## Emit operations for multiplicity tracking
-/

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

/-!
## Conditional decode infrastructure
-/

/--
Input structure for conditional decode circuit.
Contains enabled flag, raw instruction type, and dummy instruction to use when disabled.
-/
structure ConditionalDecodeInput (F : Type) where
  enabled : F
  rawInstrType : F
  dummy : DecodedInstruction F

instance : ProvableStruct ConditionalDecodeInput where
  components := [field, field, DecodedInstruction]
  toComponents := fun { enabled, rawInstrType, dummy } =>
    .cons enabled (.cons rawInstrType (.cons dummy .nil))
  fromComponents := fun (.cons enabled (.cons rawInstrType (.cons dummy .nil))) =>
    { enabled, rawInstrType, dummy }

/--
Main circuit for conditionally decoding instruction based on enabled flag.
When enabled is 0, returns the provided dummy instruction.
When enabled is 1, returns the actual decoded instruction.
-/
def conditionalDecodeMain
    (input : Var ConditionalDecodeInput (F p)) :
    Circuit (F p) (Var DecodedInstruction (F p)) := do
  let enabled := input.enabled
  let rawInstrType := input.rawInstrType
  let dummy := input.dummy

  -- Decode the actual instruction
  let actualDecoded ← subcircuitWithAssertion decodeInstructionCircuit rawInstrType

  -- Use conditional gadget to select between actual and dummy based on enabled
  let result ← subcircuit Gadgets.Conditional.circuit {
    selector := enabled,
    ifTrue := actualDecoded,
    ifFalse := dummy
  }

  return result

/--
ElaboratedCircuit for conditional decode.
-/
def conditionalDecodeElaborated :
    ElaboratedCircuit (F p) ConditionalDecodeInput DecodedInstruction where
  main := conditionalDecodeMain
  localLength _ := 8  -- Same as decodeInstructionCircuit since Conditional adds 0
  localAdds_eq _ _ _ := by
    simp only [conditionalDecodeMain, circuit_norm, decodeInstructionCircuit, Gadgets.Conditional.circuit]
    simp only [Operations.collectAdds, circuit_norm]

/--
Conditional decode circuit as GeneralFormalCircuit.
Takes ConditionalDecodeInput and returns decoded instruction or dummy.
-/
def conditionalDecodeCircuit :
    GeneralFormalCircuit (F p) ConditionalDecodeInput DecodedInstruction where
  elaborated := conditionalDecodeElaborated
  Assumptions := fun input =>
    IsBool input.enabled ∧ input.rawInstrType.val < 256
  Spec := fun input output =>
    IsBool input.enabled →
    if input.enabled = 0 then
      output = input.dummy
    else
      decodeInstructionSpec input.rawInstrType output
  soundness := by
    sorry
  completeness := by
    sorry

/-!
## Dummy instructions for conditional decoding
-/

/--
Create a dummy ADD instruction with immediate addressing for all operands.
-/
def dummyADDInstruction : Var DecodedInstruction (F p) := {
  instrType := {
    isAdd := Expression.const 1,
    isMul := Expression.const 0,
    isStoreState := Expression.const 0,
    isLoadState := Expression.const 0
  },
  mode1 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode2 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode3 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  }
}

/--
Create a dummy MUL instruction with immediate addressing for all operands.
-/
def dummyMULInstruction : Var DecodedInstruction (F p) := {
  instrType := {
    isAdd := Expression.const 0,
    isMul := Expression.const 1,
    isStoreState := Expression.const 0,
    isLoadState := Expression.const 0
  },
  mode1 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode2 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode3 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  }
}

def dummyStoreStateInstruction : Var DecodedInstruction (F p) := {
  instrType := {
    isAdd := Expression.const 0,
    isMul := Expression.const 0,
    isStoreState := Expression.const 1,
    isLoadState := Expression.const 0
  },
  mode1 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode2 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode3 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  }
}

def dummyLoadStateInstruction : Var DecodedInstruction (F p) := {
  instrType := {
    isAdd := Expression.const 0,
    isMul := Expression.const 0,
    isStoreState := Expression.const 0,
    isLoadState := Expression.const 1
  },
  mode1 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode2 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  },
  mode3 := {
    isImmediate := Expression.const 1,
    isDoubleAddressing := Expression.const 0,
    isApRelative := Expression.const 0,
    isFpRelative := Expression.const 0
  }
}

end Examples.NanoCairoMultiplicity.Helpers
