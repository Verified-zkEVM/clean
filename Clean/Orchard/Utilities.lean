import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Gadgets.Equality
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard utility gadgets

Clean approximations of small utility gates used by Orchard and `halo2_gadgets`.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/cond_swap.rs`
- `CondSwapChip::configure`
- `CondSwapInstructions::swap`
- `CondSwapInstructions::mux`

These gadgets model the arithmetic gate constraints, not Halo2 selectors, regions, or
column layout.
-/

namespace Orchard
namespace Utilities

variable {F : Type} [Field F]

def ternary (choice ifTrue ifFalse : F) : F :=
  choice * ifTrue + (1 - choice) * ifFalse

structure CondSwapInputs (F : Type) where
  a : F
  b : F
  swap : F
deriving ProvableStruct

structure CondSwapOutput (F : Type) where
  aSwapped : F
  bSwapped : F
deriving ProvableStruct

namespace CondSwap

def outputValue (input : CondSwapInputs F) : CondSwapOutput F where
  aSwapped := ternary input.swap input.b input.a
  bSwapped := ternary input.swap input.a input.b

def main (input : Var CondSwapInputs F) : Circuit F (Var CondSwapOutput F) := do
  let aSwapped ← witnessField fun env => ternary (env input.swap) (env input.b) (env input.a)
  let bSwapped ← witnessField fun env => ternary (env input.swap) (env input.a) (env input.b)
  aSwapped === input.swap * input.b + (1 - input.swap) * input.a
  bSwapped === input.swap * input.a + (1 - input.swap) * input.b
  assertZero (input.swap * (input.swap - 1))
  return { aSwapped, bSwapped }

@[circuit_norm]
def Assumptions (input : CondSwapInputs F) : Prop :=
  IsBool input.swap

@[circuit_norm]
def Spec [DecidableEq F] (input : CondSwapInputs F) (output : CondSwapOutput F) : Prop :=
  output = if input.swap = 1 then
    { aSwapped := input.b, bSwapped := input.a }
  else
    { aSwapped := input.a, bSwapped := input.b }

instance elaborated : ElaboratedCircuit F CondSwapInputs CondSwapOutput main := by
  elaborate_circuit

theorem outputValue_eq_of_bool [DecidableEq F] {input : CondSwapInputs F}
    (hbool : IsBool input.swap) :
    outputValue input = if input.swap = 1 then
      { aSwapped := input.b, bSwapped := input.a }
    else
      { aSwapped := input.a, bSwapped := input.b } := by
  rcases hbool with hzero | hone
  · simp [outputValue, ternary, hzero]
  · simp [outputValue, ternary, hone]

theorem soundness [DecidableEq F] :
    Soundness F main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, outputValue, ternary]
  have hbool : IsBool input_swap :=
    IsBool.iff_mul_sub_one.mpr (by simpa [sub_eq_add_neg] using h_holds.2.2)
  rcases hbool with hzero | hone
  · rw [h_holds.1, h_holds.2.1]
    simp [hzero]
  · rw [h_holds.1, h_holds.2.1]
    simp [hone]

theorem completeness [DecidableEq F] :
    Completeness F main Assumptions := by
  circuit_proof_start [main, Assumptions, outputValue, ternary]
  constructor
  · rw [h_env.1]
    ring_nf
  · constructor
    · rw [h_env.2]
      ring_nf
    · simpa [sub_eq_add_neg] using IsBool.iff_mul_sub_one.mp h_assumptions

def circuit [DecidableEq F] : FormalCircuit F CondSwapInputs CondSwapOutput where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end CondSwap

end Utilities
end Orchard
