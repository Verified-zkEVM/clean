import Clean.Circuit
import Clean.Circuit.RawCircuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems

/-!
# RawAddition8FullCarry — end-to-end demo of the `RawFormalCircuit` pipeline

This file proves the `Addition8FullCarry` circuit using `RawFormalCircuit`, demonstrating
the alternative proof pipeline where `subcircuit_norm` performs the subcircuit constraint
→ spec transformation that `ConstraintsHold.Soundness` does automatically in the
standard `FormalCircuit` pipeline.

## How it differs from `Addition8FullCarry`

`Addition8FullCarry.circuit` (in `Addition8FullCarry.lean`) uses `FormalCircuit`. Its
soundness proof is given `h_holds : ConstraintsHold.Soundness env ...`. In that type,
the `assertBool carryOut` subcircuit constraint automatically appears as `IsBool carry_out`
(its `Spec`), so no extra work is needed.

`Raw.circuit` here uses `RawFormalCircuit`. Its soundness proof is given
`h_holds : ConstraintsHold env ...`. In this type, the `assertBool carryOut` subcircuit
constraint appears as the raw flat constraint:
```
ConstraintsHoldFlat env (assertBool.toSubcircuit n carryOut_var).ops.toFlat
```

## The alternative proof pipeline

```
circuit_proof_start_raw [main, ByteTable]   ← new tactic: unfolds RawSoundness
                                              expands h_holds using ConstraintsHold
  ↓ h_holds : z.val < 256
            ∧ ConstraintsHoldFlat env (assertBool.toSubcircuit n x).ops.toFlat  ← raw!
            ∧ x + y + carryIn + -z + -(carryOut * 256) = 0
  ↓
obtain ⟨h_byte, h_bool_raw, h_add⟩ := h_holds
  ↓
subcircuit_norm                             ← new tactic: forward reasoning
  ↓ h_bool_raw : (assertBool.toSubcircuit n x).Spec env
  ↓
simp [circuit_norm] at h_bool_raw
  ↓ h_bool_raw : IsBool carry_out          ← same state as in FormalCircuit proof!
  ↓
... same arithmetic proof as Addition8FullCarry.circuit.soundness ...
```
-/

namespace Gadgets.Addition8FullCarry.Raw
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

-- Reuse the circuit body from Addition8FullCarry
open Gadgets.Addition8FullCarry (Inputs Outputs main Assumptions Spec)

/--
The 8-bit addition circuit with carry, proved using `RawFormalCircuit`.

**Key difference from `Addition8FullCarry.circuit`**: The `soundness` proof uses the
raw `ConstraintsHold` hypothesis and the `subcircuit_norm` tactic. The automatic
`ConstraintsHold.Soundness` mechanism — which requires storing `Spec`/`ProverAssumptions`/
`ProverSpec` on `Subcircuit` — is not needed.
-/
def circuit : RawFormalCircuit (F p) Inputs Outputs where
  main := main
  Assumptions := Assumptions
  Spec := Spec
  localLength _ := 2
  output _ i0 := { z := var ⟨i0⟩, carryOut := var ⟨i0 + 1⟩ }

  soundness := by
    -- circuit_proof_start_raw:
    --  1. unfolds RawSoundness (not Soundness) and introduces i₀, env, input_var, input,
    --     h_input, h_assumptions, h_holds
    --  2. applies provable_struct_simp to decompose struct inputs
    --  3. simplifies h_input, h_assumptions, h_holds with circuit_norm + main + ByteTable
    -- After this, h_holds has type:
    --   (env.get i₀).val < 256
    --   ∧ ConstraintsHoldFlat env (assertBool.toSubcircuit n (var ⟨i₀+1⟩)).ops.toFlat
    --   ∧ input_x + input_y + input_carryIn + -(env.get i₀) + -(env.get (i₀+1) * 256) = 0
    -- (i.e. ConstraintsHold expanded, NOT ConstraintsHold.Soundness)
    circuit_proof_start_raw [main, ByteTable]

    set z := env.get i₀
    set carry_out := env.get (i₀ + 1)

    -- Split h_holds into its three parts:
    --   h_byte     : z.val < 256
    --   h_bool_raw : ConstraintsHoldFlat env (assertBool.toSubcircuit n x).ops.toFlat
    --   h_add      : x + y + carryIn + -z + -(carry_out * 256) = 0
    obtain ⟨h_byte, h_bool_raw, h_add⟩ := h_holds

    -- KEY STEP: subcircuit_norm applies FormalAssertion.toSubcircuit_spec_of_constraints,
    -- transforming h_bool_raw from:
    --   ConstraintsHoldFlat env (assertBool.toSubcircuit n x).ops.toFlat
    -- into:
    --   (assertBool.toSubcircuit n x).Spec env
    subcircuit_norm

    -- Simplify the spec using circuit_norm:
    --   (assertBool.toSubcircuit n x).Spec env  =  True → IsBool (eval env x)
    --                                           =  IsBool carry_out
    simp only [circuit_norm] at h_bool_raw

    -- From here, the proof is identical to Addition8FullCarry.circuit.soundness
    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    apply Addition8.Theorems.soundness input_x input_y z input_carryIn carry_out
      as_x as_y h_byte as_carry_in h_bool_raw h_add

  completeness := by
    -- Completeness is unchanged; use the standard pipeline.
    circuit_proof_start [main, ByteTable]
    set z := env.get i₀
    set carry_out := env.get (i₀ + 1)
    obtain ⟨hz, hcarry_out⟩ := h_env
    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    have carry_in_bound := IsBool.val_lt_two as_carry_in
    exact ⟨ by rw [hz]; exact ByteUtils.mod256_lt,
            by rw [hcarry_out]; exact Addition8.Theorems.completeness_bool _ _ _ as_x as_y carry_in_bound,
            by rw [hz, hcarry_out]; exact Addition8.Theorems.completeness_add _ _ _ as_x as_y carry_in_bound ⟩

end Gadgets.Addition8FullCarry.Raw
