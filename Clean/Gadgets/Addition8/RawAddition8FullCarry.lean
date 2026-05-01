import Clean.Circuit
import Clean.Circuit.RawCircuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems

/-!
# RawAddition8FullCarry — end-to-end demo of the `RawFormalCircuit` pipeline

This file defines and proves the `Addition8FullCarry` circuit using `RawFormalCircuit`,
demonstrating the alternative proof pipeline where `subcircuit_norm` performs the
subcircuit constraint → spec transformation that `ConstraintsHold.Soundness` does
automatically in the standard `FormalCircuit` pipeline.

## How it differs from `Addition8FullCarry`

`Addition8FullCarry.circuit` (in `Addition8FullCarry.lean`) uses `FormalCircuit`. Its
soundness proof receives `h_holds : ConstraintsHold.Soundness env ...`. In that type,
the `assertBool carryOut` subcircuit constraint automatically appears as `IsBool carry_out`
(its `Spec`), so no extra work is needed.

`Raw.circuit` here uses `RawFormalCircuit`. Its soundness proof receives
`h_holds : ConstraintsHold env ...`. In this type, the `assertBool carryOut` subcircuit
constraint appears as the raw flat constraint:
```
ConstraintsHoldFlat env (assertBool.toSubcircuit n carryOut_var).ops.toFlat
```

## The alternative proof pipeline

```
circuit_proof_start_raw [ByteTable]     (intro + normalize h_holds in the raw setting)
  ↓ introduces the offset variable (written as `i₀` in this example)
  h_holds : z.val < 256
          ∧ IsBool carry_out
          ∧ x + y + carryIn + -z + -(carryOut * 256) = 0
  ↓
obtain ⟨h_byte, h_bool_raw, h_add⟩ := h_holds
  ↓
... same arithmetic proof as Addition8FullCarry.circuit.soundness ...
```

Note: this file now uses `circuit_proof_start_raw` directly in the real
`RawAddition8FullCarry.soundness` proof. For this circuit, `h_holds` starts out as a
conjunction, and `circuit_proof_start_raw` now uses the deep `subcircuit_norm` traversal
to rewrite the raw `assertBool` subcircuit fact *inside that conjunction* before the user
continues the proof. For circuits with a single subcircuit
(e.g. `Addition8Full.Raw`, `Addition8.Raw`), the whole proof reduces to a single
`circuit_proof_all_raw [...]` invocation.
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
    -- `circuit_proof_start_raw` does the standard RawSoundness introductions and
    -- normalization. For this conjunction-shaped `h_holds`, it also rewrites the
    -- raw `assertBool` subcircuit fact inside the conjunction automatically.
    -- The offset variable introduced by the tactic is `i₀`, which is then used below
    -- to name the witness positions for `z` and `carry_out`.
    circuit_proof_start_raw [ByteTable]

    set z := env.get i₀
    set carry_out := env.get (i₀ + 1)
    obtain ⟨h_byte, h_bool_raw, h_add⟩ := h_holds

    -- From here, identical to Addition8FullCarry.circuit.soundness
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ IsBool carry_in
    guard_hyp h_byte : z.val < 256
    guard_hyp h_bool_raw : IsBool carry_out
    guard_hyp h_add : x + y + carry_in + -z + -(carry_out * 256) = 0
    show z.val = (x.val + y.val + carry_in.val) % 256 ∧
         carry_out.val = (x.val + y.val + carry_in.val) / 256

    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    apply Addition8.Theorems.soundness x y z carry_in carry_out
      as_x as_y h_byte as_carry_in h_bool_raw h_add

  completeness := by
    -- Completeness is the same as FormalCircuit.
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ h_env ⟨x, y, carry_in⟩ h_inputs h_assumptions
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in := by
      simpa [circuit_norm] using h_inputs
    simp only [circuit_norm, h_inputs, Assumptions, main, ByteTable] at *
    obtain ⟨hz, hcarry_out⟩ := h_env
    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    have carry_in_bound := IsBool.val_lt_two as_carry_in
    exact ⟨ by rw [hz]; exact ByteUtils.mod256_lt,
            by rw [hcarry_out]; exact Addition8.Theorems.completeness_bool _ _ _ as_x as_y carry_in_bound,
            by rw [hz, hcarry_out]; exact Addition8.Theorems.completeness_add _ _ _ as_x as_y carry_in_bound ⟩

end Gadgets.Addition8FullCarry.Raw
