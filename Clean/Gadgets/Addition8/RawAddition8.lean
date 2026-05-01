import Clean.Circuit
import Clean.Circuit.RawCircuit
import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Gadgets.Addition8.Addition8

/-!
# Raw analogues of Addition8Full and Addition8

This file defines `RawFormalCircuit` versions of `Addition8Full.circuit` and
`Addition8.circuit`, demonstrating that **a single `circuit_proof_all_raw [...]` invocation
is sufficient** for circuits whose soundness reduces to a single subcircuit call.

## The key point

`Addition8Full.circuit` (in `Addition8.lean`) wraps `Addition8FullCarry.circuit` as a
subcircuit.  Its standard `FormalCircuit` proof uses the `ConstraintsHold.Soundness`
definition, which automatically replaces the subcircuit constraint with its `Spec`:

```lean
-- Standard FormalCircuit proof (one simp_all):
soundness := by simp_all [circuit_norm,
  Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]
```

The **raw** version uses `ConstraintsHold`, so the subcircuit constraint appears as a raw
`ConstraintsHoldFlat` term after expansion.  `circuit_proof_all_raw` bridges the gap via
the `subcircuit_norm` step it includes internally:

```lean
-- Raw proof (also one tactic invocation):
soundness := by
  circuit_proof_all_raw [Addition8FullCarry.circuit,
                          Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]
```

`circuit_proof_all_raw [...]` internally performs:
1. `circuit_proof_start [...]`  — introduces params, expands `h_holds` to `ConstraintsHoldFlat`
2. `subcircuit_norm`             — `ConstraintsHoldFlat` → `Subcircuit.Spec` (implication form)
3. `simp [circuit_norm, ...]`   — `Subcircuit.Spec` → `Assumptions → circuit.Spec`
4. `simp_all`                   — applies `h_holds` to `h_assumptions`, closes goal

The same pattern applies to `Addition8.Raw.circuit` which wraps `Addition8Full.circuit`.
-/

namespace Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Raw analogue of `Addition8Full.circuit` using `RawFormalCircuit`.

The circuit body is identical to `Addition8Full.circuit`; only the soundness proof
obligation changes (raw `ConstraintsHold` instead of `ConstraintsHold.Soundness`).
The proof is a single `circuit_proof_all_raw` invocation.
-/
def Addition8Full.Raw.circuit : RawFormalCircuit (F p) Addition8FullCarry.Inputs field where
  main := fun inputs => do
    let { z, .. } ← Addition8FullCarry.circuit inputs
    return z

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions := fun { x, y, carryIn } =>
    x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

  Spec := fun { x, y, carryIn } z =>
    z.val = (x.val + y.val + carryIn.val) % 256

  -- One tactic: expand h_holds, apply subcircuit_norm, simplify, close.
  soundness := by
    circuit_proof_all_raw [Addition8FullCarry.circuit,
                            Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]

  completeness := by
    simp_all [circuit_norm, Addition8FullCarry.circuit, Addition8FullCarry.Assumptions]

namespace Addition8.Raw
structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

/--
Raw analogue of `Addition8.circuit` using `RawFormalCircuit`.

The circuit body is identical to `Addition8.circuit`; only the soundness proof obligation
changes.  The proof is a single `circuit_proof_all_raw` invocation.
-/
def circuit : RawFormalCircuit (F p) Inputs field where
  -- Uses the standard FormalCircuit (Gadgets.Addition8Full.circuit), not Addition8Full.Raw.circuit.
  main := fun { x, y } =>
    Addition8Full.circuit { x, y, carryIn := 0 }

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions | { x, y } => x.val < 256 ∧ y.val < 256

  Spec | { x, y }, z => z.val = (x.val + y.val) % 256

  -- One tactic: wraps Addition8Full.circuit (the standard FormalCircuit, not Addition8Full.Raw.circuit).
  soundness := by
    circuit_proof_all_raw [Addition8Full.circuit, IsBool]

  completeness := by
    simp_all [circuit_norm, Addition8Full.circuit, IsBool]

end Addition8.Raw
end Gadgets
