import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F : Type} [Field F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-!
# RawFormalCircuit: Formal circuits with raw soundness

This module defines `RawFormalCircuit`, a variant of `FormalCircuit` whose soundness
proof obligation uses `RawSoundness` (raw `ConstraintsHold`) instead of `Soundness`
(`ConstraintsHold.Soundness`).

## Background

In `FormalCircuit`, soundness uses `ConstraintsHold.Soundness`, which automatically
replaces subcircuit constraints with their high-level `Spec` (by definition):
```lean
| .subcircuit s :: ops => s.Spec eval ∧ ConstraintsHold.Soundness eval ops
```

In `RawFormalCircuit`, soundness uses plain `ConstraintsHold`, which keeps subcircuit
constraints as raw flat operation constraints:
```lean
| .subcircuit s :: ops => ConstraintsHoldFlat eval s.ops.toFlat ∧ ConstraintsHold eval ops
```

This means `h_holds` in a `RawFormalCircuit` soundness proof still contains raw
`ConstraintsHoldFlat env s.ops.toFlat` terms for subcircuits, rather than the
automatically simplified `s.Spec env`.

## Using `subcircuit_norm` for proofs

The `subcircuit_norm` tactic bridges this gap. After expanding `h_holds` with
`simp [circuit_norm]`, the user can:

1. `subcircuit_norm` to deeply transform any `ConstraintsHoldFlat env s.ops.toFlat`
   subexpression inside `h_holds` into `s.Spec env`
2. `simp [circuit_norm]` to further simplify the spec
3. `obtain`/`rcases` only afterwards, if desired, to unpack the normalized conjunction

This demonstrates that `Subcircuit.Spec` (which `ConstraintsHold.Soundness` uses)
could in principle be removed from the `Subcircuit` type, with `subcircuit_norm`
providing the same functionality via explicit forward reasoning.

## Relationship to `FormalCircuit`

- Any `FormalCircuit` can be converted to a `RawFormalCircuit` via
  `FormalCircuit.toRawFormalCircuit` (using `Circuit.can_replace_soundness`)
- `RawFormalCircuit.soundness` is logically stronger than `FormalCircuit.soundness`
  (since `ConstraintsHold` is stronger than `ConstraintsHold.Soundness`)
  but less convenient to prove without `subcircuit_norm`
-/

section

open Circuit

/--
Alternative soundness definition using raw `ConstraintsHold` instead of
`ConstraintsHold.Soundness`.

The key difference from `Soundness`:
- `Soundness` provides `h_holds : ConstraintsHold.Soundness env ops`
  where subcircuits automatically appear as `s.Spec env`
- `RawSoundness` provides `h_holds : ConstraintsHold env ops`
  where subcircuits appear as `ConstraintsHoldFlat env s.ops.toFlat`

To transform raw subcircuit constraints into their specs, use `subcircuit_norm`
after expanding `h_holds` with `simp [circuit_norm]`.
-/
@[circuit_norm]
def RawSoundness (F : Type) [Field F] (circuit : ElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop) (Spec : Input F → Output F → Prop) :=
  ∀ offset : ℕ, ∀ env : Environment F,
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- Uses plain ConstraintsHold, not ConstraintsHold.Soundness.
  -- Subcircuit constraints appear as ConstraintsHoldFlat env s.ops.toFlat.
  ConstraintsHold env (circuit.main input_var |>.operations offset) →
  let output := eval env (circuit.output input_var offset)
  Spec input output

end

/--
`RawFormalCircuit` is a variant of `FormalCircuit` where the soundness proof uses
`RawSoundness` (raw `ConstraintsHold`) instead of `Soundness` (`ConstraintsHold.Soundness`).

**Motivation**: The current `FormalCircuit` stores `Spec`/`ProverAssumptions`/`ProverSpec`
on `Subcircuit` so that `ConstraintsHold.Soundness` can automatically simplify subcircuit
constraints. `RawFormalCircuit` demonstrates that this is not strictly necessary:
the `subcircuit_norm` tactic can perform the same transformation explicitly.

**Proof pipeline for soundness**:
1. `circuit_proof_start_raw` — introduces parameters with `h_holds : ConstraintsHold env ...`
2. `simp [circuit_norm, h_input]` at `h_holds` — expands the raw constraints,
    exposing `ConstraintsHoldFlat env s.ops.toFlat` for subcircuits
3. `subcircuit_norm` — deeply transforms `ConstraintsHoldFlat env s.ops.toFlat` → `s.Spec env`
   inside the resulting proposition
4. `simp [circuit_norm]` — further simplifies the resulting `s.Spec env` subexpressions
5. `obtain ⟨h1, h2, ...⟩ := h_holds` — optionally splits the normalized conjunction

**Completeness**: Unchanged from `FormalCircuit` — uses the same `Completeness` definition.

**Relationship to `FormalCircuit`**: Any `FormalCircuit` can be converted to a
`RawFormalCircuit` using `FormalCircuit.toRawFormalCircuit`.
-/
structure RawFormalCircuit (F : Type) [Field F] (Input Output : TypeMap)
    [ProvableType Input] [ProvableType Output]
    extends elaborated : ElaboratedCircuit F Input Output where
  Assumptions (_ : Input F) : Prop := True
  Spec : Input F → Output F → Prop
  soundness : RawSoundness F elaborated Assumptions Spec
  completeness : Completeness F elaborated Assumptions

/--
Any `FormalCircuit` can be converted to a `RawFormalCircuit`.

This conversion is possible because `ConstraintsHold env ops → ConstraintsHold.Soundness env ops`
(via `Circuit.can_replace_soundness`): given the stronger raw constraints, we can derive
the weaker `.Soundness` constraints and then apply the original `FormalCircuit.soundness`.

**Interpretation**: This shows that `RawFormalCircuit` is a valid alternative to
`FormalCircuit` — any circuit provable under the standard pipeline is also provable
under the raw pipeline.
-/
def FormalCircuit.toRawFormalCircuit (circuit : FormalCircuit F Input Output) :
    RawFormalCircuit F Input Output :=
  { circuit with
    soundness := fun offset env input_var input h_input h_assumptions h_holds =>
      circuit.soundness offset env input_var input h_input h_assumptions
        (Circuit.can_replace_soundness h_holds) }
