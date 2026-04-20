# FormalCircuitWithInteractions Full Soundness Plan

## Goal
Prove a foundational theorem in `Clean/Circuit/Foundations.lean`:

- `ConstraintsHold` + `Operations.FullGuarantees`
- imply
- `Spec` + `Operations.FullRequirements`

for `FormalCircuitWithInteractions`.

## Constraints
- Do not change the `FormalCircuitWithInteractions` user-facing interface.
- Minimize user-facing proof obligations.
- Focus on soundness first; defer completeness work.

## Important Prioritization
- We **do not** care about filling sorries in `toSubcircuit` proofs for:
  - `FormalCircuit`
  - `FormalAssertion`
  - `GeneralFormalCircuit`
- It is acceptable to place `sorry` in `Clean/Circuit/Subcircuit.lean` for those three paths.
- A key objective is to fill the current sorries in
  `FormalCircuitWithInteractions.toSubcircuit`.

## Core Design Choice
Update the subcircuit soundness contract (soundness-side only):

- `Subcircuit.imply_soundness` should use constraints + guarantees and produce both:
  - `Soundness`
  - local `FlatOperation.Requirements`

This keeps `Subcircuit.Soundness` spec-like while making requirements propagation explicit.

## Implementation Steps
1. Complete the `FormalCircuitWithInteractions.toSubcircuit` soundness proof path.
2. Add internal replacement lemmas needed to derive recursive requirements from:
   - recursive constraints,
   - recursive full guarantees,
   - top-level requirements from `FormalCircuitWithInteractions.soundness`.
3. Complete `FormalCircuitWithInteractions.original_full_soundness` in `Foundations.lean`.
4. Revisit example files only after the foundational theorem is in place.
