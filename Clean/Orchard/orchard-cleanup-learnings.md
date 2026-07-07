# Orchard Cleanup Learnings

Commit range: `6451581a^..0e96c5f1`

- Model Halo2 method boundaries explicitly. `witness_point` and
  `witness_point_non_id` are entry circuits, while `"GATE witness point"` and
  `"GATE witness non-identity point"` are custom gates under `.Gate`.
- Do not add gate calls just to restate an input assumption. Complete addition takes
  already-assigned points, so it should call the complete-add gate and use point validity
  as its API precondition.
- Avoid extra constraints that are not enabled by the source helper. The non-identity
  point mux selects between non-identity inputs; its output curve property follows from
  the mux spec and input assumptions, not from an additional witness-point gate.
- For simple entry circuits, prefer inline `FormalCircuit` /
  `GeneralFormalCircuit.WithHint` definitions. Factoring out `main`, `Spec`, and proofs
  is useful for large circuits, but can obscure tiny wrappers.
- Omit fields whose defaults already say exactly what is intended, such as
  `Assumptions := True`.
- Model Halo2 `Value<T>` inputs with Clean's hint-aware circuit types:
  `Unconstrained T` / `UnconstrainedDep T` plus `GeneralFormalCircuit.WithHint`.
- When witnessing a high-level structured value, use `witness` on that high-level type
  instead of manually splitting it into coordinate-level `witnessField` calls. This keeps
  the Clean code closer to the Halo2 API and reduces proof noise.
- For elliptic-curve closure facts, use the established theorem layer in
  `Clean/Orchard/Specs/Elliptic` and add small bridge lemmas as needed. Do not brute-force
  large affine-coordinate preservation proofs inside circuit files with `field_simp` and
  `ring_nf`.
- Keep Lean module filenames and namespaces aligned with the actual Halo2 source module
  names, not with illustrative examples in the plan. For example, source
  `add_incomplete.rs` / `mod add_incomplete` maps to Lean `AddIncomplete`, not
  `IncompleteAdd`.
- Order circuit namespaces as complete packages: define the gate package first when it
  corresponds to `configure`/`create_gate`, then define the source-level entry circuit
  package with its `main`, `Assumptions`, `Spec`, and proofs.
- Use dot notation for namespaced point operations when it makes the code shorter and
  clearer, such as `input.p.onCurve`, `input.p.isIdentityEncoding`, and `output.coords`.
- Avoid unnecessary struct type annotations. Let Lean infer literals such as
  `outputValue { p := ..., q := ... }` and `Gate.circuit { ... }` when the expected type
  is already clear.
- Name gate input bundles by their role in Clean, usually `Input`, even when they contain
  multiple Halo2 rows. Preserve Halo2 column names and rotation structure inside the
  fields, such as `x_qr : CurrentNext F`.
- Prefer theorem names that follow mathlib directionality, such as
  `polys_zero_of_outputValue` and `eq_outputValue_of_polys_zero`.
- Do not assume Gregor is wrong about Lean syntax or conventions. If something he
  suggests does not immediately work, investigate the local namespace/import context
  before substituting a different style.
- Do not over-nest namespaces just because source files live in nested directories. Use
  the shortest namespace that communicates the concept, and enter it directly when
  defining a new namespace.
- Lean can enter nested namespaces in one command, such as
  `namespace Orchard.Specs.Pallas`; use that instead of stacked namespace blocks when it
  is clearer.
- When proof automation can see through copied values, prefer short proof scripts using
  `set`, `specialize`, `simp only`, and existing helper theorems over manually rebuilding
  full gate input records in the proof.

Pow5 review: <https://github.com/Verified-zkEVM/clean/pull/405#pullrequestreview-3430008781>

- For multi-component namespaces, use dotted namespace declarations such as
  `namespace Orchard.Poseidon.Permute`; do not stack `namespace Orchard`,
  `namespace Poseidon`, `namespace Permute` blocks.
- Put a custom gate and its source-level wrapper next to each other in the same source
  namespace: `FullRound.Gate.circuit` followed by `FullRound.main` /
  `FullRound.circuit`, and similarly for `PartialRounds`.
- Expose Orchard field names by namespace export (`export Ecc (Fp Fq)`) instead of abbrev
  aliases, and use those Orchard-level names in Orchard gadget code.
- Keep large ported constants and their arithmetic proof lemmas in constants modules, not
  inline with gadget/chip code.
- Remove unused source markers, compatibility wrappers, explanatory dead-code notes, and
  imports immediately; dead or decorative code is a style violation even when harmless.
- Namespace-local gate input bundles should be named `Input`, not ad-hoc names like `Row`,
  especially when a gate spans more than one Halo2 row.
- Do not factor tiny one-off gate expressions into named helpers when Halo2 writes them
  inline. Both layers are wrong: `output0 := ...` for a one-line gate expression, and
  `next0Check := output0 params row - row.next0` for its residual. These are not useful
  abstractions; they are non-source-shaped indirection. Inline such expressions in the
  gate `main` / assertion list unless the helper names a real Halo2 concept or is
  substantively reused.
- Use the unqualified exported Orchard names, not `Ecc.`-qualified ones. `Ecc.Defs`
  does `export Ecc (Fp Fq)` and defines `Point`, and Orchard gadget files sit under
  the `Orchard.Ecc.*` namespace, so write `Fp`, `Fq`, `Point`, `Add.circuit`,
  `AddIncomplete.circuit` — never `Ecc.Fp`, `Point`, `Ecc.Add.circuit`. (The sibling
  `FullWidth`/`Short` files already do this; match them.)
- Use Clean's existing top-level `IsBool` (from `Gadgets.Boolean`) and its lemmas, not a
  per-namespace re-definition. Do not redefine `IsBool`/`ternary` in a local `Defs` module
  when an exported one exists.
- State point-valued circuit specs at the `Point` level, e.g. `output = s • B` (or
  the point itself), not by projecting coordinates: avoid
  `output.coords = ((s • B.point).x, (s • B.point).y)`. The `.x`/`.coords` projection in a
  contract is ugly and non-semantic; use the high-level point equality.
