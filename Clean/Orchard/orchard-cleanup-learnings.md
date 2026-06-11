# Orchard Cleanup Learnings

Commit range: `18d7ce73^..96821754`

- Recent commits: `18d7ce73`, `0e96c5f1`, `9d3117a8`, `c63e4995`,
  `96821754`.
- Keep Halo2 method boundaries explicit. Entry circuits such as
  `witness_point`, `witness_point_non_id`, complete add, and incomplete add
  should be separate from their custom gates.
- Put custom gates under a `.Gate` namespace and give each bundled
  `FormalAssertion` the exact source gate name with a `GATE ` prefix, such as
  `"GATE witness point"` or `"GATE incomplete addition"`.
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
- Model Halo2 `copy_advice` in entry circuits by allocating copied cells with `<==`
  before passing them to a gate. The copied values, not the original API inputs, are the
  cells that participate in the source-shaped gate row.
- Prefer factoring a gate out of a useful entry-level API instead of replacing that API
  with a lower-level gate. The entry circuit is the Orchard-facing method; the gate is
  the layout assertion it invokes.
- Keep audit and map documents focused on current conformance gaps. Avoid tombstones
  about deleted or already-fixed wrong code.
