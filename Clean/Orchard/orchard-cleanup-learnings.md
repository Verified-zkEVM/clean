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
