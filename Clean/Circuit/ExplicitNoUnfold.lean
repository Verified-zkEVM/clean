import Lean

open Lean

/-- Heads tagged with this attribute are semantic circuit constructors for explicit inference.
`infer_explicit_circuits` may unfold user wrappers around circuits, but it must not unfold these heads
because doing so destroys the shape used by explicit instances and loop dispatch. -/
register_label_attr explicit_circuit_no_unfold
