import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Structural reductions used by the `keygen_registration` tactic. -/
register_simp_attr keygen_norm

/-- Cheap operation-spine reductions run before the broader keygen normalization set. -/
register_simp_attr keygen_spine
