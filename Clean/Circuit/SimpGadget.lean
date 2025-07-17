import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

register_simp_attr circuit_norm
-- DEPRECATED: Use specific simplification lemmas (e.g., toSubcircuit_soundness, toSubcircuit_completeness) instead
-- TODO: Remove subcircuit_norm usage from the codebase
register_simp_attr subcircuit_norm
register_simp_attr explicit_circuit_norm
register_simp_attr explicit_provable_type
