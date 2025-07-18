import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

register_simp_attr circuit_norm
register_simp_attr explicit_circuit_norm
register_simp_attr explicit_provable_type
/-- Simp attribute for natural evaluation lemmas -/
register_simp_attr natural_eval
