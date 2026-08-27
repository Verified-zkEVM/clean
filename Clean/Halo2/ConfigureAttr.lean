import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Structural reductions for configure-time selector requirements. -/
register_simp_attr configure_selector_norm

/-- Structural reductions for configure-time query requirements. -/
register_simp_attr configure_query_norm
