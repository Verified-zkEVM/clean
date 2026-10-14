module

public import Mathlib.Init
public meta import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.SimpTheorems
public meta import Lean.Meta.Tactic.Simp.RegisterCommand
public import Lean.Meta.Tactic.Simp.RegisterCommand

public meta section

/-- The simp set used to normalize circuits and their semantics in proofs. -/
register_simp_attr circuit_norm
