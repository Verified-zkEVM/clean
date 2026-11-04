module

public import Mathlib.Init
public meta import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.SimpTheorems
public meta import Lean.Meta.Tactic.Simp.RegisterCommand
public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.LabelAttribute
public import Lean.LabelAttribute

public meta section

register_simp_attr circuit_norm
register_simp_attr explicit_circuit_norm
register_simp_attr explicit_provable_type

/-- Laws of `computable_witnesses`: equations and implications that transport evaluation from a
prover environment to another one agreeing with it below some offset. A law states its two
prover environments as its first two `ProverEnvironment` binders; the tactic instantiates them
with the environments of the obligation and rewrites with the result. -/
register_label_attr computable_witnesses_law
