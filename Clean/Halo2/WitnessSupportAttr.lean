import Lean.LabelAttribute

/-- A read-support rule: `WitnessFunctionSupport reads compute` for one shape of witness
program, universally quantified in the program's inputs. `solve_by_elim using witness_support`
closes support goals from these rules, assigning the read set by unification. -/
register_label_attr witness_support
