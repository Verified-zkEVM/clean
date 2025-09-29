import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

register_simp_attr circuit_norm
register_simp_attr explicit_circuit_norm
register_simp_attr explicit_provable_type

-- default tactic: just run `simp only [circuit_norm, main, ...lemmas]`; this closes many trivial goals
syntax "circuit_simp" ("[" term,* "]")? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| circuit_simp $[[$terms:term,*]]?) => do
  let lemmas : Syntax.TSepArray _ _ ← (match terms with
    | some terms => terms.getElems.map fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    | none => #[]).mapM id
  evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `main):ident, $lemmas,*] at *))
