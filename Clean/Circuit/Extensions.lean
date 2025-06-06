/- This file contains possible additions to the Circuit DSL that aren't currently used -/
import Clean.Circuit.Constant

variable {F : Type} [Field F]

instance {α: TypeMap} [ProvableType α] : Inhabited (Circuit F (Var α F)) where
  default := ProvableType.witness default

def copy_to_var (x: Expression F) : Circuit F (Variable F) := do
  let x' ← witness_var x.eval
  assert_zero (x - (var x'))
  return x'

def to_var : Expression F → Circuit F (Variable F)
  | var v => pure v
  | x => copy_to_var x
