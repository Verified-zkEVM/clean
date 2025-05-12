/- This file contains possible additions to the Circuit DSL that aren't currently used -/
import Clean.Circuit.Lawful

variable {F : Type} [Field F]
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

namespace ProvableType
@[circuit_norm]
def witness (compute : Environment F → α F) := do
  -- TODO this should be defined directly with `modifyGet` and return `var_from_offset α ops.offset`
  let vars ← Circuit.witness_vars (size α) (fun env => compute env |> to_elements)
  return from_vars <| vars.map Expression.var

instance : Inhabited (Circuit F (Var α F)) where
  default := witness default

instance : ConstantLawfulCircuits (witness (α:=α) (F:=F)) := by
  infer_constant_lawful_circuits
end ProvableType

def copy_to_var (x: Expression F) : Circuit F (Variable F) := do
  let x' ← witness_var x.eval
  assert_zero (x - (var x'))
  return x'

def to_var : Expression F → Circuit F (Variable F)
  | var v => pure v
  | x => copy_to_var x
