/- This file contains possible additions to the Circuit DSL that aren't currently used -/
import Clean.Circuit.Basic

variable {F :Type} [Field F]

namespace Provable
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

@[circuit_norm]
def witness (α: TypeMap) [inst: ProvableType α] (compute : Environment F → α F) := do
  let vars ← Circuit.witness_vars inst.size (fun env => compute env |> to_elements)
  return from_vars <| Vector.map Expression.var vars

@[circuit_norm]
def assert_equal (a a': Var α F) : Circuit F Unit :=
  let vars := to_vars a
  let vars' := to_vars a'
  let eqs := (vars.zip vars').map (fun ⟨ x, x' ⟩ => assert_zero (x - x'))
  do let _ ← eqs.mapM
end Provable

namespace Circuit
def to_var [Field F] (x: Expression F) : Circuit F (Variable F) :=
  match x with
  | var v => pure v
  | x => do
    let x' ← witness_var (fun eval => eval x)
    assert_zero (x - (var x'))
    return x'

end Circuit
