/- This file contains possible additions to the Circuit DSL that aren't currently used -/
import Clean.Circuit.Basic

variable {F :Type} [Field F]

namespace Provable
variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

@[simp]
def witness {F: Type} [Field F] [ProvableType F α] (compute : Environment F → α.value) :=
  let varsM := Vector.init
    (fun i => Circuit.witness (fun env => compute env |> to_values |>.get i))
  do
    let vars ← varsM.mapM
    return from_vars vars

@[simp]
def assert_equal {F: Type} [Field F] [ProvableType F α] (a a': α.var) : Circuit F Unit :=
  let vars := to_vars a
  let vars' := to_vars a'
  let eqs := (vars.zip vars').map (fun ⟨ x, x' ⟩ => Circuit.assert_zero (x - x'))
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
