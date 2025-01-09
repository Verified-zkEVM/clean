/- This file contains possible additions to the Circuit DSL that aren't currently used -/
import Clean.Circuit.Basic

variable {F :Type} [Field F]

namespace Provable
variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

@[simp]
def witness {F: Type} [Field F] [ProvableType F α] (compute : Unit → α.value) :=
  let n := ProvableType.size F α
  let values : Vector F n := ProvableType.to_values (compute ())
  let varsM : Vector (Circuit F (Expression F)) n := values.map (fun v => Circuit.witness (fun () => v))
  do
    let vars ← varsM.mapM
    return ProvableType.from_vars vars

@[simp]
def assert_equal {F: Type} [Field F] [ProvableType F α] (a a': α.var) : Circuit F Unit :=
  let n := ProvableType.size F α
  let vars: Vector (Expression F) n := ProvableType.to_vars a
  let vars': Vector (Expression F) n := ProvableType.to_vars a'
  let eqs := (vars.zip vars').map (fun ⟨ x, x' ⟩ => Circuit.assert_zero (x - x'))
  do let _ ← eqs.mapM
end Provable

namespace Circuit
def to_var [Field F] (x: Expression F) : Circuit F (Variable F) :=
  match x with
  | Expression.var v => pure v
  | x => do
    let x' ← witness_var (fun _ => x.eval)
    assert_zero (x - (Expression.var x'))
    return x'

-- inputs, already connected to a cell, that you can assign the next row's value of
-- TODO figure out if this is the best way to connect to a trace
structure InputCell (F : Type) where
  cell: { cell: Cell F // cell.row = RowIndex.Current }
  var: Variable F

def InputCell.set_next [Field F] (c: InputCell F) (v: Expression F) := do
  let v' ← to_var v
  assign_cell { c.cell.val with row := RowIndex.Next } v'

instance : Coe (InputCell F) (Variable F) where
  coe x := x.var
end Circuit
