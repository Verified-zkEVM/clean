import Mathlib.Data.ZMod.Basic
import Clean.Utils.Vector
import Clean.Circuit.Expression

variable {F: Type} [Field F]

structure TypePair where
  var: Type
  value: Type

-- class of types that are composed of variables,
-- and can be evaluated into something that is composed of field elements
class ProvableType (F: Type) (α: TypePair) where
  size : ℕ
  to_vars : α.var → Vector (Expression F) size
  from_vars : Vector (Expression F) size → α.var
  to_values : α.value → Vector F size
  from_values : Vector F size → α.value

export ProvableType (size to_vars from_vars to_values from_values)

namespace Provable
variable {α β γ: TypePair} [ProvableType F α] [ProvableType F β] [ProvableType F γ]

@[simp]
def eval (env: Environment F) (x: α.var) : α.value :=
  let vars := to_vars x
  let values := vars.map env
  from_values values

def const (F: Type) [ProvableType F α] (x: α.value) : α.var :=
  let values : Vector F _ := to_values x
  from_vars (values.map .const)

@[reducible]
def unit : TypePair := ⟨ Unit, Unit ⟩

instance : ProvableType F unit where
  size := 0
  to_vars _ := vec []
  from_vars _ := ()
  to_values _ := vec []
  from_values _ := ()

@[reducible]
def field (F : Type) : TypePair := ⟨ Expression F, F ⟩

@[simp]
instance : ProvableType F (field F) where
  size := 1
  to_vars x := vec [x]
  from_vars v := v.get ⟨ 0, by norm_num ⟩
  to_values x := vec [x]
  from_values v := v.get ⟨ 0, by norm_num ⟩

@[reducible]
def pair (α β : TypePair) : TypePair := ⟨ α.var × β.var, α.value × β.value ⟩

@[reducible]
def field2 (F : Type) : TypePair := pair (field F) (field F)

@[simp]
instance : ProvableType F (field2 F) where
  size := 2
  to_vars pair := vec [pair.1, pair.2]
  from_vars v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)
  to_values pair :=vec [pair.1, pair.2]
  from_values v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)

variable {n: ℕ}
def vec (α: TypePair) (n: ℕ) : TypePair := ⟨ Vector α.var n, Vector α.value n ⟩

@[reducible]
def fields (F: Type) (n: ℕ) : TypePair := vec (field F) n

@[simp]
instance : ProvableType F (fields F n) where
  size := n
  to_vars x := x
  from_vars v := v
  to_values x := x
  from_values v := v
end Provable

export Provable (eval)
