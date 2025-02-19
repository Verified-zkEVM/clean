import Mathlib.Data.ZMod.Basic
import Clean.Utils.Vector
import Clean.Circuit.Expression

structure TypePair where
  var (F: Type) : Type
  value (F: Type) : Type

def Var (α : TypePair) (F : Type) := α.var F
def Value (α : TypePair) (F : Type) := α.value F

variable {F: Type} [Field F] {M: Type → Type}

def TypePair.from (M: Type → Type) : TypePair where
  var F := M (Expression F)
  value F := M F

instance : Coe (Type → Type) TypePair where
  coe M := TypePair.from M

-- class of types that are composed of variables,
-- and can be evaluated into something that is composed of field elements
class ProvableType (α: TypePair) where
  size : ℕ
  to_vars {F: Type} : α.var F → Vector (Expression F) size
  from_vars {F: Type} : Vector (Expression F) size → α.var F
  to_values {F: Type} : α.value F → Vector F size
  from_values {F: Type} : Vector F size → α.value F

export ProvableType (size to_vars from_vars to_values from_values)

namespace Provable
variable {α β γ: TypePair} [ProvableType α] [ProvableType β] [ProvableType γ]

@[simp]
def eval (env: Environment F) (x: Var α F) : Value α F :=
  let vars := to_vars x
  let values := vars.map env
  from_values values

def const (x: Value α F) : Var α F :=
  let values : Vector F _ := to_values x
  from_vars (values.map .const)

@[reducible]
def unit (_: Type) := Unit

instance : ProvableType unit where
  size := 0
  to_vars _ := vec []
  from_vars _ := ()
  to_values _ := vec []
  from_values _ := ()

@[reducible]
def field : Type → Type := id

@[simp]
instance : ProvableType field where
  size := 1
  to_vars x := vec [x]
  from_vars v := v.get ⟨ 0, by norm_num ⟩
  to_values x := vec [x]
  from_values v := v.get ⟨ 0, by norm_num ⟩

@[reducible]
def pair (α β : Type → Type) := fun F => α F × β F

@[reducible]
def field2 := pair field field

@[simp]
instance : ProvableType field2 where
  size := 2
  to_vars pair := vec [pair.1, pair.2]
  from_vars v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)
  to_values pair :=vec [pair.1, pair.2]
  from_values v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)

variable {n: ℕ}
def vec (α: Type → Type) (n: ℕ) := fun f => Vector (α f) n

@[reducible]
def fields (n: ℕ) := vec field n

@[simp]
instance : ProvableType (fields n) where
  size := n
  to_vars x := x
  from_vars v := v
  to_values x := x
  from_values v := v
end Provable

export Provable (eval)
