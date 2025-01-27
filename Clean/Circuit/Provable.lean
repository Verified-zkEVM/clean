import Mathlib.Data.ZMod.Basic
import Clean.Utils.Vector
import Clean.Circuit.Expression

variable {F: Type} [Field F]

def TypePair := Type → Type
def TypePair.var (t: TypePair) (F) := t (Expression F)
def TypePair.value (t: TypePair) (F) := t F

-- class of types that are composed of variables,
-- and can be evaluated into something that is composed of field elements
class ProvableType (F: Type) (α: TypePair) where
  size : ℕ
  to_vars : α.var F → Vector (Expression F) size
  from_vars : Vector (Expression F) size → α.var F
  to_values : α.value F → Vector F size
  from_values : Vector F size → α.value F

namespace Provable
variable {α β γ: TypePair} [ProvableType F α] [ProvableType F β] [ProvableType F γ]

@[simp]
def eval (env: Environment F) (x: α.var F) : α.value F :=
  let n := ProvableType.size F α
  let vars : Vector (Expression F) n := ProvableType.to_vars x
  let values := vars.map env
  ProvableType.from_values values

def const [ProvableType F α] (x: α.value F) : α.var F :=
  let n := ProvableType.size F α
  let values : Vector F n := ProvableType.to_values x
  ProvableType.from_vars (values.map (fun v => Expression.const v))

@[reducible]
def unit : TypePair := fun _ => Unit

instance : ProvableType F unit where
  size := 0
  to_vars _ := vec []
  from_vars _ := ()
  to_values _ := vec []
  from_values _ := ()

@[reducible]
def field : TypePair := id

@[simp]
instance : ProvableType F field where
  size := 1
  to_vars x := vec [x]
  from_vars v := v.get ⟨ 0, by norm_num ⟩
  to_values x := vec [x]
  from_values v := v.get ⟨ 0, by norm_num ⟩

@[reducible]
def pair (α β : TypePair) : TypePair := fun f => α f × β f

@[reducible]
def field2 : TypePair := pair field field

@[simp]
instance : ProvableType F field2 where
  size := 2
  to_vars pair := vec [pair.1, pair.2]
  from_vars v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)
  to_values pair :=vec [pair.1, pair.2]
  from_values v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)

variable {n: ℕ}
def vec (α: TypePair) (n: ℕ) : TypePair := fun f => Vector (α f) n

@[reducible]
def fields (n: ℕ) : TypePair := vec field n

@[simp]
instance : ProvableType F (fields n) where
  size := n
  to_vars x := x
  from_vars v := v
  to_values x := x
  from_values v := v
end Provable
