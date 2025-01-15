import Mathlib.Data.ZMod.Basic
import Clean.Utils.Vector
import Clean.Circuit.Expression

variable {F: Type} [Field F] {s : ℕ}

structure TypePair where
  var: Type
  value: Type

/--
class of types that are composed of variables,
and can be evaluated into something that is composed of field elements
-/
class ProvableType (F: Type) (α: TypePair) (s : ℕ) where
  size : ℕ
  to_vars : α.var → Vector (Expression F s) size
  from_vars : Vector (Expression F s) size → α.var
  to_values : α.value → Vector F size
  from_values : Vector F size → α.value

namespace Provable
variable {α β γ: TypePair} [ProvableType F α s] [ProvableType F β s] [ProvableType F γ s]

@[simp]
def eval_env (env: Fin s → F) (x: α.var) : α.value :=
  let n := ProvableType.size F α s
  let vars : Vector (Expression F s) n := ProvableType.to_vars x
  let values := vars.map (fun v => v.eval_env env)
  ProvableType.from_values values

def const (F: Type) [ProvableType F α s] (x: α.value) : α.var :=
  let n := ProvableType.size F α s
  let values : Vector F n := ProvableType.to_values x
  ProvableType.from_vars (values.map (fun v => Expression.const v))

@[reducible]
def unit : TypePair := ⟨ Unit, Unit ⟩

instance : ProvableType F unit s where
  size := 0
  to_vars _ := vec []
  from_vars _ := ()
  to_values _ := vec []
  from_values _ := ()

@[reducible]
def field (F : Type) : TypePair := ⟨ Expression F s, F ⟩

@[simp]
instance : ProvableType F (field F (s:=s)) s where
  size := 1
  to_vars x := vec [x]
  from_vars v := v.get ⟨ 0, by norm_num ⟩
  to_values x := vec [x]
  from_values v := v.get ⟨ 0, by norm_num ⟩

@[reducible]
def pair (α β : TypePair) : TypePair := ⟨ α.var × β.var, α.value × β.value ⟩

@[reducible]
def field2 (F : Type) : TypePair := pair (field F (s:=s)) (field F (s:=s))

@[simp]
instance : ProvableType F (field2 F (s:=s)) s where
  size := 2
  to_vars pair := vec [pair.1, pair.2]
  from_vars v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)
  to_values pair :=vec [pair.1, pair.2]
  from_values v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)

variable {n: ℕ}
def vec (α: TypePair) (n: ℕ) : TypePair := ⟨ Vector α.var n, Vector α.value n ⟩

@[reducible]
def fields (F: Type) (n: ℕ) : TypePair := vec (field F (s:=s)) n

@[simp]
instance : ProvableType F (fields F n (s:=s)) s where
  size := n
  to_vars x := x
  from_vars v := v
  to_values x := x
  from_values v := v
end Provable
