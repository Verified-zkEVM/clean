import Mathlib.Data.ZMod.Basic
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.SimpGadget

/--
'Provable types' are structured collections of field elements.

 We represent them as types generic over a single type argument (the field element),
 i.e. `Type → Type`.
-/
def TypeMap := Type → Type

def Var (M: Type → Type) (F : Type) := M (Expression F)

variable {F: Type} [Field F]

/--
  Class of types that can be used inside a circuit,
  because they can be flattened into a vector of (field) elements.
-/
class ProvableType (M : Type -> Type) where
  size : ℕ
  to_elements {F: Type} : M F -> Vector F size
  from_elements {F: Type} : Vector F size -> M F

class NonEmptyProvableType (M : Type -> Type) extends ProvableType M where
  nonempty : size > 0 := by norm_num

attribute [circuit_norm] ProvableType.size
attribute [circuit_norm] ProvableType.to_elements
attribute [circuit_norm] ProvableType.from_elements

variable {M: Type → Type} [ProvableType M]

export ProvableType (size to_elements from_elements)

@[circuit_norm]
def to_vars (var: M (Expression F)) := to_elements var

@[circuit_norm]
def from_vars (vars: Vector (Expression F) (ProvableType.size M)) := from_elements vars

@[circuit_norm]
alias to_values := to_elements
@[circuit_norm]
alias from_values := from_elements

namespace Provable
variable {α β γ: TypeMap} [ProvableType α] [ProvableType β] [ProvableType γ]

@[circuit_norm]
def eval (env: Environment F) (x: Var α F) : α F :=
  let vars := to_vars x
  let values := vars.map env
  from_values values

def const (x: α F) : Var α F :=
  let values : Vector F _ := to_values x
  from_vars (values.map .const)

@[reducible]
def unit (_: Type) := Unit

instance : ProvableType unit where
  size := 0
  to_elements _ := vec []
  from_elements _ := ()

@[reducible]
def field : Type → Type := id

@[circuit_norm]
instance : ProvableType field where
  size := 1
  to_elements x := vec [x]
  from_elements v := v.get ⟨ 0, by norm_num ⟩

@[reducible]
def pair (α β : Type → Type) := fun F => α F × β F

@[reducible]
def field2 := pair field field

@[circuit_norm]
instance : ProvableType field2 where
  size := 2
  to_elements pair := vec [pair.1, pair.2]
  from_elements v := (v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩)

variable {n: ℕ}
def vec (α: Type → Type) (n: ℕ) := fun f => Vector (α f) n

@[reducible]
def fields (n: ℕ) := vec field n

@[circuit_norm]
instance : ProvableType (fields n) where
  size := n
  to_elements x := x
  from_elements v := v

end Provable

export Provable (eval)
