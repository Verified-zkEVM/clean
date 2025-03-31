import Mathlib.Data.ZMod.Basic
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.SimpGadget

/--
'Provable types' are structured collections of field elements.

 We represent them as types generic over a single type argument (the field element),
 i.e. `Type → Type`.
-/
@[reducible]
def TypeMap := Type → Type

def Var (M : TypeMap) (F : Type) := M (Expression F)

variable {F : Type} [Field F]

/--
  Class of types that can be used inside a circuit,
  because they can be flattened into a vector of (field) elements.
-/
class ProvableType (M : TypeMap) where
  size : ℕ
  to_elements {F: Type} : M F -> Vector F size
  from_elements {F: Type} : Vector F size -> M F

class NonEmptyProvableType (M : TypeMap) extends ProvableType M where
  nonempty : size > 0 := by norm_num

attribute [circuit_norm] ProvableType.size
attribute [circuit_norm] ProvableType.to_elements
attribute [circuit_norm] ProvableType.from_elements

variable {M : TypeMap} [ProvableType M]

export ProvableType (size to_elements from_elements)

@[circuit_norm]
def to_vars (var: M (Expression F)) := to_elements var

@[circuit_norm]
def from_vars (vars: Vector (Expression F) (ProvableType.size M)) := from_elements vars

namespace Provable
variable {α β γ: TypeMap} [ProvableType α] [ProvableType β] [ProvableType γ]

@[circuit_norm]
def eval (env: Environment F) (x: Var α F) : α F :=
  let vars := to_vars x
  let values := vars.map env
  from_elements values

def const (x: α F) : Var α F :=
  let values : Vector F _ := to_elements x
  from_vars (values.map .const)

@[reducible]
def unit (_: Type) := Unit

instance : ProvableType unit where
  size := 0
  to_elements _ := #v[]
  from_elements _ := ()

@[reducible]
def field : TypeMap := id

@[circuit_norm]
instance : ProvableType field where
  size := 1
  to_elements x := #v[x]
  from_elements v := v.get 0

@[reducible]
def pair (α β : TypeMap) := fun F => α F × β F

@[reducible]
def field2 := pair field field

@[circuit_norm]
instance : ProvableType field2 where
  size := 2
  to_elements pair := #v[pair.1, pair.2]
  from_elements v := (v.get 0, v.get 1)

variable {n: ℕ}
def vec (α: TypeMap) (n: ℕ) := fun F => Vector (α F) n

@[reducible]
def fields (n: ℕ) := vec field n

@[circuit_norm]
instance : ProvableType (fields n) where
  size := n
  to_elements x := x
  from_elements v := v

/--
  Vector of provable types of the same size.
-/
def vec_provable (α: TypeMap) [ProvableType α] (n: ℕ) : TypeMap :=
  fun F => Vector (α F) n

@[circuit_norm]
instance {α: TypeMap} [ProvableType α] : ProvableType (vec_provable α n) where
  size := n * ProvableType.size α
  to_elements x := x.map to_elements |> .flatten
  from_elements {F} v := aux F n v
    where
    aux (F : Type) : (s : ℕ) -> Vector F (s * size α) -> Vector (α F) s
    | 0, _ => #v[]
    | s + 1, v =>
      let v0 : Vector _ (ProvableType.size α) := (v.take <| ProvableType.size α).cast (by
        simp only [Nat.add_one_mul, le_add_iff_nonneg_left, zero_le, inf_of_le_left])
      let inner_provable : α _ := ProvableType.from_elements v0
      let rest := aux F s ((v.drop <| ProvableType.size α).cast (by
        simp only [Nat.add_one_mul, add_tsub_cancel_right]))
      #v[inner_provable].append rest |> .cast (by rw [add_comm])


def synthesize_value : α F :=
  let zeros := Vector.fill (size α) 0
  from_elements zeros

instance [Field F] : Inhabited (α F) where
  default := synthesize_value

def synthesize_const_var : Var α F :=
  let zeros := Vector.fill (size α) 0
  from_vars (zeros.map .const)

instance [Field F] : Inhabited (Var α F) where
  default := synthesize_const_var
end Provable

export Provable (eval vec_provable)
