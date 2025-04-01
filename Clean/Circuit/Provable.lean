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

export ProvableType (size to_elements from_elements)

attribute [circuit_norm] size
-- tagged with low priority to prefer higher-level `ProvableStruct` decompositions
attribute [circuit_norm low] to_elements from_elements

variable {M : TypeMap} [ProvableType M]


@[circuit_norm]
def to_vars (var: M (Expression F)) := to_elements var

@[circuit_norm]
def from_vars (vars: Vector (Expression F) (size M)) := from_elements vars

namespace Provable
variable {α β γ: TypeMap} [ProvableType α] [ProvableType β] [ProvableType γ]

-- tagged with low priority to prefer higher-level `ProvableStruct` decompositions
@[circuit_norm low]
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

@[circuit_norm]
def from_offset (α : TypeMap) [ProvableType α] (offset : Nat) : Var α F :=
  let vars := Vector.init fun i => ⟨offset + i⟩
  from_vars <| vars.map Expression.var
end Provable

export Provable (eval)

namespace ProvableStruct
structure WithProvableType where
  type : TypeMap
  provable_type : ProvableType type := by infer_instance

instance {c : WithProvableType} : ProvableType c.type := c.provable_type

instance {α: TypeMap} [ProvableType α] : CoeDep TypeMap (α) WithProvableType where
  coe := { type := α }

-- custom heterogeneous list
inductive ProvableTypeList (F: Type) : List WithProvableType → Type 1 where
| nil : ProvableTypeList F []
| cons : ∀ {a : WithProvableType} {as : List WithProvableType}, a.type F → ProvableTypeList F as → ProvableTypeList F (a :: as)
end ProvableStruct

-- if we can split a type into components that are provable types, then this gives us a provable type
class ProvableStruct (α : TypeMap) where
  components : List ProvableStruct.WithProvableType
  to_components {F} : α F → ProvableStruct.ProvableTypeList F components
  from_components {F} : ProvableStruct.ProvableTypeList F components → α F

export ProvableStruct (components to_components from_components)

attribute [circuit_norm] to_components
attribute [circuit_norm] from_components

def ProvableStruct.combined_size (cs : List WithProvableType) : ℕ :=
  cs.map (fun x => x.provable_type.size) |>.sum

open ProvableStruct in
instance ProvableType.from_struct {α : TypeMap} [ProvableStruct α] : ProvableType α where
  size := combined_size (ProvableStruct.components α)
  to_elements {F} (x : α F) :=
    go_to_elements F (ProvableStruct.components α) (ProvableStruct.to_components x)
  from_elements {F} (v : Vector F (combined_size (ProvableStruct.components α))) :=
    ProvableStruct.from_components (go_from_elements F (ProvableStruct.components α) v)
  where
  go_to_elements (F : Type) : (cs: List WithProvableType) → ProvableTypeList F cs → Vector F (combined_size cs)
    | [], .nil => #v[]
    | c :: cs, .cons a as => (c.provable_type.to_elements a) ++ go_to_elements F cs as
  go_from_elements (F : Type) : (cs: List WithProvableType) → Vector F (combined_size cs) → ProvableTypeList F cs
    | [], _ => .nil
    | c :: cs, (v : Vector F (c.provable_type.size + combined_size cs)) =>
      let size := c.provable_type.size
      have h_take : size ⊓ (size + combined_size cs) = size := Nat.min_add_right
      have h_drop : size + combined_size cs - size = combined_size cs := Nat.add_sub_self_left size (combined_size cs)
      let head : Vector F size := h_take ▸ v.take size
      let tail : Vector F (combined_size cs) := h_drop ▸ v.drop size
      .cons (c.provable_type.from_elements head) (go_from_elements F cs tail)

namespace ProvableStruct
variable {α : TypeMap} [ProvableStruct α] {F : Type} [Field F]

@[circuit_norm ↓ high]
def eval (env : Environment F) (var: α (Expression F)) : α F :=
  go_map (components α) (to_components var) |> from_components
  where
  @[circuit_norm]
  go_map: (cs : List WithProvableType) → ProvableTypeList (Expression F) cs → ProvableTypeList F cs
    | [], .nil => .nil
    | _ :: cs, .cons a as => .cons (Provable.eval env a) (go_map cs as)

@[circuit_norm ↓ high]
lemma eval_struct {α: TypeMap} [ProvableStruct α] : ∀ (env : Environment F) (x : Var α F),
    Provable.eval env x = ProvableStruct.eval env x := by
  sorry
end ProvableStruct

@[circuit_norm ↓ high]
lemma eval_field {F : Type} [Field F] (env : Environment F) (x : Var Provable.field F) :
  eval env x = x.eval env := by rfl
