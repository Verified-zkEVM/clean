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

class LawfulProvableType (M : TypeMap) extends ProvableType M where
  to_elements_from_elements {F: Type} : ∀ v: Vector F size, to_elements (from_elements v) = v
    := by
    intro _
    try (simp; done)
    try (
      intro ⟨ .mk l ,  h_size⟩
      simp [size] at h_size
      repeat (
        cases l
        try simp at h_size
        rename_i _ l h_size
        try (simp at h_size; subst h_size; rfl)
      )
    )
    done
  from_elements_to_elements {F: Type} : ∀ x: M F, from_elements (to_elements x) = x
    := by intros; rfl

namespace Provable
variable {α β γ: TypeMap} [ProvableType α] [ProvableType β] [ProvableType γ]

/--
Evaluate a variable in the given environment.

Note: this is not tagged with `circuit_norm`, to enable higher-level `ProvableStruct`
decompositions. Sometimes you will need to add `eval` to the simp set manually.
-/
def eval (env: Environment F) (x: Var α F) : α F :=
  let vars := to_vars x
  let values := vars.map (Expression.eval env)
  from_elements values

def const (x: α F) : Var α F :=
  let values : Vector F _ := to_elements x
  from_vars (values.map .const)

@[reducible]
def unit (_: Type) := Unit

instance : LawfulProvableType unit where
  size := 0
  to_elements _ := #v[]
  from_elements _ := ()

@[reducible]
def field : TypeMap := id

@[circuit_norm]
instance : LawfulProvableType field where
  size := 1
  to_elements x := #v[x]
  from_elements v := v.get 0

@[reducible]
def pair (α β : TypeMap) := fun F => α F × β F

@[reducible]
def field2 := pair field field

@[circuit_norm]
instance : LawfulProvableType field2 where
  size := 2
  to_elements pair := #v[pair.1, pair.2]
  from_elements v := (v.get 0, v.get 1)

variable {n: ℕ}
def vec (α: TypeMap) (n: ℕ) := fun F => Vector (α F) n

@[reducible]
def fields (n: ℕ) := vec field n

@[circuit_norm]
instance : LawfulProvableType (fields n) where
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

export Provable (eval const field)

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

  combined_size : ℕ := components.map (fun x => x.provable_type.size) |>.sum
  combined_size_eq : combined_size = (components.map (fun x => x.provable_type.size) |>.sum) := by rfl

export ProvableStruct (components to_components from_components)

def ProvableStruct.combined_size' (cs : List WithProvableType) : ℕ :=
  cs.map (fun x => x.provable_type.size) |>.sum

attribute [circuit_norm] components to_components from_components
  ProvableStruct.combined_size ProvableStruct.combined_size'

lemma ProvableStruct.combined_size'_eq {α : TypeMap} [ProvableStruct α] :
    combined_size' (components α) = combined_size α := by
  symm; apply combined_size_eq

open ProvableStruct in
instance ProvableType.from_struct {α : TypeMap} [ProvableStruct α] : ProvableType α where
  size := combined_size α
  to_elements {F} (x : α F) :=
    go_to_elements F (components α) (to_components x) |>.cast combined_size'_eq
  from_elements {F} (v : Vector F (combined_size α)) :=
    from_components (go_from_elements F (components α) (v.cast combined_size'_eq.symm))
  where
  go_to_elements (F : Type) : (cs: List WithProvableType) → ProvableTypeList F cs → Vector F (combined_size' cs)
    | [], .nil => #v[]
    | c :: cs, .cons a as => (c.provable_type.to_elements a) ++ go_to_elements F cs as
  go_from_elements (F : Type) : (cs: List WithProvableType) → Vector F (combined_size' cs) → ProvableTypeList F cs
    | [], _ => .nil
    | c :: cs, (v : Vector F (c.provable_type.size + combined_size' cs)) =>
      let size := c.provable_type.size
      have h_take : size ⊓ (size + combined_size' cs) = size := Nat.min_add_right
      have h_drop : size + combined_size' cs - size = combined_size' cs := Nat.add_sub_self_left size (combined_size' cs)
      let head : Vector F size := (v.take size).cast h_take
      let tail : Vector F (combined_size' cs) := (v.drop size).cast h_drop
      .cons (c.provable_type.from_elements head) (go_from_elements F cs tail)

attribute [circuit_norm] ProvableType.from_struct.go_to_elements ProvableType.from_struct.go_from_elements

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

-- helper lemma to prove `eval_struct`
lemma eval_struct_aux (env : Environment F) : (cs : List WithProvableType) → (as : ProvableTypeList (Expression F) cs) →
    eval.go_map env cs as =
      ProvableType.from_struct.go_from_elements F cs (
        Vector.map (Expression.eval env) (ProvableType.from_struct.go_to_elements (Expression F) cs as))
  | [], .nil => rfl
  | c :: cs, .cons a as => by
    unfold ProvableType.from_struct.go_to_elements ProvableType.from_struct.go_from_elements eval.go_map Provable.eval to_vars
    simp only
    -- two equalities needed below
    have h_size : size c.type = (Array.map (fun x ↦ Expression.eval env x) (to_elements a).toArray).toList.length := by simp
    have h_combined_size : combined_size' cs = (Array.map (fun x ↦ Expression.eval env x)
      (ProvableType.from_struct.go_to_elements (Expression F) cs as).toArray).toList.length := by simp
    congr
    simp only [Vector.map_append, Vector.take_eq_extract, Vector.extract, Nat.sub_zero,
      Vector.toArray_append, Vector.toArray_map, Vector.cast_mk, Vector.eq_mk]
    -- move to List and back to use `List.take` theorems; should be abstracted
    rw [← Array.toArray_toList (_ ++ _), List.extract_toArray, Array.toList_append,
        List.extract_eq_drop_take, List.drop_zero, Nat.sub_zero, List.take_append_of_le_length (Nat.le_of_eq h_size),
        List.take_of_length_le (Nat.le_of_eq h_size.symm), List.toArray_toList]

    -- recursively use this lemma!
    rw [eval_struct_aux]
    congr
    simp only [Vector.map_append, Vector.drop_eq_cast_extract, Vector.extract,
      Vector.toArray_append, Vector.toArray_map, Vector.cast_mk, Vector.eq_mk]
    -- move to List to use `List.drop` theorems; should be abstracted
    rw [← Array.toArray_toList (_ ++ _), List.extract_toArray, Array.toList_append,
        List.extract_eq_drop_take, Nat.add_sub_self_left, List.drop_append_of_le_length (Nat.le_of_eq h_size),
        List.drop_of_length_le (Nat.le_of_eq h_size.symm), List.nil_append,
        List.take_of_length_le (Nat.le_of_eq (h_combined_size.symm)), List.toArray_toList]

/--
`eval` = split into `ProvableStruct` components and `eval` them

this gets high priority and is applied before simplifying arguments,
to ensure we preserve `ProvableStruct` components instead of going all the way down to field elements.
-/
@[circuit_norm ↓ high]
lemma eval_struct {α: TypeMap} [ProvableStruct α] : ∀ (env : Environment F) (x : Var α F),
    Provable.eval env x = ProvableStruct.eval env x := by
  intro env x
  symm
  simp only [eval, Provable.eval, from_elements, to_vars, to_elements, size]
  congr 1
  apply eval_struct_aux
end ProvableStruct

@[circuit_norm ↓ high]
lemma eval_field {F : Type} [Field F] (env : Environment F) (x : Var Provable.field F) :
  eval env x = x.eval env := by rfl

namespace LawfulProvableType
@[circuit_norm]
lemma eval_const {F : Type} [Field F] {α: TypeMap} [LawfulProvableType α] (env : Environment F) (x : α F) :
  eval env (const x) = x := by
  simp only [circuit_norm, const, eval]
  rw [to_elements_from_elements, Vector.map_map]
  have : Expression.eval env ∘ Expression.const = id := by
    funext
    simp only [Function.comp_apply, Expression.eval, id_eq]
  rw [this, Vector.map_id_fun, id_eq, from_elements_to_elements]
end LawfulProvableType
