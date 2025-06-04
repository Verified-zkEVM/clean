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

@[reducible] def Var (M : TypeMap) (F : Type) := M (Expression F)

variable {F : Type} [Field F]

/--
  Class of types that can be used inside a circuit,
  because they can be flattened into a vector of (field) elements.
-/
class ProvableType (M : TypeMap) where
  size : ℕ
  to_elements {F: Type} : M F -> Vector F size
  from_elements {F: Type} : Vector F size -> M F

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

class NonEmptyProvableType (M : TypeMap) extends ProvableType M where
  nonempty : size > 0 := by try simp only [size]; try norm_num

export ProvableType (size to_elements from_elements)

attribute [circuit_norm] size
-- tagged with low priority to prefer higher-level `ProvableStruct` decompositions
attribute [circuit_norm low] to_elements from_elements

variable {M : TypeMap} [ProvableType M]

@[circuit_norm]
def to_vars (var: M (Expression F)) := to_elements var

@[circuit_norm]
def from_vars (vars: Vector (Expression F) (size M)) := from_elements vars

namespace ProvableType
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

def var_from_offset (α : TypeMap) [ProvableType α] (offset : ℕ) : Var α F :=
  let vars := Vector.mapRange (size α) fun i => var ⟨offset + i⟩
  from_vars vars
end ProvableType

export ProvableType (eval const var_from_offset)

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
  from_elements v := let ⟨ .mk [x], _ ⟩ := v; x
instance : NonEmptyProvableType field where

@[reducible]
def ProvablePair (α β : TypeMap) := fun F => α F × β F

@[reducible]
def field2 := ProvablePair field field

@[circuit_norm]
instance : ProvableType field2 where
  size := 2
  to_elements pair := #v[pair.1, pair.2]
  from_elements v := (v.get 0, v.get 1)

variable {n: ℕ}
@[reducible]
def ProvableVector (α: TypeMap) (n: ℕ) := fun F => Vector (α F) n

@[reducible]
def fields (n: ℕ) := fun F => Vector F n

@[circuit_norm]
instance : ProvableType (fields n) where
  size := n
  to_elements x := x
  from_elements v := v

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

@[reducible]
def combined_size' (cs : List WithProvableType) : ℕ := cs.map (fun x => x.provable_type.size) |>.sum
end ProvableStruct

-- if we can split a type into components that are provable types, then this gives us a provable type
open ProvableStruct in
class ProvableStruct (α : TypeMap) where
  components : List WithProvableType
  to_components {F : Type} : α F → ProvableTypeList F components
  from_components {F : Type} : ProvableTypeList F components → α F

  combined_size : ℕ := combined_size' components
  combined_size_eq : combined_size = combined_size' components := by rfl

  -- for convenience, we require lawfulness by default (these tactics should always work)
  from_components_to_components : ∀ {F : Type} (x : α F),
    from_components (to_components x) = x := by
    intros; rfl
  to_components_from_components : ∀ {F : Type} (x : ProvableTypeList F components),
      to_components (from_components x) = x := by
    intro _ xs
    try rfl
    try (
      repeat rcases xs with _ | ⟨ x, xs ⟩
      rfl
    )
    done

export ProvableStruct (components to_components from_components)

attribute [circuit_norm] components to_components from_components
  ProvableStruct.combined_size ProvableStruct.combined_size'

namespace ProvableStruct
-- convert between `ProvableTypeList` and a single flat `Vector` of field elements

@[circuit_norm]
def components_to_elements {F : Type} : (cs: List WithProvableType) → ProvableTypeList F cs → Vector F (combined_size' cs)
    | [], .nil => #v[]
    | _ :: cs, .cons a as => to_elements a ++ components_to_elements cs as

@[circuit_norm]
def components_from_elements {F : Type} : (cs: List WithProvableType) → Vector F (combined_size' cs) → ProvableTypeList F cs
    | [], _ => .nil
    | c :: cs, (v : Vector F (size c.type + combined_size' cs)) =>
      let head_size := size c.type
      let tail_size := combined_size' cs
      have h_head : head_size ⊓ (head_size + tail_size) = head_size := Nat.min_add_right_self
      have h_tail : head_size + tail_size - head_size = tail_size := Nat.add_sub_self_left _ _
      let head : Vector F head_size := (v.take head_size).cast h_head
      let tail : Vector F tail_size := (v.drop head_size).cast h_tail
      .cons (from_elements head) (components_from_elements cs tail)
end ProvableStruct

open ProvableStruct in
instance ProvableType.from_struct {α : TypeMap} [ProvableStruct α] : ProvableType α where
  size := combined_size α
  to_elements x :=
    to_components x |> components_to_elements (components α) |>.cast combined_size_eq.symm
  from_elements v :=
    v.cast combined_size_eq |> components_from_elements (components α) |> from_components
  from_elements_to_elements x := by
    simp only [Vector.cast_cast, Vector.cast_rfl]
    sorry
  to_elements_from_elements x := by
    sorry

namespace ProvableStruct
variable {α : TypeMap} [ProvableStruct α] {F : Type} [Field F]

/--
Alterℕive `eval` which evaluates each component separately.
-/
@[circuit_norm]
def eval (env : Environment F) (var: α (Expression F)) : α F :=
  to_components var |> go (components α) |> from_components
where
  @[circuit_norm]
  go: (cs : List WithProvableType) → ProvableTypeList (Expression F) cs → ProvableTypeList F cs
    | [], .nil => .nil
    | _ :: cs, .cons a as => .cons (ProvableType.eval env a) (go cs as)

/--
`ProvableType.eval` === `ProvableStruct.eval`

This gets high priority and is applied before simplifying arguments,
because we prefer `ProvableStruct.eval` if it's available:
It preserves high-level components instead of unfolding everything down to field elements.
-/
@[circuit_norm ↓ high]
theorem eval_eq_eval_struct {α: TypeMap} [ProvableStruct α] : ∀ (env : Environment F) (x : Var α F),
    ProvableType.eval env x = ProvableStruct.eval env x := by
  intro env x
  symm
  simp only [eval, ProvableType.eval, from_elements, to_vars, to_elements, size]
  congr 1
  apply eval_eq_eval_struct_aux
where
  eval_eq_eval_struct_aux (env : Environment F) : (cs : List WithProvableType) → (as : ProvableTypeList (Expression F) cs) →
    eval.go env cs as = (components_to_elements cs as |> Vector.map (Expression.eval env) |> components_from_elements cs)
  | [], .nil => rfl
  | c :: cs, .cons a as => by
    simp only [components_to_elements, components_from_elements, eval.go, ProvableType.eval, to_vars]
    rw [Vector.map_append, Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]
    congr
    -- recursively use this lemma!
    apply eval_eq_eval_struct_aux

/--
Alterℕive `var_from_offset` which creates each component separately.
-/
@[circuit_norm]
def var_from_offset (α : TypeMap) [ProvableStruct α] (offset : ℕ) : Var α F :=
  go (components α) offset |> from_components (F:=Expression F)
where
  @[circuit_norm]
  go : (cs : List WithProvableType) → ℕ → ProvableTypeList (Expression F) cs
    | [], _ => .nil
    | c :: cs, offset => .cons (ProvableType.var_from_offset c.type offset) (go cs (offset + c.provable_type.size))

omit [Field F] in
/--
  `var_from_offset` === `ProvableStruct.var_from_offset`
-/
@[circuit_norm ↓ high]
theorem from_offset_eq_from_offset_struct {α: TypeMap} [ProvableStruct α] (offset : ℕ) :
    ProvableType.var_from_offset (F:=F) α offset = ProvableStruct.var_from_offset α offset := by
  symm
  simp only [var_from_offset, ProvableType.var_from_offset, from_vars, size, from_elements]
  congr
  rw [←Vector.cast_mapRange combined_size_eq.symm]
  apply from_offset_eq_from_offset_struct_aux (components α) offset
where
  from_offset_eq_from_offset_struct_aux : (cs : List WithProvableType) → (offset: ℕ) →
    var_from_offset.go cs offset = (
      Vector.mapRange (combined_size' cs) (fun i => var (F:=F) ⟨offset + i⟩) |> components_from_elements cs)
    | [], _ => rfl
    | c :: cs, offset => by
      simp only [var_from_offset.go, components_from_elements, ProvableType.var_from_offset, from_vars]
      have h_size : combined_size' (c :: cs) = size c.type + combined_size' cs := rfl
      rw [Vector.cast_mapRange h_size, Vector.mapRange_add_eq_append, Vector.cast_rfl,
        Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]
      congr
      -- recursively use this lemma
      rw [from_offset_eq_from_offset_struct_aux]
      ac_rfl
end ProvableStruct

@[circuit_norm ↓ high]
theorem eval_field {F : Type} [Field F] (env : Environment F) (x : Var field F) :
  ProvableType.eval env x = Expression.eval env x := by rfl

omit [Field F] in
@[circuit_norm ↓]
theorem var_from_offset_field (offset : ℕ) :
  var_from_offset (F:=F) field offset = var ⟨offset⟩ := by rfl

@[circuit_norm ↓]
theorem eval_fields {F : Type} [Field F] (env : Environment F) (x : Var (fields n) F) :
  ProvableType.eval env x = x.map (Expression.eval env) := rfl

omit [Field F] in
@[circuit_norm ↓]
theorem var_from_offset_fields (offset : ℕ) :
  var_from_offset (F:=F) (fields n) offset = .mapRange n fun i => var ⟨offset + i⟩ := rfl

namespace ProvableType
@[circuit_norm]
theorem eval_const {F : Type} [Field F] {α: TypeMap} [ProvableType α] (env : Environment F) (x : α F) :
  eval env (const x) = x := by
  simp only [circuit_norm, const, eval]
  rw [to_elements_from_elements, Vector.map_map]
  have : Expression.eval env ∘ Expression.const = id := by
    funext
    simp only [Function.comp_apply, Expression.eval, id_eq]
  rw [this, Vector.map_id_fun, id_eq, from_elements_to_elements]

theorem eval_var_from_offset {α: TypeMap} [ProvableType α] (env : Environment F) (offset : ℕ) :
    eval env (var_from_offset α offset) = from_elements (.mapRange (size α) fun i => env.get (offset + i)) := by
  simp only [eval, var_from_offset, to_vars, from_vars, to_elements, from_elements]
  rw [to_elements_from_elements]
  congr
  rw [Vector.ext_iff]
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]

theorem ext_iff {F : Type} {α: TypeMap} [ProvableType α] (x y : α F) :
    x = y ↔ ∀ i (hi : i < size α), (to_elements x)[i] = (to_elements y)[i] := by
  rw [←Vector.ext_iff]
  constructor
  · intro h; rw [h]
  intro h
  have h' := congrArg from_elements h
  simp only [from_elements_to_elements] at h'
  exact h'
end ProvableType

-- more concrete ProvableType instances

-- `ProvableVector`

@[reducible]
def psize (α : TypeMap) [NonEmptyProvableType α] : ℕ+ :=
  ⟨ size α, NonEmptyProvableType.nonempty⟩

instance ProvableVector.instance {α: TypeMap} [NonEmptyProvableType α] : ProvableType (ProvableVector α n) where
  size := n * size α
  to_elements x := x.map to_elements |>.flatten
  from_elements v := v.toChunks (psize α) |>.map from_elements
  from_elements_to_elements x := by
    sorry
  to_elements_from_elements v := by
    sorry

theorem eval_vector {F : Type} [Field F] {α: TypeMap} [NonEmptyProvableType α] (env : Environment F)
  (x : Var (ProvableVector α n) F) :
    eval env x = x.map (eval env) := by
  simp only [eval, to_vars, to_elements, from_elements]
  simp only [Vector.map_flatten, Vector.map_map]
  rw [Vector.flatten_toChunks]
  simp [from_elements, eval, to_vars]

theorem var_from_offset_vector {F : Type} [Field F] {α: TypeMap} [NonEmptyProvableType α] (offset : ℕ) :
    var_from_offset (F:=F) (ProvableVector α n) offset
    = .mapRange n fun i => var_from_offset α (offset + (size α)*i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Vector.mapRange_succ, ←ih]
    simp only [var_from_offset, from_vars, from_elements, size]
    rw [←Vector.map_push, Vector.toChunks_push]
    congr
    conv => rhs; congr; rhs; congr; intro i; rw [mul_comm, add_assoc]
    let create (i : ℕ) : Expression F := var ⟨ offset + i ⟩
    have h_create : (fun i => var ⟨ offset + (n * size α + i) ⟩) = (fun i ↦ create (n * size α + i)) := by rfl
    rw [h_create, ←Vector.mapRange_add_eq_append]
    have h_size_succ : (n + 1) * size α = n * size α + size α := by rw [add_mul]; ac_rfl
    rw [←Vector.cast_mapRange h_size_succ]

-- `ProvablePair`

instance ProvablePair.instance {α β: TypeMap} [ProvableType α] [ProvableType β] : ProvableType (ProvablePair α β) where
  size := size α + size β
  to_elements := fun (a, b) => to_elements a ++ to_elements b
  from_elements {F} v :=
    let a : α F := v.take (size α) |>.cast Nat.min_add_right_self |> from_elements
    let b : β F := v.drop (size α) |>.cast (Nat.add_sub_self_left _ _) |> from_elements
    (a, b)
  from_elements_to_elements x := by
    rcases x with ⟨a, b⟩
    simp only
    rw [Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]
    simp only [ProvableType.from_elements_to_elements]
  to_elements_from_elements v := by
    simp only [ProvableType.to_elements_from_elements]
    simp [Vector.cast]

@[circuit_norm ↓ high]
theorem eval_pair {α β: TypeMap} [ProvableType α] [ProvableType β] (env : Environment F)
  (a : Var α F) (b : Var β F) :
    eval (α:=ProvablePair α β) env (a, b) = (eval env a, eval env b) := by
  simp only [eval, to_vars, to_elements, from_elements, Vector.map_append]
  rw [Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]
