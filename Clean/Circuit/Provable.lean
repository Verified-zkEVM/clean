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

/--
`Var M F` is the type of variables that appear in the monadic notation of
`Circuit F _`s. Most elements of `Var M F`, especially interesting ones, are not
constant values of `M F` because variables in a circuit can depend on contents of
the environment.

An element of `Var M F` represents a `M F` that's polynomially dependent
on the environment. More concretely, an element of `Var M F` is a value of `M F`
with missing holes, and each hole contains a polynomial that can refer to fixed
positions of the environment. Given an environment, `Var M F` can be evaluated
to a `M F` (see `eval` below).
-/
@[reducible] def Var (M : TypeMap) (F : Type) := M (Expression F)

variable {F : Type} [Field F]

/--
  Class of types that can be used inside a circuit,
  because they can be flattened into a vector of (field) elements.
-/
class ProvableType (M : TypeMap) where
  size : ℕ
  toElements {F: Type} : M F -> Vector F size
  fromElements {F: Type} : Vector F size -> M F

  toElements_fromElements {F: Type} : ∀ v: Vector F size, toElements (fromElements v) = v := by
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
  fromElements_toElements {F: Type} : ∀ x: M F, fromElements (toElements x) = x
    := by intros; rfl

class NonEmptyProvableType (M : TypeMap) extends ProvableType M where
  nonempty : size > 0 := by try simp only [size]; try norm_num

export ProvableType (size toElements fromElements)

attribute [circuit_norm] size
-- tagged with low priority to prefer higher-level `ProvableStruct` decompositions
-- note that this is not added to `circuit_norm`, since in general we won't need or want
-- to explicitly unfold provable type definitions
attribute [explicit_provable_type low] toElements fromElements

variable {M : TypeMap} [ProvableType M]

@[circuit_norm]
def toVars (var: M (Expression F)) := toElements var

@[circuit_norm]
def fromVars (vars: Vector (Expression F) (size M)) := fromElements vars

namespace ProvableType
variable {α β γ: TypeMap} [ProvableType α] [ProvableType β] [ProvableType γ]

/--
Evaluate a variable in the given environment.

Note: this is not tagged with `circuit_norm`, to enable higher-level `ProvableStruct`
decompositions. Sometimes you will need to add `explicit_provable_type` to the simp set.
-/
@[explicit_provable_type]
def eval (env: Environment F) (x: Var α F) : α F :=
  let vars := toVars x
  let values := vars.map (Expression.eval env)
  fromElements values

/-- `ProvableType.eval` is the normal form. This is needed to simplify lookup constraints. -/
@[circuit_norm]
theorem fromElements_eval_toElements {env : Environment F} (x : α (Expression F)) :
  fromElements (Vector.map (Expression.eval env) (toElements x)) = eval env x := rfl

def const (x: α F) : Var α F :=
  let values : Vector F _ := toElements x
  fromVars (values.map .const)

def synthesizeValue : α F :=
  let zeros := Vector.fill (size α) 0
  fromElements zeros

instance [Field F] : Inhabited (α F) where
  default := synthesizeValue

def synthesizeConstVar : Var α F :=
  let zeros := Vector.fill (size α) 0
  fromVars (zeros.map .const)

instance [Field F] : Inhabited (Var α F) where
  default := synthesizeConstVar

@[explicit_provable_type]
def varFromOffset (α : TypeMap) [ProvableType α] (offset : ℕ) : Var α F :=
  let vars := Vector.mapRange (size α) fun i => var ⟨offset + i⟩
  fromVars vars

-- under `explicit_provable_type`, it makes sense to fully resolve `mapRange` as well
attribute [explicit_provable_type] Vector.mapRange_succ Vector.mapRange_zero
end ProvableType

export ProvableType (eval const varFromOffset)

@[reducible]
def unit (_: Type) := Unit

instance : ProvableType unit where
  size := 0
  toElements _ := #v[]
  fromElements _ := ()

@[reducible] def field : TypeMap := id

@[reducible] def fieldVar (F : Type) := field (Expression F)

@[circuit_norm]
instance : ProvableType field where
  size := 1
  toElements x := #v[x]
  fromElements := fun ⟨⟨[x]⟩, _⟩ => x
instance : NonEmptyProvableType field where

@[reducible]
def ProvablePair (α β : TypeMap) := fun F => α F × β F

@[reducible]
def fieldPair : TypeMap := fun F => F × F

@[reducible]
def fieldTriple : TypeMap := fun F => F × F × F

instance : ProvableType fieldPair where
  size := 2
  toElements := fun (x, y) => #v[x, y]
  fromElements := fun ⟨⟨[x, y]⟩, _ ⟩ => (x, y)
instance : NonEmptyProvableType fieldPair where

instance : ProvableType fieldTriple where
  size := 3
  toElements := fun (x, y, z) => #v[x, y, z]
  fromElements := fun ⟨⟨[x, y, z]⟩, _ ⟩ => (x, y, z)
instance : NonEmptyProvableType fieldTriple where

variable {n: ℕ}
@[reducible]
def ProvableVector (α: TypeMap) (n: ℕ) := fun F => Vector (α F) n

@[reducible]
def fields (n: ℕ) := fun F => Vector F n

@[circuit_norm]
instance : ProvableType (fields n) where
  size := n
  toElements x := x
  fromElements v := v

namespace ProvableStruct
structure WithProvableType where
  type : TypeMap
  provableType : ProvableType type := by infer_instance

instance {c : WithProvableType} : ProvableType c.type := c.provableType

instance {α: TypeMap} [ProvableType α] : CoeDep TypeMap (α) WithProvableType where
  coe := { type := α }

-- custom heterogeneous list
inductive ProvableTypeList (F: Type) : List WithProvableType → Type 1 where
| nil : ProvableTypeList F []
| cons : ∀ {a : WithProvableType} {as : List WithProvableType}, a.type F → ProvableTypeList F as → ProvableTypeList F (a :: as)

@[reducible]
def combinedSize' (cs : List WithProvableType) : ℕ := cs.map (fun x => x.provableType.size) |>.sum
end ProvableStruct

-- if we can split a type into components that are provable types, then this gives us a provable type
open ProvableStruct in
class ProvableStruct (α : TypeMap) where
  components : List WithProvableType
  toComponents {F : Type} : α F → ProvableTypeList F components
  fromComponents {F : Type} : ProvableTypeList F components → α F

  combinedSize : ℕ := combinedSize' components
  combinedSize_eq : combinedSize = combinedSize' components := by rfl

  -- for convenience, we require lawfulness by default (these tactics should always work)
  fromComponents_toComponents : ∀ {F : Type} (x : α F),
    fromComponents (toComponents x) = x := by
    intros; rfl
  toComponents_fromComponents : ∀ {F : Type} (x : ProvableTypeList F components),
      toComponents (fromComponents x) = x := by
    intro _ xs
    try rfl
    try (
      repeat rcases xs with _ | ⟨ x, xs ⟩
      rfl
    )
    done

export ProvableStruct (components toComponents fromComponents)

attribute [circuit_norm] components toComponents fromComponents
  ProvableStruct.combinedSize ProvableStruct.combinedSize'

namespace ProvableStruct
-- convert between `ProvableTypeList` and a single flat `Vector` of field elements

@[circuit_norm]
def componentsToElements {F : Type} : (cs: List WithProvableType) → ProvableTypeList F cs → Vector F (combinedSize' cs)
  | [], .nil => #v[]
  | _ :: cs, .cons a as => toElements a ++ componentsToElements cs as

@[circuit_norm]
def componentsFromElements {F : Type} : (cs: List WithProvableType) → Vector F (combinedSize' cs) → ProvableTypeList F cs
  | [], _ => .nil
  | c :: cs, (v : Vector F (size c.type + combinedSize' cs)) =>
    let head_size := size c.type
    let tail_size := combinedSize' cs
    have h_head : head_size ⊓ (head_size + tail_size) = head_size := Nat.min_add_right_self
    have h_tail : head_size + tail_size - head_size = tail_size := Nat.add_sub_self_left _ _
    let head : Vector F head_size := (v.take head_size).cast h_head
    let tail : Vector F tail_size := (v.drop head_size).cast h_tail
    .cons (fromElements head) (componentsFromElements cs tail)

variable {F : Type}

theorem fromElements_toElements {F} : (cs: List WithProvableType) → (xs : ProvableTypeList F cs) →
    componentsFromElements cs (componentsToElements cs xs) = xs
  | [], .nil => rfl
  | c :: cs, .cons a as => by
    rw [componentsFromElements, componentsToElements,
      Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length,
      ProvableType.fromElements_toElements, fromElements_toElements]

theorem toElements_fromElements {F} : (cs: List WithProvableType) → (xs : Vector F (combinedSize' cs)) →
    componentsToElements cs (componentsFromElements cs xs) = xs
  | [], ⟨ .mk [], _ ⟩ => rfl
  | c :: cs, (v : Vector F (size c.type + combinedSize' cs)) => by
    simp only [componentsToElements, componentsFromElements,
      toElements_fromElements, ProvableType.toElements_fromElements]
    rw [Vector.append_take_drop]
end ProvableStruct

open ProvableStruct in
instance ProvableType.fromStruct {α : TypeMap} [ProvableStruct α] : ProvableType α where
  size := combinedSize α
  toElements x :=
    toComponents x |> componentsToElements (components α) |>.cast combinedSize_eq.symm
  fromElements v :=
    v.cast combinedSize_eq |> componentsFromElements (components α) |> fromComponents
  fromElements_toElements x := by
    simp only [Vector.cast_cast, Vector.cast_rfl]
    rw [ProvableStruct.fromElements_toElements, fromComponents_toComponents]
  toElements_fromElements x := by
    rw [toComponents_fromComponents, ProvableStruct.toElements_fromElements]
    simp only [Vector.cast_cast, Vector.cast_rfl]

namespace ProvableStruct
variable {α : TypeMap} [ProvableStruct α] {F : Type} [Field F]

/--
Alternative `eval` which evaluates each component separately.
-/
@[circuit_norm]
def eval (env : Environment F) (var: α (Expression F)) : α F :=
  toComponents var |> go (components α) |> fromComponents
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
theorem eval_eq_eval {α: TypeMap} [ProvableStruct α] : ∀ (env : Environment F) (x : Var α F),
    ProvableType.eval env x = ProvableStruct.eval env x := by
  intro env x
  symm
  simp only [eval, ProvableType.eval, fromElements, toVars, toElements, size]
  congr 1
  apply eval_eq_eval_aux
where
  eval_eq_eval_aux (env : Environment F) : (cs : List WithProvableType) → (as : ProvableTypeList (Expression F) cs) →
    eval.go env cs as = (componentsToElements cs as |> Vector.map (Expression.eval env) |> componentsFromElements cs)
  | [], .nil => rfl
  | c :: cs, .cons a as => by
    simp only [componentsToElements, componentsFromElements, eval.go, ProvableType.eval, toVars]
    rw [Vector.map_append, Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]
    congr
    -- recursively use this lemma!
    apply eval_eq_eval_aux

/--
Alternative `varFromOffset` which creates each component separately.
-/
@[circuit_norm]
def varFromOffset (α : TypeMap) [ProvableStruct α] (offset : ℕ) : Var α F :=
  go (components α) offset |> fromComponents (F:=Expression F)
where
  @[circuit_norm]
  go : (cs : List WithProvableType) → ℕ → ProvableTypeList (Expression F) cs
    | [], _ => .nil
    | c :: cs, offset => .cons (ProvableType.varFromOffset c.type offset) (go cs (offset + c.provableType.size))

omit [Field F] in
/--
  `varFromOffset` === `ProvableStruct.varFromOffset`
-/
@[circuit_norm ↓ high]
theorem varFromOffset_eq_varFromOffset {α: TypeMap} [ProvableStruct α] (offset : ℕ) :
    ProvableType.varFromOffset (F:=F) α offset = ProvableStruct.varFromOffset α offset := by
  symm
  simp only [varFromOffset, ProvableType.varFromOffset, fromVars, size, fromElements]
  congr
  rw [←Vector.cast_mapRange combinedSize_eq.symm]
  apply varFromOffset_eq_varFromOffset_aux (components α) offset
where
  varFromOffset_eq_varFromOffset_aux : (cs : List WithProvableType) → (offset: ℕ) →
    varFromOffset.go cs offset = (
      Vector.mapRange (combinedSize' cs) (fun i => var (F:=F) ⟨offset + i⟩) |> componentsFromElements cs)
    | [], _ => rfl
    | c :: cs, offset => by
      simp only [varFromOffset.go, componentsFromElements, ProvableType.varFromOffset, fromVars]
      have h_size : combinedSize' (c :: cs) = size c.type + combinedSize' cs := rfl
      rw [Vector.cast_mapRange h_size, Vector.mapRange_add_eq_append, Vector.cast_rfl,
        Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]
      congr
      -- recursively use this lemma
      rw [varFromOffset_eq_varFromOffset_aux]
      ac_rfl
end ProvableStruct

namespace ProvableType
variable {α: TypeMap} [ProvableType α]

-- resolve `eval` and `varFromOffset` for a few basic types

@[circuit_norm ↓ high]
theorem eval_field {F : Type} [Field F] (env : Environment F) (x : Var field F) :
  ProvableType.eval env x = Expression.eval env x := by rfl

@[circuit_norm ↓]
theorem varFromOffset_field {F} (offset : ℕ) :
  varFromOffset (F:=F) field offset = var ⟨offset⟩ := by rfl

@[circuit_norm ↓]
theorem eval_fields {F : Type} [Field F] (env : Environment F) (x : Var (fields n) F) :
  ProvableType.eval env x = x.map (Expression.eval env) := rfl

@[circuit_norm ↓]
theorem varFromOffset_fields {F} (offset : ℕ) :
  varFromOffset (F:=F) (fields n) offset = .mapRange n fun i => var ⟨offset + i⟩ := rfl

@[circuit_norm ↓]
theorem eval_fieldPair {F : Type} [Field F] (env : Environment F) (t : Var fieldPair F) :
  ProvableType.eval env t = (match t with | (x, y) => (Expression.eval env x, Expression.eval env y)) := rfl

@[circuit_norm ↓]
theorem eval_fieldTriple {F : Type} [Field F] (env : Environment F) (t : Var fieldTriple F) :
  ProvableType.eval env t = (match t with
    | (x, y, z) => (Expression.eval env x, Expression.eval env y, Expression.eval env z)) := rfl

@[circuit_norm ↓]
theorem varFromOffset_fieldPair {F} (offset : ℕ) :
  varFromOffset (F:=F) fieldPair offset = (var ⟨offset⟩, var ⟨offset + 1⟩) := rfl

@[circuit_norm ↓]
theorem varFromOffset_fieldTriple {F} (offset : ℕ) :
  varFromOffset (F:=F) fieldTriple offset = (var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩) := rfl

-- a few general lemmas about provable types

lemma toElements_comp_fromElements {F} :
    toElements ∘ @fromElements α _ F = id := by
  funext x
  simp [toElements_fromElements]

lemma fromElements_comp_toElements {F} :
    fromElements ∘ @toElements α _ F = id := by
  funext x
  simp [fromElements_toElements]

@[circuit_norm]
theorem eval_const {F : Type} [Field F] {α: TypeMap} [ProvableType α] {env : Environment F} {x : α F} :
    eval env (const x) = x := by
  simp only [const, fromVars, explicit_provable_type, toVars]
  rw [toElements_fromElements, Vector.map_map]
  have : Expression.eval env ∘ Expression.const = id := by
    funext
    simp only [Function.comp_apply, Expression.eval, id_eq]
  rw [this, Vector.map_id_fun, id_eq, fromElements_toElements]

theorem eval_varFromOffset {α: TypeMap} [ProvableType α] (env : Environment F) (offset : ℕ) :
    eval env (varFromOffset α offset) = fromElements (.mapRange (size α) fun i => env.get (offset + i)) := by
  simp only [eval, varFromOffset, toVars, fromVars, toElements, fromElements]
  rw [toElements_fromElements]
  congr
  rw [Vector.ext_iff]
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]

theorem ext_iff {F : Type} {α: TypeMap} [ProvableType α] (x y : α F) :
    x = y ↔ ∀ i (hi : i < size α), (toElements x)[i] = (toElements y)[i] := by
  rw [←Vector.ext_iff]
  constructor
  · intro h; rw [h]
  intro h
  have h' := congrArg fromElements h
  simp only [fromElements_toElements] at h'
  exact h'

theorem eval_fromElements {F : Type} [Field F] {α: TypeMap} [ProvableType α] (env : Environment F)
  (xs : Vector (Expression F) (size α)) :
    eval env (fromElements (F:=Expression F) xs) = fromElements (xs.map env) := by
  simp only [eval, toVars, fromVars, toElements_fromElements]

theorem eval_fromVars {F : Type} [Field F] {α: TypeMap} [ProvableType α] (env : Environment F)
  (xs : Vector (Expression F) (size α)) :
    eval env (fromVars xs) = fromElements (xs.map env) := eval_fromElements ..

theorem getElem_eval_toElements {F : Type} [Field F] {α: TypeMap} [ProvableType α]
  {env : Environment F} (x : α (Expression F)) (i : ℕ) (hi : i < size α) :
    Expression.eval env (toElements x)[i] = (toElements (eval env x))[i] := by
  rw [eval, toElements_fromElements, Vector.getElem_map, toVars]

theorem getElem_eval_toVars {F : Type} [Field F] {α: TypeMap} [ProvableType α]
  {env : Environment F} (x : Var α F) (i : ℕ) (hi : i < size α) :
    Expression.eval env (toVars x)[i] = (toElements (eval env x))[i] := getElem_eval_toElements ..
end ProvableType

-- more concrete ProvableType instances

-- `ProvableVector`
section
variable {n: ℕ} {α: TypeMap} [NonEmptyProvableType α]

@[reducible]
def psize (α : TypeMap) [NonEmptyProvableType α] : ℕ+ :=
  ⟨ size α, NonEmptyProvableType.nonempty⟩

instance ProvableVector.instance : ProvableType (ProvableVector α n) where
  size := n * size α
  toElements x := x.map toElements |>.flatten
  fromElements v := v.toChunks (psize α) |>.map fromElements
  fromElements_toElements x := by
    rw [Vector.flatten_toChunks, Vector.map_map, ProvableType.fromElements_comp_toElements, Vector.map_id]
  toElements_fromElements v := by
    rw [Vector.map_map, ProvableType.toElements_comp_fromElements, Vector.map_id, Vector.toChunks_flatten]

theorem eval_vector (env : Environment F)
  (x : Var (ProvableVector α n) F) :
    eval env x = x.map (eval env) := by
  simp only [eval, toVars, toElements, fromElements]
  simp only [Vector.map_flatten, Vector.map_map]
  rw [Vector.flatten_toChunks]
  simp [fromElements, eval, toVars]

theorem getElem_eval_vector (env : Environment F) (x : Var (ProvableVector α n) F) (i : ℕ) (h : i < n) :
    (eval env x[i]) = (eval env x)[i] := by
  rw [eval_vector, Vector.getElem_map]

theorem varFromOffset_vector {F : Type} [Field F] {α: TypeMap} [NonEmptyProvableType α] (offset : ℕ) :
    varFromOffset (F:=F) (ProvableVector α n) offset
    = .mapRange n fun i => varFromOffset α (offset + (size α)*i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Vector.mapRange_succ, ←ih]
    simp only [varFromOffset, fromVars, fromElements, size]
    rw [←Vector.map_push, Vector.toChunks_push]
    congr
    conv => rhs; congr; rhs; congr; intro i; rw [mul_comm, add_assoc]
    let create (i : ℕ) : Expression F := var ⟨ offset + i ⟩
    have h_create : (fun i => var ⟨ offset + (n * size α + i) ⟩) = (fun i ↦ create (n * size α + i)) := by rfl
    rw [h_create, ←Vector.mapRange_add_eq_append]
    have h_size_succ : (n + 1) * size α = n * size α + size α := by rw [add_mul]; ac_rfl
    rw [←Vector.cast_mapRange h_size_succ]
end

-- `ProvablePair`

instance ProvablePair.instance {α β: TypeMap} [ProvableType α] [ProvableType β] : ProvableType (ProvablePair α β) where
  size := size α + size β
  toElements := fun (a, b) => toElements a ++ toElements b
  fromElements {F} v :=
    let a : α F := v.take (size α) |>.cast Nat.min_add_right_self |> fromElements
    let b : β F := v.drop (size α) |>.cast (Nat.add_sub_self_left _ _) |> fromElements
    (a, b)
  fromElements_toElements x := by
    rcases x with ⟨a, b⟩
    simp only [Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length,
      ProvableType.fromElements_toElements]
  toElements_fromElements v := by
    simp [ProvableType.toElements_fromElements, Vector.cast]

instance {α β: TypeMap} [NonEmptyProvableType α] [NonEmptyProvableType β] :
  NonEmptyProvableType (ProvablePair α β) where
  nonempty := by
    simp only [ProvablePair.instance, size]
    have h1 := NonEmptyProvableType.nonempty (M := α)
    have h2 := NonEmptyProvableType.nonempty (M := β)
    omega

def ProvablePair.fromElements {α β: TypeMap} [ProvableType α] [ProvableType β] (xs : Vector F (size α + size β)) : α F × β F :=
  (ProvableType.fromElements xs : ProvablePair α β F)

def ProvablePair.toElements {α β: TypeMap} [ProvableType α] [ProvableType β] (pair : α F × β F) : Vector F (size α + size β) :=
  ProvableType.toElements (M:=ProvablePair α β) pair

@[circuit_norm ↓ high]
theorem eval_pair {α β: TypeMap} [ProvableType α] [ProvableType β] (env : Environment F)
  (a : Var α F) (b : Var β F) :
    eval (α:=ProvablePair α β) env (a, b) = (eval env a, eval env b) := by
  simp only [eval, toVars, toElements, fromElements, Vector.map_append]
  rw [Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]

omit [Field F] in
@[circuit_norm ↓ high]
theorem varFromOffset_pair {α β: TypeMap} [ProvableType α] [ProvableType β] (offset : ℕ) :
    varFromOffset (F:=F) (ProvablePair α β) offset
    = (varFromOffset α offset, varFromOffset β (offset + size α)) := by
  simp only [varFromOffset, fromVars, ProvablePair.instance]
  rw [Vector.mapRange_add_eq_append, Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length]
  ac_rfl

-- be able to use `field (Expression F)` in expressions

instance : HAdd (field (Expression F)) (Expression F) (Expression F) where
  hAdd (x : Expression F) y := x + y
instance : HAdd (Expression F) (field (Expression F)) (Expression F) where
  hAdd x (y : Expression F) := x + y
instance : HAdd (field (Expression F)) (field (Expression F)) (field (Expression F)) where
  hAdd (a : Expression F) (b : Expression F) := a + b

instance : HSub (field (Expression F)) (Expression F) (Expression F) where
  hSub (x : Expression F) y := x - y
instance : HSub (Expression F) (field (Expression F)) (Expression F) where
  hSub x (y : Expression F) := x - y
instance : HSub (field (Expression F)) (field (Expression F)) (field (Expression F)) where
  hSub (a : Expression F) (b : Expression F) := a - b

instance : HMul (field (Expression F)) (Expression F) (Expression F) where
  hMul (x : Expression F) y := x * y
instance : HMul (Expression F) (field (Expression F)) (Expression F) where
  hMul x (y : Expression F) := x * y
instance : HMul F (field (Expression F)) (field (Expression F)) where
  hMul x y : Expression F := x * y
instance : HMul (field (Expression F)) F (field (Expression F)) where
  hMul x y : Expression F := x * y
instance : HMul (field (Expression F)) (field (Expression F)) (field (Expression F)) where
  hMul (a : Expression F) (b : Expression F) := a * b

instance : Inv (field F) where
  inv (x : F) : F := x⁻¹

instance {n: ℕ} [OfNat F n] : OfNat (field F) n where
  ofNat : F := OfNat.ofNat n

instance [Coe ℕ F] : Coe ℕ (field F) where
  coe n : F := n
instance [CoeOut ℕ F] : CoeOut ℕ (field F) where
  coe n : F := n
instance [CoeTail ℕ F] : CoeTail ℕ (field F) where
  coe n : F := n
instance [CoeHead ℕ F] : CoeHead ℕ (field F) where
  coe n : F := n

instance [DecidableEq F] : DecidableEq (field F) :=
  inferInstanceAs (DecidableEq F)
