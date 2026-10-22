module

public import CleanCompStark.Transfer
public import Clean.Examples.KeccakAir.Component

/-!
# The Keccak-f component is bridgeable

`bridgeable (component height) = true`, proved by the shape of the constraints rather than by
evaluating them: every constraint is written over the cells of the current and the next row with
`+`, `-`, `*` and numerals, and multiplied by at most one selector, at the top or as the left
factor of a product that is the left factor of the constraint (`when_transition` of
`1 - step_flags[23]`).

A `Shape` abstracts an expression: `plain` (it reads only cells of the two rows), a `selector`, a
`gated` constraint (`splitSelector` takes its selector off and leaves a plain body), or `bad`.
Shapes have the operations of the constraints, and so do expressions paired with a shape that
describes them (`Tagged`). The constraints of the component's variables are the first components of
the constraints of the variables tagged with their shapes (`IsHom.map_constraints`), and the shapes
of those are the constraints of the cells' shapes, all of them `plain` or `gated`
(`gateable_constraints`), which `simp` shows family by family. The window's variables enter only
through where their cells are (`VarWindow`), so no proof evaluates the 3182 constraints or the
5269 variables.
-/

@[expose] public section

namespace CleanCompStark.KeccakAir
open Air.Flat Air.Flat.WitnessGeneration Backends _root_.KeccakAir

/-- The shape of an expression of a window. -/
inductive Shape where
  /-- Reads only cells of the current and the next row. -/
  | plain
  /-- A selector cell. -/
  | selector (gate : Gate)
  /-- A selector times a plain body, as `splitSelector` splits it. -/
  | gated (gate : Gate)
  /-- Any other expression. -/
  | bad

namespace Shape

/-- The shape of a sum or a difference. -/
def add : Shape → Shape → Shape
  | plain, plain => plain
  | _, _ => bad

/-- The shape of a product. -/
def mul : Shape → Shape → Shape
  | plain, plain => plain
  | selector gate, plain | plain, selector gate => gated gate
  | gated gate, plain | plain, gated gate => gated gate
  | _, _ => bad

instance : Add Shape := ⟨add⟩
instance : Sub Shape := ⟨add⟩
instance : Mul Shape := ⟨mul⟩
instance {n : ℕ} : OfNat Shape n := ⟨plain⟩

/-- A constraint of this shape can be split into a gate and a body. -/
def Gateable : Shape → Prop
  | plain | gated _ => True
  | selector _ | bad => False

@[simp] lemma plain_add_plain : plain + plain = plain := rfl
@[simp] lemma plain_sub_plain : plain - plain = plain := rfl
@[simp] lemma plain_mul_plain : plain * plain = plain := rfl
@[simp] lemma selector_mul_plain (gate : Gate) : selector gate * plain = gated gate := rfl
@[simp] lemma gated_mul_plain (gate : Gate) : gated gate * plain = gated gate := rfl
@[simp] lemma one_eq_plain : (1 : Shape) = plain := rfl
@[simp] lemma two_eq_plain : (2 : Shape) = plain := rfl
@[simp] lemma four_eq_plain : (4 : Shape) = plain := rfl
@[simp] lemma gateable_plain : Gateable plain := trivial
@[simp] lemma gateable_gated (gate : Gate) : Gateable (gated gate) := trivial

@[simp] lemma boolCheck_plain : boolCheck plain = plain := rfl
@[simp] lemma xor_plain : xor plain plain = plain := rfl
@[simp] lemma andn_plain : andn plain plain = plain := rfl

lemma horner_plain (n : ℕ) : horner (fun _ => plain) n = plain := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [horner, ih]; rfl

@[simp] lemma limbOf_plain (limb : Fin 4) : limbOf (fun _ => plain) limb = plain :=
  horner_plain 15

@[simp] lemma iotaBit_plain {α : Type} (flags : Vector α 24) (z : Fin 64) :
    iotaBit (flags.map fun _ => plain) plain z = plain := by
  have hfold (rounds : List (Fin 24)) (sum : Shape) (hsum : sum = plain) :
      rounds.foldl (fun sum (r : Fin 24) => sum + (flags.map fun _ => plain)[r]) sum =
        plain := by
    induction rounds generalizing sum with
    | nil => exact hsum
    | cons r rounds ih =>
      rw [List.foldl_cons]
      exact ih _ (by rw [hsum, getElem_map_fin]; rfl)
  unfold iotaBit
  split
  · rfl
  · rw [hfold _ _ (getElem_map_fin _ _ _)]
    rfl

end Shape

/-- The shapes of a window whose rows are plain. -/
def plainWindow {α : Type} (current next : Row α) : Window Row Shape where
  current := current.map fun _ => .plain
  next := next.map fun _ => .plain
  isFirstRow := .selector .firstRow
  isLastRow := .selector .lastRow
  isTransition := .selector .transition

/-- The shapes of the constraints of a window whose rows are plain are `plain` or `gated`. -/
theorem gateable_constraints {α : Type} (current next : Row α) :
    ∀ s ∈ constraints (plainWindow current next), s.Gateable := by
  simp only [plainWindow, constraints, roundFlagConstraints, preimageConstraints,
    exportConstraints, thetaColumnConstraints, thetaConstraints, parityConstraints,
    chiConstraints, iotaConstraints, outputConstraints, transitionInPermutation,
    List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap, Row.map_stepFlags,
    Row.map_exportFlag, Row.map_aPrimePrime00Bits, Row.map_aPrimePrimePrime00Limbs,
    Row.map_preimageLimb, Row.map_aLimb, Row.map_cBit, Row.map_cPrimeBit, Row.map_aPrimeBit,
    Row.map_aPrimePrimeLimb, Row.map_b, Row.map_aPrimePrimePrimeLimb, Vector.getElem_ofFn,
    Fin.getElem_fin, Vector.getElem_map, Shape.plain_add_plain,
    Shape.plain_sub_plain, Shape.plain_mul_plain, Shape.selector_mul_plain, Shape.gated_mul_plain,
    Shape.one_eq_plain, Shape.two_eq_plain, Shape.four_eq_plain, Shape.boolCheck_plain,
    Shape.xor_plain, Shape.andn_plain, Shape.limbOf_plain, Shape.iotaBit_plain, or_imp,
    forall_and, forall_exists_index, and_imp,
    forall_eq, implies_true, Shape.gateable_plain, Shape.gateable_gated,
    List.not_mem_nil, false_imp_iff, and_self]
  and_intros <;> first | trivial | (intros; subst_vars; trivial)

/-! ### Expressions with a shape -/

section Tagged
variable {F : Type} (w : ℕ)

/-- An expression reads only cells of the current and the next row, of `w` cells each. -/
def Plain (x : Expression F) : Prop := ∀ j ∈ expressionCells x, j < 2 * w

instance : DecidablePred (Plain (F := F) w) := fun _ => by unfold Plain; infer_instance

/-- An expression has a shape, for rows of `w` cells. -/
def Good : Expression F × Shape → Prop
  | (x, .plain) => Plain w x
  | (x, .selector gate) => selectorGate? w x = some gate
  | (x, .gated gate) => (∃ body, splitSelector w x = some (gate, body) ∧ Plain w body) ∧
      ∀ j ∈ expressionCells x, j < 2 * w + 3
  | (_, .bad) => True

variable {w}

lemma Plain.left {x y : Expression F}
    (h : ∀ j ∈ expressionCells x ++ expressionCells y, j < 2 * w) :
    Plain w x := fun j hj => h j (List.mem_append_left _ hj)

lemma Plain.right {x y : Expression F}
    (h : ∀ j ∈ expressionCells x ++ expressionCells y, j < 2 * w) :
    Plain w y := fun j hj => h j (List.mem_append_right _ hj)

lemma Plain.append {x y : Expression F} (hx : Plain w x) (hy : Plain w y) :
    ∀ j ∈ expressionCells x ++ expressionCells y, j < 2 * w := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  exacts [hx j hj, hy j hj]

lemma Plain.lt {x : Expression F} (h : Plain w x) : ∀ j ∈ expressionCells x, j < 2 * w + 3 :=
  fun j hj => by have := h j hj; omega

lemma selectorGate?_of_plain {x : Expression F} (h : Plain w x) : selectorGate? w x = none := by
  cases x with
  | var v =>
    have := h v.index (by simp [expressionCells])
    simp only [selectorGate?]
    split_ifs <;> first | rfl | omega
  | const _ | add _ _ | mul _ _ => rfl

lemma splitSelector_of_plain : ∀ {x : Expression F}, Plain w x → splitSelector w x = none
  | .var _, _ | .const _, _ | .add _ _, _ => rfl
  | .mul a b, h => by
    have ha : Plain w a := Plain.left h
    have hb : Plain w b := Plain.right h
    simp only [splitSelector, selectorGate?_of_plain ha, selectorGate?_of_plain hb,
      splitSelector_of_plain ha, splitSelector_of_plain hb, Option.map_none]

lemma selectorGate?_of_splitSelector {x : Expression F} {gate : Gate} {body : Expression F}
    (h : splitSelector w x = some (gate, body)) : selectorGate? w x = none := by
  cases x with
  | mul _ _ => rfl
  | var _ | const _ | add _ _ => simp [splitSelector] at h

lemma cells_of_selectorGate? {x : Expression F} {gate : Gate} (h : selectorGate? w x = some gate) :
    ∀ j ∈ expressionCells x, j < 2 * w + 3 := by
  cases x with
  | var v =>
    intro j hj
    simp only [expressionCells, List.mem_singleton] at hj
    subst hj
    simp only [selectorGate?] at h
    split_ifs at h <;> omega
  | const _ | add _ _ | mul _ _ => simp [selectorGate?] at h

lemma cells_append_lt {x y : Expression F} (hx : ∀ j ∈ expressionCells x, j < 2 * w + 3)
    (hy : ∀ j ∈ expressionCells y, j < 2 * w + 3) :
    ∀ j ∈ expressionCells x ++ expressionCells y, j < 2 * w + 3 := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  exacts [hx j hj, hy j hj]

theorem good_add {x y : Expression F} {s t : Shape} (hx : Good w (x, s)) (hy : Good w (y, t)) :
    Good w (x + y, s + t) := by
  cases s <;> cases t <;> first | trivial | exact Plain.append hx hy

theorem good_sub [FiniteField F] {x y : Expression F} {s t : Shape} (hx : Good w (x, s))
    (hy : Good w (y, t)) :
    Good w (x - y, s - t) := by
  have hneg (hy : Plain w y) : Plain w (.mul (.const (-1)) y) :=
    Plain.append (x := .const (-1)) (fun _ h => by simp [expressionCells] at h) hy
  cases s <;> cases t <;> first | trivial | exact Plain.append hx (hneg hy)

theorem good_mul {x y : Expression F} {s t : Shape} (hx : Good w (x, s)) (hy : Good w (y, t)) :
    Good w (x * y, s * t) := by
  cases s <;> cases t <;> try trivial
  case plain.plain => exact Plain.append hx hy
  case plain.selector =>
    refine ⟨⟨x, ?_, hx⟩, cells_append_lt hx.lt (cells_of_selectorGate? hy)⟩
    have hy : selectorGate? w y = some _ := hy
    show splitSelector w (.mul x y) = _
    simp only [splitSelector, selectorGate?_of_plain hx, hy]
  case plain.gated =>
    obtain ⟨⟨body, hsplit, hbody⟩, hcells⟩ := hy
    refine ⟨⟨.mul x body, ?_, Plain.append hx hbody⟩, cells_append_lt hx.lt hcells⟩
    show splitSelector w (.mul x y) = _
    simp only [splitSelector, selectorGate?_of_plain hx, selectorGate?_of_splitSelector hsplit,
      splitSelector_of_plain hx, hsplit, Option.map_some]
  case selector.plain =>
    refine ⟨⟨y, ?_, hy⟩, cells_append_lt (cells_of_selectorGate? hx) hy.lt⟩
    have hx : selectorGate? w x = some _ := hx
    show splitSelector w (.mul x y) = _
    simp only [splitSelector, hx]
  case gated.plain =>
    obtain ⟨⟨body, hsplit, hbody⟩, hcells⟩ := hx
    refine ⟨⟨.mul body y, ?_, Plain.append hbody hy⟩, cells_append_lt hcells hy.lt⟩
    show splitSelector w (.mul x y) = _
    simp only [splitSelector, selectorGate?_of_splitSelector hsplit, selectorGate?_of_plain hy,
      hsplit]

/-- A constraint of a gateable shape splits into a gate and a body, and reads cells of the
window. -/
theorem gateConstraint_of_good {x : Expression F} {s : Shape} (hx : Good w (x, s))
    (hs : s.Gateable) : (gateConstraint (some w) x).isSome ∧
      ∀ j ∈ expressionCells x, j < 2 * w + 3 := by
  have hreads (y : Expression F) (hy : Plain w y) :
      (expressionCells y).any (fun cell => 2 * w ≤ cell && cell < 2 * w + 3) = false := by
    simp only [List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
    intro j hj h
    have := hy j hj
    omega
  cases s with
  | plain =>
    refine ⟨?_, Plain.lt hx⟩
    simp [gateConstraint, hreads x hx]
  | gated gate =>
    obtain ⟨⟨body, hsplit, hbody⟩, hcells⟩ := hx
    refine ⟨?_, hcells⟩
    simp only [gateConstraint]
    split
    · rfl
    · simp only [hsplit, hreads body hbody, Option.bind_eq_bind, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte, Option.isSome_some]
  | selector _ | bad => exact hs.elim

variable (w)

/-- Expressions with a shape that describes them. -/
def Tagged [FiniteField F] : Type := {t : Expression F × Shape // Good w t}

instance [FiniteField F] : Add (Tagged (F := F) w) :=
  ⟨fun a b => ⟨(a.1.1 + b.1.1, a.1.2 + b.1.2), good_add a.2 b.2⟩⟩
instance [FiniteField F] : Sub (Tagged (F := F) w) :=
  ⟨fun a b => ⟨(a.1.1 - b.1.1, a.1.2 - b.1.2), good_sub a.2 b.2⟩⟩
instance [FiniteField F] : Mul (Tagged (F := F) w) :=
  ⟨fun a b => ⟨(a.1.1 * b.1.1, a.1.2 * b.1.2), good_mul a.2 b.2⟩⟩
instance [FiniteField F] {n : ℕ} [OfNat F n] : OfNat (Tagged (F := F) w) n :=
  ⟨⟨(.const (OfNat.ofNat n), .plain), fun _ hj => nomatch hj⟩⟩

lemma isHom_expression [FiniteField F] : IsHom fun t : Tagged (F := F) w => t.1.1 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

lemma isHom_shape [FiniteField F] : IsHom fun t : Tagged (F := F) w => t.1.2 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The shape of an expression of a window: `plain`, a `selector`, or `bad`. -/
def shapeOf (x : Expression F) : Shape :=
  if Plain w x then .plain else
    match selectorGate? w x with
    | some gate => .selector gate
    | none => .bad

theorem good_shapeOf (x : Expression F) : Good w (x, shapeOf w x) := by
  unfold shapeOf
  split
  · assumption
  · split
    · assumption
    · trivial

/-- An expression with its shape. -/
def tag [FiniteField F] (x : Expression F) : Tagged (F := F) w :=
  ⟨(x, shapeOf w x), good_shapeOf w x⟩

lemma shapeOf_of_plain {x : Expression F} (h : Plain w x) : shapeOf w x = .plain := by
  simp [shapeOf, h]

lemma shapeOf_var (j : ℕ) (gate : Gate) (hj : ¬ j < 2 * w)
    (hgate : selectorGate? w (.var ⟨j⟩ : Expression F) = some gate) :
    shapeOf w (.var ⟨j⟩ : Expression F) = .selector gate := by
  have hplain : ¬ Plain w (.var ⟨j⟩ : Expression F) := fun h => hj (h j (by simp [expressionCells]))
  simp [shapeOf, hplain, hgate]

end Tagged

/-! ### The component's constraints -/

lemma Row.map_congr {α β : Type} {f g : α → β} (row : Row α)
    (h : ∀ x ∈ (toElements row).toList, f x = g x) : row.map f = row.map g := by
  rw [ProvableStruct.toList_toElements] at h
  simp only [ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.componentsToList, List.mem_append, List.append_nil] at h
  have hv {n : ℕ} (v : Vector α n) (hv : ∀ x ∈ v.toList, f x = g x) : v.map f = v.map g := by
    ext i hi
    simp only [Vector.getElem_map]
    exact hv _ (by simp)
  have hfield (x : α) : x ∈ (toElements (M := field) x).toList := List.mem_singleton_self x
  unfold Row.map
  congr 1
  all_goals first
    | exact hv _ fun x hx => h x (by simp only [toElements] at *; simp only [hx, true_or, or_true])
    | exact h _ (Or.inr (Or.inl (hfield _)))

lemma Row.map_map {α β γ : Type} (f : α → β) (g : β → γ) (row : Row α) :
    (row.map f).map g = row.map (g ∘ f) := by
  simp only [Row.map, Vector.map_map, Function.comp_apply]

lemma Row.map_id' {α : Type} (row : Row α) : row.map (fun x => x) = row := by
  simp only [Row.map, Vector.map_id']

lemma mapWindow_mapWindow {α β γ : Type} (f : α → β) (g : β → γ) (window : Window Row α) :
    mapWindow g (mapWindow f window) = mapWindow (g ∘ f) window := by
  simp only [mapWindow, Row.map_map, Function.comp_apply]

lemma constraints_map_assert {F : Type} [FiniteField F] (l : List (Expression F)) :
    Operations.constraints (l.map Operation.assert) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, Operations.constraints, ih]

lemma lookups_map_assert {F : Type} [FiniteField F] (l : List (Expression F)) :
    Operations.lookups (l.map Operation.assert) = [] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, Operations.lookups, ih]

lemma expressionBadVariable_eq_none {F : Type} (width : ℕ) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, j < width) → expressionBadVariable width x = none
  | .var v, h => by simp [expressionBadVariable, h v.index (by simp [expressionCells])]
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [expressionBadVariable,
      expressionBadVariable_eq_none width a fun j hj => h j (Or.inl hj),
      expressionBadVariable_eq_none width b fun j hj => h j (Or.inr hj), Option.orElse_none]

section Variables
variable {F : Type} {R : TypeMap} [ProvableType R]

lemma toElements_varFromOffset_window :
    toElements (varFromOffset (F := F) (Window R) 0) =
      Vector.mapRange (size (Window R)) fun i => .var ⟨0 + i⟩ :=
  ProvableType.toElements_fromElements _

lemma varFromOffset_current :
    ∀ x ∈ (toElements (varFromOffset (F := F) (Window R) 0).current).toList,
    ∃ j < size R, x = .var ⟨j⟩ := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < size R := by simpa using hj
  refine ⟨j, hj', ?_⟩
  have h := congrArg (fun v : Vector (Expression F) (Window.layout R).rowWidth => v[j]'hj')
    (Window.layout_current (varFromOffset (F := F) (Window R) 0))
  simp only [Vector.getElem_toList]
  refine h.symm.trans ?_
  simp only [WindowLayout.current, WindowLayout.cell, Vector.getElem_ofFn,
    toElements_varFromOffset_window, Vector.getElem_mapRange, Nat.zero_add]

lemma varFromOffset_next : ∀ x ∈ (toElements (varFromOffset (F := F) (Window R) 0).next).toList,
    ∃ j < size R, x = .var ⟨size R + j⟩ := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < size R := by simpa using hj
  refine ⟨j, hj', ?_⟩
  have h := congrArg (fun v : Vector (Expression F) (Window.layout R).rowWidth => v[j]'hj')
    (Window.layout_next (varFromOffset (F := F) (Window R) 0))
  simp only [Vector.getElem_toList]
  refine h.symm.trans ?_
  simp only [WindowLayout.next, WindowLayout.cell, Vector.getElem_ofFn,
    toElements_varFromOffset_window, Vector.getElem_mapRange, Nat.zero_add]
  rfl

lemma varFromOffset_isFirstRow :
    (varFromOffset (F := F) (Window R) 0).isFirstRow = .var ⟨2 * size R⟩ := by
  rw [← Window.layout_isFirstRow]
  simp only [WindowLayout.isFirstRow, WindowLayout.cell, toElements_varFromOffset_window,
    Vector.getElem_mapRange, Nat.zero_add, Window.layout]

lemma varFromOffset_isLastRow :
    (varFromOffset (F := F) (Window R) 0).isLastRow = .var ⟨2 * size R + 1⟩ := by
  rw [← Window.layout_isLastRow]
  simp only [WindowLayout.isLastRow, WindowLayout.cell, toElements_varFromOffset_window,
    Vector.getElem_mapRange, Nat.zero_add, Window.layout]

lemma varFromOffset_isTransition :
    (varFromOffset (F := F) (Window R) 0).isTransition = .var ⟨2 * size R + 2⟩ := by
  rw [← Window.layout_isTransition]
  simp only [WindowLayout.isTransition, WindowLayout.cell, toElements_varFromOffset_window,
    Vector.getElem_mapRange, Nat.zero_add, Window.layout]

end Variables

section Component
variable {p : ℕ}

/-- The variables of a window, the input of the component's row operations. -/
abbrev vars : Window Row (Expression (F p)) := varFromOffset (Window Row) 0

/-- A window of variables: the rows' cells, then the selectors. -/
structure VarWindow (window : Window Row (Expression (F p))) : Prop where
  current : ∀ x ∈ (toElements window.current).toList, ∃ j < size Row, x = .var ⟨j⟩
  next : ∀ x ∈ (toElements window.next).toList, ∃ j < size Row, x = .var ⟨size Row + j⟩
  isFirstRow : window.isFirstRow = .var ⟨2 * size Row⟩
  isLastRow : window.isLastRow = .var ⟨2 * size Row + 1⟩
  isTransition : window.isTransition = .var ⟨2 * size Row + 2⟩

theorem varWindow_vars : VarWindow (vars (p := p)) :=
  ⟨varFromOffset_current, varFromOffset_next, varFromOffset_isFirstRow, varFromOffset_isLastRow,
    varFromOffset_isTransition⟩

/-- The shapes of a window of variables: the rows are plain, the selectors are selectors. -/
theorem shapes_varWindow {window : Window Row (Expression (F p))} (h : VarWindow window) :
    mapWindow (shapeOf (size Row)) window = plainWindow window.current window.next := by
  have hplain (j : ℕ) (hj : j < 2 * size Row) :
      shapeOf (size Row) (.var ⟨j⟩ : Expression (F p)) = .plain :=
    shapeOf_of_plain _ fun i hi => by simp only [expressionCells, List.mem_singleton] at hi; omega
  have hselector (j : ℕ) (gate : Gate) (hj : 2 * size Row ≤ j)
      (hgate : selectorGate? (size Row) (.var ⟨j⟩ : Expression (F p)) = some gate) :
      shapeOf (size Row) (.var ⟨j⟩ : Expression (F p)) = .selector gate :=
    shapeOf_var _ j gate (by omega) hgate
  have hfirst := hselector (2 * size Row) .firstRow le_rfl (by simp [selectorGate?])
  have hlast := hselector (2 * size Row + 1) .lastRow (by omega) (by simp [selectorGate?])
  have htransition := hselector (2 * size Row + 2) .transition (by omega) (by simp [selectorGate?])
  simp only [mapWindow, plainWindow, h.isFirstRow, h.isLastRow, h.isTransition, hfirst, hlast,
    htransition]
  congr 1
  · exact Row.map_congr _ fun x hx => by
      obtain ⟨j, hj, rfl⟩ := h.current x hx
      exact hplain j (by omega)
  · exact Row.map_congr _ fun x hx => by
      obtain ⟨j, hj, rfl⟩ := h.next x hx
      exact hplain _ (by omega)

/-- Every constraint of a window of variables splits into a gate and a body, and reads cells of
the window. -/
theorem constraints_varWindow [Fact p.Prime] {window : Window Row (Expression (F p))}
    (h : VarWindow window) : ∀ x ∈ constraints window,
      (gateConstraint (some (size Row)) x).isSome ∧
        ∀ j ∈ expressionCells x, j < 2 * size Row + 3 := by
  intro x hx
  have hfst : mapWindow (fun t : Tagged (F := F p) (size Row) => t.1.1)
      (mapWindow (tag _) window) = window := by
    rw [mapWindow_mapWindow]
    simp only [mapWindow, Function.comp_def, tag, Row.map_id']
  have hsnd : mapWindow (fun t : Tagged (F := F p) (size Row) => t.1.2)
      (mapWindow (tag _) window) = plainWindow window.current window.next := by
    rw [mapWindow_mapWindow, ← shapes_varWindow h]
    rfl
  rw [← hfst, ← (isHom_expression (size Row)).map_constraints] at hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have hs : t.1.2 ∈ constraints (plainWindow window.current window.next) := by
    rw [← hsnd, ← (isHom_shape (size Row)).map_constraints]
    exact List.mem_map_of_mem ht
  exact gateConstraint_of_good t.2 (gateable_constraints _ _ _ hs)

variable [Fact p.Prime] [Fact (2 ^ 16 < p)]

lemma rowOperations_component (height : UInt64) :
    (component (p := p) height).rowOperations = (constraints vars).map Operation.assert := by
  unfold Component.rowOperations
  rfl

/-- **The Keccak-f component is bridgeable**: no legacy lookups, every constraint is a gate times
a body that reads no selector, and every expression reads cells of the row. -/
theorem bridgeable_component (height : UInt64) : bridgeable (component (p := p) height) = true := by
  have hwidth : 2 * size Row + 3 ≤ (component (p := p) height).width :=
    rowWidth_le_size (component := component (p := p) height) (layout := Window.layout Row) rfl
  have hwindow : (component (p := p) height).window.map (·.rowWidth) = some (size Row) := rfl
  simp only [bridgeable, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true,
    Option.isNone_iff_eq_none, rowOperations_component, constraints_map_assert,
    lookups_map_assert, hwindow]
  refine ⟨⟨trivial, fun x hx => (constraints_varWindow varWindow_vars x hx).1⟩, ?_⟩
  simp only [rowExpressions, rowOperations_component, constraints_map_assert,
    assertZeros_interactions, List.flatMap_nil, List.append_nil, expressionsBadVariable]
  exact List.findSome?_eq_none_iff.mpr fun x hx => expressionBadVariable_eq_none _ x
    fun j hj => by have := (constraints_varWindow varWindow_vars x hx).2 j hj; omega

end Component

end CleanCompStark.KeccakAir
