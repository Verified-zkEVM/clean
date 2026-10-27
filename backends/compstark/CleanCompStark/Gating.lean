module

public import CleanCompStark.Transfer
public import Clean.Gadgets.Bits
public import Clean.Gadgets.ConditionalEquality

/-!
# Gateable constraints and their weights, circuit by circuit

What `bridgeable` asks of a two-row component's constraints, and what the degree of their lowering
is, shown for the circuits a component is built from rather than for its flattened constraints.

A `Shape` abstracts an expression of a window of rows of `w` cells: `plain` (it reads only cells
of the two rows), a `selector`, a `gated` constraint (`splitSelector` takes its selector off and
leaves a plain body), or `bad`; `Good w (x, s)` says that `s` describes `x`. Shapes have the
operations of expressions, and `Good` is closed under them (`good_add`, `good_sub`, `good_mul`). A
constraint of shape `plain` or `gated` splits into a gate and a body that reads no selector
(`gateConstraint_of_good`).

The weight of an expression (`weight`), each cell weighing what `wv` says, a constant `0`, a sum
the larger of its terms' and a product the sum of its factors', is the degree of its lowering.
`Shaped w wv s d x` says that `x` has shape `s` and weighs at most `d`; it is closed under the
operations, and so are the expressions Clean's bit gadgets build (`shaped_bitXor`,
`shaped_fieldFromBitsExpr`, ...). A constraint of a gateable shape is `Admissible`.

The constraints of a circuit's operations are those of its subcircuits and loop bodies
(`mem_constraints_assertion`, `mem_constraints_forEach`), so a circuit's constraints are admissible
when its gadgets' are: `assertBool`, `PackBits`, `PackLimbs` and `ConditionalEquality` have their
constraints described here, for inputs of a shape.
-/

@[expose] public section

namespace CleanCompStark
open Air.Flat Air.Flat.WitnessGeneration Backends

/-! ### Shapes -/

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

end Shape

/-! ### Expressions with a shape -/

section Good
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

end Good

/-! ### Weights -/

section Weight
variable {F : Type}

/-- The weight of an expression, cell `j` weighing `wv j`: a constant weighs `0`, a sum the larger
of its terms, a product the sum of its factors. -/
def weight (wv : ℕ → ℕ) : Expression F → ℕ
  | .var v => wv v.index
  | .const _ => 0
  | .add a b => max (weight wv a) (weight wv b)
  | .mul a b => weight wv a + weight wv b

/-- The weight of a gate's selector cell, for rows of `w` cells. -/
def gateWeight (w : ℕ) (wv : ℕ → ℕ) : Gate → ℕ
  | .everyRow => 0
  | .firstRow => wv (2 * w)
  | .lastRow => wv (2 * w + 1)
  | .transition => wv (2 * w + 2)

lemma weight_congr (wv wv' : ℕ → ℕ) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, wv j = wv' j) → weight wv x = weight wv' x
  | .var v, h => h v.index (by simp [expressionCells])
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [weight, weight_congr wv wv' a fun j hj => h j (Or.inl hj),
      weight_congr wv wv' b fun j hj => h j (Or.inr hj)]

/-- Splitting the selector off a product keeps its weight. -/
theorem weight_of_splitSelector {w : ℕ} (wv : ℕ → ℕ) :
    ∀ {x body : Expression F} {gate : Gate}, splitSelector w x = some (gate, body) →
      weight wv x = gateWeight w wv gate + weight wv body
  | .var _, _, _, h | .const _, _, _, h | .add _ _, _, _, h => by simp [splitSelector] at h
  | .mul left right, body, gate, h => by
    have hcell {y : Expression F} {g : Gate} (hy : selectorGate? w y = some g) :
        weight wv y = gateWeight w wv g := by
      obtain ⟨cell, hcell, rfl⟩ := selectorGate?_eq_some hy
      cases g <;> simp only [Gate.selectorCell, Option.some.injEq, reduceCtorEq] at hcell <;>
        simp only [weight, gateWeight, hcell]
    simp only [splitSelector] at h
    split at h
    · rename_i hleft
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [weight, hcell hleft]
    · rename_i hright
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [weight, hcell hright]
      omega
    · split at h
      · rename_i hsplit
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [weight, weight_of_splitSelector wv hsplit]
        omega
      · obtain ⟨⟨gate', right'⟩, hsplit, heq⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [weight, weight_of_splitSelector wv hsplit]
        omega

/-- A constraint of a window that `gateConstraint` splits: its body reads cells of the rows, and
its weight is its selector's and its body's. -/
theorem gateConstraint_weight {w : ℕ} {x : Expression F} {g : GatedConstraint F}
    (hcells : ∀ j ∈ expressionCells x, j < 2 * w + 3) (h : gateConstraint (some w) x = some g) :
    Plain w g.body ∧ ∀ wv, weight wv x = gateWeight w wv g.gate + weight wv g.body := by
  simp only [gateConstraint] at h
  split at h
  · rename_i hreads
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun j hj => ?_, fun _ => by simp only [gateWeight, Nat.zero_add]⟩
    simp only [Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq,
      not_and, not_lt] at hreads
    have := hcells j hj
    have := hreads j hj
    omega
  · obtain ⟨⟨gate, body⟩, hsplit, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rename_i hreads
      refine ⟨fun j hj => ?_, fun wv => weight_of_splitSelector wv hsplit⟩
      simp only [Bool.not_eq_true, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq,
        not_and, not_lt] at hreads
      have := hcells j (cells_subset_of_splitSelector hsplit j hj)
      have := hreads j hj
      omega

end Weight

/-! ### Shapes and weights -/

section WeightOps
variable {F : Type} (wv : ℕ → ℕ) (x y : Expression F)

@[simp] lemma weight_add : weight wv (x + y) = max (weight wv x) (weight wv y) := rfl
@[simp] lemma weight_mul : weight wv (x * y) = weight wv x + weight wv y := rfl
@[simp] lemma weight_var (v : Variable F) : weight wv (.var v) = wv v.index := rfl
@[simp] lemma weight_sub [FiniteField F] : weight wv (x - y) = max (weight wv x) (weight wv y) := by
  show max _ (0 + _) = _
  rw [Nat.zero_add]

end WeightOps

section Shaped
variable {F : Type} (w : ℕ) (wv : ℕ → ℕ)

/-- An expression has shape `s`, for rows of `w` cells, and weighs at most `d`. -/
def Shaped (s : Shape) (d : ℕ) (x : Expression F) : Prop := Good w (x, s) ∧ weight wv x ≤ d

/-- A constraint splits into a gate and a body, reads cells of the window, and weighs at most
`d`. -/
def Admissible (d : ℕ) (x : Expression F) : Prop :=
  (gateConstraint (some w) x).isSome ∧ (∀ j ∈ expressionCells x, j < 2 * w + 3) ∧ weight wv x ≤ d

variable {w wv}

theorem Shaped.mono {s : Shape} {d d' : ℕ} {x : Expression F} (h : Shaped w wv s d x)
    (hd : d ≤ d') :
    Shaped w wv s d' x :=
  ⟨h.1, h.2.trans hd⟩

theorem Shaped.admissible {s : Shape} {d : ℕ} {x : Expression F} (h : Shaped w wv s d x)
    (hs : s.Gateable) : Admissible w wv d x :=
  ⟨(gateConstraint_of_good h.1 hs).1, (gateConstraint_of_good h.1 hs).2, h.2⟩

theorem shaped_const (c : F) : Shaped w wv .plain 0 (.const c) :=
  ⟨fun _ hj => by simp [expressionCells] at hj, le_rfl⟩

theorem shaped_ofNat (n : ℕ) [OfNat F n] : Shaped w wv .plain 0 (OfNat.ofNat n : Expression F) :=
  shaped_const _

theorem shaped_var {j : ℕ} (hj : j < 2 * w) : Shaped w wv .plain (wv j) (.var ⟨j⟩ : Expression F) :=
  ⟨fun i hi => by simp only [expressionCells, List.mem_singleton] at hi; omega, le_rfl⟩

theorem shaped_add {s t : Shape} {d e : ℕ} {x y : Expression F} (hx : Shaped w wv s d x)
    (hy : Shaped w wv t e y) : Shaped w wv (s + t) (max d e) (x + y) :=
  ⟨good_add hx.1 hy.1, max_le_max hx.2 hy.2⟩

theorem shaped_sub [FiniteField F] {s t : Shape} {d e : ℕ} {x y : Expression F}
    (hx : Shaped w wv s d x)
    (hy : Shaped w wv t e y) : Shaped w wv (s - t) (max d e) (x - y) := by
  refine ⟨good_sub hx.1 hy.1, ?_⟩
  show max (weight wv x) (0 + weight wv y) ≤ max d e
  rw [Nat.zero_add]
  exact max_le_max hx.2 hy.2

theorem shaped_mul {s t : Shape} {d e : ℕ} {x y : Expression F} (hx : Shaped w wv s d x)
    (hy : Shaped w wv t e y) : Shaped w wv (s * t) (d + e) (x * y) :=
  ⟨good_mul hx.1 hy.1, Nat.add_le_add hx.2 hy.2⟩

theorem shaped_selector {j : ℕ} {gate : Gate}
    (hgate : selectorGate? w (.var ⟨j⟩ : Expression F) = some gate) :
    Shaped w wv (.selector gate) (wv j) (.var ⟨j⟩ : Expression F) :=
  ⟨hgate, le_rfl⟩

/-! #### Clean's bit gadgets -/

theorem shaped_bitXor [FiniteField F] {d e : ℕ} {x y : Expression F} (hx : Shaped w wv .plain d x)
    (hy : Shaped w wv .plain e y) : Shaped w wv .plain (d + e) (bitXor x y) :=
  (shaped_sub (shaped_add hx hy) (shaped_mul hx (shaped_mul (shaped_ofNat 2) hy))).mono (by omega)

theorem shaped_bitAndNot [FiniteField F] {d e : ℕ} {x y : Expression F}
    (hx : Shaped w wv .plain d x)
    (hy : Shaped w wv .plain e y) : Shaped w wv .plain (d + e) (bitAndNot x y) :=
  (shaped_mul (shaped_sub (shaped_ofNat 1) hx) hy).mono (by omega)

/-- The booleanity constraint `x (x - 1)` of a bit. -/
theorem shaped_boolCheck [FiniteField F] {d : ℕ} {x : Expression F} (hx : Shaped w wv .plain d x) :
    Shaped w wv .plain (2 * d) (x * (x - 1)) :=
  (shaped_mul hx (shaped_sub hx (shaped_ofNat 1))).mono (by omega)

end Shaped

/-! ### The constraints of subcircuits and loops -/

section Operations
variable {F : Type} [FiniteField F]

theorem constraints_flatten (ops : List (Operations F)) :
    Operations.constraints ops.flatten = (ops.map Operations.constraints).flatten := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simp [Operations.constraints_append, ih]

/-- The constraints of a loop are those of its bodies. -/
theorem mem_constraints_forEach {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit F Unit} {constant : Circuit.ConstantLength body} {offset : ℕ}
    {x : Expression F} :
    x ∈ ((Circuit.forEach xs body constant).operations offset).constraints ↔
      ∃ i : Fin m,
        x ∈ ((body xs[i]).operations (offset + i * constant.localLength)).constraints := by
  rw [Circuit.forEach, Circuit.ForM.operations_eq xs constant, constraints_flatten,
    List.map_ofFn]
  simp [List.mem_flatten, List.mem_ofFn, Function.comp_def]

theorem constraints_forEach {α : Type} {m : ℕ} [Inhabited α] (xs : Vector α m)
    (body : α → Circuit F Unit) (constant : Circuit.ConstantLength body) (offset : ℕ) :
    ((Circuit.forEach xs body constant).operations offset).constraints =
      (List.ofFn fun i : Fin m =>
        ((body xs[i]).operations (offset + i * constant.localLength)).constraints).flatten := by
  rw [Circuit.forEach, Circuit.ForM.operations_eq xs constant, constraints_flatten,
    List.map_ofFn]
  rfl

/-- The constraints of an assertion subcircuit are those of its circuit. -/
theorem constraints_toSubcircuit {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (offset : ℕ) (input : Var Input F) :
    FlatOperation.constraints (circuit.toSubcircuit offset input).ops.toFlat =
      ((circuit.main input).operations offset).constraints := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.constraints_toFlat]

theorem lookups_flatten (ops : List (Operations F)) :
    Operations.lookups ops.flatten = (ops.map Operations.lookups).flatten := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simp [Operations.lookups_append, ih]

/-- The lookups of a loop are those of its bodies. -/
theorem lookups_forEach {α : Type} {m : ℕ} [Inhabited α] (xs : Vector α m)
    (body : α → Circuit F Unit) (constant : Circuit.ConstantLength body) (offset : ℕ) :
    ((Circuit.forEach xs body constant).operations offset).lookups =
      (List.ofFn fun i : Fin m =>
        ((body xs[i]).operations (offset + i * constant.localLength)).lookups).flatten := by
  rw [Circuit.forEach, Circuit.ForM.operations_eq xs constant, lookups_flatten, List.map_ofFn]
  rfl

/-- The lookups of an assertion subcircuit are those of its circuit. -/
theorem lookups_toSubcircuit {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (offset : ℕ) (input : Var Input F) :
    FlatOperation.lookups (circuit.toSubcircuit offset input).ops.toFlat =
      ((circuit.main input).operations offset).lookups := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.lookups_toFlat]

end Operations

/-! ### Clean's gadgets -/

section Gadgets
variable {p : ℕ} [Fact p.Prime] {w : ℕ} {wv : ℕ → ℕ}

theorem shaped_foldr {n d : ℕ} (bit : Fin n → Expression (F p))
    (hbit : ∀ i, Shaped w wv .plain d (bit i)) {acc : Expression (F p)}
    (hacc : Shaped w wv .plain d acc) :
    Shaped w wv .plain d (Fin.foldr n (fun i acc => 2 * acc + bit i) acc) := by
  induction n with
  | zero => exact hacc
  | succ n ih =>
    rw [Fin.foldr_succ]
    have h := shaped_add (shaped_mul (shaped_ofNat (F := F p) (w := w) (wv := wv) 2)
      (ih (fun i => bit i.succ) fun i => hbit i.succ)) (hbit 0)
    exact h.mono (by omega)

theorem shaped_hornerExpr {n d : ℕ} {bits : Vector (Expression (F p)) n}
    {acc : Expression (F p)} (hbits : ∀ i : Fin n, Shaped w wv .plain d bits[i])
    (hacc : Shaped w wv .plain d acc) : Shaped w wv .plain d (Utils.Bits.hornerExpr bits acc) :=
  shaped_foldr (fun i => bits[i]) hbits hacc

theorem shaped_fieldFromBitsExpr {p : ℕ} [Fact p.Prime] {n d : ℕ}
    {bits : Vector (Expression (F p)) n} (hbits : ∀ i : Fin n, Shaped w wv .plain d bits[i]) :
    Shaped w wv .plain d (Utils.Bits.fieldFromBitsExpr bits) := by
  cases n with
  | zero => exact (shaped_ofNat 0).mono (Nat.zero_le _)
  | succ n =>
    exact shaped_hornerExpr (fun i => by simpa using hbits i.castSucc) (hbits (Fin.last n))


theorem constraints_assertBool (x : Expression (F p)) (offset : ℕ) :
    ((assertBool.main x).operations offset).constraints = [x * (x - 1)] := rfl

theorem constraints_packBits {n : ℕ} (input : Var (Gadgets.PackBits.Input n) (F p))
    (offset : ℕ) : (((Gadgets.PackBits.circuit n).main input).operations offset).constraints =
      [Utils.Bits.fieldFromBitsExpr input.bits - input.value] := rfl

theorem mem_constraints_packLimbs {k w : ℕ} [NeZero k]
    {input : Var (ProvableVector (Gadgets.PackBits.Input w) k) (F p)} {offset : ℕ}
    {x : Expression (F p)} :
    x ∈ (((Gadgets.PackLimbs.circuit k w).main input).operations offset).constraints ↔
      ∃ l : Fin k, x = Utils.Bits.fieldFromBitsExpr input[l].bits - input[l].value := by
  simp only [Gadgets.PackLimbs.circuit, Gadgets.PackLimbs.main, mem_constraints_forEach,
    circuit_norm, constraints_toSubcircuit, constraints_packBits, List.mem_singleton,
    List.append_nil]

theorem mem_constraints_conditionalEquality {M : TypeMap} [ProvableType M]
    {input : Var (Gadgets.ConditionalEquality.Input M) (F p)} {offset : ℕ}
    {x : Expression (F p)} :
    x ∈ (((Gadgets.ConditionalEquality.circuit M).main input).operations offset).constraints ↔
      ∃ i : Fin (size M),
        x = input.gate * ((toElements input.lhs)[i] - (toElements input.rhs)[i]) := by
  simp only [Gadgets.ConditionalEquality.circuit, Gadgets.ConditionalEquality.main,
    mem_constraints_forEach, circuit_norm, List.mem_singleton, Vector.getElem_map,
    Vector.getElem_zip]

theorem length_constraints_packLimbs {k w : ℕ} [NeZero k]
    (input : Var (ProvableVector (Gadgets.PackBits.Input w) k) (F p)) (offset : ℕ) :
    (((Gadgets.PackLimbs.circuit k w).main input).operations offset).constraints.length = k := by
  simp [Gadgets.PackLimbs.circuit, Gadgets.PackLimbs.main, constraints_forEach, circuit_norm,
    constraints_toSubcircuit, constraints_packBits]

theorem length_constraints_conditionalEquality {M : TypeMap} [ProvableType M]
    (input : Var (Gadgets.ConditionalEquality.Input M) (F p)) (offset : ℕ) :
    (((Gadgets.ConditionalEquality.circuit M).main input).operations offset).constraints.length =
      size M := by
  simp [Gadgets.ConditionalEquality.circuit, Gadgets.ConditionalEquality.main,
    constraints_forEach, circuit_norm]

theorem lookups_packLimbs {k w : ℕ} [NeZero k]
    (input : Var (ProvableVector (Gadgets.PackBits.Input w) k) (F p)) (offset : ℕ) :
    (((Gadgets.PackLimbs.circuit k w).main input).operations offset).lookups = [] := by
  simp [Gadgets.PackLimbs.circuit, Gadgets.PackLimbs.main, lookups_forEach, circuit_norm,
    lookups_toSubcircuit, Gadgets.PackBits.circuit, Gadgets.PackBits.main]

theorem lookups_conditionalEquality {M : TypeMap} [ProvableType M]
    (input : Var (Gadgets.ConditionalEquality.Input M) (F p)) (offset : ℕ) :
    (((Gadgets.ConditionalEquality.circuit M).main input).operations offset).lookups = [] := by
  simp [Gadgets.ConditionalEquality.circuit, Gadgets.ConditionalEquality.main, lookups_forEach,
    circuit_norm]

end Gadgets

/-! ### Expressions that read cells of a row -/

theorem expressionBadVariable_eq_none {F : Type} (width : ℕ) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, j < width) → expressionBadVariable width x = none
  | .var v, h => by simp [expressionBadVariable, h v.index (by simp [expressionCells])]
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [expressionBadVariable,
      expressionBadVariable_eq_none width a fun j hj => h j (Or.inl hj),
      expressionBadVariable_eq_none width b fun j hj => h j (Or.inr hj), Option.orElse_none]

end CleanCompStark
