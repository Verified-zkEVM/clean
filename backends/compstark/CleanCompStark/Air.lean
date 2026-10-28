module

public import Clean.Backends.Program
public import CompStark.Lookup.LogUp

/-!
# A Clean component as a CompStark AIR

A component becomes one AIR (`toAir`), as the Plonky3 backend lays it out. The fixed columns, the
input cells that the component's generation makes fixed cells, are the preprocessed trace; the trace
commits the other cells of the row's own input and the witnesses. A two-row component's window cells are not committed: the next row's
input reads the next row, and the selectors are Plonky3's. Every constraint is lowered with
`Backends.gateConstraint` and becomes its body times its gate's selector, as Plonky3's
`when_first_row`, `when_last_row` and `when_transition` do; Clean's subtraction `x + (-1) * z`
becomes a subtraction (`addExpr`). Every interaction becomes a global lookup on the bus named
after its channel, with the signed multiplicity negated and weight `0`, as the Plonky3 backend registers
it.

The constraints are over a Clean field `F` and the AIR over a CompStark base field `K`; a ring
isomorphism `e : F ≃+* K` maps the constants.

`toRows` reads a CompStark trace as the rows of a Clean table, with the window cells filled from
the next row and with the selectors `0` and `1`; `toTrace` drops the fixed and window cells of
Clean rows.
-/

@[expose] public section

namespace CleanCompStark
open Air.Flat Backends CompStark.Stark

variable {F : Type} [FiniteField F] {K : Type} [CompStark.BaseField K]

/-- The input columns of a component that are fixed columns, in increasing order: the fixed cells
of its generation. -/
def fixedColumns (component : Component F) : List ℕ :=
  (component.generation.cells.1.toList.zipIdx.filter (·.1.isFixed)).map (·.2)

/-- The number of fixed columns. -/
def fixedWidth (component : Component F) : ℕ := (fixedColumns component).length

/-- The number of fixed columns before column `j`. -/
def fixedBefore (component : Component F) (j : ℕ) : ℕ :=
  ((fixedColumns component).filter (· < j)).length

/-- The width of the committed trace of a component: its cells except the fixed and the window
cells. -/
def traceWidth (component : Component F) : ℕ :=
  component.width - fixedWidth component - component.windowWidth

/-- Cell `j` of the row's own input on the current row: a fixed column of the preprocessed trace, or
a column of the trace. -/
def ownCell (component : Component F) (j : ℕ) : Expr K :=
  if j ∈ fixedColumns component then .prepCur ((fixedColumns component).idxOf j)
  else .cur (j - fixedBefore component j)

/-- Cell `j` of the row's own input on the next row. -/
def ownCellNext (component : Component F) (j : ℕ) : Expr K :=
  if j ∈ fixedColumns component then .prepNext ((fixedColumns component).idxOf j)
  else .next (j - fixedBefore component j)

/-- The value of cell `j` of a component's row in an AIR environment: a fixed cell is the
preprocessed trace, a window cell of the next row's input is the next row, a selector cell is the
selector, and every other cell is a column of the trace. -/
def cellExpr (component : Component F) (j : ℕ) : Expr K :=
  match component.window with
  | none => ownCell component j
  | some layout =>
    let w := layout.rowWidth
    if j < w then ownCell component j
    else if j < 2 * w then ownCellNext component (j - w)
    else if j = 2 * w then .isFirstRow
    else if j = 2 * w + 1 then .isLastRow
    else if j = 2 * w + 2 then .isTransition
    else .cur (j - (w + 3) - fixedWidth component)

/-- The sum `x + y` of AIR expressions, where a summand `(-1) * z`, Clean's subtraction
`x - z = x + (-1) * z`, becomes a subtraction `x - z`, which the quotient's program computes
without a multiplication. -/
def addExpr (x : Expr K) : Expr K → Expr K
  | .mul (.const c) z => if c = -1 then .sub x z else .add x (.mul (.const c) z)
  | y => .add x y

/-- `addExpr x y` is `x + y`, or `x - z` for `y = (-1) * z`. -/
theorem addExpr_cases (x y : Expr K) :
    addExpr x y = .add x y ∨ ∃ z, y = .mul (.const (-1)) z ∧ addExpr x y = .sub x z := by
  unfold addExpr
  split
  · split_ifs with h
    · exact Or.inr ⟨_, by rw [h], rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem eval_addExpr {R : Type*} [Ring R] (env : Expr.Env K R) (hconst : env.const (-1) = -1)
    (x y : Expr K) : (addExpr x y).eval env = x.eval env + y.eval env := by
  rcases addExpr_cases x y with h | ⟨z, rfl, h⟩ <;> rw [h]
  · rfl
  · simp only [Expr.eval, hconst, neg_one_mul, sub_eq_add_neg]

theorem degree_addExpr (x y : Expr K) : (addExpr x y).degree = max x.degree y.degree := by
  rcases addExpr_cases x y with h | ⟨z, rfl, h⟩ <;> rw [h]
  · rfl
  · simp only [Expr.degree, Nat.zero_add]

theorem degProfile_addExpr (x y : Expr K) :
    (addExpr x y).degProfile =
      (max x.degProfile.1 y.degProfile.1, max x.degProfile.2 y.degProfile.2) := by
  rcases addExpr_cases x y with h | ⟨z, rfl, h⟩ <;> rw [h]
  · rfl
  · simp only [Expr.degProfile, Nat.zero_add]

theorem colsBelow_addExpr (w wNext pw pwNext : ℕ) (x y : Expr K) :
    (addExpr x y).colsBelow w wNext pw pwNext =
      (x.colsBelow w wNext pw pwNext && y.colsBelow w wNext pw pwNext) := by
  rcases addExpr_cases x y with h | ⟨z, rfl, h⟩ <;> rw [h]
  · rfl
  · simp only [Expr.colsBelow, Bool.true_and]

variable (e : F ≃+* K)

/-- A Clean expression of a component's row as an AIR expression. -/
def toExpr (component : Component F) : Expression F → Expr K
  | .var v => cellExpr component v.index
  | .const c => .const (e c)
  | .add a b => addExpr (toExpr component a) (toExpr component b)
  | .mul a b => .mul (toExpr component a) (toExpr component b)

/-- A constraint body checked on the rows of its gate: Plonky3's `when_*(selector)`. -/
def gateExpr : Gate → Expr K → Expr K
  | .everyRow, body => body
  | .firstRow, body => .isFirstRow * body
  | .lastRow, body => .isLastRow * body
  | .transition, body => .isTransition * body

/-- The component's constraints, each split into its gate and body (`Backends.gateConstraint`). A
constraint that cannot be split is dropped; `Bridgeable` excludes such components. -/
def gatedConstraints (component : Component F) : List (GatedConstraint F) :=
  component.rowOperations.constraints.filterMap
    (gateConstraint (component.window.map (·.rowWidth)))

/-- An interaction as a global lookup on the bus of its channel's name, one tuple with the
negated signed multiplicity, a provided entry of weight `0`: a push counts `-mult`, a pull
`mult`. -/
def toLookup (component : Component F) (interaction : AbstractInteraction F) :
    CompStark.Stark.Lookup K :=
  ⟨some interaction.channel.name,
    [(interaction.msg.toList.map (toExpr e component),
      .provided (match interaction.direction with
        | .push => .const 0 - toExpr e component interaction.mult
        | .pull => toExpr e component interaction.mult))]⟩

/-- The values of the fixed columns on row `i`: the fixed cells of the generation, evaluated at the
row index. -/
def fixedValues (component : Component F) (i : ℕ) : List F :=
  let (cells, steps) := component.generation.cells
  let ctx := WitnessGeneration.inputContext steps (WitnessGeneration.rowEnvironment (.empty F)) i
  (fixedColumns component).map fun j =>
    match cells.toList[j]? with
    | some (WitnessGeneration.Cell.fixed value) => value.eval ctx
    | _ => 0

/-- The preprocessed trace of `2 ^ logN` rows: the fixed columns' values, row-major. -/
def fixedTrace (component : Component F) (logN : ℕ) : Array K :=
  let width := fixedWidth component
  Array.ofFn (n := 2 ^ logN * width) fun k =>
    e ((fixedValues component (k / width))[k % width]?.getD 0)

/-- The AIR of a component on `2 ^ logN` rows. -/
def toAir (component : Component F) (logN : ℕ) : Air K where
  width := traceWidth component
  numPublicValues := 0
  constraints := (gatedConstraints component).map fun g =>
    gateExpr g.gate (toExpr e component g.body)
  preprocessedWidth := fixedWidth component
  preprocessed := fixedTrace e component logN
  lookups := component.rowOperations.interactions.map (toLookup e component)

/-- The committed trace of Clean rows: each row's cells but the fixed and the window cells. -/
def toTrace (component : Component F) (rows : List (Array F)) : Array K :=
  let w := component.ownInputWidth
  (rows.toArray.flatMap fun row =>
    ((row.extract 0 w).zipIdx.filter (·.2 ∉ fixedColumns component)).map (·.1) ++
    row.extract (w + component.windowWidth) component.width).map e

/-- Row `i` of a Clean table read off a trace of `2 ^ logN` rows of the component's AIR: every
cell's `cellExpr` on the row, with the selectors `0` and `1` (`Lookup.generationRow`). -/
def toRow (component : Component F) (logN : ℕ) (trace : Array K) (i : ℕ) : Array F :=
  Array.ofFn (n := component.width) fun j => e.symm ((cellExpr component j).eval
    (CompStark.Lookup.generationRow (toAir e component logN) logN trace [] i))

/-- The rows of a Clean table read off a trace of `2 ^ logN` rows of the component's AIR. -/
def toRows (component : Component F) (logN : ℕ) (trace : Array K) : List (Array F) :=
  List.ofFn fun i : Fin (2 ^ logN) => toRow e component logN trace i

end CleanCompStark
