/-
Boundary assertions: the counterpart of classic AIR boundary constraints. An assertion pins the
typed input prefix of the first or last trace row against the public input, assert-only (no
witnesses, lookups or channels), matching Plonky3's `when_first_row` / `when_last_row`.

Together with a transition component, these make shift-constraint AIR tables expressible: the
transition constraint carries the induction, a first-row assertion pins the seed and a last-row
assertion exports the result.
-/
import Clean.Air.FlatComponent

namespace Air.Flat.Boundary
variable {F : Type} [FiniteField F]
variable {PublicIO Input : TypeMap} [ProvableType PublicIO] [ProvableType Input]

/-- The trace row a boundary assertion constrains. Only the two rows with native AIR selectors
are expressible, matching `when_first_row` / `when_last_row`. -/
inductive Row where
  | first
  | last
deriving DecidableEq

/-- The designated row of a committed trace, if it exists. On an empty trace there is no such
row, and a boundary assertion is unsatisfiable -- an assertion forces its table nonempty. -/
def Row.resolve : Row → List (Array F) → Option (Array F)
  | .first, rows => rows.head?
  | .last, rows => rows.getLast?

/-- The environment a boundary assertion is evaluated in: the designated row's typed input
prefix at cells `[0, size Input)`, the public input directly after it. Witness-suffix cells of
the row are deliberately not present. -/
def assertionEnv (Input : TypeMap) [ProvableType Input] (row : Array F) (publicIO : PublicIO F)
    (data : ProverData F) : Environment F where
  get j :=
    if j < size Input then row[j]?.getD 0
    else (toElements publicIO)[j - size Input]?.getD 0
  data

/-- A boundary assertion: constraint polynomials over one trace row's typed input prefix and the
public input, each asserted zero on the designated row, bundled with the `Spec` they imply. There
is no completeness obligation, mirroring `Verifier.Program`. -/
structure Assertion (F : Type) [FiniteField F] (PublicIO Input : TypeMap)
    [ProvableType PublicIO] [ProvableType Input] where
  row : Row
  /-- Constraints over the row's input prefix and the public input; each is asserted zero. -/
  constraints : Var Input F → Var PublicIO F → List (Expression F)
  /-- The semantic contract: what the constraints mean about the row and the public input. -/
  Spec : Input F → PublicIO F → Prop
  soundness : ∀ (env : Environment F) (input : Var Input F) (publicIO : Var PublicIO F),
    (∀ e ∈ constraints input publicIO, Expression.eval env e = 0) →
    Spec (eval env input) (eval env publicIO)

lemma eval_assertionEnv_input (row : Array F) (publicIO : PublicIO F) (data : ProverData F) :
    eval (assertionEnv (PublicIO := PublicIO) Input row publicIO data)
      (varFromOffset (F := F) Input 0) = valueFromOffset Input 0 (.fromArray row data) := by
  rw [ProvableType.eval_varFromOffset, valueFromOffset]
  congr 1
  rw [Vector.ext_iff]
  intro i hi
  simp only [Vector.getElem_mapRange, zero_add, assertionEnv]
  rw [if_pos hi]

lemma eval_assertionEnv_publicIO (row : Array F) (publicIO : PublicIO F) (data : ProverData F) :
    eval (assertionEnv (PublicIO := PublicIO) Input row publicIO data)
      (varFromOffset (F := F) PublicIO (size Input)) = publicIO := by
  rw [ProvableType.eval_varFromOffset, ProvableType.fromElements_eq_iff, Vector.ext_iff]
  intro i hi
  simp only [Vector.getElem_mapRange, assertionEnv]
  rw [if_neg (by omega), show size Input + i - size Input = i by omega,
    Vector.getElem?_eq_getElem hi, Option.getD_some]

/-- The assertion's constraints, instantiated at the canonical variable layout and evaluated
on a concrete row and public input. This is the form that enters `Ensemble.Statement`. -/
def Assertion.Holds (assertion : Assertion F PublicIO Input) (row : Array F)
    (publicIO : PublicIO F) (data : ProverData F) : Prop :=
  ∀ e ∈ assertion.constraints (varFromOffset Input 0) (varFromOffset PublicIO (size Input)),
    Expression.eval (assertionEnv Input row publicIO data) e = 0

/-- The assertion's `Spec`, stated of a concrete row's typed input prefix. -/
def Assertion.RowSpec (assertion : Assertion F PublicIO Input) (row : Array F)
    (publicIO : PublicIO F) (data : ProverData F) : Prop :=
  assertion.Spec (valueFromOffset Input 0 (.fromArray row data)) publicIO

theorem Assertion.rowSpec_of_holds (assertion : Assertion F PublicIO Input) {row : Array F}
    {publicIO : PublicIO F} {data : ProverData F} (h : assertion.Holds row publicIO data) :
    assertion.RowSpec row publicIO data := by
  have hs := assertion.soundness (assertionEnv Input row publicIO data)
    (varFromOffset Input 0) (varFromOffset PublicIO (size Input)) h
  rwa [eval_assertionEnv_input, eval_assertionEnv_publicIO] at hs

/-- A boundary assertion attached to an ensemble table, keyed by component name -- stable under
`addTable`, which prepends and so shifts positional indices. -/
structure Entry (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Input : TypeMap}
  [provableInput : ProvableType Input]
  /-- `circuit.name` of the component whose trace this assertion constrains. -/
  table : String
  assertion : Assertion F PublicIO Input

instance (entry : Entry F PublicIO) : ProvableType entry.Input := entry.provableInput

/-- The named table exists, its designated row exists, and the assertion's constraints hold
there -- so an assertion on a missing table or an empty trace is unsatisfiable, not vacuous. -/
def Entry.Holds (entry : Entry F PublicIO) (tables : List (Table F)) (publicIO : PublicIO F)
    (data : ProverData F) : Prop :=
  ∃ table ∈ tables, table.component.circuit.name = entry.table ∧
    ∃ row, entry.assertion.row.resolve table.table = some row ∧
      entry.assertion.Holds row publicIO data

/-- The assertion's `Spec` holds of the designated row of the named table. -/
def Entry.Spec (entry : Entry F PublicIO) (tables : List (Table F)) (publicIO : PublicIO F)
    (data : ProverData F) : Prop :=
  ∃ table ∈ tables, table.component.circuit.name = entry.table ∧
    ∃ row, entry.assertion.row.resolve table.table = some row ∧
      entry.assertion.RowSpec row publicIO data

theorem Entry.spec_of_holds (entry : Entry F PublicIO) {tables : List (Table F)}
    {publicIO : PublicIO F} {data : ProverData F} (h : entry.Holds tables publicIO data) :
    entry.Spec tables publicIO data := by
  obtain ⟨table, htable, hname, row, hrow, hholds⟩ := h
  exact ⟨table, htable, hname, row, hrow, entry.assertion.rowSpec_of_holds hholds⟩

end Air.Flat.Boundary
