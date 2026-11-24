import Clean.Halo2.Configure.Extensions
import Clean.Halo2.Operations
import Clean.Halo2.SynthesisSummary.Region

/-!
# The meaning of the entries no shadow states

`rows` gates and unstated lookups have no Clean gate or lookup that synthesis enables, so
`Constraints` says nothing about them. `ConfigurationHolds` is their meaning, over the whole
placed circuit: every `rows` polynomial vanishes at every row of the domain, with rotations
wrapping, and every unstated lookup holds at every usable row where its selector is nonzero.
Selectors are read from the operations' enables. Stated entries add nothing, so for a program
that records only those, including every `Configure.Unextended` one, it is `True`.

`RowsCircuit` is the closed circuit whose soundness assumes it. `TopLevelCircuit` takes
soundness from `Constraints` alone, so no `RowsCircuit` reaches the zcash compiler.
-/

namespace Halo2

variable {F : Type}

/-- `(selector index, absolute row)` for each enable in a region starting at `start`: a gate's
own selector and a lookup's enabled ones. -/
def RegionOperations.enabledSelectors (start : ℕ) (body : RegionOperations F) :
    List (ℕ × ℕ) :=
  (body.flatMap FloorPlanner.regionOperationSelectorActivations).map fun (selector, row) =>
    (selector, start + row)

/-- The enables of the placed operations, the `i`th region placed at `place i`. -/
def Operations.enabledSelectors (place : RegionIndex → ℕ) :
    Operations F → RegionIndex → List (ℕ × ℕ)
  | [], _ => []
  | .region _ body :: ops, i =>
      body.enabledSelectors (place i) ++ Operations.enabledSelectors place ops (i + 1)
  | .constrainInstance _ _ _ :: ops, i => Operations.enabledSelectors place ops i
  | .loadTable _ _ :: ops, i => Operations.enabledSelectors place ops i

/-- A query's value at `row` of an `n`-row domain: a column cell at `row + rotation` modulo
`n`, since rotations wrap, and a selector 1 where `enabled` lists it, else 0. -/
def wrappedRowValue [Field F] (n : ℕ) (enabled : List (ℕ × ℕ)) (env : Environment F)
    (row : ℕ) : Query → F
  | .selector s => if (s.index, row) ∈ enabled then 1 else 0
  | .fixed column rotation => env.fixed column (((row : ℤ) + rotation) % (n : ℤ))
  | .advice column rotation => env.advice column (((row : ℤ) + rotation) % (n : ℤ))
  | .instance column rotation => env.inst column (((row : ℤ) + rotation) % (n : ℤ))

/-- Tuple `j` takes each column's `j`-th input. The width is the first column's, as in Rust. -/
def LookupExtension.tuples [Field F] (entry : LookupExtension F) :
    List (List (Expression F Query)) :=
  let width := (entry.columns.head?.map (·.1.length)).getD 0
  (List.range width).map fun j => entry.columns.map fun column => column.1.getD j (.const 0)

def LookupExtension.tables (entry : LookupExtension F) : List (Expression F Query) :=
  entry.columns.map (·.2)

/-- An entry's meaning at the valuation `value row` of each row. Stated entries add nothing.
A lookup's table side is read at the table row, selectors included, as LogUp weighs only the
inputs by the selector. -/
def ConfigureExtension.Holds [Field F] (n usable : ℕ) (value : ℕ → Query → F) :
    ConfigureExtension F → Prop
  | .gate entry => entry.mode = .rows → ∀ row < n,
      entry.constraints.Forall fun c => c.poly.eval (value row) = 0
  | .lookup entry => entry.stated = false → ∀ row < usable,
      entry.selectorExpr.eval (value row) ≠ 0 →
      entry.tuples.Forall fun tuple => ∃ tableRow < usable,
        tuple.map (·.eval (value row)) = entry.tables.map (·.eval (value tableRow))
  | .minimumDegree _ | .rejected _ => True

theorem ConfigureExtension.holds_of_stated [Field F] {n usable : ℕ} {value : ℕ → Query → F}
    {entry : ConfigureExtension F} (h : entry.stated = true) : entry.Holds n usable value := by
  cases entry with
  | gate gate =>
    intro rows
    simp [ConfigureExtension.stated, rows] at h
  | lookup lookup =>
    intro unstated
    simp [ConfigureExtension.stated, unstated] at h
  | minimumDegree => trivial
  | rejected => trivial

/-- Every entry holds at the valuation `value`. -/
def ConfigurationHoldsAt [Field F] (cs : ConstraintSystem F) (n usable : ℕ)
    (value : ℕ → Query → F) : Prop :=
  cs.extensions.Forall (·.Holds n usable value)

/-- The meaning of `cs`'s entries on the placed operations, over an `n`-row domain whose usable
rows are `env.usableRows`. -/
def ConfigurationHolds [Field F] (cs : ConstraintSystem F) (n : ℕ) (ops : Operations F)
    (place : RegionIndex → ℕ) (env : Environment F) : Prop :=
  ConfigurationHoldsAt cs n env.usableRows (wrappedRowValue n (ops.enabledSelectors place 0) env)

theorem ConfigurationHoldsAt.of_stated [Field F] {cs : ConstraintSystem F} {n usable : ℕ}
    {value : ℕ → Query → F} (h : cs.extensions.all (·.stated) = true) :
    ConfigurationHoldsAt cs n usable value :=
  List.forall_iff_forall_mem.mpr fun _ hentry =>
    ConfigureExtension.holds_of_stated (List.all_eq_true.mp h _ hentry)

theorem ConfigurationHolds.of_stated [Field F] {cs : ConstraintSystem F} {n : ℕ}
    {ops : Operations F} {place : RegionIndex → ℕ} {env : Environment F}
    (h : cs.extensions.all (·.stated) = true) : ConfigurationHolds cs n ops place env :=
  ConfigurationHoldsAt.of_stated h

/-- A program recording no entry means nothing beyond `Constraints`. -/
theorem ConfigurationHolds.of_unextended [Field F] {α : Type} (program : Configure F α)
    [h : Configure.Unextended program] (n : ℕ) (ops : Operations F) (place : RegionIndex → ℕ)
    (env : Environment F) : ConfigurationHolds (program.run {}).2 n ops place env := by
  unfold ConfigurationHolds ConfigurationHoldsAt
  show List.Forall _ (([] : List (ConfigureExtension F)) ++ ConfigureExtension.rebase 0 0
    (program.delta (ConfigureCounts.ofConstraintSystem {})).extensions)
  rw [h.extensions_eq_nil]
  simp

/-- A closed circuit whose configuration may record entries no shadow states: its soundness
assumes `ConfigurationHolds` beside `Constraints`, at every domain size `n`. -/
structure RowsCircuit (F : Type) [FiniteField F] (Config : Type) where
  configure : Configure F Config
  synthesize : Config → Operations F
  Spec : Config → ℕ → (RegionIndex → ℕ) → Environment F → Prop
  soundness : ∀ (n : ℕ) (place : RegionIndex → ℕ) (env : Environment F),
    Constraints place env (synthesize (configure.run {}).1) 0 →
    ConfigurationHolds (configure.run {}).2 n (synthesize (configure.run {}).1) place env →
    Spec (configure.run {}).1 n place env

namespace RowsCircuit

variable [FiniteField F] {Config : Type}

def config (circuit : RowsCircuit F Config) : Config := (circuit.configure.run {}).1

def constraintSystem (circuit : RowsCircuit F Config) : ConstraintSystem F :=
  (circuit.configure.run {}).2

def operations (circuit : RowsCircuit F Config) : Operations F :=
  circuit.synthesize circuit.config

/-- A circuit whose soundness needs `Constraints` alone. -/
def ofConstraints (configure : Configure F Config) (synthesize : Config → Operations F)
    (Spec : Config → (RegionIndex → ℕ) → Environment F → Prop)
    (soundness : ∀ place env, Constraints place env (synthesize (configure.run {}).1) 0 →
      Spec (configure.run {}).1 place env) : RowsCircuit F Config where
  configure := configure
  synthesize := synthesize
  Spec config _ := Spec config
  soundness := fun _ place env constraints _ => soundness place env constraints

end RowsCircuit

end Halo2
