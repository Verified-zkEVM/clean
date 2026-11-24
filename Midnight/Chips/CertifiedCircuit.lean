import Midnight.Keygen.ConfigureLawful
import Midnight.Chips.Layout
import Midnight.Chips.CopyLawful
import Midnight.Chips.OperationsLawful

/-! Structural certificates for the explicit-assignment Midnight circuit fragment.
The source configuration, operations, domain size and planner index the certificate, so
proofs cannot be detached from the data passed to the layout compiler. This is
not a witness-correctness proof or a proof of the cryptographic backend. -/

namespace Midnight.Chips.CertifiedCircuit
open Halo2 Midnight.Keygen

def permutationColumns (source : CS) : List Halo2.Layout.ColRef :=
  source.permutation.toList.map fun column =>
    match column.kind with
    | .advice => .advice column.index
    | .fixed => .fixed column.index
    | .instance => .instance column.index

def fixedColumns (source : CS) : List (Column .fixed) :=
  (List.range source.numFixed).map fun index => ⟨index⟩

def layoutConfig (source : CS) (k : Nat) : Midnight.Chips.Layout.Config :=
  { numAdvice := source.numAdvice
    numFixed := source.numFixed
    numInstance := source.numInstance
    numSelectors := source.numSelectors
    blindingFactors := source.blindingFactors
    k := k
    constant := source.constantColumn }

/-- The planner's data is the source's. -/
def plannerFor (source : CS) : Layout.Planner → Prop
  | .simple => True
  | .v1 columns => columns = source.constantColumns.toList

/-- The certificate of the stream Lean lowers. Rust's key for a stream `ops` is that of
`Canonical.rustOps source ops` (`Export.layout`), which admits every enable and instance-copy
form Rust keys. -/
structure Certificate (source : CS) (ops : Operations F) (k : Nat)
    (planner : Layout.Planner := .simple) : Type where
  configuration : source.WellFormed
  /-- Rust's `minimum_rows`: keygen fails with `NotEnoughRowsAvailable` below it. -/
  rows : source.blindingFactors + 3 ≤ 2 ^ k
  layout : Midnight.Chips.Layout.CertifiedLayout ops
    (permutationColumns source) (layoutConfig source k) planner
  copies : CopyLawful.Lawful ops
    (CS.Checked.toCleanDelta ⟨source, configuration⟩).gates
    (CS.Checked.toCleanDelta ⟨source, configuration⟩).lookups
    (fixedColumns source) (permutationColumns source)
    (planner.starts source.constantColumn ops) (layoutConfig source k).usableRows
    source.constantColumn planner
  operations : OperationsLawful.Lawful ops
    (CS.Checked.toCleanDelta ⟨source, configuration⟩).gates
    (CS.Checked.toCleanDelta ⟨source, configuration⟩).lookups
    source.counts (planner.starts source.constantColumn ops) (layoutConfig source k).usableRows
  /-- V1 fills the source's constants columns (`keygen_vk` passes `cs.constants`). -/
  planned : plannerFor source planner := by first | exact True.intro | rfl

/-- The advice cells the regions assign, at absolute rows. -/
def adviceCells (starts : List Nat) (ops : Operations F) : List (Nat × Nat) :=
  (indexedRegions ops 0).1.flatMap fun (region, body) => body.filterMap fun
    | .assignAdvice column row _ => some (column.index, Halo2.Layout.place starts region + row)
    | _ => none

/-- What Rust's vanishing argument reads at `row` of the `2^k`-row domain, rotations wrapping:
selectors from the activations, fixed columns from the keygen matrix (0 where nothing is
written), assigned advice from `env` and 0 at other usable rows, `blind` at the unusable rows
the prover randomizes (prover.rs:552), and instance from `env`, 0 at unusable rows. Rows are at
the Simple planner's placement; V1 certificates are out of scope. -/
def rowValuation (source : CS) (ops : Operations F) (k : Nat) (env : Environment F)
    (blind : Nat → Nat → F) (row : Nat) : Query → F :=
  let config := layoutConfig source k
  let fixed := LayoutLawful.dense config.rows config.numFixed (Layout.sourceFixedWrites ops config)
  let at_ (rotation : Int) : Nat := ((row + rotation : ℤ) % (2 ^ k : Nat)).toNat
  fun
  | .selector q =>
      if (q.index, row) ∈ Layout.sourceActivations ops source.constantColumn then 1 else 0
  | .fixed column rotation => (((fixed.getD column.index []).getD (at_ rotation) 0 : Nat) : F)
  | .advice column rotation =>
      let r := at_ rotation
      if config.usableRows ≤ r then blind column.index r
      else if (column.index, r) ∈ adviceCells (Layout.Planner.simple.starts source.constantColumn ops) ops
      then env.advice column r else 0
  | .instance column rotation =>
      let r := at_ rotation
      if config.usableRows ≤ r then 0 else env.inst column r

/-- The meaning of the source's `rows` gates and trash arguments, which no Clean operation states:
every polynomial vanishes at every row of the domain for every blinding, since custom gates carry
no `l_active` factor (proofs/src/plonk/evaluation.rs:848). A trash argument's identity
`Σ rⁱ cᵢ = (1 - q) · trash` also holds at every row, so where its 0/1 selector `q` is 1 each `cᵢ`
vanishes (up to the challenge `r`), which is `q * cᵢ = 0`. -/
def RowGatesHold (source : CS) (ops : Operations F) (k : Nat) (env : Environment F) : Prop :=
  source.gateSpecs.Forall fun g => g.rows = true →
    ∀ blind : Nat → Nat → F, ∀ row < 2 ^ k, g.polynomials.toList.Forall fun p =>
      p.eval (rowValuation source ops k env blind row) = 0

/-- An `owned` lookup whose table columns `ops` all load: Clean's `enableLookup` then reads Rust's
table, since `loadTable` pins each column on every usable row and a row past Rust's usable ones
repeats row 0. Its every-row meaning needs no other statement. -/
def _root_.Midnight.Keygen.BatchedLookup.stated (l : BatchedLookup) (ops : Operations F) : Bool :=
  l.owned && l.table.toList.all fun e =>
    (tableColumn? e).any (OperationsLawful.tableColumns ops).contains

/-- The meaning of the source's lookups that are not `stated`, which no Clean operation fixes to
Rust's columns: at every usable row where the selector (`Constant(1)` for `None`) is nonzero, each
input tuple is the table tuple of some usable row, both read from Rust's columns, real selector
columns included. LogUp's accumulator weighs the inputs by the selector and the table by nothing
(logup.rs:397-399). -/
def RowLookupsHold (source : CS) (ops : Operations F) (k : Nat) (env : Environment F) : Prop :=
  source.lookups.toList.Forall fun l => l.stated ops = false →
    ∀ blind : Nat → Nat → F, ∀ row < (layoutConfig source k).usableRows,
      l.selector.eval (rowValuation source ops k env blind row) ≠ 0 →
      l.inputs.toList.Forall fun tuple => ∃ tableRow < (layoutConfig source k).usableRows,
        tuple.toList.map (·.eval (rowValuation source ops k env blind row)) =
          l.table.toList.map (·.eval (rowValuation source ops k env blind tableRow))

/-- Rust's vanishing argument on the stream: Clean's constraints on the operations, which carry
every owned gate and lookup, `RowGatesHold` and `RowLookupsHold`, the latter two at the Simple
planner's placement (see `rowValuation`). A completeness claim states this; soundness may assume
`Constraints` alone. -/
def Satisfied (source : CS) (ops : Operations F) (k : Nat) (place : RegionIndex → Nat)
    (env : Environment F) : Prop :=
  Constraints place env ops 0 ∧ RowGatesHold source ops k env ∧ RowLookupsHold source ops k env

theorem RowGatesHold.of_owned {source : CS} (owned : source.gateSpecs.all (fun g => !g.rows) = true)
    (ops : Operations F) (k : Nat) (env : Environment F) : RowGatesHold source ops k env := by
  unfold RowGatesHold
  rw [List.forall_iff_forall_mem]
  intro g hg rows
  have hg := List.all_eq_true.mp owned g hg
  simp [rows] at hg

theorem RowLookupsHold.of_stated {source : CS} {ops : Operations F}
    (stated : source.lookups.toList.all (·.stated ops) = true) (k : Nat) (env : Environment F) :
    RowLookupsHold source ops k env := by
  unfold RowLookupsHold
  rw [List.forall_iff_forall_mem]
  intro l hl notStated
  simp [List.all_eq_true.mp stated l hl] at notStated

def Certificate.toDerivedLayout {source : CS} {ops : Operations F} {k : Nat} {planner : Layout.Planner}
    (cert : Certificate source ops k planner) : Midnight.Chips.Layout.DerivedLayout :=
  cert.layout.toDerivedLayout

end Midnight.Chips.CertifiedCircuit
