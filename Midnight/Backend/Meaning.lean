import Midnight.Backend.Compile
import Midnight.Chips.CertifiedCircuit
import Clean.Halo2.ConfigurationHolds

/-! `ConfigurationHolds` against the reference meaning of a compiled source, `RowGatesHold` and
`RowLookupsHold`. `Agrees` checks, per circuit, that `compile` kept each `rows` entry's
polynomials and each unstated lookup's selector, tuples and tables, in order. Under it the two
are equivalent at every valuation: at the valuation one assignment gives, which is what
`RowsCircuit.soundness` needs (`configurationHolds_iff_of_reads`), and at Rust's reference
valuation (`rowValuation`) for every blinding, which is the completeness side. -/

namespace Midnight.Backend
open Halo2 (ConstraintSystem ConfigureExtension GateExtension LookupExtension Query
  ConfigurationHoldsAt)
open Midnight.Keygen Midnight.Chips.CertifiedCircuit

private def rowsOf : ConfigureExtension F → Option (GateExtension F)
  | .gate entry => if entry.mode = .rows then some entry else none
  | _ => none

private def unstatedOf : ConfigureExtension F → Option (LookupExtension F)
  | .lookup entry => if entry.stated = false then some entry else none
  | _ => none

/-- The `rows` entries, in order. -/
def rowsEntries (cs : ConstraintSystem F) : List (GateExtension F) :=
  cs.extensions.filterMap rowsOf

/-- The unstated lookup entries, in order. -/
def unstatedEntries (cs : ConstraintSystem F) : List (LookupExtension F) :=
  cs.extensions.filterMap unstatedOf

/-- Lookup data compared across the two sides: selector, tuples, tables. -/
abbrev LookupData := E × List (List E) × List E

def LookupExtension.data (entry : LookupExtension F) : LookupData :=
  (entry.selectorExpr, entry.tuples, entry.tables)

def _root_.Midnight.Keygen.BatchedLookup.data (l : BatchedLookup) : LookupData :=
  (l.selector, l.inputs.toList.map Array.toList, l.table.toList)

/-- `compile` kept, in order, the `rows` entries as the source's `rows` gates and the unstated
lookups as its unowned batches. -/
def Agrees (cs : ConstraintSystem F) (source : CS) : Bool :=
  (source.gateSpecs.filter (·.rows)).map (·.polynomials.toList) ==
      (rowsEntries cs).map (·.constraints.map (·.poly)) &&
    (source.lookups.toList.filter (·.owned == false)).map (·.data) ==
      (unstatedEntries cs).map LookupExtension.data

/-- Polynomials vanishing at every row. -/
def Vanish (n : ℕ) (value : ℕ → Query → F) (polys : List E) : Prop :=
  ∀ row < n, polys.Forall fun p => p.eval (value row) = 0

/-- Lookup membership at every usable row where the selector is nonzero. -/
def Member (usable : ℕ) (value : ℕ → Query → F) (lookup : LookupData) : Prop :=
  ∀ row < usable, lookup.1.eval (value row) ≠ 0 → lookup.2.1.Forall fun tuple =>
    ∃ tableRow < usable,
      tuple.map (·.eval (value row)) = lookup.2.2.map (·.eval (value tableRow))

/-- `RowGatesHold` at one valuation. -/
def RowGatesHoldAt (source : CS) (n : ℕ) (value : ℕ → Query → F) : Prop :=
  source.gateSpecs.Forall fun g => g.rows = true → ∀ row < n,
    g.polynomials.toList.Forall fun p => p.eval (value row) = 0

/-- `RowLookupsHold` at one valuation, over the unowned lookups. -/
def RowLookupsHoldAt (source : CS) (usable : ℕ) (value : ℕ → Query → F) : Prop :=
  source.lookups.toList.Forall fun l => l.owned = false → ∀ row < usable,
    l.selector.eval (value row) ≠ 0 → l.inputs.toList.Forall fun tuple =>
      ∃ tableRow < usable,
        tuple.toList.map (·.eval (value row)) = l.table.toList.map (·.eval (value tableRow))

private theorem forall_map_iff {α β : Type} (l : List α) (f : α → β) (P : β → Prop) :
    (l.map f).Forall P ↔ l.Forall fun a => P (f a) := by
  simp [List.forall_iff_forall_mem]

private theorem forall_filter_iff {α : Type} (l : List α) (p : α → Bool) (P : α → Prop) :
    (l.filter p).Forall P ↔ l.Forall fun a => p a = true → P a := by
  simp [List.forall_iff_forall_mem, List.mem_filter]

private theorem holds_iff {n usable : ℕ} {value : ℕ → Query → F}
    (e : ConfigureExtension F) :
    e.Holds n usable value ↔
      (∀ g, rowsOf e = some g → Vanish n value (g.constraints.map (·.poly))) ∧
      (∀ l, unstatedOf e = some l → Member usable value (LookupExtension.data l)) := by
  cases e with
  | gate g =>
    have hu : unstatedOf (.gate g) = none := rfl
    by_cases hm : g.mode = .rows
    · have hr : rowsOf (.gate g) = some g := by simp [rowsOf, hm]
      rw [hr, hu]
      constructor
      · intro h
        refine ⟨fun g' hg' => ?_, fun _ hl => (nomatch hl)⟩
        cases hg'
        unfold Vanish
        intro row hrow
        exact (forall_map_iff _ _ _).mpr (h hm row hrow)
      · rintro ⟨h, -⟩ _ row hrow
        exact (forall_map_iff _ _ _).mp (h g rfl row hrow)
    · have hr : rowsOf (.gate g) = none := by simp [rowsOf, hm]
      rw [hr, hu]
      constructor
      · intro _
        exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
      · intro _ h
        exact absurd h hm
  | lookup l =>
    have hr : rowsOf (.lookup l) = none := rfl
    cases hs : l.stated
    · have hu : unstatedOf (.lookup l) = some l := by simp [unstatedOf, hs]
      rw [hr, hu]
      constructor
      · intro h
        refine ⟨fun _ h' => (nomatch h'), fun l' hl' => ?_⟩
        cases hl'
        exact h hs
      · rintro ⟨-, h⟩ _
        exact h l rfl
    · have hu : unstatedOf (.lookup l) = none := by simp [unstatedOf, hs]
      rw [hr, hu]
      constructor
      · intro _
        exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
      · intro _ h
        exact Bool.noConfusion (hs.symm.trans h)
  | minimumDegree => simp [ConfigureExtension.Holds, rowsOf, unstatedOf]
  | rejected => simp [ConfigureExtension.Holds, rowsOf, unstatedOf]

/-- `ConfigurationHoldsAt` is the meaning of the `rows` entries and the unstated lookups. -/
theorem configurationHoldsAt_iff_entries (cs : ConstraintSystem F) (n usable : ℕ)
    (value : ℕ → Query → F) :
    ConfigurationHoldsAt cs n usable value ↔
      ((rowsEntries cs).map (·.constraints.map (·.poly))).Forall (Vanish n value) ∧
      ((unstatedEntries cs).map LookupExtension.data).Forall (Member usable value) := by
  rw [forall_map_iff, forall_map_iff]
  simp only [ConfigurationHoldsAt, rowsEntries, unstatedEntries, List.forall_iff_forall_mem,
    List.mem_filterMap]
  constructor
  · intro h
    exact ⟨fun g ⟨e, he, hg⟩ => ((holds_iff e).mp (h e he)).1 g hg,
      fun l ⟨e, he, hl⟩ => ((holds_iff e).mp (h e he)).2 l hl⟩
  · rintro ⟨hg, hl⟩ e he
    exact (holds_iff e).mpr
      ⟨fun g hge => hg g ⟨e, he, hge⟩, fun l hle => hl l ⟨e, he, hle⟩⟩

theorem rowGatesHoldAt_iff (source : CS) (n : ℕ) (value : ℕ → Query → F) :
    RowGatesHoldAt source n value ↔
      ((source.gateSpecs.filter (·.rows)).map (·.polynomials.toList)).Forall
        (Vanish n value) := by
  rw [forall_map_iff, forall_filter_iff]
  rfl

theorem rowLookupsHoldAt_iff (source : CS) (usable : ℕ) (value : ℕ → Query → F) :
    RowLookupsHoldAt source usable value ↔
      ((source.lookups.toList.filter (·.owned == false)).map (·.data)).Forall
        (Member usable value) := by
  rw [forall_map_iff, forall_filter_iff]
  unfold RowLookupsHoldAt Member BatchedLookup.data
  simp only [beq_iff_eq, forall_map_iff]

/-- Under `Agrees`, `ConfigurationHoldsAt` is the reference meaning at every valuation. -/
theorem configurationHoldsAt_iff {cs : ConstraintSystem F} {source : CS}
    (agrees : Agrees cs source = true) (n usable : ℕ) (value : ℕ → Query → F) :
    ConfigurationHoldsAt cs n usable value ↔
      RowGatesHoldAt source n value ∧ RowLookupsHoldAt source usable value := by
  simp only [Agrees, Bool.and_eq_true, beq_iff_eq] at agrees
  rw [configurationHoldsAt_iff_entries, rowGatesHoldAt_iff, rowLookupsHoldAt_iff, agrees.1,
    agrees.2]

/-- One environment's `ConfigurationHolds` is the reference meaning at any valuation `read` that
agrees with Clean's wrapped reading of it, such as Rust's checks on one assignment. This is the
predicate `RowsCircuit.soundness` assumes; the `∀ blind` form below is for completeness. -/
theorem configurationHolds_iff_of_reads {cs : ConstraintSystem F} {source : CS}
    (agrees : Agrees cs source = true) {n : ℕ} {ops : Halo2.Operations F}
    {place : Halo2.RegionIndex → ℕ} {env : Halo2.Environment F} {read : ℕ → Query → F}
    (reads : Halo2.wrappedRowValue n (ops.enabledSelectors place 0) env = read) :
    Halo2.ConfigurationHolds cs n ops place env ↔
      RowGatesHoldAt source n read ∧ RowLookupsHoldAt source env.usableRows read := by
  unfold Halo2.ConfigurationHolds
  rw [reads]
  exact configurationHoldsAt_iff agrees n env.usableRows read

/-- `configurationHolds_iff_of_reads` with `read` agreeing with Clean's wrapped reading only on
the domain, which holds the usable rows. Off it a periodic Rust reader and Clean's unwrapped
selector rows differ, and neither side reads there. -/
theorem configurationHolds_iff_of_readsOn {cs : ConstraintSystem F} {source : CS}
    (agrees : Agrees cs source = true) {n : ℕ} {ops : Halo2.Operations F}
    {place : Halo2.RegionIndex → ℕ} {env : Halo2.Environment F} {read : ℕ → Query → F}
    (usable : env.usableRows ≤ n)
    (reads : ∀ row < n, Halo2.wrappedRowValue n (ops.enabledSelectors place 0) env row = read row) :
    Halo2.ConfigurationHolds cs n ops place env ↔
      RowGatesHoldAt source n read ∧ RowLookupsHoldAt source env.usableRows read := by
  refine (configurationHolds_iff_of_reads (n := n) (ops := ops) (place := place) (env := env)
    agrees rfl).trans (and_congr ?_ ?_)
  · unfold RowGatesHoldAt
    simp only [List.forall_iff_forall_mem]
    exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun row => forall_congr' fun hrow => by rw [reads row hrow]
  · unfold RowLookupsHoldAt
    simp only [List.forall_iff_forall_mem]
    refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun row => forall_congr' fun hrow => ?_
    rw [reads row (lt_of_lt_of_le hrow usable)]
    exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      exists_congr fun tableRow => and_congr_right fun htable => by
        rw [reads tableRow (lt_of_lt_of_le htable usable)]

theorem rowGatesHold_iff (source : CS) (ops : Halo2.Operations F) (k : ℕ)
    (env : Halo2.Environment F) :
    RowGatesHold source ops k env ↔
      ∀ blind, RowGatesHoldAt source (2 ^ k) (rowValuation source ops k env blind) := by
  unfold RowGatesHold RowGatesHoldAt
  simp only [List.forall_iff_forall_mem]
  exact ⟨fun h blind g hg rows => h g hg rows blind, fun h g hg rows blind => h blind g hg rows⟩

/-- With every owned lookup's tables loaded, the lookups `RowLookupsHold` covers are the
unowned ones. -/
theorem rowLookupsHold_iff {source : CS} {ops : Halo2.Operations F}
    (loaded : source.lookups.toList.all (fun l => !l.owned || l.stated ops) = true) (k : ℕ)
    (env : Halo2.Environment F) :
    RowLookupsHold source ops k env ↔ ∀ blind,
      RowLookupsHoldAt source (layoutConfig source k).usableRows
        (rowValuation source ops k env blind) := by
  have key : ∀ l ∈ source.lookups.toList, l.stated ops = false ↔ l.owned = false := by
    intro l hl
    have hload := List.all_eq_true.mp loaded l hl
    cases ho : l.owned
    · simp [BatchedLookup.stated, ho]
    · simp only [ho, Bool.not_true, Bool.false_or] at hload
      simp [hload]
  unfold RowLookupsHold RowLookupsHoldAt
  simp only [List.forall_iff_forall_mem]
  exact ⟨fun h blind l hl owned => h l hl ((key l hl).mpr owned) blind,
    fun h l hl unstated blind => h blind l hl ((key l hl).mp unstated)⟩

theorem loaded_of_unowned {source : CS} {ops : Halo2.Operations F}
    (unowned : source.lookups.toList.all (fun l => !l.owned) = true) :
    source.lookups.toList.all (fun l => !l.owned || l.stated ops) = true :=
  List.all_eq_true.mpr fun l hl => by simp [List.all_eq_true.mp unowned l hl]

/-- On a compiled program: `ConfigurationHolds` at Rust's valuation, for every blinding, is the
source's `RowGatesHold ∧ RowLookupsHold`. -/
theorem compiled_configurationHolds_iff {cs : ConstraintSystem F} {source : CS}
    (agrees : Agrees cs source = true) {ops : Halo2.Operations F}
    (loaded : source.lookups.toList.all (fun l => !l.owned || l.stated ops) = true) (k : ℕ)
    (env : Halo2.Environment F) :
    (∀ blind, ConfigurationHoldsAt cs (2 ^ k) (layoutConfig source k).usableRows
        (rowValuation source ops k env blind)) ↔
      RowGatesHold source ops k env ∧ RowLookupsHold source ops k env := by
  rw [rowGatesHold_iff, rowLookupsHold_iff loaded]
  simp only [configurationHoldsAt_iff agrees]
  exact ⟨fun h => ⟨fun blind => (h blind).1, fun blind => (h blind).2⟩,
    fun h blind => ⟨h.1 blind, h.2 blind⟩⟩

end Midnight.Backend
