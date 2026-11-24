import Midnight.Keygen.Configure
import Clean.Halo2.Configure.Queries
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
Proof-carrying source configurations. Gate and lookup polynomials are Clean's own
`Halo2.Expression`, so the structural laws are upstream's `SelectorFree`, `QueriesDeclared` and
`QueryAtom`, decided through their executable forms. Only registration against
Midnight's recorded query layouts is stated here. The Clean view describes active-row
gate equations and lookup membership; it does not identify LogUp or additive-selector
protocol soundness with those relations, nor prove that a source port implements SHA.
-/

namespace Midnight.Keygen
open Halo2 (Expression)

/-- An ordinary query is present in the authoritative source registration list.
Selectors have no query-layout slot; their allocation is checked separately. -/
def CS.RegistersQuery (s : CS) : Halo2.Query → Prop
  | .selector _ => True
  | .advice c r => (c.index, r) ∈ s.adviceQueries.toList
  | .fixed c r => (c.index, r) ∈ s.fixedQueries.toList
  | .instance c r => (c.index, r) ∈ s.instanceQueries.toList

instance (s : CS) (q : Halo2.Query) : Decidable (s.RegistersQuery q) := by
  cases q <;> unfold CS.RegistersQuery <;> infer_instance

/-- Every query atom of a polynomial is registered in the source layouts. -/
def _root_.Halo2.Expression.Registered (s : CS) (e : E) : Prop :=
  e.queryAtoms.Forall s.RegistersQuery

/-- The selectors the gate uses are allocated. -/
def GateSpec.SelectorsAllocated (s : CS) (g : GateSpec) : Prop :=
  g.selectorUses.Forall (·.index < s.numSelectors)

instance (s : CS) (g : GateSpec) : Decidable (g.SelectorsAllocated s) := by
  unfold GateSpec.SelectorsAllocated; infer_instance

def GateSpec.Lawful (s : CS) (g : GateSpec) : Prop :=
  g.SelectorsAllocated s ∧
  g.queries.toList.Forall (fun q => queryAtom q = true ∧ s.RegistersQuery q) ∧
  g.constraints.toList.Forall (fun c =>
    (g.rows || g.bodyValid c.2) = true ∧ c.2.QueriesDeclared (g.queries.toList.map (.var ·)))

theorem GateSpec.Lawful.valid {s : CS} {g : GateSpec} (h : g.Lawful s) : g.valid = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro q hq
    exact ((List.forall_iff_forall_mem.mp h.2.1) q hq).1
  · apply List.all_eq_true.mpr
    rintro ⟨name, p⟩ hc
    have hp := (List.forall_iff_forall_mem.mp h.2.2) (name, p) hc
    exact Bool.and_eq_true_iff.mpr ⟨hp.1, (Expression.declared_iff p _).mpr hp.2⟩

/-- The selectors the lookup uses are allocated. -/
def BatchedLookup.SelectorAllocated (s : CS) (l : BatchedLookup) : Prop :=
  l.selectorAtoms.Forall (·.index < s.numSelectors)

instance (s : CS) (l : BatchedLookup) : Decidable (l.SelectorAllocated s) := by
  unfold BatchedLookup.SelectorAllocated; infer_instance

/-- A rectangular batch of at least one table expression querying only registered columns and
allocated selectors. Rust keys a batch of no tuples (logup.rs:296). -/
def BatchedLookup.Lawful (s : CS) (l : BatchedLookup) : Prop :=
  l.valid = true ∧ l.SelectorAllocated s ∧ 0 < l.table.size ∧
  l.table.toList.Forall (·.Registered s) ∧
  l.inputs.toList.Forall (fun row => row.toList.Forall (·.Registered s))

theorem BatchedLookup.Lawful.valid {s : CS} {l : BatchedLookup}
    (h : l.Lawful s) : l.valid = true := h.1

def CS.counts (s : CS) : Halo2.ConfigureCounts :=
  ⟨s.numAdvice, s.numFixed, s.numInstance, s.numSelectors⟩

def CS.gateSpecs (s : CS) : List GateSpec := (s.gates ++ s.trashcans).toList

def CS.selectorUses (s : CS) : List Halo2.Selector :=
  s.gateSpecs.flatMap (·.selectorUses) ++ s.lookups.toList.flatMap (·.selectorAtoms)

def CS.RegistersPermutation (s : CS) (c : Halo2.AnyColumn) : Prop :=
  s.RegistersQuery (match c.kind with
    | .advice => .advice ⟨c.index⟩ 0
    | .fixed => .fixed ⟨c.index⟩ 0
    | .instance => .instance ⟨c.index⟩ 0)

instance (s : CS) (c : Halo2.AnyColumn) : Decidable (s.RegistersPermutation c) := by
  unfold CS.RegistersPermutation
  infer_instance

def QueryLayout.Allocated (count : Nat) (queries : Array (Nat × Int)) : Prop :=
  queries.toList.Nodup ∧ queries.toList.Forall (fun q => q.1 < count)

instance (count : Nat) (queries : Array (Nat × Int)) :
    Decidable (QueryLayout.Allocated count queries) := by
  unfold QueryLayout.Allocated
  infer_instance

/-- Enabled constant columns are allocated, unique and equality registered. -/
def CS.ConstantsWellFormed (s : CS) : Prop :=
  s.constantColumns.toList.Nodup ∧ s.constantColumns.toList.Forall
    (fun column => column < s.numFixed ∧ ⟨.fixed, column⟩ ∈ s.permutation.toList)

instance (s : CS) : Decidable s.ConstantsWellFormed := by
  unfold CS.ConstantsWellFormed
  infer_instance

/-- Structural obligations for the Clean view (queries, allocation, selector ownership, lookup
arity), plus `CS.validate`, which rejects what Rust's keygen would not key. -/
@[mk_iff] structure CS.WellFormed (s : CS) : Prop where
  source : s.selectorFixedStart = none
  noErrors : s.errors = #[]
  advice : QueryLayout.Allocated s.numAdvice s.adviceQueries
  fixed : QueryLayout.Allocated s.numFixed s.fixedQueries
  instanceQueries : QueryLayout.Allocated s.numInstance s.instanceQueries
  gates : s.gateSpecs.Forall (GateSpec.Lawful s)
  lookups : s.lookups.toList.Forall (BatchedLookup.Lawful s)
  permutation : s.permutation.toList.Nodup ∧ s.permutation.toList.Forall s.RegistersPermutation
  trashComplex : s.trashcans.toList.Forall (fun g => g.selector.simple = false)
  /-- Native `create_gate` checks the body before moving additive constraints
  into a trash argument. `additiveGate`'s empty gate entries are permitted. -/
  trashNonempty : s.trashcans.toList.Forall (fun g => 0 < g.constraints.size)
  /-- Trash arguments have no `without_selector` form (`validate`): `q * c` is their meaning. -/
  trashSelected : s.trashcans.toList.Forall (fun g => g.raw = false)
  selectorKinds : s.selectorUses.Forall (fun q =>
    s.selectorUses.Forall (fun r => q.index = r.index → q.simple = r.simple))
  constants : s.ConstantsWellFormed
  validated : s.validate.isOk = true

/-- The protocol data and a certificate for its active-row Clean interpretation. -/
structure CS.Checked where
  raw : CS
  lawful : raw.WellFormed

private def typedQueries (kind : Halo2.ColumnKind) (queries : Array (Nat × Int)) :
    List (Halo2.Column kind × Int) :=
  queries.toList.map fun (c, r) => (⟨c⟩, r)

/-- One Clean gate per source gate and trashcan. -/
def CS.Checked.gateHandles (c : CS.Checked) : List (Halo2.Gate F) :=
  c.raw.gateSpecs.attach.map fun ⟨g, hg⟩ =>
    g.toClean (((List.forall_iff_forall_mem.mp c.lawful.gates) g hg).valid)

/-- `rows` gates' handles on their non-owner selectors. -/
def CS.Checked.rowsHandles (c : CS.Checked) : List (Halo2.Gate F) :=
  c.raw.gateSpecs.attach.flatMap fun ⟨g, hg⟩ =>
    g.rowsHandles (((List.forall_iff_forall_mem.mp c.lawful.gates) g hg).valid)

theorem CS.Checked.rowsHandles_of_owned (c : CS.Checked)
    (owned : c.raw.gateSpecs.all (fun g => !g.rows) = true) : c.rowsHandles = [] := by
  unfold CS.Checked.rowsHandles
  apply List.flatMap_eq_nil_iff.mpr
  rintro ⟨g, hg⟩ _
  exact GateSpec.rowsHandles_of_owned _ _ (by simpa using List.all_eq_true.mp owned g hg)

/-- Handles on the selectors of lookups that are not `owned`. -/
def CS.Checked.lookupHandles (c : CS.Checked) : List (Halo2.Gate F) :=
  c.raw.lookups.toList.flatMap (·.handles)

theorem CS.Checked.lookupHandles_of_owned (c : CS.Checked)
    (owned : c.raw.lookups.toList.all (·.owned) = true) : c.lookupHandles = [] := by
  unfold CS.Checked.lookupHandles
  apply List.flatMap_eq_nil_iff.mpr
  intro l hl
  exact BatchedLookup.handles_of_owned l (List.all_eq_true.mp owned l hl)

/-- Selectors no gate or lookup uses. Rust may still enable them. -/
def CS.unusedSelectors (s : CS) : List Nat :=
  (List.range s.numSelectors).filter fun i => !s.selectorUses.any (·.index == i)

/-- Handles on unused selectors, so that their enables are configured. -/
def CS.Checked.unusedHandles (c : CS.Checked) : List (Halo2.Gate F) :=
  c.raw.unusedSelectors.map fun i =>
    ({ name := "", selector := ⟨i, false⟩, queries := #[], constraints := #[], rows := true } :
      GateSpec).toCleanRows rfl

theorem CS.Checked.unusedHandles_of_used (c : CS.Checked) (used : c.raw.unusedSelectors = []) :
    c.unusedHandles = [] := by
  simp [CS.Checked.unusedHandles, used]

def CS.Checked.toCleanDelta (c : CS.Checked) : Halo2.ConfigureDelta F where
  gates := c.gateHandles ++ c.rowsHandles ++ c.lookupHandles ++ c.unusedHandles
  lookups := c.raw.lookups.toList.attach.flatMap fun ⟨l, hl⟩ =>
    l.toClean (((List.forall_iff_forall_mem.mp c.lawful.lookups) l hl).valid)
  adviceQueries := typedQueries .advice c.raw.adviceQueries
  fixedQueries := typedQueries .fixed c.raw.fixedQueries
  instanceQueries := typedQueries .instance c.raw.instanceQueries
  permutationRequests := c.raw.permutation.toList
  constants := c.raw.constantColumns.toList.map fun index => ⟨index⟩

end Midnight.Keygen
