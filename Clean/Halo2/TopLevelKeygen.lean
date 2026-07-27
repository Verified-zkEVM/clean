import Clean.Halo2.TopLevel
import Clean.Halo2.Keygen

/-!
# Keygen data derived from a top-level circuit

The semantic `TopLevelCircuit` stays independent of any verifier implementation.
This module adds the circuit-owned keygen view: pinned constraint system, V1
placement, domain-fit quantities, and the generic proof that a fitting keygen domain
supplies `SynthesisWellFormed`.
-/

namespace Halo2

namespace SynthesisWellFormed

variable {F : Type} [FiniteField F]

private theorem accumulator_le_foldl_max (values : List ℕ) (acc : ℕ) :
    acc ≤ values.foldl max acc := by
  induction values generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons value values ih =>
      exact le_trans (Nat.le_max_left acc value) (ih (max acc value))

private theorem member_le_foldl_max (values : List ℕ) (value acc : ℕ)
    (hmember : value ∈ values) :
    value ≤ values.foldl max acc := by
  induction values generalizing acc with
  | nil => simp only [List.not_mem_nil] at hmember
  | cons head tail ih =>
      simp only [List.mem_cons] at hmember
      rcases hmember with hhead | htail
      · rw [hhead]
        exact le_trans (Nat.le_max_right acc head)
          (accumulator_le_foldl_max tail (max acc head))
      · exact ih (max acc head) htail

omit [FiniteField F] in
private theorem loadTable_length_le_usedRows
    (operations : Operations F) (table : TableColumn) (values : List F)
    (hload : Operation.loadTable table values ∈ operations) :
    values.length ≤ Halo2.usedRows operations := by
  let tableLengths := operations.filterMap fun operation =>
    match operation with
    | .loadTable _ loaded => some loaded.length
    | _ => none
  have hlength : values.length ∈ tableLengths := by
    apply List.mem_filterMap.mpr
    exact ⟨.loadTable table values, hload, rfl⟩
  have htable : values.length ≤ tableLengths.foldl max 0 :=
    member_le_foldl_max tableLengths values.length 0 hlength
  unfold Halo2.usedRows
  exact le_trans htable (Nat.le_max_right _ _)

/--
Every table block fits an environment whose usable rows cover the keygen operation
footprint.  This is the generic compiler/layout fact consumed by top-level circuit
closure.
-/
theorem of_usedRows
    (env : Environment F) (operations : Operations F)
    (hrows : Halo2.usedRows operations ≤ env.usableRows) :
    SynthesisWellFormed env operations where
  tablesFit table values hload :=
    le_trans (loadTable_length_le_usedRows operations table values hload) hrows

end SynthesisWellFormed

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- The pinned constraint system derived solely from the closed circuit. -/
def pinnedCS (self : TopLevelCircuit F Config PublicInput) :
    PinnedConstraintSystem F :=
  self.formalCircuit.toPinnedCS () ()

/-- V1 region starts derived from the circuit's own operation stream. -/
def regionStarts (self : TopLevelCircuit F Config PublicInput) : List ℕ :=
  FloorPlanner.V1.starts self.operations

/-- Selector activations produced by the circuit's own synthesis and V1 placement. -/
def selectorActivations
    (self : TopLevelCircuit F Config PublicInput) :
    List (ℕ × ℕ) :=
  activations self.regionStarts
    (indexedRegions self.operations 0).1

/-- The circuit-owned V1 placement function. -/
def placement (self : TopLevelCircuit F Config PublicInput) :
    RegionIndex → ℕ :=
  fun region => self.regionStarts.getD region 0

@[simp] theorem placement_apply
    (self : TopLevelCircuit F Config PublicInput) (region : RegionIndex) :
    self.placement region = self.regionStarts.getD region 0 :=
  rfl

/-- The operation footprint that key generation requires to fit in usable rows. -/
def usedRows (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  Halo2.usedRows self.operations

/-- The smallest keygen domain exponent derived from this circuit's CS and operations. -/
def domainExponent (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  Halo2.minimalK self.constraintSystem self.operations

/--
The selector-compression map derived from the circuit's own constraint system,
operation stream, placement, and minimal fitting domain.
-/
def selectorMap
    (self : TopLevelCircuit F Config PublicInput) :
    SelCompressMap :=
  deriveSelCompressMap self.constraintSystem
    (2 ^ self.domainExponent) self.selectorActivations

/--
The circuit-owned pinned constraint system is exactly the projection using its
circuit-owned selector map.
-/
theorem pinnedCS_eq_derive
    (self : TopLevelCircuit F Config PublicInput) :
    self.pinnedCS =
      PinnedConstraintSystem.derive self.constraintSystem self.selectorMap := by
  rfl

/-- The blinding-row count derived from the circuit's own configure run. -/
def blindingFactors (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.constraintSystem.blindingFactors

/-- Halo2's usable-row count at a proposed evaluation-domain exponent. -/
def usableRowsAt (self : TopLevelCircuit F Config PublicInput) (k : ℕ) : ℕ :=
  2 ^ k - self.blindingFactors - 1

/-- The keygen fit assertion for a proposed domain exponent. -/
def FitsAt (self : TopLevelCircuit F Config PublicInput) (k : ℕ) : Prop :=
  self.usedRows + self.blindingFactors + 1 ≤ 2 ^ k

/--
The bounded `minimalK` search supplies the keygen fit inequality whenever it returns
a supported Pasta domain exponent rather than its sentinel value `33`.
-/
theorem fitsAt_domainExponent
    (self : TopLevelCircuit F Config PublicInput)
    (hbound : self.domainExponent < 33) :
    self.FitsAt self.domainExponent := by
  let need :=
    max (self.usedRows + self.blindingFactors + 1)
      self.constraintSystem.minimumRows
  have findFits (need : ℕ)
      (hbound :
        ((List.range 33).find? (fun k => need ≤ 2 ^ k)).getD 33 < 33) :
      need ≤ 2 ^
        ((List.range 33).find? (fun k => need ≤ 2 ^ k)).getD 33 := by
    generalize hfind :
      (List.range 33).find? (fun k => need ≤ 2 ^ k) = result at hbound ⊢
    cases result with
    | none => simp at hbound
    | some k =>
        simpa using List.find?_some hfind
  have hk : need ≤ 2 ^ self.domainExponent := by
    apply findFits need
    simpa [domainExponent, Halo2.minimalK, need] using hbound
  unfold FitsAt
  exact (Nat.le_max_left _ _).trans hk

/-- A fitting keygen domain has strictly more rows than its blinding count. -/
theorem blindingFactors_lt_domainSize
    (self : TopLevelCircuit F Config PublicInput)
    (k : ℕ) (hfit : self.FitsAt k) :
    self.blindingFactors < 2 ^ k := by
  unfold FitsAt at hfit
  omega

/--
A nonempty operation footprint leaves at least one non-blinding usable row
before the final usable row.
-/
theorem blindingFactors_succ_lt_domainSize
    (self : TopLevelCircuit F Config PublicInput)
    (k : ℕ) (hfit : self.FitsAt k)
    (hused : 0 < self.usedRows) :
    self.blindingFactors + 1 < 2 ^ k := by
  unfold FitsAt at hfit
  omega

theorem usedRows_le_usableRowsAt
    (self : TopLevelCircuit F Config PublicInput) (k : ℕ)
    (hfit : self.FitsAt k) :
    self.usedRows ≤ self.usableRowsAt k := by
  unfold FitsAt at hfit
  unfold usableRowsAt
  omega

/--
A fitting circuit-owned keygen domain supplies the exact synthesis well-formedness
certificate expected by generic top-level soundness.
-/
theorem synthesisWellFormed
    (self : TopLevelCircuit F Config PublicInput)
    (k : ℕ) (env : Environment F)
    (husable : env.usableRows = self.usableRowsAt k)
    (hfit : self.FitsAt k) :
    SynthesisWellFormed env self.operations := by
  apply SynthesisWellFormed.of_usedRows
  rw [husable]
  exact self.usedRows_le_usableRowsAt k hfit

end TopLevelCircuit

end Halo2
