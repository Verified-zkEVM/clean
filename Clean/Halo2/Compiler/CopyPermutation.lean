import Clean.Halo2.Compiler.CompiledCopies
import Clean.Halo2.Compiler.PermutationAssembly
import Clean.Halo2.Compiler.PermutationRows
import Clean.Halo2.Compiler.FieldSupport

/-! # The compiled copy permutation

Registration, placement and constant allocation give bounded copy cells. Executable
assembly implements their permutation, whose cycles enforce the source equalities.
-/

variable {F : Type} [FiniteField F]

namespace Halo2.TopLevelCircuit

open Layout

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Compiler permutation columns in verifying-key order. -/
def permutationLayout : List ColRef :=
  permColsOf top.constraintSystem

/-- The copy compiler and the published shape use the same column count. -/
theorem permutationLayout_length : (top.permutationLayout).length = top.permutationColumnCount := by
  rw [top.permutationColumnCount_eq_permutationColumns_length]
  simp only [permutationLayout, Layout.permColsOf, List.length_map, permutationColumns]

/-- Fixed cells allocated by V1 for constant copies. -/
def constantCopyEntries : List (ℕ × ℕ × ℕ) :=
  Layout.constantCopyEntries top.constraintSystem top.operations

theorem usedRows_le_domainSize :
    Halo2.usedRows top.operations ≤ top.n :=
  top.operations_usedRows_le_usedRows.trans
    (top.usedRows_le_usableRowsAt_domainExponent.trans
      top.usableRowsAt_domainExponent_le_n)

omit [TopLevelShape top] in
/-- Every allocated constant uses an equality-enabled fixed column. -/
theorem const_column_mem_permutationColumns
    (entry : ℕ × ℕ × ℕ) (hentry : entry ∈ (top.constantCopyEntries)) :
    (AnyColumn.mk .fixed entry.2.1) ∈
      top.constraintSystem.permutationColumns := by
  rw [constantCopyEntries, Layout.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact top.constantAssignmentColumn_mem_permutationColumns
    hassignment

/-- Both endpoints of a compiled copy belong to the permutation-column layout. -/
theorem copyPairs_columns_lt : ∀ t ∈ top.copyPairs,
    t.1 < top.permutationColumnCount ∧ t.2.2.1 < top.permutationColumnCount := by
  intro tuple htuple
  rw [← top.permutationLayout_length]
  apply V1_copyList_columns_lt top.constraintSystem
    top.operations top.keygenCoherent
    top.regionStarts (top.constantCopyEntries)
    (const_column_mem_permutationColumns top) tuple
  simpa only [copyPairs, permutationLayout] using htuple

omit [TopLevelShape top] in
/-- Every V1 circuit constant allocation lies below the compiler-derived operation
footprint. -/
theorem const_row_lt_usedRows
    (entry : ℕ × ℕ × ℕ) (hentry : entry ∈ (top.constantCopyEntries)) :
    entry.2.2 < Halo2.usedRows top.operations := by
  rw [constantCopyEntries, Layout.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact V1_constantAssignments_row_lt_usedRows
    top.operations
    (top.constraintSystem.constants.map (·.index))
    hassignment

omit [TopLevelShape top] in
/-- Every raw circuit keygen copy endpoint lies below the compiler-derived operation
footprint. -/
theorem copyPairs_rows_lt_usedRows
    (tuple : ℕ × ℕ × ℕ × ℕ) (htuple : tuple ∈ top.copyPairs) :
    tuple.2.1 < Halo2.usedRows top.operations ∧
      tuple.2.2.2 < Halo2.usedRows top.operations := by
  apply V1_copyList_rows_lt_usedRows top.operations
    (top.permutationLayout) (top.constantCopyEntries)
    (const_row_lt_usedRows top) tuple
  simpa only [copyPairs, regionStarts,
    TopLevelCompilation.regionStarts] using htuple

/-- Registration and the compiler footprint bound both coordinates of each copy. -/
theorem copyPairs_bounds : ∀ t ∈ top.copyPairs, t.1 < top.permutationColumnCount ∧
    t.2.1 < top.n ∧ t.2.2.1 < top.permutationColumnCount ∧
    t.2.2.2 < top.n := by
  intro tuple htuple
  have hcolumns := (top.copyPairs_columns_lt) tuple htuple
  have hrows := (top.copyPairs_rows_lt_usedRows) tuple htuple
  exact ⟨hcolumns.1, hrows.1.trans_le (usedRows_le_domainSize top),
    hcolumns.2, hrows.2.trans_le (usedRows_le_domainSize top)⟩

/-- The decoded circuit copy list. -/
def boundedCopyPairs :
    List (FlatCell top.permutationColumnCount top.n ×
      FlatCell top.permutationColumnCount top.n) :=
  decodeCopies top.permutationColumnCount top.n top.copyPairs (top.copyPairs_bounds)

/-- Every decoded copy pair lies in the compiler-derived usable-row prefix. -/
theorem boundedCopyPairs_rows_lt
    (pair : FlatCell top.permutationColumnCount top.n ×
      FlatCell top.permutationColumnCount top.n)
    (hpair : pair ∈ (top.boundedCopyPairs)) :
    (pair.1.2 : ℕ) < (top.usableRowsAt top.domainExponent) ∧
      (pair.2.2 : ℕ) < (top.usableRowsAt top.domainExponent) := by
  have hrawMap := decodeCopies_map top.permutationColumnCount top.n
    top.copyPairs (top.copyPairs_bounds)
  have hraw :
      (pair.1.pair.1, pair.1.pair.2,
        pair.2.pair.1, pair.2.pair.2) ∈ top.copyPairs := by
    rw [← hrawMap]
    exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  have hrows := (top.copyPairs_rows_lt_usedRows) _ hraw
  have husedRows :
      Halo2.usedRows top.operations ≤ (top.usableRowsAt top.domainExponent) :=
    top.operations_usedRows_le_usedRows.trans
      top.usedRows_le_usableRowsAt_domainExponent
  exact ⟨hrows.1.trans_le husedRows, hrows.2.trans_le husedRows⟩

/-- The compiled permutation, in global column/row coordinates. -/
def copyPermutation : Equiv.Perm (FlatCell top.permutationColumnCount top.n) :=
  PermConstruction.replay (top.boundedCopyPairs)

/-- Circuit keygen replays preserve the usable-row prefix. -/
theorem copyPermutation_preserves_usableRows
    (cell : FlatCell top.permutationColumnCount top.n)
    (hcell : (cell.2 : ℕ) < (top.usableRowsAt top.domainExponent)) :
    ((top.copyPermutation cell).2 : ℕ) <
      (top.usableRowsAt top.domainExponent) := by
  apply PermConstruction.replay_preserves (top.boundedCopyPairs)
    (fun candidate => (candidate.2 : ℕ) < (top.usableRowsAt top.domainExponent))
  · intro pair hpair
    exact (top.boundedCopyPairs_rows_lt) pair hpair
  · exact hcell

/-- Decode membership in the raw circuit copy list to a typed copy pair. -/
theorem exists_pair_of_raw
    {tuple : ℕ × ℕ × ℕ × ℕ} (hraw : tuple ∈ top.copyPairs) :
    ∃ pair ∈ (top.boundedCopyPairs),
      pair.1.pair = (tuple.1, tuple.2.1) ∧
        pair.2.pair = (tuple.2.2.1, tuple.2.2.2) := by
  have hrawMap :
      top.copyPairs = (top.boundedCopyPairs).map
        (fun pair =>
          (pair.1.pair.1, pair.1.pair.2,
            pair.2.pair.1, pair.2.pair.2)) :=
    (decodeCopies_map top.permutationColumnCount top.n
      top.copyPairs (top.copyPairs_bounds)).symm
  rw [hrawMap, List.mem_map] at hraw
  obtain ⟨pair, hpair, htuple⟩ := hraw
  refine ⟨pair, hpair, ?_, ?_⟩
  · rw [← htuple]
  · rw [← htuple]

/-- The circuit cell valuation: the environment read of the cell's permutation column
at the cell's absolute row. -/
def permutationValue (env : Environment F)
    (fc : FlatCell top.permutationColumnCount top.n) : F :=
  env.get (ColRef.toAny ((top.permutationLayout).getD (fc.1 : ℕ) (.advice 0)))
    (fc.2 : ℕ)

/-- Equality along compiled cycles recovers the resolved copies and their source semantics. -/
theorem copiesCompiled_of_permutation
    (assignment : ProofAssignment F)
    (hvalues : ∀ left right : FlatCell top.permutationColumnCount top.n,
      (left.2 : ℕ) < top.usableRowsAt top.domainExponent →
      (right.2 : ℕ) < top.usableRowsAt top.domainExponent →
      top.copyPermutation.SameCycle left right →
      top.permutationValue (top.environment assignment) left =
        top.permutationValue (top.environment assignment) right) :
    top.CopiesCompiled assignment := by
  intro tuple htuple
  obtain ⟨pair, hpair, hleft, hright⟩ := top.exists_pair_of_raw htuple
  have hrows := top.boundedCopyPairs_rows_lt pair hpair
  have heq := hvalues pair.1 pair.2 hrows.1 hrows.2
    (PermConstruction.sameCycle_replay_of_mem top.boundedCopyPairs hpair)
  simp only [FlatCell.pair, Prod.mk.injEq] at hleft hright
  simpa only [permutationValue, rawCopyValue, permutationLayout,
    hleft.1, hleft.2, hright.1, hright.2] using heq

/-- A σ-row entry names the image of its cell under the compiled permutation. -/
theorem permutationRows_getD [FieldDomainParams F]
    (cell : FlatCell top.permutationColumnCount top.n) :
    (top.permutationRows cell.1).getD cell.2 0 =
      FieldDomainParams.delta ^ (top.copyPermutation cell).1.val *
        top.omega ^ (top.copyPermutation cell).2.val := by
  have hcopies : top.copyPairs = top.boundedCopyPairs.map
      (fun pair => (pair.1.pair.1, pair.1.pair.2, pair.2.pair.1, pair.2.pair.2)) :=
    (decodeCopies_map _ _ top.copyPairs top.copyPairs_bounds).symm
  have hcount : top.permutationColumnCount = (Layout.permColsOf top.constraintSystem).length := by
    simpa only [permutationLayout] using top.permutationLayout_length.symm
  have h := Layout.Asm.permutationRows_getD_eq top.constraintSystem top.operations
    hcount top.n_eq_two_pow_domainExponent top.boundedCopyPairs
    (by simpa only [copyPairs, regionStarts] using hcopies) cell.1 cell.2
  simpa only [permutationRows, copyPermutation, omega] using h

end Halo2.TopLevelCircuit
