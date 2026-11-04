import Clean.Halo2.Keygen.Layout

/-! # Bounded copy-table coordinates -/

variable {F : Type} [FiniteField F]

namespace Halo2

/-- A flat permutation-table cell: a permutation column and a row. -/
abbrev FlatCell (numCols n : ℕ) := Fin numCols × Fin n

/-- The `(column, row)` pair the assembly arrays index by. -/
def FlatCell.pair {numCols n : ℕ} (c : FlatCell numCols n) : ℕ × ℕ :=
  ((c.1 : ℕ), (c.2 : ℕ))

theorem FlatCell.pair_injective {numCols n : ℕ} :
    Function.Injective (FlatCell.pair (numCols := numCols) (n := n)) := by
  intro c d h
  simp only [FlatCell.pair, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨Fin.ext h.1, Fin.ext h.2⟩

end Halo2

/-! # Column layout and constant allocation for the copy compiler -/

namespace Halo2.Layout

/-- V1 constant allocations in the legacy copy-list tuple order. Values remain
field-valued in Clean; only this permutation-copy adapter reads `FiniteField.val`. -/
def constantCopyEntries (cs : ConstraintSystem F) (ops : Operations F) :
    List (ℕ × ℕ × ℕ) :=
  (FloorPlanner.V1.constantAssignments ops (cs.constants.map (·.index))).map
    fun (value, column, row) => (FiniteField.val value, column, row)

/-- The permutation columns as `ColRef`s in `enable_equality` order
(`cs.permutationColumns`) — the order the keygen `Assembly` mapping and the `δ^i` scaling
are indexed by, and the column shape `V1.copyList` resolves cells against. -/
def permColsOf (cs : ConstraintSystem F) : List Halo2.Layout.ColRef :=
  cs.permutationColumns.map fun c =>
    match c.kind with
    | .advice => .advice c.index
    | .fixed => .fixed c.index
    | .instance => .instance c.index

omit [FiniteField F] in
/-- Translating the keygen permutation columns back to Clean columns is lossless. -/
theorem permColsOf_map_toAny (cs : ConstraintSystem F) :
    (permColsOf cs).map Halo2.Layout.ColRef.toAny =
      cs.permutationColumns := by
  rw [permColsOf, List.map_map]
  induction cs.permutationColumns with
  | nil => rfl
  | cons column rest ih =>
      simp only [List.map_cons]
      rw [ih]
      rcases column with ⟨kind, index⟩
      cases kind <;> rfl

end Halo2.Layout
