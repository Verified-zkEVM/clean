import Midnight.Field
import Clean.Halo2.Keygen.Layout

/-! Proof-carrying sparse-to-dense fixed compilation. These results are independent
of the floor planner: the caller supplies the fixed writes at its derived starts.
No V1 placement or constant-allocation theorem is used. -/

namespace Midnight.Chips.LayoutLawful
open Halo2.Layout

abbrev Write := FixedAssignment Nat

/-- Bounds of every source write. Conflicting writes are admitted: `dense` keeps the last, as
Rust's keygen does (keygen.rs:116-174), so `writes` must be in stream order. -/
structure WritesLawful (rows columns : Nat) (writes : List Write) : Prop where
  bounds : ∀ write ∈ writes, write.1 < columns ∧ write.2.1 < rows

/-- Clean's generic dense compiler; each cell takes its last write. -/
def dense (rows columns : Nat) (writes : List Write) : List (List Nat) :=
  denseFixedColumns rows columns (dedupAssignments writes)

/-- Midnight keeps one new fixed column per selector, with Boolean entries. -/
def selectorWrites (numFixed : Nat) (activations : List (Nat × Nat)) : List Write :=
  activations.map fun (selector, row) => (numFixed + selector, row, 1)

/-- The compiled matrix carries its source bounds and exact-value theorems. -/
structure CertifiedFixed (rows usable numFixed numSelectors : Nat)
    (writes : List Write) (activations : List (Nat × Nat)) : Type where
  sourceLawful : WritesLawful usable numFixed writes
  usable_le_rows : usable ≤ rows
  activationBounds : ∀ activation ∈ activations,
    activation.1 < numSelectors ∧ activation.2 < usable

def CertifiedFixed.columns {rows usable numFixed numSelectors : Nat}
    {writes : List Write} {activations : List (Nat × Nat)}
    (_ : CertifiedFixed rows usable numFixed numSelectors writes activations) : List (List Nat) :=
  dense rows (numFixed + numSelectors) (writes ++ selectorWrites numFixed activations)

end Midnight.Chips.LayoutLawful
