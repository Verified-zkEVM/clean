import Midnight.Field

namespace Midnight.SHA256

/-- Insert a zero between adjacent bits, least significant bit first.
Rust reference: `circuits/src/hash/utils.rs`, `spread`. -/
def spread : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + 4 * spread ((n + 1) / 2)
termination_by n => n

/-- Supported SHA lookup widths; eight is omitted to fit the table at k=13.
Rust: `hash/sha256/utils.rs::gen_spread_table`. -/
def spreadWidths : List Nat := [0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12]

def spreadRows : List (Nat × Nat × Nat) :=
  spreadWidths.flatMap fun width =>
    (List.range (2 ^ width)).map fun value => (width, value, spread value)

/-- The range table includes the disabled row and only widths requested by
synthesis. Byte assignment and digest decomposition request width eight. -/
def rangeRows (requested : List Nat) : List (Nat × Nat) :=
  let widths := (List.range (requested.foldl max 0 + 1)).filter
    fun w => w == 0 || requested.contains w
  widths.flatMap fun width =>
    (List.range (2 ^ width)).map fun value => (width, value)

def byteRangeRows : List (Nat × Nat) := rangeRows [8]

/-- Actual Clean lookup-table load operations, parameterized by configured columns.
Only the check knows the reference column numbers. -/
def loadSpread (tag plain expanded : Halo2.TableColumn) : Halo2.Circuit F Unit := do
  Halo2.loadTable tag (spreadRows.map fun row => (row.1 : F))
  Halo2.loadTable plain (spreadRows.map fun row => (row.2.1 : F))
  Halo2.loadTable expanded (spreadRows.map fun row => (row.2.2 : F))

def loadRange (tag value : Halo2.TableColumn) (requested : List Nat) :
    Halo2.Circuit F Unit := do
  Halo2.loadTable tag ((rangeRows requested).map fun row => (row.1 : F))
  Halo2.loadTable value ((rangeRows requested).map fun row => (row.2 : F))

/-- The five SHA table loads (Rust's two table-loading calls) on their native columns 11 to 15,
shared by synthesis and its semantics; `Synthesis.tableOperations` is their operation list. -/
def shaTables : Halo2.Circuit F Unit := do
  Halo2.loadTable ⟨⟨11⟩⟩ (byteRangeRows.map fun x => (x.1 : F))
  Halo2.loadTable ⟨⟨12⟩⟩ (byteRangeRows.map fun x => (x.2 : F))
  Halo2.loadTable ⟨⟨13⟩⟩ (spreadRows.map fun x => (x.1 : F))
  Halo2.loadTable ⟨⟨14⟩⟩ (spreadRows.map fun x => (x.2.1 : F))
  Halo2.loadTable ⟨⟨15⟩⟩ (spreadRows.map fun x => (x.2.2 : F))

end Midnight.SHA256
