import LoweringFixtures.Common

/-! Stated lookups over two tables of different lengths, one loaded after the region using it: an
owned two-column, two-parallel `batched_lookup` (default fill pairs `t0`'s row 0 with `t1`'s later
rows), an owned `lookup_any` into `t0` queried bare inside its closure with a fixed input at
rotation -1 (wrapping at row 0), and a `batched_lookup(None)` into `t1`. -/
namespace LoweringFixtures.LookupStatedTwoTables
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t0 ← fixedColumn
  let t1 ← fixedColumn
  let f ← fixedColumn
  let q ← selector false
  batchedLookup "pair" q do
    let y ← advice b
    let x ← advice a
    return #[(#[x, Rust.scale y 2], t0), (#[y, x], t1)]
  lookupAny "any bare" q do
    let fv ← fixed f (-1)
    let tv ← fixed t0
    return #[(fv, tv)]
  batchedLookup "none" none do
    let x ← advice a 1
    return #[(#[x], t1)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def qAt (row : Nat) : RegionOperations F :=
  [.enableLookup (cleanLookup (lk 0) 0) [⟨0, false⟩] row, .enableLookup (cleanLookup (lk 0) 1) [⟨0, false⟩] row,
   .enableLookup (cleanLookup (lk 1)) [⟨0, false⟩] row]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [1, 2],
    .region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness] ++ qAt 0 ++
      [.assignFixed ⟨2⟩ 1 1, .assignAdvice ⟨0⟩ 1 witness] ++ qAt 2),
    .loadTable ⟨⟨1⟩⟩ [5, 6, 7]]

#guard source.validate.isOk && (lk 0).stated fixture.ops && (lk 1).stated fixture.ops && !(lk 2).owned
#guard source.fixedQueries == #[(0, 0), (1, 0), (2, -1)]

end LoweringFixtures.LookupStatedTwoTables
