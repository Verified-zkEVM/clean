import LoweringFixtures.Common
import Midnight.Chips.CertifiedCircuit

/-! Owned lookups whose bare fixed table no `loadTable` fills, so Clean's `env` does not pin it and
the lookup is not `stated`: `RowLookupsHold` reads the keygen matrix. A `lookup_any(Some(q))` into
a fixed column that `assign_fixed` writes on rows 0 and 2 only (Rust has 0 elsewhere), and a
`batched_lookup` into a table column no table loads (all 0 in Rust), beside a loaded, stated one. -/
namespace LoweringFixtures.LookupUnloadedTable
open Halo2 Midnight Midnight.Keygen LoweringFixtures

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let u ← fixedColumn
  let q ← selector false
  lookupAny "assigned" q do
    let tf ← fixed f
    let x ← advice a
    return #[(x, tf)]
  batchedLookup "unloaded" q do
    let x ← advice a 1
    return #[(#[x], t)]
  batchedLookup "loaded" q do
    let x ← advice a
    return #[(#[x], u)]

def source : CS := (configure.run {}).2
def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def ops : Operations F :=
  [.loadTable ⟨⟨2⟩⟩ [0, 7],
   .region "f" [.assignFixed ⟨0⟩ 0 3, .assignFixed ⟨0⟩ 2 9],
   .region "use" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
     .enableLookup (cleanLookup (lk 0)) [⟨0, false⟩] 0, .enableLookup (cleanLookup (lk 1)) [⟨0, false⟩] 0,
     .enableLookup (cleanLookup (lk 2)) [⟨0, false⟩] 0]]

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := ops

#guard source.validate.isOk && (List.range 3).all fun i => (lk i).owned
#guard !(lk 0).stated ops && !(lk 1).stated ops && (lk 2).stated ops

end LoweringFixtures.LookupUnloadedTable
