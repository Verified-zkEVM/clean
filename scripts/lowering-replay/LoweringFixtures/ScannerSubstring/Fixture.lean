import LoweringFixtures.Common

/-! The scanner's substring lookups (circuits/src/parsing/scanner/mod.rs:472-492): three
`lookup_any(None)` batches of `(tag, q * tag)` and `(query, q * (index * 257 + table) + (1 - q) * query)`
over a shared index column, a tag column and two advice columns each. One region fills an
11-letter table with tag 1 and enables `q` on the three query rows. -/
namespace LoweringFixtures.ScannerSubstring
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let cols ← (List.range 6).mapM fun _ => adviceColumn
  let indexCol ← fixedColumn
  let tagCol ← fixedColumn
  let q ← selector false
  for batch in [0:3] do
    lookupAny s!"substring lookup (batch {batch})" none do
      let sel ← query (.selector q)
      let notSel := Rust.sub (.const 1) sel
      let index ← fixed indexCol
      let tag ← fixed tagCol
      let shift : E := .const 257
      let table ← advice (cols.getD (2 * batch) 0)
      let packed ← advice (cols.getD (2 * batch + 1) 0)
      return #[(tag, Rust.mul sel tag),
        (packed, .add (Rust.mul sel (.add (Rust.mul index shift) table)) (Rust.mul notSel packed))]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [.region "substring" ((List.range 11).flatMap fun r =>
      [.assignFixed ⟨1⟩ r 1, .assignFixed ⟨0⟩ r r] ++
      (List.range 6).map (fun c => .assignAdvice ⟨c⟩ r witness) ++
      (if r < 3 then [.enableGate (lookupHandle (lk (r % 3)) 0) r] else []))]

#guard source.validate.isOk && source.lookups.all (!·.owned)
#guard source.lookups.size == 3

end LoweringFixtures.ScannerSubstring
