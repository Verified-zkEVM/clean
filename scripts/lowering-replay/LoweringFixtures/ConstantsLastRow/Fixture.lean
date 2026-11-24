import LoweringFixtures.Common

/-! Deferred constants up to the last usable row: the region fills constants-column rows
0..6 and its two constants take rows 7 and 8 of the 9 usable rows. -/
namespace LoweringFixtures.ConstantsLastRow
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant c

def source : CS := (configure.run {}).2

/-- Seven constants-column rows written by the region, then `count` constants. -/
def body (count : Nat) : RegionOperations F :=
  (List.range 7).map (fun row => .assignFixed ⟨0⟩ row ((row + 1 : ℕ) : F)) ++
  (List.range count).flatMap fun row =>
    [.assignAdvice ⟨0⟩ row witness, .constrainConstant (cell 0 row .advice 0) ((row + 20 : ℕ) : F)]

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r0" (body 2)]

#guard (Chips.CertifiedCircuit.layoutConfig source 4).usableRows == 9

end LoweringFixtures.ConstantsLastRow
