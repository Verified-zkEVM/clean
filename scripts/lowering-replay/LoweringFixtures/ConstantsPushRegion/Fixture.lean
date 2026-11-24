import LoweringFixtures.Common

/-! Constants push a later region on the constants column: eight constants fill constants-column
rows 0..7 of 9 usable, so the next region on that column starts at row 8 and its `assign_fixed` at
offset 1 lands on row 9. Rust fails with `NotEnoughRowsAvailable`; Lean rejects the region bound. -/
namespace LoweringFixtures.ConstantsPushRegion
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _b ← adviceColumn
  let c ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant c

def source : CS := (configure.run {}).2

/-- `ConstantsPushRegionFits` writes at `offset` 0. -/
def ops (offset : Nat := 1) : Operations F := [
  .region "r0" ((List.range 8).flatMap fun row =>
    [.assignAdvice ⟨0⟩ row witness, .constrainConstant (cell 0 row .advice 0) ((row + 1 : ℕ) : F)]),
  .region "r1" [.assignAdvice ⟨1⟩ 0 witness, .assignFixed ⟨0⟩ offset 5]]

def fixture : Export.Replay.Fixture := { source, ops := ops, k := 4 }

#guard (Chips.CertifiedCircuit.layoutConfig source 4).usableRows == 9

end LoweringFixtures.ConstantsPushRegion
