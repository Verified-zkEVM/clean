import Midnight.Frontend.Native
import Midnight.Poseidon.RoundSkips

/-! `ZkStdLib::configure` for the Poseidon-only architecture at midnight-zk 1e39c120: native,
pow2range and `PoseidonChip::configure` (poseidon_chip.rs:180-262), the partial-round batch an
additive gate. -/
namespace Midnight.Frontend.Poseidon
open scoped Halo2.ElaboratedConfigure
open Halo2 (Column)
open Keygen (E)
open Midnight.Poseidon (width circuitSkips mds constProduct partialExpressions)

private def exprAt (xs : Array E) (index : Nat) : E := xs[index]?.getD (.const 0)

def poseidonConfigure (registers : Array (Column .advice)) (constants : Array (Column .fixed)) :
    Configure Unit := do
  let q_full_round ← selector
  let q_partial_round ← complexSelector
  for c in registers.extract 0 width do enableEquality c
  gate "full_round_gate" q_full_round do
    let pairs ← (Array.range width).mapM fun i => do
      let x ← advice registers[i]!
      let hint ← advice registers[i + width]!
      return (x, hint)
    let outputs ← (registers.extract 0 width).mapM fun c => advice c 1
    let cs ← (constants.extract 0 width).mapM fun c => fixed c
    let sboxed := pairs.map fun (x, hint) => (x * x) * hint
    let mut ids := pairs.map fun (x, hint) => x * (x * x) - hint
    for i in [:width] do
      let mut id := exprAt cs i - exprAt outputs i
      for j in [:width] do
        id := id + constProduct ((mds[i]!)[j]!) (exprAt sboxed j)
      ids := ids.push id
    return ids.map ("", ·)
  additiveGate "partial_round_gate" q_partial_round do
    let inputs ← registers.mapM fun c => advice c
    let cs ← constants.mapM fun c => fixed c
    let outputs ← (registers.extract 0 width).mapM fun c => advice c 1
    let constraints := partialExpressions inputs
    let mut result := #[]
    for i in [:width - 1] do
      result := result.push ("", exprAt cs i - exprAt outputs i + exprAt constraints i)
    for i in [width - 1:width + circuitSkips - 1] do
      result := result.push ("", exprAt cs i - exprAt inputs (i + 1) + exprAt constraints i)
    let last := width + circuitSkips - 1
    result := result.push
      ("", exprAt cs last - exprAt outputs (width - 1) + exprAt constraints last)
    return result

/-- The shared-resource maxima come from the source: 8 advice, max(5+4, WIDTH+SKIPS) = 9 fixed. -/
def configure : Configure Unit := do
  let adviceCount := max 5 (max (2 * width) (width + circuitSkips))
  let fixedCount := max (5 + 4) (width + circuitSkips)
  let advice_columns ← (Array.range adviceCount).mapM fun _ => adviceColumn
  let fixed_columns ← (Array.range fixedCount).mapM fun _ => fixedColumn
  let committed_instance_column ← instanceColumn
  let instance_column ← instanceColumn
  nativeConfigure (advice_columns.extract 0 5) (fixed_columns.extract 0 (5 + 4))
    #[committed_instance_column, instance_column]
  rangeConfigure (advice_columns.extract 1 2)
  poseidonConfigure advice_columns (fixed_columns.extract 0 (width + circuitSkips))

/-- Metadata only, never run, like the SHA-256 program's. -/
noncomputable instance (registers : Array (Column .advice)) (constants : Array (Column .fixed)) :
    Halo2.ElaboratedConfigure (poseidonConfigure registers constants) := by
  unfold poseidonConfigure
  try dsimp only
  elaborate_configure

noncomputable instance : Halo2.ElaboratedConfigure configure := by
  unfold configure
  try dsimp only
  elaborate_configure

end Midnight.Frontend.Poseidon
