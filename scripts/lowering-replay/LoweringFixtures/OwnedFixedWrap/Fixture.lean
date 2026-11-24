import LoweringFixtures.Common
import Midnight.Chips.CertifiedCircuit

/-! An owned gate `qc * (f(-1) - 1)` enabled at absolute row 0. Rust reads fixed row 2^k - 1, which
keygen leaves 0, so the gate is -1 there for every witness and no proof exists. Clean's
`Constraints` reads `env.fixed f (-1)`, unwrapped and unpinned, so `overclaim` proves `Satisfied`.
-/
namespace LoweringFixtures.OwnedFixedWrap
open Halo2 Midnight Midnight.Keygen LoweringFixtures

def configure : ConfigM Unit := do
  let f ← fixedColumn
  let qc ← selector false
  gate "prev" qc do
    let w ← fixed f (-1)
    return #[("", Rust.sub w (.const 1))]

def source : CS := (configure.run {}).2
def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, false⟩, #[], #[], false, false⟩
def ops : Operations F := [.region "r" [.enableGate (cleanGate g) 0]]

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := ops

#guard source.validate.isOk && !g.rows && !g.raw

/-- `Satisfied` holds although Rust's vanishing argument fails at row 0. -/
theorem overclaim : ∃ env : Environment F,
    Midnight.Chips.CertifiedCircuit.Satisfied source ops 4 (fun _ => 0) env := by
  refine ⟨⟨fun _ _ => 1, 16⟩, ?_, Midnight.Chips.CertifiedCircuit.RowGatesHold.of_owned (by decide +kernel) _ _ _,
    Midnight.Chips.CertifiedCircuit.RowLookupsHold.of_stated (by decide +kernel) _ _⟩
  have hv : g.valid = true := by decide +kernel
  have hr : g.rows = false := by decide +kernel
  have hw : g.raw = false := by decide +kernel
  simp only [ops, cleanGate, dite_eq_left hv, Constraints, RegionOperations.Constraints,
    RegionOperation.Constraints, GateSpec.toClean, hr, hw]
  have hc : g.constraints.toList =
      [("", .add (.var (.fixed ⟨0⟩ (-1))) (.mul (.const (-1)) (.const 1)))] := by decide +kernel
  have hs : g.selector = ⟨0, false⟩ := by decide +kernel
  simp [Gate.withSelector, hc, hs, Expression.eval, Query.eval, Environment.fixed, querySelector]

end LoweringFixtures.OwnedFixedWrap
