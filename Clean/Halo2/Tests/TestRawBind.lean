import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.CircuitProofStart2
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add

/-! # Raw-used-bind shape pin for CPS v2

A layouter parent that witnesses a point in a RAW `assignRegion` (a non-call bind whose
value IS used) and feeds it twice into a child call. Pins the atomic-binds delivery for
this shape (design doc, "Raw binds, loops, and the mint gate"):

- the raw binder mints do-binder-named atoms (`p_x`/`p_y`) whose defining equations
  (`p_eq`) are the concrete boundary facts, reduced separately;
- the call contract (`s_spec`) and naming equation (`s_eq`) spell those atoms — the
  concrete cell record never propagates;
- the raw step's region count folds (the child contract's index is the literal
  `i₀ + 1`, converged with `s_eq`'s spelling);
- the content-free raw chunk (`region_0 : True`) is auto-cleared.

The proofs end in `sorry` deliberately: the circuit has no gate on the witnessed point,
so its `Spec` is not provable — the DELIVERED STATE is what this test pins (the
`guard_hyp`s), the established sorry-pin style. -/

namespace Zcash.Circuits.Ecc.TestRawBind

open Halo2

/-- Doubling a witnessed point: raw witness region + one `addFormal` call on `⟨p, p⟩`. -/
def double : FormalCircuit Fp
    ((Column .advice × Column .advice) × Add.Config)
    ((Column .advice × Column .advice) × Add.Config)
    (Unconstrained Point) Point where
  name := "raw-bind double"
  configure := fun ((x, y), acfg) => do
    enableEquality x.toAny
    enableEquality y.toAny
    pure ((x, y), acfg)

  synthesize | ((x, y), acfg), input => do
    let p ← assignRegion "witness p" (do
      let xVar ← assignAdvice x 0 (Witgen.MOver.toIRScalar (Point.x <$> input))
      let yVar ← assignAdvice y 0 (Witgen.MOver.toIRScalar (Point.y <$> input))
      pure ({ x := xVar, y := yVar } : Var Point Fp))
    let s ← Add.addFormal.call acfg { p := p, q := p }
    pure s

  elaborated := {
    keygenRequirements :=
      { configLawful input := Add.add.Configured input.2
        gates _ configured := configured.gates
        lookups _ configured := configured.lookups }
    registered := by
      intro configInput counts hconfig input i
      simp only [keygen_spine]
      change Add.add.Configured configInput.2 at hconfig
      apply Add.addFormal.call_keygenRegistered configInput.2 hconfig.toFormal
      · intro gate hgate
        simpa only [FormalRegionCircuit.Configured.toFormal,
          FormalCircuit.Configured.gates,
          FormalRegionCircuit.Configured.gates,
          FormalRegionCircuit.toFormal_keygenRequirements,
          List.append_nil] using hgate
      · intro argument hargument
        simpa only [FormalRegionCircuit.Configured.toFormal,
          FormalCircuit.Configured.lookups,
          FormalRegionCircuit.Configured.lookups,
          FormalRegionCircuit.toFormal_keygenRequirements,
          List.append_nil] using hargument
    regionCount _ := 2 }

  Spec _ output _ := output.Valid

  ProverAssumptions input _ _ := input.Valid

  soundness := by
    circuit_proof_start2 [Add.addFormal]
    -- the minted boundary facts and the atom-spelled contract, pinned
    guard_hyp p_eq : AssignedCell.of i₀ 0 cfg_1.1 = p_x ∧ AssignedCell.of i₀ 0 cfg_1.2 = p_y
    guard_hyp s_eq : Add.addFormal.output cfg
        { p := { x := p_x, y := p_y }, q := { x := p_x, y := p_y } } (i₀ + 1)
      = { x := s_x, y := s_y }
    guard_hyp output_eq : AssignedCell.eval place env s_x = output_x
      ∧ AssignedCell.eval place env s_y = output_y
    sorry

  completeness := by
    circuit_proof_start2 [Add.addFormal]
    sorry

end Zcash.Circuits.Ecc.TestRawBind
