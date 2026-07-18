import Clean.Ironwood.NoteCommit.Main

/-!
# NoteCommit bundle proofs (soundness / completeness / the `circuit` def)

Kept separate from `Main.lean` (the defs/contract layer) while the proofs are built:
this file is the kernel-heavy part.

WIP: NOT imported by `Clean/Ironwood.lean` until sorry-free — the soundness and
completeness proofs below are under construction (the `trace_state`/`sorry` tail marks
the frontier).
-/

namespace Halo2.Ironwood.NoteCommit.Main

open Halo2.Ironwood (Fp)
open Orchard (Point)
open Orchard.Ecc.MulFixed (FixedBase)
open Orchard.Specs (bitrange)
open Orchard.Specs.Sinsemilla (Generators hashToPoint)
open CompElliptic.Fields.Pasta (Fq)

/-! ## Child contract bridges (`rfl`, children stay folded) -/

section ChildBridges

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

variable (n b : ℕ)

private theorem short_spec_eq :
    (LookupRangeCheck.shortRangeCheck 10 b).Spec
      = fun _ (out : Fp) _ => out.val < 2 ^ b := rfl

private theorem short_assumptions_eq :
    (LookupRangeCheck.shortRangeCheck 10 b).Assumptions
      = fun _ => b ≤ 10 ∧ 2 ^ 10 * 2 ^ 10 < PALLAS_BASE_CARD := rfl

private theorem short_envAssumptions_eq (cfg : LookupRangeCheck.Config 10)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.shortRangeCheck 10 b).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded 10 cfg env.env ∧
          cfg.qLookup.index ≠ cfg.qRunning.index) := rfl

private theorem short_output (cfg : LookupRangeCheck.Config 10) (i : RegionIndex) :
    (LookupRangeCheck.shortRangeCheck 10 b).output cfg 0 () i
      = .of i 0 cfg.runningSum := by
  show ((LookupRangeCheck.shortRangeCheck 10 b).synthesize cfg 0 ()).output i = _
  simp only [LookupRangeCheck.shortRangeCheck, circuit_norm, RegionCircuit.output_bind,
    output_cellAt, Nat.zero_add]

private theorem rangeCheckAt_spec_eq :
    (LookupRangeCheck.rangeCheckAt 10 n false).Spec
      = fun _ output (elt : Fp) =>
          output.z0 = elt ∧
          (∃ lo : ℕ, lo < 2 ^ (10 * n) ∧
            elt = (lo : Fp) + ((2 ^ (10 * n) : ℕ) : Fp) * output.zLast) ∧
          (false = true → output.zLast = 0 ∧ elt.val < 2 ^ (10 * n)) := rfl

private theorem rangeCheckAt_assumptions_eq :
    (LookupRangeCheck.rangeCheckAt 10 n false).Assumptions
      = fun _ => 2 ^ (10 * n) ≤ PALLAS_BASE_CARD ∧ 2 ^ 10 ≤ PALLAS_BASE_CARD := rfl

private theorem rangeCheckAt_envAssumptions_eq (cfg : LookupRangeCheck.Config 10)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.rangeCheckAt 10 n false).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded 10 cfg env.env ∧
          cfg.qLookup.index ≠ cfg.qRunning.index) := rfl

private theorem rangeCheckAt_output (cfg : LookupRangeCheck.Config 10) (i : RegionIndex) :
    (LookupRangeCheck.rangeCheckAt 10 n false).output cfg 0 () i
      = { z0 := .of i 0 cfg.runningSum, zLast := .of i n cfg.runningSum } := by
  show ((LookupRangeCheck.rangeCheckAt 10 n false).synthesize cfg 0 ()).output i = _
  simp only [LookupRangeCheck.rangeCheckAt, circuit_norm, RegionCircuit.output_bind,
    output_cellAt, Bool.false_eq_true, if_false, Nat.zero_add]

private theorem yc_call_regionCount (w : WitgenIR Fp 1)
    (c : YCanonicity.Config × LookupRangeCheck.Config 10)
    (inp : Var YCanonicityCheck.Inputs Fp) (j : RegionIndex) :
    Operations.regionCount
      (((YCanonicityCheck.circuit w).call c inp).operations j) = 5 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem commit_call_regionCount (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp) (j : RegionIndex) :
    Operations.regionCount
      (((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil ns_pos).call
        c inp).operations j) = 4 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem yc_spec_eq (w : WitgenIR Fp 1) :
    (YCanonicityCheck.circuit w).Spec
      = fun input (out : Fp) (wit : Fp) =>
          out = wit ∧
          (IsBool out → Orchard.Action.NoteCommit.IsLowBit input.y out) := rfl

private theorem yc_assumptions_eq (w : WitgenIR Fp 1) :
    (YCanonicityCheck.circuit w).Assumptions = fun _ => True := rfl

private theorem yc_envAssumptions_eq (w : WitgenIR Fp 1)
    (c : YCanonicity.Config × LookupRangeCheck.Config 10) (env : Placed Environment Fp) :
    (YCanonicityCheck.circuit w).EnvAssumptions c env
      = (LookupRangeCheck.TableLoaded 10 c.2 env.env ∧
          c.2.qLookup.index ≠ c.2.qRunning.index) := rfl

private theorem yc_output (w : WitgenIR Fp 1)
    (c : YCanonicity.Config × LookupRangeCheck.Config 10)
    (inp : Var YCanonicityCheck.Inputs Fp) (i : RegionIndex) :
    (YCanonicityCheck.circuit w).output c inp i
      = AssignedCell.of (i + 4) 0 (c.1.advices 6) := rfl

private theorem yc_extract (w : WitgenIR Fp 1)
    (c : YCanonicity.Config × LookupRangeCheck.Config 10)
    (inp : Var YCanonicityCheck.Inputs Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (YCanonicityCheck.circuit w).extract c inp i env
      = eval env (AssignedCell.of (i + 4) 0 (c.1.advices 6) : Var field Fp) := rfl

private theorem commit_spec_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil ns_pos).Spec
      = fun input (output : Value Point Fp) wit =>
          ∃ chunks : List ℕ,
            Sinsemilla.Chain.PieceChunks ns input.pieces chunks ∧
            Sinsemilla.Chain.ZsFacts ns chunks wit.1.zs ∧
            ∀ B, hashToPoint G.S Q chunks = some B →
              output.Valid ∧ output = B + (wit.2.2 • R : Point Fp) := rfl

private theorem commit_assumptions_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil ns_pos).Assumptions
      = fun _ => True := rfl

private theorem commit_envAssumptions_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (env : Placed Environment Fp) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil ns_pos).EnvAssumptions
        c env
      = (Sinsemilla.GeneratorTableLoaded G c.2.1.generatorTable env.env ∧
          Ecc.MulFixed.FullWidth.EnvAssumptions c.1 env) := rfl

private theorem commit_extract_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil ns_pos).extract
        c inp i env
      = ((Sinsemilla.HashToPoint.hashCircuit G ns Q hQ ns_ne_nil ns_pos).extract c.2.1
          { pieces := inp.pieces } (i + 2) env,
         Ecc.MulFixed.FullWidth.fwExtract c.1 i env) := rfl

end ChildBridges

theorem soundness (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config) :
    FormalCircuit.Soundness (Witness := fun _ => Fq) (synth G R windows Q hQ cfg)
      (rcmExtract cfg) (EnvAssumptions G cfg) Assumptions (Spec G Q R) := by
  circuit_proof_start
  obtain ⟨hTableG, hMulE, hTableL, hDistinct⟩ := _hE
  simp only [synth, currentRegion, circuit_norm] at hc
  have hP := hc.1
  have hCk := hc.2.1
  have hGt := hc.2.2
  clear hc
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm] at hP
  simp only [synthChecks, synthPieces, LookupRangeCheck.witnessShortCheck,
    LookupRangeCheck.witnessCheck, Sinsemilla.HashToPoint.witnessMessagePiece,
    circuit_norm] at hCk
  simp only [Operations.regionCount] at hCk
  rw [yc_call_regionCount, yc_call_regionCount, commit_call_regionCount] at hCk
  simp only [synthGates, synthChecks, synthPieces, LookupRangeCheck.witnessShortCheck,
    LookupRangeCheck.witnessCheck, Sinsemilla.HashToPoint.witnessMessagePiece,
    circuit_norm] at hGt
  -- ── stage 1: the seven sub-piece short checks ──
  have hSb0 := hP.1
  have hSb3 := hP.2.1
  have hSd2 := hP.2.2.1
  have hSe0 := hP.2.2.2.1
  have hSe1 := hP.2.2.2.2.1
  have hSg1 := hP.2.2.2.2.2.1
  have hSh0 := hP.2.2.2.2.2.2
  clear hP
  subcircuit_rw at hSb0
  subcircuit_rw at hSb3
  subcircuit_rw at hSd2
  subcircuit_rw at hSe0
  subcircuit_rw at hSe1
  subcircuit_rw at hSg1
  subcircuit_rw at hSh0
  have hb0 := hSb0 (by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [short_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [short_spec_eq, short_output] at hb0
  simp only [circuit_norm] at hb0
  have hb3 := hSb3 (by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [short_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [short_spec_eq, short_output] at hb3
  simp only [circuit_norm] at hb3
  have hd2 := hSd2 (by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [short_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [short_spec_eq, short_output] at hd2
  simp only [circuit_norm] at hd2
  have he0 := hSe0 (by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [short_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [short_spec_eq, short_output] at he0
  simp only [circuit_norm] at he0
  have he1 := hSe1 (by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [short_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [short_spec_eq, short_output] at he1
  simp only [circuit_norm] at he1
  have hg1 := hSg1 (by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [short_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [short_spec_eq, short_output] at hg1
  simp only [circuit_norm] at hg1
  have hh0 := hSh0 (by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [short_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [short_spec_eq, short_output] at hh0
  simp only [circuit_norm] at hh0
  clear hSb0 hSb3 hSd2 hSe0 hSe1 hSg1 hSh0
  -- ── stage 2: the y-canonicity flows, the commitment, the shift witness_checks ──
  have hY1 := hCk.1
  have hY2 := hCk.2.1
  have hCm := hCk.2.2.1
  have hWa := hCk.2.2.2.1
  have hWb := hCk.2.2.2.2.1
  have hWe := hCk.2.2.2.2.2.1
  have hWg := hCk.2.2.2.2.2.2
  clear hCk
  subcircuit_rw at hY1
  subcircuit_rw at hY2
  subcircuit_rw at hCm
  subcircuit_rw at hWa
  subcircuit_rw at hWb
  subcircuit_rw at hWe
  subcircuit_rw at hWg
  have hY1S := hY1 (by rw [yc_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [yc_assumptions_eq]; trivial)
  rw [yc_spec_eq, yc_output, yc_extract] at hY1S
  simp only [circuit_norm] at hY1S
  have hY2S := hY2 (by rw [yc_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [yc_assumptions_eq]; trivial)
  rw [yc_spec_eq, yc_output, yc_extract] at hY2S
  simp only [circuit_norm] at hY2S
  clear hY1 hY2
  have hCmS := hCm
    (by rw [commit_envAssumptions_eq]; exact ⟨hTableG, hMulE⟩)
    (by rw [commit_assumptions_eq]; trivial)
  rw [commit_spec_eq, commit_extract_eq] at hCmS
  clear hCm
  -- the four shift `witness_check`s: telescoped decompositions
  have hWaS := hWa (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWaS
  simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hWaS
  obtain ⟨haz0, loA, hloA, htelA⟩ := hWaS
  have hWbS := hWb (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWbS
  simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hWbS
  obtain ⟨hbz0, loB, hloB, htelB⟩ := hWbS
  have hWeS := hWe (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWeS
  simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hWeS
  obtain ⟨hez0, loE, hloE, htelE⟩ := hWeS
  have hWgS := hWg (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWgS
  simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hWgS
  obtain ⟨hgz0, loG, hloG, htelG⟩ := hWgS
  clear hWa hWb hWe hWg
  trace_state
  sorry

theorem completeness (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config) :
    FormalCircuit.Completeness (Witness := fun _ => Fq) (synth G R windows Q hQ cfg)
      (rcmExtract cfg) (EnvAssumptions G cfg) Assumptions (ProverAssumptions G Q)
      (fun _ _ _ _ => True) := by
  sorry

/-- Rust `NoteCommitChip::commit` as a proof-carrying bundle. -/
def circuit (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) :
    FormalCircuit Fp Config Config Inputs Point where
  name := "NoteCommit"
  configure := pure
  synthesize := synth G R windows Q hQ
  elaborated := elaborated G R windows Q hQ
  Witness := fun _ => Fq
  extract := rcmExtract
  EnvAssumptions := EnvAssumptions G
  Assumptions := Assumptions
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q
  ProverSpec := fun _ _ _ _ => True
  soundness := soundness G R windows Q hQ
  completeness := completeness G R windows Q hQ

end Halo2.Ironwood.NoteCommit.Main
