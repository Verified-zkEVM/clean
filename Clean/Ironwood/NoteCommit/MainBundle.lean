import Clean.Ironwood.NoteCommit.Main
import Clean.Orchard.Sinsemilla.HashToPoint

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
      (((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).call
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
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).Spec
      = fun input (output : Value Point Fp) wit =>
          ∃ chunks : List ℕ,
            Sinsemilla.Chain.PieceChunks ns input.pieces chunks ∧
            Sinsemilla.Chain.ZsFacts ns chunks wit.1.zs ∧
            ∀ B, hashToPoint G.S Q chunks = some B →
              output.Valid ∧ output = B + (wit.2.2 • R : Point Fp) := rfl

private theorem commit_assumptions_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).Assumptions
      = fun _ => True := rfl

private theorem commit_envAssumptions_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (env : Placed Environment Fp) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).EnvAssumptions
        c env
      = (Sinsemilla.GeneratorTableLoaded G c.2.1.generatorTable env.env ∧
          Ecc.MulFixed.FullWidth.EnvAssumptions c.1 env) := rfl

private theorem commit_extract_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).extract
        c inp i env
      = ((Sinsemilla.HashToPoint.hashCircuit G ns Q hQ ns_ne_nil).extract c.2.1
          { pieces := inp.pieces } (i + 2) env,
         Ecc.MulFixed.FullWidth.fwExtract c.1 i env) := rfl

private theorem toFormal_call_regionCount {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) (cfg : Cfg)
    (inp : Var In Fp) (j : RegionIndex) :
    Operations.regionCount (((b.toFormal name).call cfg inp).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem toFormal_spec_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).Spec = b.Spec := rfl

private theorem toFormal_assumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).Assumptions = b.Assumptions := rfl

private theorem toFormal_envAssumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).EnvAssumptions = b.EnvAssumptions := rfl

private theorem toFormal_extract_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) (cfg : Cfg)
    (inp : Var In Fp) (i : RegionIndex) (env : Placed Environment Fp) :
    (b.toFormal name).extract cfg inp i env = b.extract cfg 0 inp i env := rfl

private theorem decomposeB_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeB.Config) (inp : Var DecomposeB.Inputs Fp) (i : RegionIndex) :
    ((DecomposeB.bundle w).toFormal name).output cfg inp i
      = AssignedCell.of i 0 cfg.colR := by
  show (((DecomposeB.bundle w).synthesize cfg 0 inp)).output i = _
  simp only [DecomposeB.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

private theorem decomposeD_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeD.Config) (inp : Var DecomposeD.Inputs Fp) (i : RegionIndex) :
    ((DecomposeD.bundle w).toFormal name).output cfg inp i
      = AssignedCell.of i 0 cfg.colM := by
  show (((DecomposeD.bundle w).synthesize cfg 0 inp)).output i = _
  simp only [DecomposeD.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

private theorem decomposeG_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeG.Config) (inp : Var DecomposeG.Inputs Fp) (i : RegionIndex) :
    ((DecomposeG.bundle w).toFormal name).output cfg inp i
      = AssignedCell.of i 0 cfg.colM := by
  show (((DecomposeG.bundle w).synthesize cfg 0 inp)).output i = _
  simp only [DecomposeG.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

private theorem decomposeH_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeH.Config) (inp : Var DecomposeH.Inputs Fp) (i : RegionIndex) :
    ((DecomposeH.bundle w).toFormal name).output cfg inp i
      = AssignedCell.of i 0 cfg.colR := by
  show (((DecomposeH.bundle w).synthesize cfg 0 inp)).output i = _
  simp only [DecomposeH.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

end ChildBridges

private theorem gd_assumptions_eq :
    GdCanonicity.bundle.Assumptions = fun input =>
      IsBool input.b1 ∧ input.a.val < 2 ^ 250 ∧ input.b0.val < 2 ^ 4 ∧
      input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp) ∧
      ∃ lo : ℕ, lo < 2 ^ 130 ∧
        input.aPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13APrime := rfl

private theorem gd_spec_eq :
    GdCanonicity.bundle.Spec = fun input _ _ =>
      Orchard.Action.NoteCommit.GdCanonicity.Gate.Spec (GdCanonicity.toDonor input) := rfl

private theorem pkd_assumptions_eq :
    PkdCanonicity.bundle.Assumptions = fun input =>
      IsBool input.d0 ∧ input.c.val < 2 ^ 250 ∧ input.b3.val < 2 ^ 4 ∧
      input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp) ∧
      ∃ lo : ℕ, lo < 2 ^ 140 ∧
        input.b3CPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14B3CPrime := rfl

private theorem pkd_spec_eq :
    PkdCanonicity.bundle.Spec = fun input _ _ =>
      Orchard.Action.NoteCommit.PkdCanonicity.Gate.Spec
        (PkdCanonicity.toDonor input) := rfl

private theorem value_assumptions_eq :
    ValueCanonicity.bundle.Assumptions = fun input =>
      input.d2.val < 2 ^ 8 ∧ input.d3.val < 2 ^ 50 ∧ input.e0.val < 2 ^ 6 := rfl

private theorem value_spec_eq :
    ValueCanonicity.bundle.Spec = fun input _ _ =>
      Orchard.Action.NoteCommit.ValueCanonicity.Gate.Spec
        (ValueCanonicity.toDonor input) := rfl

private theorem rho_assumptions_eq :
    RhoCanonicity.bundle.Assumptions = fun input =>
      IsBool input.g0 ∧ input.f.val < 2 ^ 250 ∧ input.e1.val < 2 ^ 4 ∧
      input.z13F = ((input.f.val / 2 ^ 130 : ℕ) : Fp) ∧
      ∃ lo : ℕ, lo < 2 ^ 140 ∧
        input.e1FPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14E1FPrime := rfl

private theorem rho_spec_eq :
    RhoCanonicity.bundle.Spec = fun input _ _ =>
      Orchard.Action.NoteCommit.RhoCanonicity.Gate.Spec
        (RhoCanonicity.toDonor input) := rfl

private theorem psi_assumptions_eq :
    PsiCanonicity.bundle.Assumptions = fun input =>
      IsBool input.h1 ∧ input.g1.val < 2 ^ 9 ∧ input.g2.val < 2 ^ 240 ∧
      input.h0.val < 2 ^ 5 ∧
      input.z13G = (((input.g1.val + input.g2.val * 2 ^ 9) / 2 ^ 129 : ℕ) : Fp) ∧
      ∃ lo : ℕ, lo < 2 ^ 130 ∧
        input.g1G2Prime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13G1G2Prime := rfl

private theorem psi_spec_eq :
    PsiCanonicity.bundle.Spec = fun input _ _ =>
      Orchard.Action.NoteCommit.PsiCanonicity.Gate.Spec
        (PsiCanonicity.toDonor input) := rfl

private theorem prefixRows_ns_0 : Sinsemilla.Chain.prefixRows ns 0 = 0 := rfl
private theorem prefixRows_ns_2 : Sinsemilla.Chain.prefixRows ns 2 = 26 := rfl
private theorem prefixRows_ns_3 : Sinsemilla.Chain.prefixRows ns 3 = 51 := rfl
private theorem prefixRows_ns_5 : Sinsemilla.Chain.prefixRows ns 5 = 58 := rfl
private theorem prefixRows_ns_6 : Sinsemilla.Chain.prefixRows ns 6 = 83 := rfl

/-- The Ironwood `Chain.PieceChunks` is the donor's, verbatim — the bridge unlocks the
donor's piece-value/chunk-equality connectors. -/
private theorem pieceChunks_donor_iff :
    ∀ (ms : List ℕ) (pieces : Vector Fp ms.length) (chunks : List ℕ),
      Sinsemilla.Chain.PieceChunks ms pieces chunks ↔
      Orchard.Sinsemilla.Chain.PieceChunks ms pieces chunks := by
  intro ms
  induction ms with
  | nil =>
    intro pieces chunks
    simp only [Sinsemilla.Chain.PieceChunks, Orchard.Sinsemilla.Chain.PieceChunks]
  | cons n rest ih =>
    intro pieces chunks
    constructor
    · rintro ⟨msf, h1, h2, tailChunks, h3, h4⟩
      exact ⟨msf, h1, h2, tailChunks, h3, (ih _ _).mp h4⟩
    · rintro ⟨msf, h1, h2, tailChunks, h3, h4⟩
      exact ⟨msf, h1, h2, tailChunks, h3, (ih _ _).mpr h4⟩

set_option linter.unusedSimpArgs false in
/-- Stage-3 peel, standalone (kernel-checked alone): the ten folded gate-call chunks at
clean relative indices. -/
private theorem peelGates (cfg : Config) (input : Inputs (AssignedCell Fp))
    (pcs : PieceCells) (ccs : CheckCells) (iHash : RegionIndex)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (h : Constraints place env ((synthGates cfg input pcs ccs iHash).operations i₀) i₀) :
    Constraints place env
      ((((DecomposeB.bundle (brWit input.gdX 254 1)).toFormal
        "NoteCommit MessagePiece b").call cfg.gates.b
        { b := pcs.b, b0 := pcs.b0, b2 := ccs.b2, b3 := pcs.b3 }).operations i₀) i₀ ∧
    Constraints place env
      ((((DecomposeD.bundle (brWit input.pkdX 254 1)).toFormal
        "NoteCommit MessagePiece d").call cfg.gates.d
        { d := pcs.d, d1 := ccs.d1, d2 := pcs.d2,
          d3 := zCell cfg.hashConfig iHash 3 1 }).operations (i₀ + 1)) (i₀ + 1) ∧
    Constraints place env
      (((DecomposeE.bundle.toFormal "NoteCommit MessagePiece e").call cfg.gates.e
        { e := pcs.e, e0 := pcs.e0, e1 := pcs.e1 }).operations (i₀ + 2)) (i₀ + 2) ∧
    Constraints place env
      ((((DecomposeG.bundle (brWit input.rho 254 1)).toFormal
        "NoteCommit MessagePiece g").call cfg.gates.g
        { g := pcs.g, g1 := pcs.g1,
          g2 := zCell cfg.hashConfig iHash 6 1 }).operations (i₀ + 3)) (i₀ + 3) ∧
    Constraints place env
      ((((DecomposeH.bundle (brWit input.psi 254 1)).toFormal
        "NoteCommit MessagePiece h").call cfg.gates.h
        { h := pcs.h, h0 := pcs.h0 }).operations (i₀ + 4)) (i₀ + 4) ∧
    Constraints place env
      (((GdCanonicity.bundle.toFormal "NoteCommit input g_d").call cfg.gates.gd
        { gdX := input.gdX, b0 := pcs.b0, b1 := AssignedCell.of i₀ 0 cfg.gates.b.colR,
          a := pcs.a, aPrime := ccs.aZs.z0,
          z13A := zCell cfg.hashConfig iHash 0 13,
          z13APrime := ccs.aZs.zLast }).operations (i₀ + 5)) (i₀ + 5) ∧
    Constraints place env
      (((PkdCanonicity.bundle.toFormal "NoteCommit input pk_d").call cfg.gates.pkd
        { pkdX := input.pkdX, b3 := pcs.b3,
          d0 := AssignedCell.of (i₀ + 1) 0 cfg.gates.d.colM, c := pcs.c,
          b3CPrime := ccs.bZs.z0, z13C := zCell cfg.hashConfig iHash 2 13,
          z14B3CPrime := ccs.bZs.zLast }).operations (i₀ + 6)) (i₀ + 6) ∧
    Constraints place env
      (((ValueCanonicity.bundle.toFormal "NoteCommit input value").call cfg.gates.value
        { value := input.value, d2 := pcs.d2, d3 := zCell cfg.hashConfig iHash 3 1,
          e0 := pcs.e0 }).operations (i₀ + 7)) (i₀ + 7) ∧
    Constraints place env
      (((RhoCanonicity.bundle.toFormal "NoteCommit input rho").call cfg.gates.rho
        { rho := input.rho, e1 := pcs.e1,
          g0 := AssignedCell.of (i₀ + 3) 0 cfg.gates.g.colM, f := pcs.f,
          e1FPrime := ccs.eZs.z0, z13F := zCell cfg.hashConfig iHash 5 13,
          z14E1FPrime := ccs.eZs.zLast }).operations (i₀ + 8)) (i₀ + 8) ∧
    Constraints place env
      (((PsiCanonicity.bundle.toFormal "NoteCommit input psi").call cfg.gates.psi
        { psi := input.psi, h0 := pcs.h0, g1 := pcs.g1,
          h1 := AssignedCell.of (i₀ + 4) 0 cfg.gates.h.colR,
          g2 := zCell cfg.hashConfig iHash 6 1, g1G2Prime := ccs.gZs.z0,
          z13G := zCell cfg.hashConfig iHash 6 13,
          z13G1G2Prime := ccs.gZs.zLast }).operations (i₀ + 9)) (i₀ + 9) := by
  simp only [synthGates, circuit_norm, decomposeB_output,
    decomposeD_output, decomposeG_output, decomposeH_output] at h
  rw [toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount,
    toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount,
    toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount] at h
  exact h

/-- The Ironwood `Chain.ZsFacts` is the donor's, verbatim. -/
private theorem zsFacts_donor_iff :
    ∀ (ms : List ℕ) (chunks : List ℕ)
      (zs : Orchard.Sinsemilla.HVec (Sinsemilla.Chain.zLengths ms) Fp),
      Sinsemilla.Chain.ZsFacts ms chunks zs ↔
      Orchard.Sinsemilla.Chain.ZsFacts ms chunks zs := by
  intro ms
  induction ms with
  | nil =>
    intro chunks zs
    simp only [Sinsemilla.Chain.ZsFacts, Orchard.Sinsemilla.Chain.ZsFacts]
  | cons n rest ih =>
    intro chunks zs
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (ih _ _).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (ih _ _).mpr h2⟩

/-- The hash child's extracted running sums are the `bits`-column reads. -/
private theorem hashExtract_zs (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Sinsemilla.HashPiece.Config)
    (inp : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (iH : RegionIndex)
    (place : RegionIndex → ℕ) (env : Environment Fp) :
    ((Sinsemilla.HashToPoint.hashCircuit G ns Q hQ ns_ne_nil).extract cfg inp iH
        (⟨place, env⟩ : Placed Environment Fp)).zs
      = Sinsemilla.Chain.zsFam
          (fun r => env.advice cfg.bits ((place iH + r : ℕ) : ℤ)) ns 0 := by
  show (eval (⟨place, env⟩ : Placed Environment Fp)
    (Sinsemilla.Chain.zsCellsVal cfg iH ns 0)
    : Orchard.Sinsemilla.HVec (Sinsemilla.Chain.zLengths ns) Fp) = _
  exact Sinsemilla.Chain.eval_zsCellsVal cfg iH _ ns 0

/-- The six hash running-sum reads the gates copy, at the concrete `ns` layout
(rows: piece starts `[0,25,26,51,57,58,83,108]`). -/
private theorem zs_get_z13a (f : ℕ → Fp) :
    (Orchard.Sinsemilla.HVec.get (Orchard.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨0, by decide⟩)[13]'(by decide) = f 13 := by
  simp only [ns, Sinsemilla.Chain.zLengths, Orchard.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Orchard.Sinsemilla.HVec.get,
    Orchard.Sinsemilla.HVec.head_cons, Orchard.Sinsemilla.HVec.tail_cons,
    Vector.getElem_ofFn, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Orchard.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z13c (f : ℕ → Fp) :
    (Orchard.Sinsemilla.HVec.get (Orchard.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨2, by decide⟩)[13]'(by decide) = f 39 := by
  simp only [ns, Sinsemilla.Chain.zLengths, Orchard.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Orchard.Sinsemilla.HVec.get,
    Orchard.Sinsemilla.HVec.head_cons, Orchard.Sinsemilla.HVec.tail_cons,
    Vector.getElem_ofFn, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Orchard.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z1d (f : ℕ → Fp) :
    (Orchard.Sinsemilla.HVec.get (Orchard.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨3, by decide⟩)[1]'(by decide) = f 52 := by
  simp only [ns, Sinsemilla.Chain.zLengths, Orchard.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Orchard.Sinsemilla.HVec.get,
    Orchard.Sinsemilla.HVec.head_cons, Orchard.Sinsemilla.HVec.tail_cons,
    Vector.getElem_ofFn, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  exact (congrArg (fun v => v[1]'(by norm_num))
    (Orchard.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z13f (f : ℕ → Fp) :
    (Orchard.Sinsemilla.HVec.get (Orchard.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨5, by decide⟩)[13]'(by decide) = f 71 := by
  simp only [ns, Sinsemilla.Chain.zLengths, Orchard.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Orchard.Sinsemilla.HVec.get,
    Orchard.Sinsemilla.HVec.head_cons, Orchard.Sinsemilla.HVec.tail_cons,
    Vector.getElem_ofFn, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Orchard.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z1g (f : ℕ → Fp) :
    (Orchard.Sinsemilla.HVec.get (Orchard.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨6, by decide⟩)[1]'(by decide) = f 84 := by
  simp only [ns, Sinsemilla.Chain.zLengths, Orchard.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Orchard.Sinsemilla.HVec.get,
    Orchard.Sinsemilla.HVec.head_cons, Orchard.Sinsemilla.HVec.tail_cons,
    Vector.getElem_ofFn, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  exact (congrArg (fun v => v[1]'(by norm_num))
    (Orchard.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z13g (f : ℕ → Fp) :
    (Orchard.Sinsemilla.HVec.get (Orchard.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨6, by decide⟩)[13]'(by decide) = f 96 := by
  simp only [ns, Sinsemilla.Chain.zLengths, Orchard.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Orchard.Sinsemilla.HVec.get,
    Orchard.Sinsemilla.HVec.head_cons, Orchard.Sinsemilla.HVec.tail_cons,
    Vector.getElem_ofFn, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Orchard.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

theorem soundness (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config) :
    FormalCircuit.Soundness (Witness := fun _ => Vector Fp 85 × Fq)
      (synth G R windows Q hQ cfg)
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
  -- ── stage 3: the ten gate regions (standalone peel) ──
  simp only [synthPieces_nextRegionIndex, synthChecks_nextRegionIndex,
    synthPieces_regionCount, synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd] at hGt
  have hGates := peelGates cfg _ _ _ _ _ place env hGt
  clear hGt
  have hGb := hGates.1
  have hGd := hGates.2.1
  have hGe := hGates.2.2.1
  have hGg := hGates.2.2.2.1
  have hGh := hGates.2.2.2.2.1
  have hGgd := hGates.2.2.2.2.2.1
  have hGpkd := hGates.2.2.2.2.2.2.1
  have hGval := hGates.2.2.2.2.2.2.2.1
  have hGrho := hGates.2.2.2.2.2.2.2.2.1
  have hGpsi := hGates.2.2.2.2.2.2.2.2.2
  clear hGates
  subcircuit_rw at hGb
  subcircuit_rw at hGd
  subcircuit_rw at hGe
  subcircuit_rw at hGg
  subcircuit_rw at hGh
  subcircuit_rw at hGgd
  subcircuit_rw at hGpkd
  subcircuit_rw at hGval
  subcircuit_rw at hGrho
  subcircuit_rw at hGpsi
  -- the five decomposition gates (no rely-conditions)
  have hGbS := hGb (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq]; trivial)
  rw [toFormal_spec_eq, decomposeB_output, toFormal_extract_eq] at hGbS
  simp only [DecomposeB.bundle, circuit_norm] at hGbS
  have hGdS := hGd (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq]; trivial)
  rw [toFormal_spec_eq, decomposeD_output, toFormal_extract_eq] at hGdS
  simp only [DecomposeD.bundle, circuit_norm] at hGdS
  have hGeS := hGe (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq]; trivial)
  rw [toFormal_spec_eq] at hGeS
  simp only [DecomposeE.bundle, circuit_norm] at hGeS
  have hGgS := hGg (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq]; trivial)
  rw [toFormal_spec_eq, decomposeG_output, toFormal_extract_eq] at hGgS
  simp only [DecomposeG.bundle, circuit_norm] at hGgS
  have hGhS := hGh (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq]; trivial)
  rw [toFormal_spec_eq, decomposeH_output, toFormal_extract_eq] at hGhS
  simp only [DecomposeH.bundle, circuit_norm] at hGhS
  clear hGb hGd hGe hGg hGh
  simp only [synthPieces_output, synthChecks_output, circuit_norm, zCell,
    AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
    Environment.get_advice] at hGbS hGdS hGeS hGgS hGhS hY1S hY2S hCmS
  -- ── the six hash running-sum value facts ──
  obtain ⟨chunks, hPC, hZs, hContract⟩ := hCmS
  rw [hashExtract_zs] at hZs
  have hPC' := (pieceChunks_donor_iff _ _ _).mp hPC
  have hZs' := (zsFacts_donor_iff _ _ _).mp hZs
  have hz13a := Orchard.Action.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨0, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13a] at hz13a
  have hz13c := Orchard.Action.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨2, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13c] at hz13c
  have hz1d := Orchard.Action.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨3, by decide⟩ hPC' hZs' (by decide) (r := 1) (by decide)
  rw [zs_get_z1d] at hz1d
  have hz13f := Orchard.Action.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨5, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13f] at hz13f
  have hz1g := Orchard.Action.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨6, by decide⟩ hPC' hZs' (by decide) (r := 1) (by decide)
  rw [zs_get_z1g] at hz1g
  have hz13g := Orchard.Action.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨6, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13g] at hz13g
  -- ── normalize region-index spellings ──
  simp only [Nat.add_assoc, Nat.reduceAdd] at hGbS hGdS hGeS hGgS hGhS hY1S hY2S
  simp only [Nat.add_assoc, Nat.reduceAdd] at haz0 htelA hbz0 htelB hez0 htelE hgz0 htelG
  simp only [Nat.add_assoc, Nat.reduceAdd] at hz13a hz13c hz1d hz13f hz1g hz13g
  simp only [Nat.add_assoc, Nat.reduceAdd] at hb0 hb3 hd2 he0 he1 hg1 hh0
  -- ── the piece-value bounds (from the chunk decompositions) ──
  have hpieceA := Orchard.Action.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨0, by decide⟩ hPC' (by decide)
  have hpieceC := Orchard.Action.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨2, by decide⟩ hPC' (by decide)
  have hpieceD := Orchard.Action.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨3, by decide⟩ hPC' (by decide)
  have hpieceF := Orchard.Action.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨5, by decide⟩ hPC' (by decide)
  have hpieceG := Orchard.Action.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨6, by decide⟩ hPC' (by decide)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hpieceA hpieceC hpieceD hpieceF hpieceG
  -- restate the vector-element facts on the piece reads (defeq transport)
  have haval : (env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ)).val
      < 2 ^ 250 := by with_unfolding_all exact hpieceA
  have hcval : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ)).val
      < 2 ^ 250 := by with_unfolding_all exact hpieceC
  have hdval : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ)).val
      < 2 ^ 60 := by with_unfolding_all exact hpieceD
  have hfval : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 10) : ℕ) : ℤ)).val
      < 2 ^ 250 := by with_unfolding_all exact hpieceF
  have hgval : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ)).val
      < 2 ^ 250 := by with_unfolding_all exact hpieceG
  have hza : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 13 : ℕ) : ℤ)
      = (((env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ)).val
        / 2 ^ 130 : ℕ) : Fp) := by with_unfolding_all exact hz13a
  have hzc : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 39 : ℕ) : ℤ)
      = (((env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ)).val
        / 2 ^ 130 : ℕ) : Fp) := by with_unfolding_all exact hz13c
  have hzd : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 52 : ℕ) : ℤ)
      = (((env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ)).val
        / 2 ^ 10 : ℕ) : Fp) := by with_unfolding_all exact hz1d
  have hzf : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 71 : ℕ) : ℤ)
      = (((env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 10) : ℕ) : ℤ)).val
        / 2 ^ 130 : ℕ) : Fp) := by with_unfolding_all exact hz13f
  have hzg1 : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 84 : ℕ) : ℤ)
      = (((env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ)).val
        / 2 ^ 10 : ℕ) : Fp) := by with_unfolding_all exact hz1g
  have hzg13 : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 96 : ℕ) : ℤ)
      = (((env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ)).val
        / 2 ^ 130 : ℕ) : Fp) := by with_unfolding_all exact hz13g
  -- cast-value bounds for the copied running-sum cells
  have hzdval : ((((env.advice cfg.hashConfig.witnessPieces
        ((place (i₀ + 6) : ℕ) : ℤ)).val / 2 ^ 10 : ℕ) : Fp)).val < 2 ^ 50 := by
    rw [ZMod.val_natCast_of_lt (by
      have h60 : (2 : ℕ) ^ 60 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
      have := Nat.div_le_self (env.advice cfg.hashConfig.witnessPieces
        ((place (i₀ + 6) : ℕ) : ℤ)).val (2 ^ 10)
      omega)]
    have := hdval
    have h50 : (2 : ℕ) ^ 60 = 2 ^ 50 * 2 ^ 10 := by norm_num
    exact Nat.div_lt_of_lt_mul (by omega)
  have hzg1val : ((((env.advice cfg.hashConfig.witnessPieces
        ((place (i₀ + 12) : ℕ) : ℤ)).val / 2 ^ 10 : ℕ) : Fp)).val < 2 ^ 240 := by
    rw [ZMod.val_natCast_of_lt (by
      have h250 : (2 : ℕ) ^ 250 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
      have := Nat.div_le_self (env.advice cfg.hashConfig.witnessPieces
        ((place (i₀ + 12) : ℕ) : ℤ)).val (2 ^ 10)
      omega)]
    have := hgval
    have h240 : (2 : ℕ) ^ 250 = 2 ^ 240 * 2 ^ 10 := by norm_num
    exact Nat.div_lt_of_lt_mul (by omega)
  -- ── the five canonicity gates ──
  have hGgdS := hGgd (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, gd_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
          prefixRows_ns_2, prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGbS.1, haval, hb0, hza, loA, hloA, by rw [← haz0] at htelA; exact htelA⟩)
  rw [toFormal_spec_eq, gd_spec_eq] at hGgdS
  simp only [GdCanonicity.toDonor, Orchard.Action.NoteCommit.GdCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0, prefixRows_ns_2,
    prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGgdS
  have hGpkdS := hGpkd (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, pkd_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
          prefixRows_ns_2, prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGdS.1, hcval, hb3, hzc, loB, hloB, by rw [← hbz0] at htelB; exact htelB⟩)
  rw [toFormal_spec_eq, pkd_spec_eq] at hGpkdS
  simp only [PkdCanonicity.toDonor, Orchard.Action.NoteCommit.PkdCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0, prefixRows_ns_2,
    prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGpkdS
  have hGvalS := hGval (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, value_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
          prefixRows_ns_2, prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hd2, by rw [hzd]; exact hzdval, he0⟩)
  rw [toFormal_spec_eq, value_spec_eq] at hGvalS
  simp only [ValueCanonicity.toDonor, Orchard.Action.NoteCommit.ValueCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0, prefixRows_ns_2,
    prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGvalS
  have hGrhoS := hGrho (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, rho_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
          prefixRows_ns_2, prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGgS.1, hfval, he1, hzf, loE, hloE, by rw [← hez0] at htelE; exact htelE⟩)
  rw [toFormal_spec_eq, rho_spec_eq] at hGrhoS
  simp only [RhoCanonicity.toDonor, Orchard.Action.NoteCommit.RhoCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0, prefixRows_ns_2,
    prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGrhoS
  simp only [prefixRows_ns_0, prefixRows_ns_2, prefixRows_ns_3, prefixRows_ns_5,
    prefixRows_ns_6, Nat.reduceAdd] at hGbS hGdS hGeS hGgS hGhS
  -- Psi: the z13G tail via the donor bridge over the DecomposeG facts
  have hz13G_tail := Orchard.Action.NoteCommit.z13G_tail_of_decompose_g
    hGgS.1 hg1 (by rw [hzg1]; exact hzg1val) hGgS.2 hzg13
  have hGpsiS := hGpsi (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, psi_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
          prefixRows_ns_2, prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGhS.1, hg1, by rw [hzg1]; exact hzg1val, hh0, hz13G_tail,
          loG, hloG, by rw [← hgz0] at htelG; exact htelG⟩)
  rw [toFormal_spec_eq, psi_spec_eq] at hGpsiS
  simp only [PsiCanonicity.toDonor, Orchard.Action.NoteCommit.PsiCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0, prefixRows_ns_2,
    prefixRows_ns_3, prefixRows_ns_5, prefixRows_ns_6, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGpsiS
  -- ── the chunk-equality assembly ──
  have hLow1 := hY1S hGbS.2.1
  have hLow2 := hY2S hGdS.2.1
  have hz1dEq := Orchard.Action.NoteCommit.cell_eq_of_val hGvalS.2.2.1
  have hz1gEq := Orchard.Action.NoteCommit.cell_eq_of_val hGpsiS.2.1
  have hchunksEq := Orchard.Action.NoteCommit.note_chunks_eq_of_cellFacts
    (gd := ⟨env.get input_var_gdX.cell.column
        ((place input_var_gdX.cell.regionIndex + input_var_gdX.cell.rowOffset : ℕ) : ℤ),
      env.get input_var_gdY.cell.column
        ((place input_var_gdY.cell.regionIndex + input_var_gdY.cell.rowOffset : ℕ) : ℤ)⟩)
    (pkd := ⟨env.get input_var_pkdX.cell.column
        ((place input_var_pkdX.cell.regionIndex + input_var_pkdX.cell.rowOffset : ℕ) : ℤ),
      env.get input_var_pkdY.cell.column
        ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ)⟩)
    (value := env.get input_var_value.cell.column
      ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))
    (rho := env.get input_var_rho.cell.column
      ((place input_var_rho.cell.regionIndex + input_var_rho.cell.rowOffset : ℕ) : ℤ))
    (psi := env.get input_var_psi.cell.column
      ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))
    (cells :=
      { a := env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ),
        b := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ),
        c := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ),
        d := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ),
        e := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 9) : ℕ) : ℤ),
        f := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 10) : ℕ) : ℤ),
        g := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ),
        h := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 14) : ℕ) : ℤ),
        b0 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 1) : ℕ) : ℤ),
        b1 := env.advice cfg.gates.b.colR ((place (i₀ + 33) : ℕ) : ℤ),
        b2 := env.advice (cfg.gates.y.advices 6) ((place (i₀ + 19) : ℕ) : ℤ),
        b3 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 2) : ℕ) : ℤ),
        d0 := env.advice cfg.gates.d.colM ((place (i₀ + 34) : ℕ) : ℤ),
        d1 := env.advice (cfg.gates.y.advices 6) ((place (i₀ + 24) : ℕ) : ℤ),
        d2 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 5) : ℕ) : ℤ),
        e0 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 7) : ℕ) : ℤ),
        e1 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 8) : ℕ) : ℤ),
        g0 := env.advice cfg.gates.g.colM ((place (i₀ + 36) : ℕ) : ℤ),
        g1 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 11) : ℕ) : ℤ),
        h0 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 13) : ℕ) : ℤ),
        h1 := env.advice cfg.gates.h.colR ((place (i₀ + 37) : ℕ) : ℤ) })
    (by with_unfolding_all exact hPC')
    ⟨hGgdS.1, hGgdS.2.1, hGgdS.2.2.1, hLow1, hGpkdS.1, hGpkdS.2.1, hGpkdS.2.2.1, hLow2,
     hGvalS.2.1, hGvalS.2.2.2, hGrhoS.1, hGrhoS.2.1, hGrhoS.2.2.1, hGpsiS.1,
     hGpsiS.2.2.1, hGpsiS.2.2.2.1,
     hGbS.2.2, by rw [← hz1dEq]; exact hGdS.2.2, hGeS,
     by rw [← hz1gEq]; exact hGgS.2, hGhS.2⟩
    hGvalS.1
  -- ── land the Spec ──
  simp only [Spec]
  intro B hB
  obtain ⟨higdX, higdY, hipkdX, hipkdY, hival, hirho, hipsi⟩ := h_input
  rw [higdX, higdY, hipkdX, hipkdY, hival, hirho, hipsi] at hchunksEq
  rw [show (Orchard.Action.NoteCommit.noteScalars ⟨input_gdX, input_gdY⟩
      ⟨input_pkdX, input_pkdY⟩ input_value input_rho input_psi).chunks
    = Orchard.Specs.Sinsemilla.noteCommitChunks input_gdX.val (input_gdY.val % 2)
      input_pkdX.val (input_pkdY.val % 2) input_value.val input_rho.val input_psi.val
    from rfl] at hB
  rw [← hchunksEq] at hB
  obtain ⟨-, hOut⟩ := hContract B hB
  have hOutVar : ({ x := output_x, y := output_y } : Orchard.Point Fp)
      = eval (⟨place, env⟩ : Placed Environment Fp)
        ((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).output
          (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
          { pieces :=
              #v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 1 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 2 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 4 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 7 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 8 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 10 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 12 + 2) 0 cfg.hashConfig.witnessPieces] }
          (i₀ + 15 + 5 + 5)) := by
    rw [← h_output]
    with_unfolding_all rfl
  rw [hOutVar]
  exact hOut

theorem completeness (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config) :
    FormalCircuit.Completeness (Witness := fun _ => Vector Fp 85 × Fq)
      (synth G R windows Q hQ cfg)
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
  Witness := fun _ => Vector Fp 85 × Fq
  extract := rcmExtract
  EnvAssumptions := EnvAssumptions G
  Assumptions := Assumptions
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q
  ProverSpec := fun _ _ _ _ => True
  soundness := soundness G R windows Q hQ
  completeness := completeness G R windows Q hQ

end Halo2.Ironwood.NoteCommit.Main
