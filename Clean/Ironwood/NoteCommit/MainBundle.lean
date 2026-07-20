import Clean.Ironwood.NoteCommit.Main
import Clean.Ironwood.Sinsemilla.ChainTheorems

/-!
# NoteCommit bundle proofs (soundness / completeness / the `circuit` def)

Kept separate from `Main.lean` (the defs/contract layer): this file is the kernel-heavy
part — the fully proven soundness/completeness theorems and the bundled `circuit`.
-/

namespace Halo2.Ironwood.NoteCommit.Main

open Halo2.Ironwood (Fp)
open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)
open Halo2.Ironwood.Specs (bitrange)
open Halo2.Ironwood.Specs.Sinsemilla (Generators hashToPoint)
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
          (IsBool out → Halo2.Ironwood.NoteCommit.IsLowBit input.y out) := rfl

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

private theorem yc_proverAssumptions_eq (w : WitgenIR Fp 1) :
    (YCanonicityCheck.circuit w).ProverAssumptions
      = fun input (wit : Fp) _ =>
          Halo2.Ironwood.NoteCommit.IsLowBit input.y wit := rfl

private theorem commit_proverAssumptions_eq (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).ProverAssumptions
      = fun input wit _ =>
          Sinsemilla.Chain.PieceBounds ns input.pieces ∧
          (∃ B, hashToPoint G.S Q
            (Sinsemilla.Chain.honestChunks ns input.pieces) = some B) ∧
          ∀ w : Fin 85, (wit.2.1[w.val]).val < 8 := rfl

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
  simp only [DecomposeH.bundle, circuit_norm, RegionCircuit.output_bind]

end ChildBridges

private theorem gd_assumptions_eq :
    GdCanonicity.bundle.Assumptions = fun input =>
      IsBool input.b1 ∧ input.a.val < 2 ^ 250 ∧ input.b0.val < 2 ^ 4 ∧
      input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp) ∧
      ∃ lo : ℕ, lo < 2 ^ 130 ∧
        input.aPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13APrime := rfl

private theorem gd_spec_eq :
    GdCanonicity.bundle.Spec = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.GdCanonicity.Gate.Spec (GdCanonicity.toDonor input) := rfl

private theorem pkd_assumptions_eq :
    PkdCanonicity.bundle.Assumptions = fun input =>
      IsBool input.d0 ∧ input.c.val < 2 ^ 250 ∧ input.b3.val < 2 ^ 4 ∧
      input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp) ∧
      ∃ lo : ℕ, lo < 2 ^ 140 ∧
        input.b3CPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14B3CPrime := rfl

private theorem pkd_spec_eq :
    PkdCanonicity.bundle.Spec = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.PkdCanonicity.Gate.Spec
        (PkdCanonicity.toDonor input) := rfl

private theorem value_assumptions_eq :
    ValueCanonicity.bundle.Assumptions = fun input =>
      input.d2.val < 2 ^ 8 ∧ input.d3.val < 2 ^ 50 ∧ input.e0.val < 2 ^ 6 := rfl

private theorem value_spec_eq :
    ValueCanonicity.bundle.Spec = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.ValueCanonicity.Gate.Spec
        (ValueCanonicity.toDonor input) := rfl

private theorem rho_assumptions_eq :
    RhoCanonicity.bundle.Assumptions = fun input =>
      IsBool input.g0 ∧ input.f.val < 2 ^ 250 ∧ input.e1.val < 2 ^ 4 ∧
      input.z13F = ((input.f.val / 2 ^ 130 : ℕ) : Fp) ∧
      ∃ lo : ℕ, lo < 2 ^ 140 ∧
        input.e1FPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14E1FPrime := rfl

private theorem rho_spec_eq :
    RhoCanonicity.bundle.Spec = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.RhoCanonicity.Gate.Spec
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
      Halo2.Ironwood.NoteCommit.PsiCanonicity.Gate.Spec
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
      Halo2.Ironwood.Sinsemilla.Chain.PieceChunks ms pieces chunks := by
  intro ms
  induction ms with
  | nil =>
    intro pieces chunks
    simp only [Sinsemilla.Chain.PieceChunks, Halo2.Ironwood.Sinsemilla.Chain.PieceChunks]
  | cons n rest ih =>
    intro pieces chunks
    constructor
    · rintro ⟨msf, h1, h2, tailChunks, h3, h4⟩
      exact ⟨msf, h1, h2, tailChunks, h3, (ih _ _).mp h4⟩
    · rintro ⟨msf, h1, h2, tailChunks, h3, h4⟩
      exact ⟨msf, h1, h2, tailChunks, h3, (ih _ _).mpr h4⟩

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
      (zs : Halo2.Ironwood.Sinsemilla.HVec (Sinsemilla.Chain.zLengths ms) Fp),
      Sinsemilla.Chain.ZsFacts ms chunks zs ↔
      Halo2.Ironwood.Sinsemilla.Chain.ZsFacts ms chunks zs := by
  intro ms
  induction ms with
  | nil =>
    intro chunks zs
    simp only [Sinsemilla.Chain.ZsFacts, Halo2.Ironwood.Sinsemilla.Chain.ZsFacts]
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
    : Halo2.Ironwood.Sinsemilla.HVec (Sinsemilla.Chain.zLengths ns) Fp) = _
  exact Sinsemilla.Chain.eval_zsCellsVal cfg iH _ ns 0

/-- The six hash running-sum reads the gates copy, at the concrete `ns` layout
(rows: piece starts `[0,25,26,51,57,58,83,108]`). -/
private theorem zs_get_z13a (f : ℕ → Fp) :
    (Halo2.Ironwood.Sinsemilla.HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨0, by decide⟩)[13]'(by decide) = f 13 := by
  simp only [ns, Halo2.Ironwood.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Halo2.Ironwood.Sinsemilla.HVec.get,
        Nat.reduceAdd, Nat.zero_add]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Halo2.Ironwood.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z13c (f : ℕ → Fp) :
    (Halo2.Ironwood.Sinsemilla.HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨2, by decide⟩)[13]'(by decide) = f 39 := by
  simp only [ns, Halo2.Ironwood.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Halo2.Ironwood.Sinsemilla.HVec.get,
    Halo2.Ironwood.Sinsemilla.HVec.tail_cons,
    Nat.reduceAdd, Nat.zero_add]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Halo2.Ironwood.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z1d (f : ℕ → Fp) :
    (Halo2.Ironwood.Sinsemilla.HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨3, by decide⟩)[1]'(by decide) = f 52 := by
  simp only [ns, Halo2.Ironwood.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Halo2.Ironwood.Sinsemilla.HVec.get,
    Halo2.Ironwood.Sinsemilla.HVec.tail_cons,
    Nat.reduceAdd, Nat.zero_add]
  exact (congrArg (fun v => v[1]'(by norm_num))
    (Halo2.Ironwood.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z13f (f : ℕ → Fp) :
    (Halo2.Ironwood.Sinsemilla.HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨5, by decide⟩)[13]'(by decide) = f 71 := by
  simp only [ns, Halo2.Ironwood.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Halo2.Ironwood.Sinsemilla.HVec.get,
    Halo2.Ironwood.Sinsemilla.HVec.tail_cons,
    Nat.reduceAdd, Nat.zero_add]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Halo2.Ironwood.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z1g (f : ℕ → Fp) :
    (Halo2.Ironwood.Sinsemilla.HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨6, by decide⟩)[1]'(by decide) = f 84 := by
  simp only [ns, Halo2.Ironwood.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Halo2.Ironwood.Sinsemilla.HVec.get,
    Halo2.Ironwood.Sinsemilla.HVec.tail_cons,
    Nat.reduceAdd, Nat.zero_add]
  exact (congrArg (fun v => v[1]'(by norm_num))
    (Halo2.Ironwood.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

private theorem zs_get_z13g (f : ℕ → Fp) :
    (Halo2.Ironwood.Sinsemilla.HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns)
      (Sinsemilla.Chain.zsFam f ns 0) ⟨6, by decide⟩)[13]'(by decide) = f 96 := by
  simp only [ns, Halo2.Ironwood.Sinsemilla.Chain.zLengths,
    List.map_cons, List.map_nil,
    Sinsemilla.Chain.zsFam, Halo2.Ironwood.Sinsemilla.HVec.get,
    Halo2.Ironwood.Sinsemilla.HVec.tail_cons,
    Nat.reduceAdd, Nat.zero_add]
  exact (congrArg (fun v => v[13]'(by norm_num))
    (Halo2.Ironwood.Sinsemilla.HVec.head_cons _ _)).trans (by simp)

/-- Build direction of `peelGates` (kernel-checked alone). -/
private theorem buildGates (cfg : Config) (input : Inputs (AssignedCell Fp))
    (pcs : PieceCells) (ccs : CheckCells) (iHash : RegionIndex)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (h : 
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
          z13G1G2Prime := ccs.gZs.zLast }).operations (i₀ + 9)) (i₀ + 9)) :
    Constraints place env ((synthGates cfg input pcs ccs iHash).operations i₀) i₀ := by
  simp only [synthGates, circuit_norm, decomposeB_output,
    decomposeD_output, decomposeG_output, decomposeH_output]
  rw [toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount,
    toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount,
    toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount]
  exact h

private theorem rangeCheckAt_proverSpec_eq (n : ℕ) :
    (LookupRangeCheck.rangeCheckAt 10 n false).ProverSpec
      = fun _ output (elt : Fp) _ =>
          output.z0 = elt ∧
          output.zLast = ((elt.val / 2 ^ (10 * n) : ℕ) : Fp) := rfl

private theorem rangeCheckAt_extract_eq (n : ℕ) (cfg : LookupRangeCheck.Config 10)
    (i : RegionIndex) (env : Placed Environment Fp) :
    (LookupRangeCheck.rangeCheckAt 10 n false).extract cfg 0 () i env
      = (env.env.advice cfg.runningSum ((env.place i : ℕ) : ℤ) : Fp) := by
  show eval env (AssignedCell.of i 0 cfg.runningSum : Var field Fp) = _
  simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_zero]

private theorem rangeCheckAt_proverAssumptions_eq (n : ℕ) :
    (LookupRangeCheck.rangeCheckAt 10 n false).ProverAssumptions
      = fun _ (elt : Fp) _ => (false = true → elt.val < 2 ^ (10 * n)) := rfl

private theorem short_proverAssumptions_eq (b : ℕ) :
    (LookupRangeCheck.shortRangeCheck 10 b).ProverAssumptions
      = fun _ (wit : Fp) _ => wit.val < 2 ^ b := rfl

private theorem short_extract_eq' (b : ℕ) (cfg : LookupRangeCheck.Config 10)
    (i : RegionIndex) (env : Placed Environment Fp) :
    (LookupRangeCheck.shortRangeCheck 10 b).extract cfg 0 () i env
      = (env.env.advice cfg.runningSum ((env.place i : ℕ) : ℤ) : Fp) := by
  show eval env (AssignedCell.of i 0 cfg.runningSum : Var field Fp) = _
  simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_zero]

/-- Build direction for stage 1: the seven short-check chunks give the stage. -/
private theorem buildPieces (cfg : Config) (input : Inputs (AssignedCell Fp))
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (h :
    RegionOperations.Constraints place (i₀ + 1) env
      (((LookupRangeCheck.shortRangeCheck 10 4).call cfg.lookupConfig 0 ()).operations
        (i₀ + 1)) ∧
    RegionOperations.Constraints place (i₀ + 2) env
      (((LookupRangeCheck.shortRangeCheck 10 4).call cfg.lookupConfig 0 ()).operations
        (i₀ + 2)) ∧
    RegionOperations.Constraints place (i₀ + 5) env
      (((LookupRangeCheck.shortRangeCheck 10 8).call cfg.lookupConfig 0 ()).operations
        (i₀ + 5)) ∧
    RegionOperations.Constraints place (i₀ + 7) env
      (((LookupRangeCheck.shortRangeCheck 10 6).call cfg.lookupConfig 0 ()).operations
        (i₀ + 7)) ∧
    RegionOperations.Constraints place (i₀ + 8) env
      (((LookupRangeCheck.shortRangeCheck 10 4).call cfg.lookupConfig 0 ()).operations
        (i₀ + 8)) ∧
    RegionOperations.Constraints place (i₀ + 11) env
      (((LookupRangeCheck.shortRangeCheck 10 9).call cfg.lookupConfig 0 ()).operations
        (i₀ + 11)) ∧
    RegionOperations.Constraints place (i₀ + 13) env
      (((LookupRangeCheck.shortRangeCheck 10 5).call cfg.lookupConfig 0 ()).operations
        (i₀ + 13))) :
    Constraints place env ((synthPieces cfg input).operations i₀) i₀ := by
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm, Nat.add_assoc,
    Nat.reduceAdd]
  exact h

/-- Build direction for stage 2: the y-flows, the commit, the four witness_checks. -/
private theorem buildChecks (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Inputs (AssignedCell Fp)) (pcs : PieceCells) (iHash : RegionIndex)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (h :
    Constraints place env
      (((YCanonicityCheck.circuit (brWit input.gdY 0 1)).call
        (cfg.gates.y, cfg.lookupConfig) { y := input.gdY }).operations i₀) i₀ ∧
    Constraints place env
      (((YCanonicityCheck.circuit (brWit input.pkdY 0 1)).call
        (cfg.gates.y, cfg.lookupConfig) { y := input.pkdY }).operations (i₀ + 5))
      (i₀ + 5) ∧
    Constraints place env
      (((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).call
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
        { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h] }).operations
        (i₀ + 10)) (i₀ + 10) ∧
    RegionOperations.Constraints place (i₀ + 14) env
      (((LookupRangeCheck.rangeCheckAt 10 13 false).call cfg.lookupConfig 0 ()).operations
        (i₀ + 14)) ∧
    RegionOperations.Constraints place (i₀ + 15) env
      (((LookupRangeCheck.rangeCheckAt 10 14 false).call cfg.lookupConfig 0 ()).operations
        (i₀ + 15)) ∧
    RegionOperations.Constraints place (i₀ + 16) env
      (((LookupRangeCheck.rangeCheckAt 10 14 false).call cfg.lookupConfig 0 ()).operations
        (i₀ + 16)) ∧
    RegionOperations.Constraints place (i₀ + 17) env
      (((LookupRangeCheck.rangeCheckAt 10 13 false).call cfg.lookupConfig 0 ()).operations
        (i₀ + 17))) :
    Constraints place env
      ((synthChecks G R windows Q hQ cfg input pcs iHash).operations i₀) i₀ := by
  simp only [synthChecks, LookupRangeCheck.witnessCheck, circuit_norm]
  rw [yc_call_regionCount, yc_call_regionCount, commit_call_regionCount]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  exact h

/-- Assemble the three stage constraint blocks into the whole flow. -/
private theorem buildSynth (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Inputs (AssignedCell Fp)) (i₀ : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp)
    (h1 : Constraints place env ((synthPieces cfg input).operations i₀) i₀)
    (h2 : Constraints place env
      ((synthChecks G R windows Q hQ cfg input
        ((synthPieces cfg input).output i₀) (i₀ + 27)).operations (i₀ + 15)) (i₀ + 15))
    (h3 : Constraints place env
      ((synthGates cfg input ((synthPieces cfg input).output i₀)
        ((synthChecks G R windows Q hQ cfg input ((synthPieces cfg input).output i₀)
          (i₀ + 27)).output (i₀ + 15)) (i₀ + 27)).operations (i₀ + 33)) (i₀ + 33)) :
    Constraints place env
      ((synth G R windows Q hQ cfg input).operations i₀) i₀ := by
  simp only [synth, circuit_norm, synthPieces_nextRegionIndex,
    synthChecks_nextRegionIndex, synthPieces_regionCount, synthChecks_regionCount,
    Nat.add_assoc, Nat.reduceAdd]
  exact ⟨h1, h2, h3⟩

/-- Witness-side stage-3 peel (kernel-checked alone): the ten gate-call witness chunks. -/
private theorem peelGatesW (cfg : Config) (input : Inputs (AssignedCell Fp))
    (pcs : PieceCells) (ccs : CheckCells) (iHash : RegionIndex)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (h : ExtendsWitnesses place env
      ((synthGates cfg input pcs ccs iHash).operations i₀) i₀) :
    
    ExtendsWitnesses place env
      ((((DecomposeB.bundle (brWit input.gdX 254 1)).toFormal
        "NoteCommit MessagePiece b").call cfg.gates.b
        { b := pcs.b, b0 := pcs.b0, b2 := ccs.b2, b3 := pcs.b3 }).operations i₀) i₀ ∧
    ExtendsWitnesses place env
      ((((DecomposeD.bundle (brWit input.pkdX 254 1)).toFormal
        "NoteCommit MessagePiece d").call cfg.gates.d
        { d := pcs.d, d1 := ccs.d1, d2 := pcs.d2,
          d3 := zCell cfg.hashConfig iHash 3 1 }).operations (i₀ + 1)) (i₀ + 1) ∧
    ExtendsWitnesses place env
      (((DecomposeE.bundle.toFormal "NoteCommit MessagePiece e").call cfg.gates.e
        { e := pcs.e, e0 := pcs.e0, e1 := pcs.e1 }).operations (i₀ + 2)) (i₀ + 2) ∧
    ExtendsWitnesses place env
      ((((DecomposeG.bundle (brWit input.rho 254 1)).toFormal
        "NoteCommit MessagePiece g").call cfg.gates.g
        { g := pcs.g, g1 := pcs.g1,
          g2 := zCell cfg.hashConfig iHash 6 1 }).operations (i₀ + 3)) (i₀ + 3) ∧
    ExtendsWitnesses place env
      ((((DecomposeH.bundle (brWit input.psi 254 1)).toFormal
        "NoteCommit MessagePiece h").call cfg.gates.h
        { h := pcs.h, h0 := pcs.h0 }).operations (i₀ + 4)) (i₀ + 4) ∧
    ExtendsWitnesses place env
      (((GdCanonicity.bundle.toFormal "NoteCommit input g_d").call cfg.gates.gd
        { gdX := input.gdX, b0 := pcs.b0, b1 := AssignedCell.of i₀ 0 cfg.gates.b.colR,
          a := pcs.a, aPrime := ccs.aZs.z0,
          z13A := zCell cfg.hashConfig iHash 0 13,
          z13APrime := ccs.aZs.zLast }).operations (i₀ + 5)) (i₀ + 5) ∧
    ExtendsWitnesses place env
      (((PkdCanonicity.bundle.toFormal "NoteCommit input pk_d").call cfg.gates.pkd
        { pkdX := input.pkdX, b3 := pcs.b3,
          d0 := AssignedCell.of (i₀ + 1) 0 cfg.gates.d.colM, c := pcs.c,
          b3CPrime := ccs.bZs.z0, z13C := zCell cfg.hashConfig iHash 2 13,
          z14B3CPrime := ccs.bZs.zLast }).operations (i₀ + 6)) (i₀ + 6) ∧
    ExtendsWitnesses place env
      (((ValueCanonicity.bundle.toFormal "NoteCommit input value").call cfg.gates.value
        { value := input.value, d2 := pcs.d2, d3 := zCell cfg.hashConfig iHash 3 1,
          e0 := pcs.e0 }).operations (i₀ + 7)) (i₀ + 7) ∧
    ExtendsWitnesses place env
      (((RhoCanonicity.bundle.toFormal "NoteCommit input rho").call cfg.gates.rho
        { rho := input.rho, e1 := pcs.e1,
          g0 := AssignedCell.of (i₀ + 3) 0 cfg.gates.g.colM, f := pcs.f,
          e1FPrime := ccs.eZs.z0, z13F := zCell cfg.hashConfig iHash 5 13,
          z14E1FPrime := ccs.eZs.zLast }).operations (i₀ + 8)) (i₀ + 8) ∧
    ExtendsWitnesses place env
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

/-- The `lsb` cell witnessed inside a y-canonicity flow's gate region reads the
caller's program (two-level witness projection). -/
private theorem yc_lsb_witness (w : WitgenIR Fp 1)
    (c : YCanonicity.Config × LookupRangeCheck.Config 10)
    (inp : Var YCanonicityCheck.Inputs Fp) (i : RegionIndex)
    (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (h : ExtendsWitnesses place env
      (((YCanonicityCheck.circuit w).call c inp).operations i) i) :
    env.advice (c.1.advices 6) ((place (i + 4) : ℕ) : ℤ)
      = ((w.eval (⟨place, env⟩ : Placed ProverEnvironment Fp))[0]'(by norm_num)) := by
  rw [show ExtendsWitnesses place env
        (((YCanonicityCheck.circuit w).call c inp).operations i) i
      = ExtendsWitnesses place env
        (((YCanonicityCheck.circuit w).synthesize c inp).operations i) i from by
    simp only [FormalCircuit.call, FormalCircuit.callOps_eq, Circuit.operations]] at h
  simp only [YCanonicityCheck.circuit] at h
  simp only [YCanonicityCheck.synth, LookupRangeCheck.witnessShortCheck,
    LookupRangeCheck.witnessCheckDecomposed, LookupRangeCheck.witnessCheck,
    Circuit.operations_bind, operations_assignRegion, RegionCircuit.operations_bind,
    circuit_norm] at h
  have hg := h.2.2.2.2
  rw [YCanonicityCheck.gateChild_call_witnesses] at hg
  simp only [YCanonicity.bundle, YCanonicity.gate, circuit_norm] at hg
  have hlsb := hg.2.1
  simp only [Nat.add_assoc, Nat.reduceAdd] at hlsb ⊢
  exact hlsb

/-- The Ironwood `Chain.PieceBounds`/`honestChunks` are the donor's, verbatim. -/
private theorem pieceBounds_donor_iff :
    ∀ (ms : List ℕ) (pieces : Vector Fp ms.length),
      Sinsemilla.Chain.PieceBounds ms pieces ↔
      Halo2.Ironwood.Sinsemilla.Chain.PieceBounds ms pieces := by
  intro ms
  induction ms with
  | nil =>
    intro pieces
    simp only [Sinsemilla.Chain.PieceBounds, Halo2.Ironwood.Sinsemilla.Chain.PieceBounds]
  | cons n rest ih =>
    intro pieces
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (ih _).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (ih _).mpr h2⟩

private theorem honestChunks_donor_eq :
    ∀ (ms : List ℕ) (pieces : Vector Fp ms.length),
      Sinsemilla.Chain.honestChunks ms pieces
        = Halo2.Ironwood.Sinsemilla.Chain.honestChunks ms pieces := by
  intro ms pieces
  rfl

private theorem toFormal_proverAssumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).ProverAssumptions = b.ProverAssumptions := rfl

private theorem decomposeB_pa_eq (w : WitgenIR Fp 1) :
    (DecomposeB.bundle w).ProverAssumptions
      = fun input (wit : Fp) _ => IsBool wit ∧ IsBool input.b2 ∧
          input.b = input.b0 + wit * 16 + input.b2 * 32 + input.b3 * 64 := rfl

private theorem decomposeD_pa_eq (w : WitgenIR Fp 1) :
    (DecomposeD.bundle w).ProverAssumptions
      = fun input (wit : Fp) _ => IsBool wit ∧ IsBool input.d1 ∧
          input.d = wit + input.d1 * 2 + input.d2 * 4 + input.d3 * 1024 := rfl

private theorem decomposeE_pa_eq :
    DecomposeE.bundle.ProverAssumptions
      = fun input _ _ => input.e = input.e0 + input.e1 * 64 := rfl

private theorem decomposeG_pa_eq (w : WitgenIR Fp 1) :
    (DecomposeG.bundle w).ProverAssumptions
      = fun input (wit : Fp) _ => IsBool wit ∧
          input.g = wit + input.g1 * 2 + input.g2 * 1024 := rfl

private theorem decomposeH_pa_eq (w : WitgenIR Fp 1) :
    (DecomposeH.bundle w).ProverAssumptions
      = fun input (wit : Fp) _ => IsBool wit ∧ input.h = input.h0 + wit * 32 := rfl

private theorem decomposeB_extract_eq (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeB.Config) (inp : Var DecomposeB.Inputs Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    ((DecomposeB.bundle w).toFormal name).extract cfg inp i env
      = (eval env (AssignedCell.of i 0 cfg.colR : Var field Fp) : Fp) := rfl

private theorem decomposeD_extract_eq (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeD.Config) (inp : Var DecomposeD.Inputs Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    ((DecomposeD.bundle w).toFormal name).extract cfg inp i env
      = (eval env (AssignedCell.of i 0 cfg.colM : Var field Fp) : Fp) := rfl

private theorem decomposeG_extract_eq (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeG.Config) (inp : Var DecomposeG.Inputs Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    ((DecomposeG.bundle w).toFormal name).extract cfg inp i env
      = (eval env (AssignedCell.of i 0 cfg.colM : Var field Fp) : Fp) := rfl

private theorem decomposeH_extract_eq (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeH.Config) (inp : Var DecomposeH.Inputs Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    ((DecomposeH.bundle w).toFormal name).extract cfg inp i env
      = (eval env (AssignedCell.of i 0 cfg.colR : Var field Fp) : Fp) := rfl

private theorem z1d_div (a b c d : ℕ) (h1 : a < 2) (h2 : b < 2) (h3 : c < 2 ^ 8)
    (_h4 : d < 2 ^ 50) : (a + b * 2 + c * 4 + d * 1024) / 2 ^ 10 = d := by
  omega

private theorem z1g_div (a b c : ℕ) (h1 : a < 2) (h2 : b < 2 ^ 9) (_h3 : c < 2 ^ 240) :
    (a + b * 2 + c * 1024) / 2 ^ 10 = c := by
  omega

private theorem gd_pa_eq :
    GdCanonicity.bundle.ProverAssumptions = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.GdCanonicity.Gate.Spec (GdCanonicity.toDonor input) ∧
      input.aPrime = input.a + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP := rfl

private theorem pkd_pa_eq :
    PkdCanonicity.bundle.ProverAssumptions = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.PkdCanonicity.Gate.Spec (PkdCanonicity.toDonor input) ∧
      input.b3CPrime = input.b3 + input.c * ((2 ^ 4 : ℕ) : Fp)
        + ((2 ^ 140 : ℕ) : Fp) - Halo2.Ironwood.tP := rfl

private theorem value_pa_eq :
    ValueCanonicity.bundle.ProverAssumptions = fun input _ _ =>
      input.value = input.d2 + input.d3 * (2 ^ 8 : Fp) + input.e0 * (2 ^ 58 : Fp) := rfl

private theorem rho_pa_eq :
    RhoCanonicity.bundle.ProverAssumptions = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.RhoCanonicity.Gate.Spec (RhoCanonicity.toDonor input) ∧
      input.e1FPrime = input.e1 + input.f * ((2 ^ 4 : ℕ) : Fp)
        + ((2 ^ 140 : ℕ) : Fp) - Halo2.Ironwood.tP := rfl

private theorem psi_pa_eq :
    PsiCanonicity.bundle.ProverAssumptions = fun input _ _ =>
      Halo2.Ironwood.NoteCommit.PsiCanonicity.Gate.Spec (PsiCanonicity.toDonor input) ∧
      input.g1G2Prime = input.g1 + input.g2 * ((2 ^ 9 : ℕ) : Fp)
        + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP := rfl

private theorem bit_cast_isBool (m : ℕ) (h : m < 2) : IsBool ((m : ℕ) : Fp) := by
  interval_cases m
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)

/-- Prover-eval of the commit input record over opaque cells (doc pattern 1: the
transport lemma is checked once over abstract variables). -/
private theorem pieces_eval_eq (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
      ({ pieces := #v[c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] }
        : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)).pieces
    = #v[readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₀,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₁,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₂,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₃,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₄,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₅,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₆,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₇] := by
  with_unfolding_all rfl

/-- Environment-side sibling of `pieces_eval_eq`. -/
private theorem pieces_eval_eq_env (place : RegionIndex → ℕ) (env : Environment Fp)
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ pieces := #v[c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] }
        : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)).pieces
    = #v[env.get c₀.cell.column ((place c₀.cell.regionIndex + c₀.cell.rowOffset : ℕ) : ℤ),
        env.get c₁.cell.column ((place c₁.cell.regionIndex + c₁.cell.rowOffset : ℕ) : ℤ),
        env.get c₂.cell.column ((place c₂.cell.regionIndex + c₂.cell.rowOffset : ℕ) : ℤ),
        env.get c₃.cell.column ((place c₃.cell.regionIndex + c₃.cell.rowOffset : ℕ) : ℤ),
        env.get c₄.cell.column ((place c₄.cell.regionIndex + c₄.cell.rowOffset : ℕ) : ℤ),
        env.get c₅.cell.column ((place c₅.cell.regionIndex + c₅.cell.rowOffset : ℕ) : ℤ),
        env.get c₆.cell.column ((place c₆.cell.regionIndex + c₆.cell.rowOffset : ℕ) : ℤ),
        env.get c₇.cell.column ((place c₇.cell.regionIndex
          + c₇.cell.rowOffset : ℕ) : ℤ)] := by
  with_unfolding_all rfl

/-- The commit child's derived verifier contract on the completeness side, standalone
(the inline `layouter_completeness_derived` application hits a whnf wall in the main
proof's context). -/
private theorem commit_derived_spec (G : Generators) (R : FixedBase)
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (i : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)
    (hw : ExtendsWitnesses place env
      (((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).call
        c inp).operations i) i)
    (hEnvA : (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).EnvAssumptions
      c (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
    (hPB' : Sinsemilla.Chain.PieceBounds ns
      (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp).pieces)
    (hHon' : ∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp).pieces) = some B)
    (hWin' : ∀ w : Fin 85,
      (((Ecc.MulFixed.FullWidth.fwExtract c.1 i
        (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1)[w.val]).val < 8) :
    ∃ chunks : List ℕ,
      Sinsemilla.Chain.PieceChunks ns
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) inp).pieces chunks ∧
      Sinsemilla.Chain.ZsFacts ns chunks
        ((Sinsemilla.HashToPoint.hashCircuit G ns Q hQ ns_ne_nil).extract c.2.1
          { pieces := inp.pieces } (i + 2)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).zs ∧
      ∀ B, hashToPoint G.S Q chunks = some B →
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
          ((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).output
            c inp i) : Value Point Fp).Valid ∧
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
          ((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).output
            c inp i) : Value Point Fp)
          = B + (((Ecc.MulFixed.FullWidth.fwExtract c.1 i
              (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 • R) : Point Fp) := by
  have h := (Halo2.SubcircuitRw.layouter_completeness_derived
    (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil) c i place env inp hw
    hEnvA (by rw [commit_assumptions_eq]; trivial)
    (by rw [commit_proverAssumptions_eq, commit_extract_eq]
        exact ⟨hPB', hHon', hWin'⟩)).1
  rw [commit_spec_eq, commit_extract_eq] at h
  exact h

theorem soundness (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config) :
    FormalCircuit.Soundness (Witness := fun _ => Vector Fp 85 × Fq)
      (synth G R windows Q hQ cfg)
      (rcmExtract cfg) (EnvAssumptions G cfg) Assumptions (Spec G Q R) := by
  circuit_proof_start
  obtain ⟨hTableG, hMulE, hTableL, hDistinct⟩ := _hE
  simp only [synth, circuit_norm] at hc
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
  have hz13a := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨0, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13a] at hz13a
  have hz13c := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨2, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13c] at hz13c
  have hz1d := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨3, by decide⟩ hPC' hZs' (by decide) (r := 1) (by decide)
  rw [zs_get_z1d] at hz1d
  have hz13f := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨5, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13f] at hz13f
  have hz1g := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨6, by decide⟩ hPC' hZs' (by decide) (r := 1) (by decide)
  rw [zs_get_z1g] at hz1g
  have hz13g := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨6, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13g] at hz13g
  -- ── normalize region-index spellings ──
  simp only [Nat.add_assoc, Nat.reduceAdd] at hGbS hGdS hGeS hGgS hGhS hY1S hY2S
  simp only [Nat.add_assoc, Nat.reduceAdd] at haz0 htelA hbz0 htelB hez0 htelE hgz0 htelG
  simp only [Nat.add_assoc, Nat.reduceAdd] at hz13a hz13c hz1d hz13f hz1g hz13g
  simp only [Nat.add_assoc, Nat.reduceAdd] at hb0 hb3 hd2 he0 he1 hg1 hh0
  -- ── the piece-value bounds (from the chunk decompositions) ──
  have hpieceA := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨0, by decide⟩ hPC' (by decide)
  have hpieceC := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨2, by decide⟩ hPC' (by decide)
  have hpieceD := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨3, by decide⟩ hPC' (by decide)
  have hpieceF := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨5, by decide⟩ hPC' (by decide)
  have hpieceG := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
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
                    circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGbS.1, haval, hb0, hza, loA, hloA, by rw [← haz0] at htelA; exact htelA⟩)
  rw [toFormal_spec_eq, gd_spec_eq] at hGgdS
  simp only [GdCanonicity.toDonor, Halo2.Ironwood.NoteCommit.GdCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
    circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGgdS
  have hGpkdS := hGpkd (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, pkd_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell,
          prefixRows_ns_2,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGdS.1, hcval, hb3, hzc, loB, hloB, by rw [← hbz0] at htelB; exact htelB⟩)
  rw [toFormal_spec_eq, pkd_spec_eq] at hGpkdS
  simp only [PkdCanonicity.toDonor, Halo2.Ironwood.NoteCommit.PkdCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell, prefixRows_ns_2,
    circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGpkdS
  have hGvalS := hGval (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, value_assumptions_eq]
        simp only [synthPieces_output, zCell,
          prefixRows_ns_3,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hd2, by rw [hzd]; exact hzdval, he0⟩)
  rw [toFormal_spec_eq, value_spec_eq] at hGvalS
  simp only [ValueCanonicity.toDonor, Halo2.Ironwood.NoteCommit.ValueCanonicity.Gate.Spec,
    synthPieces_output, zCell,
    prefixRows_ns_3, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.reduceAdd, Nat.add_zero] at hGvalS
  have hGrhoS := hGrho (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, rho_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell,
          prefixRows_ns_5,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGgS.1, hfval, he1, hzf, loE, hloE, by rw [← hez0] at htelE; exact htelE⟩)
  rw [toFormal_spec_eq, rho_spec_eq] at hGrhoS
  simp only [RhoCanonicity.toDonor, Halo2.Ironwood.NoteCommit.RhoCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell,
    prefixRows_ns_5, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGrhoS
  simp only [prefixRows_ns_3,
    prefixRows_ns_6, Nat.reduceAdd] at hGbS hGdS hGeS hGgS hGhS
  -- Psi: the z13G tail via the donor bridge over the DecomposeG facts
  have hz13G_tail := Halo2.Ironwood.NoteCommit.z13G_tail_of_decompose_g
    hGgS.1 hg1 (by rw [hzg1]; exact hzg1val) hGgS.2 hzg13
  have hGpsiS := hGpsi (by rw [toFormal_envAssumptions_eq]; trivial)
    (by rw [toFormal_assumptions_eq, psi_assumptions_eq]
        simp only [synthPieces_output, synthChecks_output, zCell,
          prefixRows_ns_6,
          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
          Nat.add_zero]
        exact ⟨hGhS.1, hg1, by rw [hzg1]; exact hzg1val, hh0, hz13G_tail,
          loG, hloG, by rw [← hgz0] at htelG; exact htelG⟩)
  rw [toFormal_spec_eq, psi_spec_eq] at hGpsiS
  simp only [PsiCanonicity.toDonor, Halo2.Ironwood.NoteCommit.PsiCanonicity.Gate.Spec,
    synthPieces_output, synthChecks_output, zCell,
    prefixRows_ns_6, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hGpsiS
  -- ── the chunk-equality assembly ──
  have hLow1 := hY1S hGbS.2.1
  have hLow2 := hY2S hGdS.2.1
  have hz1dEq := Halo2.Ironwood.NoteCommit.cell_eq_of_val hGvalS.2.2.1
  have hz1gEq := Halo2.Ironwood.NoteCommit.cell_eq_of_val hGpsiS.2.1
  have hchunksEq := Halo2.Ironwood.NoteCommit.note_chunks_eq_of_cellFacts
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
  obtain ⟨higdX, higdY, hipkdX, hipkdY, hival, hirho, hipsi⟩ := h_input
  refine ⟨hival ▸ hGvalS.1, ?_⟩
  refine Halo2.Ironwood.Specs.Sinsemilla.breaksOfGuarded (Or.inl hQ)
    (fun m hm => G.S_onCurve (Halo2.Ironwood.Specs.Sinsemilla.chunksOf_mem_lt (by
      simpa [Halo2.Ironwood.NoteCommit.NoteCommitScalars.chunks,
        Halo2.Ironwood.Specs.Sinsemilla.noteCommitChunks] using hm))) ?_
  intro B hB
  rw [higdX, higdY, hipkdX, hipkdY, hival, hirho, hipsi] at hchunksEq
  rw [show (Halo2.Ironwood.NoteCommit.noteScalars ⟨input_gdX, input_gdY⟩
      ⟨input_pkdX, input_pkdY⟩ input_value input_rho input_psi).chunks
    = Halo2.Ironwood.Specs.Sinsemilla.noteCommitChunks input_gdX.val (input_gdY.val % 2)
      input_pkdX.val (input_pkdY.val % 2) input_value.val input_rho.val input_psi.val
    from rfl] at hB
  rw [← hchunksEq] at hB
  obtain ⟨-, hOut⟩ := hContract B hB
  have hOutVar : ({ x := output_x, y := output_y } : Halo2.Ironwood.Point Fp)
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
  circuit_proof_start
  obtain ⟨hTableG, hMulE, hTableL, hDistinct⟩ := _hE
  obtain ⟨hOnGd, hOnPkd, hVal64, hWin, B0, hB0⟩ := hPA
  simp only [synth, circuit_norm] at hwit ⊢
  have hWP := hwit.1
  have hWCk := hwit.2.1
  have hWGt := hwit.2.2
  clear hwit
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm, readCell] at hWP
  obtain ⟨hwa, ⟨hwb0, hWrb0⟩, ⟨hwb3, hWrb3⟩, hwb, hwc, ⟨hwd2, hWrd2⟩, hwd,
    ⟨hwe0, hWre0⟩, ⟨hwe1, hWre1⟩, hwe, hwf, ⟨hwg1, hWrg1⟩, hwg, ⟨hwh0, hWrh0⟩, hwh⟩ := hWP
  simp only [synthChecks, synthPieces, LookupRangeCheck.witnessShortCheck,
    LookupRangeCheck.witnessCheck, Sinsemilla.HashToPoint.witnessMessagePiece,
    circuit_norm, readCell] at hWCk
  simp only [Operations.regionCount] at hWCk
  rw [yc_call_regionCount, yc_call_regionCount, commit_call_regionCount] at hWCk
  obtain ⟨hWy1, hWy2, hWcm, ⟨hWaP, hWra⟩, ⟨hWbP, hWrb⟩, ⟨hWeP, hWre⟩, ⟨hWgP, hWrg⟩⟩ := hWCk
  -- ── prover-side MessageCellFacts at the read cells ──
  obtain ⟨higdX, higdY, hipkdX, hipkdY, hival, hirho, hipsi⟩ := h_input
  have hVal64' : (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ)).val < 2 ^ 64 := by
    rw [hival]; exact hVal64
  -- gate-internal witnesses (the b1/d0/g0/h1 bit cells)
  simp only [synthPieces_nextRegionIndex, synthChecks_nextRegionIndex,
    synthPieces_regionCount, synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd]
    at hWGt
  have hGW := peelGatesW cfg _ _ _ _ _ place env hWGt
  clear hWGt
  have hWgb := hGW.1
  have hWgd := hGW.2.1
  have hWgg := hGW.2.2.2.1
  have hWgh := hGW.2.2.2.2.1
  rw [FormalRegionCircuit.toFormal_call_extendsWitnesses] at hWgb hWgd hWgg hWgh
  simp only [DecomposeB.bundle, synthPieces_output, synthChecks_output,
        circuit_norm, readCell, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hWgb
  simp only [DecomposeD.bundle, synthPieces_output, synthChecks_output, zCell,
    prefixRows_ns_3,
    circuit_norm, readCell, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hWgd
  simp only [DecomposeG.bundle, synthPieces_output, zCell,
    prefixRows_ns_6,
    circuit_norm, readCell, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hWgg
  simp only [DecomposeH.bundle, synthPieces_output,
        circuit_norm, readCell, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at hWgh
  have hwb2 := yc_lsb_witness (brWit input_var_gdY 0 1) _ _ _ place env hWy1
  have hwd1 := yc_lsb_witness (brWit input_var_pkdY 0 1) _ _ _ place env hWy2
  simp only [circuit_norm, readCell, Nat.add_assoc, Nat.reduceAdd] at hwb2 hwd1
  have hwb1 := hWgb.2.2.1
  have hwd0 := hWgd.2.1
  have hwg0 := hWgg.2.1
  have hwh1 := hWgh.2.2
  have hMCF : Halo2.Ironwood.NoteCommit.MessageCellFacts
      ⟨env.get input_var_gdX.cell.column ((place input_var_gdX.cell.regionIndex + input_var_gdX.cell.rowOffset : ℕ) : ℤ), env.get input_var_gdY.cell.column ((place input_var_gdY.cell.regionIndex + input_var_gdY.cell.rowOffset : ℕ) : ℤ)⟩
      ⟨env.get input_var_pkdX.cell.column ((place input_var_pkdX.cell.regionIndex + input_var_pkdX.cell.rowOffset : ℕ) : ℤ), env.get input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ)⟩
      (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ)) (env.get input_var_rho.cell.column ((place input_var_rho.cell.regionIndex + input_var_rho.cell.rowOffset : ℕ) : ℤ)) (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))
      { a := env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ), b := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ), c := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ), d := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ),
        e := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 9) : ℕ) : ℤ), f := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 10) : ℕ) : ℤ), g := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ), h := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 14) : ℕ) : ℤ),
        b0 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 1) : ℕ) : ℤ),
        b1 := env.advice cfg.gates.b.colR ((place (i₀ + 33) : ℕ) : ℤ),
        b2 := env.advice (cfg.gates.y.advices 6) ((place (i₀ + 19) : ℕ) : ℤ),
        b3 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 2) : ℕ) : ℤ),
        d0 := env.advice cfg.gates.d.colM ((place (i₀ + 34) : ℕ) : ℤ),
        d1 := env.advice (cfg.gates.y.advices 6) ((place (i₀ + 24) : ℕ) : ℤ),
        d2 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 5) : ℕ) : ℤ), e0 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 7) : ℕ) : ℤ), e1 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 8) : ℕ) : ℤ),
        g0 := env.advice cfg.gates.g.colM ((place (i₀ + 36) : ℕ) : ℤ),
        g1 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 11) : ℕ) : ℤ), h0 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 13) : ℕ) : ℤ),
        h1 := env.advice cfg.gates.h.colR ((place (i₀ + 37) : ℕ) : ℤ) } := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwa]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwb0]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwb1]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · refine Halo2.Ironwood.NoteCommit.isLowBit_iff_mod_two.mpr ?_
      rw [hwb2, show Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_gdY.cell.column ((place input_var_gdY.cell.regionIndex + input_var_gdY.cell.rowOffset : ℕ) : ℤ))) 0 1
          = ZMod.val (env.get input_var_gdY.cell.column ((place input_var_gdY.cell.regionIndex + input_var_gdY.cell.rowOffset : ℕ) : ℤ)) % 2 from by
        simp [Halo2.Ironwood.Specs.bitrange]]
    · rw [hwb3]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwc]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwd0]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · refine Halo2.Ironwood.NoteCommit.isLowBit_iff_mod_two.mpr ?_
      rw [hwd1, show Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ))) 0 1
          = ZMod.val (env.get input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ)) % 2 from by
        simp [Halo2.Ironwood.Specs.bitrange]]
    · rw [hwd2]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwe0]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwe1]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwf]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwg0]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwg1]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwh0]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwh1]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
    · rw [hwb, ← hwb0, ← hwb1, ← hwb2, ← hwb3]
      try ring
    · rw [hwd, ← hwd0, ← hwd1, ← hwd2]
      try ring
    · rw [hwe, ← hwe0, ← hwe1]
      try ring
    · rw [hwg, ← hwg0, ← hwg1]
      try ring
    · rw [hwh, ← hwh0, ← hwh1]
      try ring
  have hPB : Sinsemilla.Chain.PieceBounds ns
      #v[env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 9) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 10) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 14) : ℕ) : ℤ)] :=
    (pieceBounds_donor_iff _ _).mpr
      (Halo2.Ironwood.NoteCommit.pieceBounds_of_cellFacts hMCF)
  have hHonest : Sinsemilla.Chain.honestChunks ns
      #v[env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 9) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 10) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 14) : ℕ) : ℤ)]
      = Halo2.Ironwood.Specs.Sinsemilla.noteCommitChunks input_gdX.val (input_gdY.val % 2)
        input_pkdX.val (input_pkdY.val % 2) input_value.val input_rho.val
        input_psi.val := by
    rw [honestChunks_donor_eq]
    have := Halo2.Ironwood.NoteCommit.honestChunks_eq_noteCommitChunks_of_cellFacts
      hMCF hVal64'
    rw [higdX, higdY, hipkdX, hipkdY, hival, hirho, hipsi] at this
    exact this
  -- ── derived child contracts for the gate rely-conditions ──
  have hPB2 : Sinsemilla.Chain.PieceBounds ns
      (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
        ({ pieces :=
          #v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 3) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 4) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 6) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 9) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 10) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 12) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 14) 0 cfg.hashConfig.witnessPieces] }
          : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)).pieces := by
    rw [pieces_eval_eq]
    simp only [readCell, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_zero]
    exact hPB
  have hHon2 : ∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          ({ pieces :=
            #v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 3) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 4) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 6) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 9) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 10) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 12) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 14) 0 cfg.hashConfig.witnessPieces] }
            : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)).pieces)
      = some B := by
    refine ⟨B0, ?_⟩
    rw [pieces_eval_eq]
    simp only [readCell, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_zero]
    rw [hHonest]
    exact hB0
  have hCmS := commit_derived_spec G R windows Q hQ
    (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) (i₀ + 25) place env _ hWcm
    (by rw [commit_envAssumptions_eq]; exact ⟨hTableG, hMulE⟩)
    hPB2 hHon2 hWin
  obtain ⟨chunks, hPC, hZs, hContract⟩ := hCmS
  rw [hashExtract_zs] at hZs
  rw [pieces_eval_eq_env] at hPC
  simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_zero, Nat.add_assoc,
    Nat.reduceAdd] at hPC
  have hPC' := (pieceChunks_donor_iff _ _ _).mp hPC
  have hZs' := (zsFacts_donor_iff _ _ _).mp hZs
  have hz13a := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨0, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13a] at hz13a
  have hz13c := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨2, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13c] at hz13c
  have hz1d := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨3, by decide⟩ hPC' hZs' (by decide) (r := 1) (by decide)
  rw [zs_get_z1d] at hz1d
  have hz13f := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨5, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13f] at hz13f
  have hz1g := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨6, by decide⟩ hPC' hZs' (by decide) (r := 1) (by decide)
  rw [zs_get_z1g] at hz1g
  have hz13g := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨6, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13g] at hz13g
  have hWaSfull := Halo2.SubcircuitRw.region_completeness_derived
    (LookupRangeCheck.rangeCheckAt 10 13 false) cfg.lookupConfig 0 (i₀ + 29)
    place env () hWra
    (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by rw [rangeCheckAt_proverAssumptions_eq]; simp)
  have hWaS := hWaSfull.1
  have hWaSPS := hWaSfull.2
  rw [rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hWaSPS
  simp only [rangeCheckAt_extract_eq, circuit_norm, show (10 * 13 : ℕ) = 130 from by
    norm_num] at hWaSPS
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWaS
  simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hWaS
  obtain ⟨haz0, loA, hloA, htelA⟩ := hWaS
  have hWbSfull := Halo2.SubcircuitRw.region_completeness_derived
    (LookupRangeCheck.rangeCheckAt 10 14 false) cfg.lookupConfig 0 (i₀ + 30)
    place env () hWrb
    (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by rw [rangeCheckAt_proverAssumptions_eq]; simp)
  have hWbS := hWbSfull.1
  have hWbSPS := hWbSfull.2
  rw [rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hWbSPS
  simp only [rangeCheckAt_extract_eq, circuit_norm, show (10 * 14 : ℕ) = 140 from by
    norm_num] at hWbSPS
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWbS
  simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hWbS
  obtain ⟨hbz0, loB, hloB, htelB⟩ := hWbS
  have hWeSfull := Halo2.SubcircuitRw.region_completeness_derived
    (LookupRangeCheck.rangeCheckAt 10 14 false) cfg.lookupConfig 0 (i₀ + 31)
    place env () hWre
    (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by rw [rangeCheckAt_proverAssumptions_eq]; simp)
  have hWeS := hWeSfull.1
  have hWeSPS := hWeSfull.2
  rw [rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hWeSPS
  simp only [rangeCheckAt_extract_eq, circuit_norm, show (10 * 14 : ℕ) = 140 from by
    norm_num] at hWeSPS
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWeS
  simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hWeS
  obtain ⟨hez0, loE, hloE, htelE⟩ := hWeS
  have hWgSfull := Halo2.SubcircuitRw.region_completeness_derived
    (LookupRangeCheck.rangeCheckAt 10 13 false) cfg.lookupConfig 0 (i₀ + 32)
    place env () hWrg
    (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [rangeCheckAt_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by rw [rangeCheckAt_proverAssumptions_eq]; simp)
  have hWgS := hWgSfull.1
  have hWgSPS := hWgSfull.2
  rw [rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hWgSPS
  simp only [rangeCheckAt_extract_eq, circuit_norm, show (10 * 13 : ℕ) = 130 from by
    norm_num] at hWgSPS
  rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hWgS
  simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hWgS
  obtain ⟨hgz0, loG, hloG, htelG⟩ := hWgS
  simp only [Nat.add_assoc, Nat.reduceAdd] at hz13a hz13c hz1d hz13f hz1g hz13g
  have hpieceA := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨0, by decide⟩ hPC' (by decide)
  have hpieceC := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨2, by decide⟩ hPC' (by decide)
  have hpieceD := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨3, by decide⟩ hPC' (by decide)
  have hpieceF := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨5, by decide⟩ hPC' (by decide)
  have hpieceG := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨6, by decide⟩ hPC' (by decide)
  have haval : (env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ)).val
      < 2 ^ 250 := by with_unfolding_all exact hpieceA
  have hcval : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ)).val
      < 2 ^ 250 := by with_unfolding_all exact hpieceC
  have hdval : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ)).val
      < 2 ^ 60 := by with_unfolding_all exact hpieceD
  have hfval : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 10) : ℕ) : ℤ)).val
      < 2 ^ 250 := by with_unfolding_all exact hpieceF
  have hgvalP : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ)).val
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
  -- honest z1 cells are the canonical middle slices
  have hdnat : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ)).val
      = Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_pkdX.cell.column ((place input_var_pkdX.cell.regionIndex + input_var_pkdX.cell.rowOffset : ℕ) : ℤ))) 254 1
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ))) 0 1 * 2
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 0 8 * 4
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 8 50 * 1024 := by
    rw [hwd, show ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_pkdX.cell.column ((place input_var_pkdX.cell.regionIndex + input_var_pkdX.cell.rowOffset : ℕ) : ℤ))) 254 1 : ℕ) : Fp)
        + ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ))) 0 1 : ℕ) : Fp) * 2
        + ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 0 8 : ℕ) : Fp) * (2 ^ 2 : Fp)
        + ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 8 50 : ℕ) : Fp) * (2 ^ 10 : Fp)
      = ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_pkdX.cell.column ((place input_var_pkdX.cell.regionIndex + input_var_pkdX.cell.rowOffset : ℕ) : ℤ))) 254 1
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ))) 0 1 * 2
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 0 8 * 4
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 8 50 * 1024 : ℕ) : Fp) from by
      push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by
      have h1 := Halo2.Ironwood.Specs.bitrange_lt (ZMod.val (env.get input_var_pkdX.cell.column ((place input_var_pkdX.cell.regionIndex + input_var_pkdX.cell.rowOffset : ℕ) : ℤ))) 254 1
      have h2 := Halo2.Ironwood.Specs.bitrange_lt (ZMod.val (env.get input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex + input_var_pkdY.cell.rowOffset : ℕ) : ℤ))) 0 1
      have h3 := Halo2.Ironwood.Specs.bitrange_lt (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 0 8
      have h4 := Halo2.Ironwood.Specs.bitrange_lt (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 8 50
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at h1 h2 h3 h4 ⊢
      omega)]
  have hzdEq : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 52 : ℕ) : ℤ)
      = ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column ((place input_var_value.cell.regionIndex + input_var_value.cell.rowOffset : ℕ) : ℤ))) 8 50 : ℕ) : Fp) := by
    rw [hzd, hdnat, z1d_div _ _ _ _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
      (Halo2.Ironwood.Specs.bitrange_lt _ _ _) (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
      (Halo2.Ironwood.Specs.bitrange_lt _ _ _)]
  have hgnat : (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ)).val
      = Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_rho.cell.column ((place input_var_rho.cell.regionIndex + input_var_rho.cell.rowOffset : ℕ) : ℤ))) 254 1
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 0 9 * 2
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 9 240 * 1024 := by
    rw [hwg, show ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_rho.cell.column ((place input_var_rho.cell.regionIndex + input_var_rho.cell.rowOffset : ℕ) : ℤ))) 254 1 : ℕ) : Fp)
        + ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 0 9 : ℕ) : Fp) * 2
        + ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 9 240 : ℕ) : Fp) * (2 ^ 10 : Fp)
      = ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_rho.cell.column ((place input_var_rho.cell.regionIndex + input_var_rho.cell.rowOffset : ℕ) : ℤ))) 254 1
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 0 9 * 2
        + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 9 240 * 1024 : ℕ) : Fp) from by
      push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by
      have h1 := Halo2.Ironwood.Specs.bitrange_lt (ZMod.val (env.get input_var_rho.cell.column ((place input_var_rho.cell.regionIndex + input_var_rho.cell.rowOffset : ℕ) : ℤ))) 254 1
      have h2 := Halo2.Ironwood.Specs.bitrange_lt (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 0 9
      have h3 := Halo2.Ironwood.Specs.bitrange_lt (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 9 240
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at h1 h2 h3 ⊢
      omega)]
  have hzgEq : env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 84 : ℕ) : ℤ)
      = ((Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column ((place input_var_psi.cell.regionIndex + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 9 240 : ℕ) : Fp) := by
    rw [hzg1, hgnat, z1g_div _ _ _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
      (Halo2.Ironwood.Specs.bitrange_lt _ _ _) (Halo2.Ironwood.Specs.bitrange_lt _ _ _)]
  have hMa := hMCF.1
  have hMb0 := hMCF.2.1
  have hMb1 := hMCF.2.2.1
  have hMb3 := hMCF.2.2.2.2.1
  have hMc := hMCF.2.2.2.2.2.1
  have hMd0 := hMCF.2.2.2.2.2.2.1
  have hMd2 := hMCF.2.2.2.2.2.2.2.2.1
  have hMe0 := hMCF.2.2.2.2.2.2.2.2.2.1
  have hMe1 := hMCF.2.2.2.2.2.2.2.2.2.2.1
  have hMf := hMCF.2.2.2.2.2.2.2.2.2.2.2.1
  have hMg0 := hMCF.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMg1 := hMCF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMh0 := hMCF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMh1 := hMCF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMgEq := hMCF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- short-check value bounds (read language)
  have hb0lt : (env.advice cfg.lookupConfig.runningSum ((place (i₀ + 1) : ℕ) : ℤ)).val
      < 2 ^ 4 := by
    rw [hwb0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have hb3lt : (env.advice cfg.lookupConfig.runningSum ((place (i₀ + 2) : ℕ) : ℤ)).val
      < 2 ^ 4 := by
    rw [hwb3, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have hd2lt : (env.advice cfg.lookupConfig.runningSum ((place (i₀ + 5) : ℕ) : ℤ)).val
      < 2 ^ 8 := by
    rw [hwd2, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have he0lt : (env.advice cfg.lookupConfig.runningSum ((place (i₀ + 7) : ℕ) : ℤ)).val
      < 2 ^ 6 := by
    rw [hwe0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have he1lt : (env.advice cfg.lookupConfig.runningSum ((place (i₀ + 8) : ℕ) : ℤ)).val
      < 2 ^ 4 := by
    rw [hwe1, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have hg1lt : (env.advice cfg.lookupConfig.runningSum ((place (i₀ + 11) : ℕ) : ℤ)).val
      < 2 ^ 9 := by
    rw [hwg1, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have hh0lt : (env.advice cfg.lookupConfig.runningSum ((place (i₀ + 13) : ℕ) : ℤ)).val
      < 2 ^ 5 := by
    rw [hwh0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have hz1glt : (env.advice cfg.hashConfig.bits
      ((place (i₀ + 27) + 84 : ℕ) : ℤ)).val < 2 ^ 240 := by
    rw [hzgEq, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  have hz1dlt : (env.advice cfg.hashConfig.bits
      ((place (i₀ + 27) + 52 : ℕ) : ℤ)).val < 2 ^ 50 := by
    rw [hzdEq, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
    exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
  -- the z13G tail at the honest values
  have hz13Gt := Halo2.Ironwood.NoteCommit.z13G_tail_of_decompose_g
    (g := env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 12) : ℕ) : ℤ))
    (g0 := env.advice cfg.gates.g.colM ((place (i₀ + 36) : ℕ) : ℤ))
    (g1 := env.advice cfg.lookupConfig.runningSum ((place (i₀ + 11) : ℕ) : ℤ))
    (g2 := env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 84 : ℕ) : ℤ))
    (z13G := env.advice cfg.hashConfig.bits ((place (i₀ + 27) + 96 : ℕ) : ℤ))
    (by rw [hwg0]; exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _))
    hg1lt hz1glt
    (by have h := hMgEq; simp only [] at h; rw [h, hzgEq])
    hzg13
  simp only [zCell,
    prefixRows_ns_6, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_assoc,
    Nat.reduceAdd, Nat.add_zero] at hWaP hWbP hWeP hWgP
  simp only [synthPieces_nextRegionIndex, synthChecks_nextRegionIndex,
    synthPieces_regionCount, synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd]
  refine ⟨buildPieces cfg _ i₀ place _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    buildChecks G R windows Q hQ cfg _ _ _ (i₀ + 15) place _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    buildGates cfg _ _ _ _ (i₀ + 33) place _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 4) cfg.lookupConfig 0 (i₀ + 1) place env ()
      hWrb0
      ⟨(by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [short_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [short_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 4).extract
             cfg.lookupConfig 0 ()
             (i₀ + 1) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 4
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 1) : ℕ) : ℤ)).val < 2 ^ 4
           rw [hwb0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 4) cfg.lookupConfig 0 (i₀ + 2) place env ()
      hWrb3
      ⟨(by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [short_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [short_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 4).extract
             cfg.lookupConfig 0 ()
             (i₀ + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 4
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 2) : ℕ) : ℤ)).val < 2 ^ 4
           rw [hwb3, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 8) cfg.lookupConfig 0 (i₀ + 5) place env ()
      hWrd2
      ⟨(by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [short_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [short_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 8).extract
             cfg.lookupConfig 0 ()
             (i₀ + 5) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 8
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 5) : ℕ) : ℤ)).val < 2 ^ 8
           rw [hwd2, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 6) cfg.lookupConfig 0 (i₀ + 7) place env ()
      hWre0
      ⟨(by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [short_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [short_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 6).extract
             cfg.lookupConfig 0 ()
             (i₀ + 7) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 6
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 7) : ℕ) : ℤ)).val < 2 ^ 6
           rw [hwe0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 4) cfg.lookupConfig 0 (i₀ + 8) place env ()
      hWre1
      ⟨(by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [short_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [short_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 4).extract
             cfg.lookupConfig 0 ()
             (i₀ + 8) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 4
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 8) : ℕ) : ℤ)).val < 2 ^ 4
           rw [hwe1, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 9) cfg.lookupConfig 0 (i₀ + 11) place env ()
      hWrg1
      ⟨(by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [short_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [short_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 9).extract
             cfg.lookupConfig 0 ()
             (i₀ + 11) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 9
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 11) : ℕ) : ℤ)).val < 2 ^ 9
           rw [hwg1, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 5) cfg.lookupConfig 0 (i₀ + 13) place env ()
      hWrh0
      ⟨(by rw [short_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [short_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [short_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 5).extract
             cfg.lookupConfig 0 ()
             (i₀ + 13) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 5
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 13) : ℕ) : ℤ)).val < 2 ^ 5
           rw [hwh0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (YCanonicityCheck.circuit (brWit input_var_gdY 0 1))
      (cfg.gates.y, cfg.lookupConfig) (i₀ + 15) place env _ hWy1
      ⟨(by rw [yc_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [yc_assumptions_eq]; trivial),
       (by rw [yc_proverAssumptions_eq, yc_extract]
           refine Halo2.Ironwood.NoteCommit.isLowBit_iff_mod_two.mpr ?_
           simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
             Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
             Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
           rw [hwb2, show Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get
               input_var_gdY.cell.column ((place input_var_gdY.cell.regionIndex
               + input_var_gdY.cell.rowOffset : ℕ) : ℤ))) 0 1
             = ZMod.val (env.get input_var_gdY.cell.column
               ((place input_var_gdY.cell.regionIndex
               + input_var_gdY.cell.rowOffset : ℕ) : ℤ)) % 2 from by
             simp [Halo2.Ironwood.Specs.bitrange]])⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (YCanonicityCheck.circuit (brWit input_var_pkdY 0 1))
      (cfg.gates.y, cfg.lookupConfig) (i₀ + 20) place env _ hWy2
      ⟨(by rw [yc_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [yc_assumptions_eq]; trivial),
       (by rw [yc_proverAssumptions_eq, yc_extract]
           refine Halo2.Ironwood.NoteCommit.isLowBit_iff_mod_two.mpr ?_
           simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
             Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
             Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
           rw [hwd1, show Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get
               input_var_pkdY.cell.column ((place input_var_pkdY.cell.regionIndex
               + input_var_pkdY.cell.rowOffset : ℕ) : ℤ))) 0 1
             = ZMod.val (env.get input_var_pkdY.cell.column
               ((place input_var_pkdY.cell.regionIndex
               + input_var_pkdY.cell.rowOffset : ℕ) : ℤ)) % 2 from by
             simp [Halo2.Ironwood.Specs.bitrange]])⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil)
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) (i₀ + 25) place env _ hWcm
      ⟨(by rw [commit_envAssumptions_eq]; exact ⟨hTableG, hMulE⟩),
       (by rw [commit_assumptions_eq]; trivial),
       (by rw [commit_proverAssumptions_eq]
           refine ⟨?_, ?_, ?_⟩
           · show Sinsemilla.Chain.PieceBounds ns _
             with_unfolding_all exact hPB
           · refine ⟨B0, ?_⟩
             rw [show (Sinsemilla.Chain.honestChunks ns _ : List ℕ)
                 = Halo2.Ironwood.Specs.Sinsemilla.noteCommitChunks input_gdX.val
                   (input_gdY.val % 2) input_pkdX.val (input_pkdY.val % 2)
                   input_value.val input_rho.val input_psi.val from by
               with_unfolding_all exact hHonest]
             exact hB0
           · exact hWin)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.rangeCheckAt 10 13 false) cfg.lookupConfig 0 (i₀ + 29)
      place env () hWra
      ⟨(by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [rangeCheckAt_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [rangeCheckAt_proverAssumptions_eq]; simp)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.rangeCheckAt 10 14 false) cfg.lookupConfig 0 (i₀ + 30)
      place env () hWrb
      ⟨(by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [rangeCheckAt_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [rangeCheckAt_proverAssumptions_eq]; simp)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.rangeCheckAt 10 14 false) cfg.lookupConfig 0 (i₀ + 31)
      place env () hWre
      ⟨(by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [rangeCheckAt_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [rangeCheckAt_proverAssumptions_eq]; simp)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.rangeCheckAt 10 13 false) cfg.lookupConfig 0 (i₀ + 32)
      place env () hWrg
      ⟨(by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [rangeCheckAt_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [rangeCheckAt_proverAssumptions_eq]; simp)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      ((DecomposeB.bundle (brWit input_var_gdX 254 1)).toFormal
        "NoteCommit MessagePiece b") cfg.gates.b (i₀ + 33) place env _ hGW.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq]; trivial),
       (by rw [toFormal_proverAssumptions_eq, decomposeB_pa_eq, decomposeB_extract_eq]
           simp only [synthPieces_output, synthChecks_output,
                          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           refine ⟨?_, ?_, ?_⟩
           · rw [hwb1]
             exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
           · rw [hwb2]
             exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
           · rw [hwb, ← hwb0, ← hwb1, ← hwb2, ← hwb3]
             try ring)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      ((DecomposeD.bundle (brWit input_var_pkdX 254 1)).toFormal
        "NoteCommit MessagePiece d") cfg.gates.d (i₀ + 34) place env _ hGW.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq]; trivial),
       (by rw [toFormal_proverAssumptions_eq, decomposeD_pa_eq, decomposeD_extract_eq]
           simp only [synthPieces_output, synthChecks_output, zCell,
             prefixRows_ns_3,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           refine ⟨?_, ?_, ?_⟩
           · rw [hwd0]
             exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
           · rw [hwd1]
             exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
           · rw [hzdEq, hwd, ← hwd0, ← hwd1, ← hwd2]
             try ring)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (DecomposeE.bundle.toFormal "NoteCommit MessagePiece e") cfg.gates.e
      (i₀ + 35) place env _ hGW.2.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq]; trivial),
       (by rw [toFormal_proverAssumptions_eq, decomposeE_pa_eq]
           simp only [synthPieces_output,
                          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice,
             Nat.add_zero]
           rw [hwe, ← hwe0, ← hwe1]
           try ring)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      ((DecomposeG.bundle (brWit input_var_rho 254 1)).toFormal
        "NoteCommit MessagePiece g") cfg.gates.g (i₀ + 36) place env _ hGW.2.2.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq]; trivial),
       (by rw [toFormal_proverAssumptions_eq, decomposeG_pa_eq, decomposeG_extract_eq]
           simp only [synthPieces_output, zCell,
             prefixRows_ns_6,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.reduceAdd,
             Nat.add_zero]
           refine ⟨?_, ?_⟩
           · rw [hwg0]
             exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
           · rw [hzgEq, hwg, ← hwg0, ← hwg1]
             try ring)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      ((DecomposeH.bundle (brWit input_var_psi 254 1)).toFormal
        "NoteCommit MessagePiece h") cfg.gates.h (i₀ + 37) place env _ hGW.2.2.2.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq]; trivial),
       (by rw [toFormal_proverAssumptions_eq, decomposeH_pa_eq, decomposeH_extract_eq]
           simp only [synthPieces_output,
                          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice,
             Nat.add_zero]
           refine ⟨?_, ?_⟩
           · rw [hwh1]
             exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _)
           · rw [hwh, ← hwh0, ← hwh1]
             try ring)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (GdCanonicity.bundle.toFormal "NoteCommit input g_d") cfg.gates.gd
      (i₀ + 38) place env _ hGW.2.2.2.2.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq, gd_assumptions_eq]
           simp only [synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
                          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           exact ⟨by rw [hwb1]; exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _),
             haval, hb0lt, hza, loA, hloA, by rw [← haz0] at htelA; exact htelA⟩),
       (by rw [toFormal_proverAssumptions_eq, gd_pa_eq]
           simp only [synthPieces_output, synthChecks_output, zCell, prefixRows_ns_0,
                          circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           simp only [GdCanonicity.toDonor,
             Halo2.Ironwood.NoteCommit.GdCanonicity.Gate.Spec]
           refine ⟨⟨hMa, hMb0, hMb1, fun h1 => ?_⟩, hWaP⟩
           obtain ⟨-, hatp, -⟩ := Halo2.Ironwood.NoteCommit.high_bit_canonical
             (ZMod.val_lt _) (Halo2.Ironwood.NoteCommit.bit_one_of_val_eq hMb1 h1)
           have hloGd : (env.advice cfg.hashConfig.witnessPieces
               ((place i₀ : ℕ) : ℤ)).val < Halo2.Ironwood.NoteCommit.tPNat := by
             rw [hMa]; exact hatp
           rw [hWaSPS, hWaP,
             Halo2.Ironwood.NoteCommit.shifted_high_zero (by norm_num) (by norm_num)
               hloGd]
           simp)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (PkdCanonicity.bundle.toFormal "NoteCommit input pk_d") cfg.gates.pkd
      (i₀ + 39) place env _ hGW.2.2.2.2.2.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq, pkd_assumptions_eq]
           simp only [synthPieces_output, synthChecks_output, zCell,
             prefixRows_ns_2,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           exact ⟨by rw [hwd0]; exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _),
             hcval, hb3lt, hzc, loB, hloB, by rw [← hbz0] at htelB; exact htelB⟩),
       (by rw [toFormal_proverAssumptions_eq, pkd_pa_eq]
           simp only [synthPieces_output, synthChecks_output, zCell,
             prefixRows_ns_2,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           simp only [PkdCanonicity.toDonor,
             Halo2.Ironwood.NoteCommit.PkdCanonicity.Gate.Spec]
           refine ⟨⟨hMb3, hMc, hMd0, fun h1 => ?_⟩, by rw [hWbP]; try ring⟩
           have hbase := Halo2.Ironwood.NoteCommit.base_val_lt_tP_val hMb3 hMc
             (ZMod.val_lt _) (Halo2.Ironwood.NoteCommit.bit_one_of_val_eq hMd0 h1)
             (by norm_num)
           rw [hWbSPS, hWbP,
             Halo2.Ironwood.NoteCommit.shifted_high_zero (by norm_num) (by norm_num)
               hbase]
           simp)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (ValueCanonicity.bundle.toFormal "NoteCommit input value") cfg.gates.value
      (i₀ + 40) place env _ hGW.2.2.2.2.2.2.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq, value_assumptions_eq]
           simp only [synthPieces_output, zCell,
             prefixRows_ns_3,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.reduceAdd,
             Nat.add_zero]
           exact ⟨hd2lt, hz1dlt, he0lt⟩),
       (by rw [toFormal_proverAssumptions_eq, value_pa_eq]
           simp only [synthPieces_output, zCell,
             prefixRows_ns_3,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.reduceAdd,
             Nat.add_zero]
           rw [hwd2, hwe0, hzdEq]
           have hvnat : (env.get input_var_value.cell.column
               ((place input_var_value.cell.regionIndex
                 + input_var_value.cell.rowOffset : ℕ) : ℤ)).val
               = Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column
                   ((place input_var_value.cell.regionIndex
                     + input_var_value.cell.rowOffset : ℕ) : ℤ))) 0 8
                 + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column
                   ((place input_var_value.cell.regionIndex
                     + input_var_value.cell.rowOffset : ℕ) : ℤ))) 8 50 * 2 ^ 8
                 + Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_value.cell.column
                   ((place input_var_value.cell.regionIndex
                     + input_var_value.cell.rowOffset : ℕ) : ℤ))) 58 6 * 2 ^ 58 := by
             have h64 := hVal64'
             simp only [Halo2.Ironwood.Specs.bitrange]
             omega
           conv_lhs => rw [← ZMod.natCast_zmod_val (env.get input_var_value.cell.column
             ((place input_var_value.cell.regionIndex
               + input_var_value.cell.rowOffset : ℕ) : ℤ)), hvnat]
           push_cast
           ring)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (RhoCanonicity.bundle.toFormal "NoteCommit input rho") cfg.gates.rho
      (i₀ + 41) place env _ hGW.2.2.2.2.2.2.2.2.1
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq, rho_assumptions_eq]
           simp only [synthPieces_output, synthChecks_output, zCell,
             prefixRows_ns_5,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           exact ⟨by rw [hwg0]; exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _),
             hfval, he1lt, hzf, loE, hloE, by rw [← hez0] at htelE; exact htelE⟩),
       (by rw [toFormal_proverAssumptions_eq, rho_pa_eq]
           simp only [synthPieces_output, synthChecks_output, zCell,
             prefixRows_ns_5,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           simp only [RhoCanonicity.toDonor,
             Halo2.Ironwood.NoteCommit.RhoCanonicity.Gate.Spec]
           refine ⟨⟨hMe1, hMf, hMg0, fun h1 => ?_⟩, by rw [hWeP]; try ring⟩
           have hbase := Halo2.Ironwood.NoteCommit.base_val_lt_tP_val hMe1 hMf
             (ZMod.val_lt _) (Halo2.Ironwood.NoteCommit.bit_one_of_val_eq hMg0 h1)
             (by norm_num)
           rw [hWeSPS, hWeP,
             Halo2.Ironwood.NoteCommit.shifted_high_zero (by norm_num) (by norm_num)
               hbase]
           simp)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (PsiCanonicity.bundle.toFormal "NoteCommit input psi") cfg.gates.psi
      (i₀ + 42) place env _ hGW.2.2.2.2.2.2.2.2.2
      ⟨(by rw [toFormal_envAssumptions_eq]; trivial),
       (by rw [toFormal_assumptions_eq, psi_assumptions_eq]
           simp only [synthPieces_output, synthChecks_output, zCell,
             prefixRows_ns_6,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           exact ⟨by rw [hwh1]; exact bit_cast_isBool _ (Halo2.Ironwood.Specs.bitrange_lt _ _ _),
             hg1lt, hz1glt, hh0lt, hz13Gt, loG, hloG,
             by rw [← hgz0] at htelG; exact htelG⟩),
       (by rw [toFormal_proverAssumptions_eq, psi_pa_eq]
           simp only [synthPieces_output, synthChecks_output, zCell,
             prefixRows_ns_6,
             circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           simp only [PsiCanonicity.toDonor,
             Halo2.Ironwood.NoteCommit.PsiCanonicity.Gate.Spec]
           have hg2val : (env.advice cfg.hashConfig.bits
               ((place (i₀ + 27) + 84 : ℕ) : ℤ)).val
               = Halo2.Ironwood.Specs.bitrange (ZMod.val (env.get input_var_psi.cell.column
                   ((place input_var_psi.cell.regionIndex
                     + input_var_psi.cell.rowOffset : ℕ) : ℤ))) 9 240 := by
             rw [hzgEq, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           refine ⟨⟨hMg1, hg2val, hMh0, hMh1, fun h1 => ?_⟩, by rw [hWgP]; try ring⟩
           have hbase := Halo2.Ironwood.NoteCommit.base_val_lt_tP_val hMg1 hg2val
             (ZMod.val_lt _) (Halo2.Ironwood.NoteCommit.bit_one_of_val_eq hMh1 h1)
             (by norm_num)
           rw [hWgSPS, hWgP,
             Halo2.Ironwood.NoteCommit.shifted_high_zero (by norm_num) (by norm_num)
               hbase]
           simp)⟩

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
