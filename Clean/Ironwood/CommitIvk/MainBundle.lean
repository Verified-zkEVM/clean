import Clean.Ironwood.CommitIvk.Main

/-!
# CommitIvk bundle proofs (soundness / completeness / the `circuit` def)

Kept separate from `Main.lean` (the defs/contract layer): this file is the
kernel-heavy part — the fully proven soundness/completeness theorems and the
bundled `circuit`. Mirrors `Clean/Ironwood/NoteCommit/MainBundle.lean` at a third
of the scale (10 children, one canonicity composite called as a unit).
-/

namespace Halo2.Ironwood.CommitIvk.Main

open Halo2.Ironwood (Fp)
open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)
open Halo2.Ironwood.Specs (bitrange)
open Halo2.Ironwood.Specs.Sinsemilla (Generators hashToPoint hashToPointB SpecOrBreak
  commitIvkChunks breaksOfGuarded chunksOf_mem_lt)
open CompElliptic.Fields.Pasta (Fq)
open Halo2.Ironwood.NoteCommit.Main (brWit currentRegion)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-! ## Child contract bridges — the contract projections come from the generated home
stacks (`LookupRangeCheck.shortRangeCheck_*`, `Sinsemilla.CommitDomain.commit_*`,
`Canonicity.circuit_*`); only the region-level output-cell bridge stays hand-written. -/

private theorem short_output (b : ℕ) (cfg : LookupRangeCheck.Config 10)
    (i : RegionIndex) :
    (LookupRangeCheck.shortRangeCheck 10 b).output cfg 0 () i
      = AssignedCell.of i 0 cfg.runningSum := rfl

/-! ## Value-level infrastructure -/

/-- The Ironwood `Chain.PieceChunks` is the donor's, verbatim. -/
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

/-- The two hash running-sum reads the composite copies, at the concrete `ns` layout
(piece row starts `[0, 25, 26, 50]`). -/
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

private theorem prefixRows_ns_2 : Sinsemilla.Chain.prefixRows ns 2 = 26 := rfl

/-! ## Soundness -/

theorem soundness (G : Generators) (R : FixedBase) (Q : Point Fp)
    (hQ : Q.OnCurve) (cfg : Config) :
    FormalCircuit.Soundness (Witness := fun _ => Vector Fp 85 × Fq)
      (synth G R Q hQ cfg)
      (rivkExtract cfg) (EnvAssumptions G cfg) (fun _ => True) (Spec G Q R) := by
  circuit_proof_start
  obtain ⟨hTableG, hMulE, hTableL, hDistinct⟩ := _hE
  simp only [synth, circuit_norm] at hc
  have hP := hc.1
  have hCm := hc.2.1
  have hCan := hc.2.2
  clear hc
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm] at hP
  -- ── the three sub-piece short checks ──
  have hSb0 := hP.1
  have hSb2 := hP.2.1
  have hSd0 := hP.2.2
  clear hP
  subcircuit_rw at hSb0
  subcircuit_rw at hSb2
  subcircuit_rw at hSd0
  have hb0 := hSb0 (by rw [LookupRangeCheck.shortRangeCheck_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [LookupRangeCheck.shortRangeCheck_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [LookupRangeCheck.shortRangeCheck_spec_eq, short_output] at hb0
  simp only [circuit_norm] at hb0
  have hb2 := hSb2 (by rw [LookupRangeCheck.shortRangeCheck_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [LookupRangeCheck.shortRangeCheck_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [LookupRangeCheck.shortRangeCheck_spec_eq, short_output] at hb2
  simp only [circuit_norm] at hb2
  have hd0 := hSd0 (by rw [LookupRangeCheck.shortRangeCheck_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [LookupRangeCheck.shortRangeCheck_assumptions_eq]
        norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [LookupRangeCheck.shortRangeCheck_spec_eq, short_output] at hd0
  simp only [circuit_norm] at hd0
  clear hSb0 hSb2 hSd0
  -- ── the commitment ──
  simp only [synthPieces_output, synthPieces_nextRegionIndex,
    synthPieces_regionCount, Nat.add_assoc] at hCm hCan
  simp only [Nat.reduceAdd] at hCan
  subcircuit_rw at hCm
  have hCmS := hCm
    (by rw [Sinsemilla.CommitDomain.commit_envAssumptions_eq]; exact ⟨hTableG, hMulE⟩)
    (by rw [Sinsemilla.CommitDomain.commit_assumptions_eq]; trivial)
  rw [Sinsemilla.CommitDomain.commit_spec_eq, Sinsemilla.CommitDomain.commit_extract_eq] at hCmS
  clear hCm
  simp only [circuit_norm] at hCmS
  obtain ⟨chunks, hPC, hZs, hContract⟩ := hCmS
  rw [hashExtract_zs] at hZs
  have hPC' := (pieceChunks_donor_iff _ _ _).mp hPC
  have hZs' := (zsFacts_donor_iff _ _ _).mp hZs
  -- the two hash running-sum value facts
  have hz13a := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨0, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13a] at hz13a
  have hz13c := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨2, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13c] at hz13c
  simp only [Nat.add_assoc, Nat.reduceAdd] at hz13a hz13c
  -- the piece value bounds
  have hpieceA := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨0, by decide⟩ hPC' (by decide)
  have hpieceC := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨2, by decide⟩ hPC' (by decide)
  -- ── the canonicity composite ──
  subcircuit_rw at hCan
  have hCanS := hCan (by rw [Canonicity.circuit_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩)
    (by rw [Canonicity.circuit_assumptions_eq]
        simp only [circuit_norm, zCell, prefixRows_ns_2,
          AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
          Cell.of_column, Environment.get_advice, Nat.reduceAdd,
          Nat.add_zero]
        refine ⟨?_, hb0, hb2, ?_, hd0, ?_, ?_⟩
        · with_unfolding_all exact hpieceA
        · with_unfolding_all exact hpieceC
        · with_unfolding_all exact hz13a
        · with_unfolding_all exact hz13c)
  rw [Canonicity.circuit_spec_eq, Canonicity.circuit_extract_eq] at hCanS
  clear hCan
  simp only [circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_assoc, Nat.reduceAdd] at hCanS
  obtain ⟨hSa, hSb0v, hSb1, hSb2v, hSc, hSd0v, hSd1, hSbW, hSdW⟩ := hCanS
  obtain ⟨hiak, hink, -⟩ := h_input
  -- ── field-level canonical piece values ──
  have haF : env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ)
      = ((bitrange (env.get input_var_ak.cell.column
          ((place input_var_ak.cell.regionIndex
            + input_var_ak.cell.rowOffset : ℕ) : ℤ)).val 0 250 : ℕ) : Fp) := by
    rw [show env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ)
        = ((env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ)).val
          : Fp) from (ZMod.natCast_rightInverse _).symm, hSa]
  have hb0F : env.advice cfg.lookupConfig.runningSum ((place (i₀ + 1) : ℕ) : ℤ)
      = ((bitrange (env.get input_var_ak.cell.column
          ((place input_var_ak.cell.regionIndex
            + input_var_ak.cell.rowOffset : ℕ) : ℤ)).val 250 4 : ℕ) : Fp) := by
    rw [show env.advice cfg.lookupConfig.runningSum ((place (i₀ + 1) : ℕ) : ℤ)
        = ((env.advice cfg.lookupConfig.runningSum ((place (i₀ + 1) : ℕ) : ℤ)).val
          : Fp) from (ZMod.natCast_rightInverse _).symm, hSb0v]
  have hb1F : env.advice (cfg.gate.advices 4) ((place (i₀ + 13) : ℕ) : ℤ)
      = ((bitrange (env.get input_var_ak.cell.column
          ((place input_var_ak.cell.regionIndex
            + input_var_ak.cell.rowOffset : ℕ) : ℤ)).val 254 1 : ℕ) : Fp) := by
    rw [show env.advice (cfg.gate.advices 4) ((place (i₀ + 13) : ℕ) : ℤ)
        = ((env.advice (cfg.gate.advices 4) ((place (i₀ + 13) : ℕ) : ℤ)).val
          : Fp) from (ZMod.natCast_rightInverse _).symm, hSb1]
  have hb2F : env.advice cfg.lookupConfig.runningSum ((place (i₀ + 2) : ℕ) : ℤ)
      = ((bitrange (env.get input_var_nk.cell.column
          ((place input_var_nk.cell.regionIndex
            + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val 0 5 : ℕ) : Fp) := by
    rw [show env.advice cfg.lookupConfig.runningSum ((place (i₀ + 2) : ℕ) : ℤ)
        = ((env.advice cfg.lookupConfig.runningSum ((place (i₀ + 2) : ℕ) : ℤ)).val
          : Fp) from (ZMod.natCast_rightInverse _).symm, hSb2v]
  have hcF : env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ)
      = ((bitrange (env.get input_var_nk.cell.column
          ((place input_var_nk.cell.regionIndex
            + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val 5 240 : ℕ) : Fp) := by
    rw [show env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ)
        = ((env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ)).val
          : Fp) from (ZMod.natCast_rightInverse _).symm, hSc]
  have hd0F : env.advice cfg.lookupConfig.runningSum ((place (i₀ + 5) : ℕ) : ℤ)
      = ((bitrange (env.get input_var_nk.cell.column
          ((place input_var_nk.cell.regionIndex
            + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val 245 9 : ℕ) : Fp) := by
    rw [show env.advice cfg.lookupConfig.runningSum ((place (i₀ + 5) : ℕ) : ℤ)
        = ((env.advice cfg.lookupConfig.runningSum ((place (i₀ + 5) : ℕ) : ℤ)).val
          : Fp) from (ZMod.natCast_rightInverse _).symm, hSd0v]
  have hd1F : env.advice (cfg.gate.advices 4) ((place (i₀ + 13) + 1 : ℕ) : ℤ)
      = ((bitrange (env.get input_var_nk.cell.column
          ((place input_var_nk.cell.regionIndex
            + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val 254 1 : ℕ) : Fp) := by
    rw [show env.advice (cfg.gate.advices 4) ((place (i₀ + 13) + 1 : ℕ) : ℤ)
        = ((env.advice (cfg.gate.advices 4) ((place (i₀ + 13) + 1 : ℕ) : ℤ)).val
          : Fp) from (ZMod.natCast_rightInverse _).symm, hSd1]
  -- ── the honest chunks are the canonical `commit_ivk` chunks ──
  have hak : (env.get input_var_ak.cell.column
      ((place input_var_ak.cell.regionIndex
        + input_var_ak.cell.rowOffset : ℕ) : ℤ)).val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt _)
      (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hnk : (env.get input_var_nk.cell.column
      ((place input_var_nk.cell.regionIndex
        + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt _)
      (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hAv : env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ)
      = (((env.get input_var_ak.cell.column
          ((place input_var_ak.cell.regionIndex
            + input_var_ak.cell.rowOffset : ℕ) : ℤ)).val
          % 2 ^ (Halo2.Ironwood.Specs.K * 25) : ℕ) : Fp) := by
    rw [haF]
    norm_num [Halo2.Ironwood.Specs.bitrange, Halo2.Ironwood.Specs.K]
  have hBv : env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ)
      = ((bitrange (env.get input_var_ak.cell.column
            ((place input_var_ak.cell.regionIndex
              + input_var_ak.cell.rowOffset : ℕ) : ℤ)).val 250 4
          + bitrange (env.get input_var_ak.cell.column
            ((place input_var_ak.cell.regionIndex
              + input_var_ak.cell.rowOffset : ℕ) : ℤ)).val 254 1 * 16
          + bitrange (env.get input_var_nk.cell.column
            ((place input_var_nk.cell.regionIndex
              + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val 0 5 * 32 : ℕ) : Fp) := by
    rw [hSbW, hb0F, hb1F, hb2F]
    push_cast
    ring
  have hCv : env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ)
      = ((((env.get input_var_nk.cell.column
          ((place input_var_nk.cell.regionIndex
            + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val / 2 ^ 5)
          % 2 ^ (Halo2.Ironwood.Specs.K * 24) : ℕ) : Fp) := by
    rw [hcF]
    norm_num [Halo2.Ironwood.Specs.bitrange, Halo2.Ironwood.Specs.K]
  have hDv : env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ)
      = ((bitrange (env.get input_var_nk.cell.column
            ((place input_var_nk.cell.regionIndex
              + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val 245 9
          + bitrange (env.get input_var_nk.cell.column
            ((place input_var_nk.cell.regionIndex
              + input_var_nk.cell.rowOffset : ℕ) : ℤ)).val 254 1 * 512 : ℕ) : Fp) := by
    rw [hSdW, hd0F, hd1F]
    push_cast
    ring
  have hchunks := Halo2.Ironwood.CommitIvk.pieceChunks_eq_commitIvkChunks_of_indexed_piece_values
    hPC'
    (by with_unfolding_all exact hAv)
    (by with_unfolding_all exact hBv)
    (by with_unfolding_all exact hCv)
    (by with_unfolding_all exact hDv)
    hak hnk
  -- ── land the Spec ──
  simp only [Spec]
  rw [hiak, hink] at hchunks
  refine breaksOfGuarded (Or.inl hQ) (fun m hm => G.S_onCurve (chunksOf_mem_lt (by
    simpa [Halo2.Ironwood.Specs.Sinsemilla.commitIvkChunks] using hm))) ?_
  intro B hB
  rw [← hchunks] at hB
  obtain ⟨-, hOut⟩ := hContract B hB
  have hOutVar : ({ x := output, y := 0 } : Point Fp).x
      = (eval (⟨place, env⟩ : Placed Environment Fp)
        ((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).output
          (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
          { pieces :=
              #v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 3) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 4) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (i₀ + 6) 0 cfg.hashConfig.witnessPieces],
            r := input_var_rivk }
          (i₀ + 7)) : Point Fp).x := by
    -- the output walk crosses the commit call (opaque): land the walk on the folded call's
    -- output projection (defeq), open it with `output_call`, then the rest is metadata defeq
    rw [← h_output, ElaboratedCircuit.output_eq,
      show (synth G R Q hQ cfg
          { ak := input_var_ak, nk := input_var_nk, rivk := input_var_rivk }).output i₀
        = ((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).output
            (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
            { pieces :=
                #v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
                  AssignedCell.of (i₀ + 3) 0 cfg.hashConfig.witnessPieces,
                  AssignedCell.of (i₀ + 4) 0 cfg.hashConfig.witnessPieces,
                  AssignedCell.of (i₀ + 6) 0 cfg.hashConfig.witnessPieces],
              r := input_var_rivk }
            (i₀ + 7)).x from by
        show (((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
            (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
            { pieces :=
                #v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
                  AssignedCell.of (i₀ + 3) 0 cfg.hashConfig.witnessPieces,
                  AssignedCell.of (i₀ + 4) 0 cfg.hashConfig.witnessPieces,
                  AssignedCell.of (i₀ + 6) 0 cfg.hashConfig.witnessPieces],
              r := input_var_rivk }).output
          (i₀ + 7)).x = _
        rw [FormalCircuit.output_call]]
    with_unfolding_all rfl
  show (output : Fp) = _
  rw [show (output : Fp) = ({ x := output, y := 0 } : Point Fp).x from rfl, hOutVar,
    hOut]
  rfl

/-! ## Completeness infrastructure -/

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

private theorem short_extract_eq' (b : ℕ) (cfg : LookupRangeCheck.Config 10)
    (i : RegionIndex) (env : Placed Environment Fp) :
    (LookupRangeCheck.shortRangeCheck 10 b).extract cfg 0 () i env
      = (env.env.advice cfg.runningSum ((env.place i : ℕ) : ℤ) : Fp) := by
  show eval env (AssignedCell.of i 0 cfg.runningSum : Var field Fp) = _
  simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_zero]

private theorem pieces_eval_eq (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (c₀ c₁ c₂ c₃ : AssignedCell Fp) (r : Var UnconstrainedNat Fp) :
    (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
      ((⟨#v[c₀, c₁, c₂, c₃], r⟩
        : Var (Sinsemilla.CommitDomain.Input ns.length) Fp).pieces)
      : Value (fields ns.length) Fp)
    = #v[readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₀,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₁,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₂,
        readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) c₃] := by
  with_unfolding_all rfl

/-- Environment-side sibling of `pieces_eval_eq`. -/
private theorem pieces_eval_eq_env (place : RegionIndex → ℕ) (env : Environment Fp)
    (c₀ c₁ c₂ c₃ : AssignedCell Fp) (r : Var UnconstrainedNat Fp) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ((⟨#v[c₀, c₁, c₂, c₃], r⟩
        : Var (Sinsemilla.CommitDomain.Input ns.length) Fp).pieces)
      : Value (fields ns.length) Fp)
    = #v[eval (⟨place, env⟩ : Placed Environment Fp) (c₀ : Var field Fp),
        eval (⟨place, env⟩ : Placed Environment Fp) (c₁ : Var field Fp),
        eval (⟨place, env⟩ : Placed Environment Fp) (c₂ : Var field Fp),
        eval (⟨place, env⟩ : Placed Environment Fp) (c₃ : Var field Fp)] := by
  with_unfolding_all rfl

/-- The commit child's derived `Spec` on the honest-prover side (standalone,
kernel-checked alone). -/
private theorem commit_derived_spec (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (i : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)
    (hw : ExtendsWitnesses place env
      (((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
        c inp).operations i) i)
    (hEnvA : (Sinsemilla.CommitDomain.commit G ns R Q hQ
      ns_ne_nil).EnvAssumptions c (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
    (hPB' : Sinsemilla.Chain.PieceBounds ns
      (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp.pieces
        : Value (fields ns.length) Fp))
    (hHon' : ∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp.pieces
          : Value (fields ns.length) Fp)) = some B) :
    ∃ chunks : List ℕ,
      Sinsemilla.Chain.PieceChunks ns
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) inp.pieces
          : Value (fields ns.length) Fp) chunks ∧
      Sinsemilla.Chain.ZsFacts ns chunks
        ((Sinsemilla.HashToPoint.hashCircuit G ns Q hQ ns_ne_nil).extract c.2.1
          { pieces := inp.pieces } (i + 2)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).zs ∧
      ∀ B, hashToPoint G.S Q chunks = some B →
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
          ((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).output
            c inp i) : Value Point Fp).Valid ∧
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
          ((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).output
            c inp i) : Value Point Fp)
          = B + (((Ecc.MulFixed.FullWidth.fwExtract c.1 i
              (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 • R) : Point Fp) := by
  have hpeP :
      (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp).pieces =
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp.pieces
          : Value (fields ns.length) Fp) := by
    with_unfolding_all rfl
  have hpeE :
      (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) inp).pieces =
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) inp.pieces
          : Value (fields ns.length) Fp) := by
    with_unfolding_all rfl
  have h := (Halo2.SubcircuitRw.layouter_completeness_derived
    (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil) c i place env inp hw
    hEnvA (by rw [Sinsemilla.CommitDomain.commit_assumptions_eq]; trivial)
    (by rw [Sinsemilla.CommitDomain.commit_proverAssumptions_eq]
        change Sinsemilla.Chain.PieceBounds ns
            (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp).pieces ∧
          ∃ B, hashToPoint G.S Q (Sinsemilla.Chain.honestChunks ns
            (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) inp).pieces) = some B
        rw [hpeP]
        exact ⟨hPB', hHon'⟩)).1
  rw [Sinsemilla.CommitDomain.commit_spec_eq, Sinsemilla.CommitDomain.commit_extract_eq] at h
  rw [hpeE] at h
  simp only at h
  exact h

/-- The `b_1`/`d_1` cells witnessed inside the canonicity gate region read the
caller's bit programs (two-level witness projection). -/
private theorem canon_bit_witness (wb1 wd1 : WitgenIR Fp 1)
    (c : CommitIvk.Config × LookupRangeCheck.Config 10)
    (inp : Var Canonicity.Inputs Fp) (i : RegionIndex)
    (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (h : ExtendsWitnesses place env
      (((Canonicity.circuit wb1 wd1).call c inp).operations i) i) :
    env.advice (c.1.advices 4) ((place (i + 2) : ℕ) : ℤ)
      = ((wb1.eval (⟨place, env⟩ : Placed ProverEnvironment Fp))[0]'(by norm_num)) ∧
    env.advice (c.1.advices 4) ((place (i + 2) + 1 : ℕ) : ℤ)
      = ((wd1.eval (⟨place, env⟩ : Placed ProverEnvironment Fp))[0]'(by norm_num)) := by
  rw [show ExtendsWitnesses place env
        (((Canonicity.circuit wb1 wd1).call c inp).operations i) i
      = ExtendsWitnesses place env
        (((Canonicity.circuit wb1 wd1).synthesize c inp).operations i) i from by
    rw [FormalCircuit.call_operations]] at h
  simp only [Canonicity.circuit] at h
  simp only [Canonicity.synth, Canonicity.gateChild, LookupRangeCheck.witnessCheck,
    Circuit.operations_bind, operations_assignRegion, RegionCircuit.operations_bind,
    circuit_norm] at h
  have hg := h.2.2
  rw [FormalRegionCircuit.toFormal_call_extendsWitnesses] at hg
  simp only [Halo2.Ironwood.CommitIvk.bundle, circuit_norm] at hg
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hg
  try simp only [Nat.add_assoc, Nat.reduceAdd]
  exact ⟨hg.2.2.2.2.1, hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Build direction for stage 1: the three short-check chunks give the stage. -/
private theorem buildPieces (cfg : Config) (ak nk : AssignedCell Fp)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (h :
    RegionOperations.Constraints place (i₀ + 1) env
      (((LookupRangeCheck.shortRangeCheck 10 4).call cfg.lookupConfig 0 ()).operations
        (i₀ + 1)) ∧
    RegionOperations.Constraints place (i₀ + 2) env
      (((LookupRangeCheck.shortRangeCheck 10 5).call cfg.lookupConfig 0 ()).operations
        (i₀ + 2)) ∧
    RegionOperations.Constraints place (i₀ + 5) env
      (((LookupRangeCheck.shortRangeCheck 10 9).call cfg.lookupConfig 0 ()).operations
        (i₀ + 5))) :
    Constraints place env
      ((synthPieces cfg ak nk).operations i₀) i₀ := by
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm, Nat.add_assoc,
    Nat.reduceAdd]
  exact h

/-! ## Completeness -/

theorem completeness (G : Generators) (R : FixedBase) (Q : Point Fp)
    (hQ : Q.OnCurve) (cfg : Config) :
    FormalCircuit.Completeness (Witness := fun _ => Vector Fp 85 × Fq)
      (synth G R Q hQ cfg)
      (rivkExtract cfg) (EnvAssumptions G cfg) (fun _ => True)
      (ProverAssumptions G Q) (fun _ _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hTableG, hMulE, hTableL, hDistinct⟩ := _hE
  obtain ⟨B0, hB0⟩ := hPA
  simp only [synth, circuit_norm] at hwit ⊢
  have hWP := hwit.1
  have hWcm := hwit.2.1
  have hWCan := hwit.2.2
  clear hwit
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm, readCell] at hWP
  obtain ⟨hwa, ⟨hwb0, hWrb0⟩, ⟨hwb2, hWrb2⟩, hwb, hwc, ⟨hwd0, hWrd0⟩, hwd⟩ := hWP
  simp only [Nat.add_assoc, Nat.reduceAdd] at hwa hwb0 hwb2 hwb hwc hwd0 hwd
  simp only [synthPieces_output, synthPieces_nextRegionIndex,
    synthPieces_regionCount, Nat.add_assoc] at hWcm hWCan
  simp only [Nat.reduceAdd] at hWCan
  obtain ⟨hiak, hink, -⟩ := h_input
  -- ── honest piece facts ──
  have hHF := Halo2.Ironwood.CommitIvk.Commit.honest_pieces_facts
    (env.get input_var_ak.cell.column
      ((place input_var_ak.cell.regionIndex
        + input_var_ak.cell.rowOffset : ℕ) : ℤ))
    (env.get input_var_nk.cell.column
      ((place input_var_nk.cell.regionIndex
        + input_var_nk.cell.rowOffset : ℕ) : ℤ))
    (env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ))
    (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ))
    (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ))
    (env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ))
    hwa (by rw [hwb]) hwc (by rw [hwd])
  obtain ⟨hPBdonor, hHonestDonor⟩ := hHF
  have hPB : Sinsemilla.Chain.PieceBounds ns
      #v[env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ)] :=
    (pieceBounds_donor_iff _ _).mpr hPBdonor
  have hHonest : Sinsemilla.Chain.honestChunks ns
      #v[env.advice cfg.hashConfig.witnessPieces ((place i₀ : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 3) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 4) : ℕ) : ℤ),
        env.advice cfg.hashConfig.witnessPieces ((place (i₀ + 6) : ℕ) : ℤ)]
      = commitIvkChunks (show Fp from input_ak).val (show Fp from input_nk).val := by
    rw [honestChunks_donor_eq]
    rw [hiak, hink] at hHonestDonor
    exact hHonestDonor
  -- ── derived commit contract (the composite's rely-conditions) ──
  have hPB2 : Sinsemilla.Chain.PieceBounds ns
      (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
        ((⟨#v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 3) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 4) 0 cfg.hashConfig.witnessPieces,
            AssignedCell.of (i₀ + 6) 0 cfg.hashConfig.witnessPieces], input_var_rivk⟩
          : Var (Sinsemilla.CommitDomain.Input ns.length) Fp).pieces)
        : Value (fields ns.length) Fp) := by
    rw [pieces_eval_eq]
    simp only [readCell, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_zero]
    exact hPB
  have hHon2 : ∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          ((⟨#v[AssignedCell.of i₀ 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 3) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 4) 0 cfg.hashConfig.witnessPieces,
              AssignedCell.of (i₀ + 6) 0 cfg.hashConfig.witnessPieces], input_var_rivk⟩
            : Var (Sinsemilla.CommitDomain.Input ns.length) Fp).pieces)
          : Value (fields ns.length) Fp))
      = some B := by
    refine ⟨B0, ?_⟩
    rw [pieces_eval_eq]
    simp only [readCell, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_zero]
    rw [hHonest]
    exact hB0
  have hCmS := commit_derived_spec G R Q hQ
    (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) (i₀ + 7) place env _ hWcm
    (by rw [Sinsemilla.CommitDomain.commit_envAssumptions_eq]; exact ⟨hTableG, hMulE⟩)
    hPB2 hHon2
  obtain ⟨chunks, hPC, hZs, hContract⟩ := hCmS
  rw [hashExtract_zs] at hZs
  rw [pieces_eval_eq_env] at hPC
  try simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_zero] at hPC
  have hPC' := (pieceChunks_donor_iff _ _ _).mp hPC
  have hZs' := (zsFacts_donor_iff _ _ _).mp hZs
  have hz13a := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨0, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13a] at hz13a
  have hz13c := Halo2.Ironwood.NoteCommit.zsFacts_cell ns _ chunks _
    ⟨2, by decide⟩ hPC' hZs' (by decide) (r := 13) (by decide)
  rw [zs_get_z13c] at hz13c
  simp only [Nat.add_assoc, Nat.reduceAdd] at hz13a hz13c
  have hpieceA := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨0, by decide⟩ hPC' (by decide)
  have hpieceC := Halo2.Ironwood.NoteCommit.pieceChunks_val_lt ns _ chunks
    ⟨2, by decide⟩ hPC' (by decide)
  -- the b1/d1 gate-internal witnesses
  have hbits := canon_bit_witness (brWit input_var_ak 254 1) (brWit input_var_nk 254 1)
    (cfg.gate, cfg.lookupConfig) _ (i₀ + 11) place env hWCan
  simp only [circuit_norm, readCell, Nat.add_assoc, Nat.reduceAdd] at hbits
  have hwb1 := hbits.1
  have hwd1 := hbits.2
  -- ── assemble ──
  simp only [synthPieces_output, synthPieces_nextRegionIndex,
    synthPieces_regionCount, Nat.add_assoc]
  simp only [Nat.reduceAdd]
  refine ⟨buildPieces cfg input_var_ak input_var_nk i₀ place _ ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 4) cfg.lookupConfig 0 (i₀ + 1) place env ()
      hWrb0
      ⟨(by rw [LookupRangeCheck.shortRangeCheck_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [LookupRangeCheck.shortRangeCheck_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [LookupRangeCheck.shortRangeCheck_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 4).extract
             cfg.lookupConfig 0 ()
             (i₀ + 1) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 4
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 1) : ℕ) : ℤ)).val < 2 ^ 4
           rw [hwb0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 5) cfg.lookupConfig 0 (i₀ + 2) place env ()
      hWrb2
      ⟨(by rw [LookupRangeCheck.shortRangeCheck_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [LookupRangeCheck.shortRangeCheck_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [LookupRangeCheck.shortRangeCheck_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 5).extract
             cfg.lookupConfig 0 ()
             (i₀ + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 5
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 2) : ℕ) : ℤ)).val < 2 ^ 5
           rw [hwb2, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.region_completeness_leaf
      (LookupRangeCheck.shortRangeCheck 10 9) cfg.lookupConfig 0 (i₀ + 5) place env ()
      hWrd0
      ⟨(by rw [LookupRangeCheck.shortRangeCheck_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [LookupRangeCheck.shortRangeCheck_assumptions_eq]
           norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]),
       (by rw [LookupRangeCheck.shortRangeCheck_proverAssumptions_eq]
           show (show Fp from (LookupRangeCheck.shortRangeCheck 10 9).extract
             cfg.lookupConfig 0 ()
             (i₀ + 5) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).val < 2 ^ 9
           rw [short_extract_eq']
           show (env.advice cfg.lookupConfig.runningSum
             ((place (i₀ + 5) : ℕ) : ℤ)).val < 2 ^ 9
           rw [hwd0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
           exact Halo2.Ironwood.Specs.bitrange_lt _ _ _)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) (i₀ + 7) place env _ hWcm
      ⟨(by rw [Sinsemilla.CommitDomain.commit_envAssumptions_eq]; exact ⟨hTableG, hMulE⟩),
       (by rw [Sinsemilla.CommitDomain.commit_assumptions_eq]; trivial),
       (by rw [Sinsemilla.CommitDomain.commit_proverAssumptions_eq]
           refine ⟨?_, ?_⟩
           · show Sinsemilla.Chain.PieceBounds ns _
             with_unfolding_all exact hPB
           · refine ⟨B0, ?_⟩
             rw [show (Sinsemilla.Chain.honestChunks ns _ : List ℕ)
                 = commitIvkChunks (show Fp from input_ak).val
                   (show Fp from input_nk).val from by
               with_unfolding_all exact hHonest]
             exact hB0)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (Canonicity.circuit (brWit input_var_ak 254 1) (brWit input_var_nk 254 1))
      (cfg.gate, cfg.lookupConfig) (i₀ + 11) place env _ hWCan
      ⟨(by rw [Canonicity.circuit_envAssumptions_eq]; exact ⟨hTableL, hDistinct⟩),
       (by rw [Canonicity.circuit_assumptions_eq]
           simp only [circuit_norm, zCell, prefixRows_ns_2,
             AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.reduceAdd,
             Nat.add_zero]
           refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
           · with_unfolding_all exact hpieceA
           · rw [hwb0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
             exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
           · rw [hwb2, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
             exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
           · with_unfolding_all exact hpieceC
           · rw [hwd0, Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num)]
             exact Halo2.Ironwood.Specs.bitrange_lt _ _ _
           · with_unfolding_all exact hz13a
           · with_unfolding_all exact hz13c),
       (by rw [Canonicity.circuit_proverAssumptions_eq, Canonicity.circuit_extract_eq]
           simp only [circuit_norm, zCell, prefixRows_ns_2,
             AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
             Cell.of_column, Environment.get_advice, Nat.add_assoc, Nat.reduceAdd,
             Nat.add_zero]
           refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
           · rw [hwa]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
           · rw [hwb0]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
           · rw [hwb1]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
           · rw [hwb2]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
           · rw [hwc]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
           · rw [hwd0]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
           · rw [hwd1]; exact Halo2.Ironwood.Specs.cast_bitrange_val (by norm_num) _
           · rw [hwb, ← hwb0, ← hwb1, ← hwb2]
             try ring
           · rw [hwd, ← hwd0, ← hwd1]
             try ring)⟩

/-- Rust `gadgets::commit_ivk` as a proof-carrying bundle. -/
def circuit (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve) :
    FormalCircuit Fp Config Config Inputs field where
  name := "CommitIvk"
  configure := pure
  synthesize := synth G R Q hQ
  elaborated := elaborated G R Q hQ
  Witness := fun _ => Vector Fp 85 × Fq
  extract := rivkExtract
  EnvAssumptions := EnvAssumptions G
  Assumptions := fun _ => True
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q
  ProverSpec := fun _ _ _ _ => True
  soundness := soundness G R Q hQ
  completeness := completeness G R Q hQ

/-! ## Bundle contract bridges (generated; the bundle stays folded) -/

derive_contract_bridges circuit (G : Generators) (R : FixedBase) (Q : Point Fp)
  (hQ : Q.OnCurve) := circuit G R Q hQ

end Halo2.Ironwood.CommitIvk.Main
