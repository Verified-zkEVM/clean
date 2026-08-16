import Clean.Ironwood.CommitIvk.Composite
import Clean.Ironwood.NoteCommit.Main
import Clean.Ironwood.Sinsemilla.CommitDomain
import Clean.Ironwood.CommitIvk.MainTheorems
import Clean.Ironwood.Specs.SinsemillaBreak
import Clean.Halo2.CircuitTypeDeriving

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/commit_ivk.rs` `gadgets::commit_ivk` (`commit_ivk.rs:261-414`).

# The CommitIvk main circuit

The full `Commit^ivk` flow, region-for-region:

1. **Pieces** (7 regions, `commit_ivk.rs:289-350`): witness piece `a = ak[0..250)`;
   short checks `b_0 = ak[250..254)` (4 bits) and `b_2 = nk[0..5)` (5 bits); piece
   `b = b_0 + 2⁴·b_1 + 2⁵·b_2`; piece `c = nk[5..245)`; short check
   `d_0 = nk[245..254)` (9 bits); piece `d = d_0 + 2⁹·d_1`.
2. **Commit** (4 regions, `commit_ivk.rs:357-366` → `CommitDomain::short_commit`,
   which is `commit` + `extract_p` — no extra regions): the `[rivk]R` blind
   (full-width fixed-base mul, 2 regions), `hash_to_point`, the complete addition.
3. **Canonicity** (3 regions, `commit_ivk.rs:375-411`): the `a'`/`b2_c'` shift
   `witness_check`s and the two-row canonicity gate region — the proven
   `CommitIvk` composite, called as a unit (contiguous in Rust).

The output is the extracted `x`-coordinate (`ivk`). `Spec` is the breaks-as-data
`Commit^ivk` relation at the extracted `rivk` window scalar (zcash/ironwood#45).
-/

namespace Zcash.Circuits.CommitIvk.Main

open Halo2
open Sinsemilla.HashToPoint (witnessMessagePiece)
open Ecc.MulFixed (FixedBase)
open Specs (bitrange)
open Specs.Sinsemilla (Generators)
open NoteCommit.Main (brWit currentRegion)

/-- Piece word counts minus one, per the chain convention: `a` = 25 words, `b` = 1,
`c` = 24, `d` = 1 (`I2LEBSP₂₅₅(ak) || I2LEBSP₂₅₅(nk)` split at `250/10/240/10` bits). -/
def ns : List ℕ := [24, 0, 23, 0]

theorem ns_ne_nil : ns ≠ [] := by simp [ns]

/-- The main circuit's inputs: the `ak`/`nk` field-element cells and the blinding
scalar's nat-valued reading program `rivk` (a prover hint). -/
structure Inputs (F : Type) where
  ak : F
  nk : F
  rivk : UnconstrainedNat F
deriving CircuitType

/-! ## Witness programs (the canonical bit-slice values; Rust computes the same from
the corresponding `Value`s) -/

/-- Piece `b = b_0 + 2⁴·b_1 + 2⁵·b_2` (`commit_ivk.rs:315-320`). -/
def bWit (ak nk : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env ak).val 250 4 : ℕ) : Fp)
      + ((bitrange (readCell env ak).val 254 1 : ℕ) : Fp) * (2 ^ 4 : Fp)
      + ((bitrange (readCell env nk).val 0 5 : ℕ) : Fp) * (2 ^ 5 : Fp)]

@[circuit_norm]
theorem bWit_eval (ak nk : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((bWit ak nk).eval env)[j]
      = ((bitrange (readCell env ak).val 250 4 : ℕ) : Fp)
        + ((bitrange (readCell env ak).val 254 1 : ℕ) : Fp) * (2 ^ 4 : Fp)
        + ((bitrange (readCell env nk).val 0 5 : ℕ) : Fp) * (2 ^ 5 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [bWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Piece `d = d_0 + 2⁹·d_1` (`commit_ivk.rs:343-347`). -/
def dWit (nk : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env nk).val 245 9 : ℕ) : Fp)
      + ((bitrange (readCell env nk).val 254 1 : ℕ) : Fp) * (2 ^ 9 : Fp)]

@[circuit_norm]
theorem dWit_eval (nk : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((dWit nk).eval env)[j]
      = ((bitrange (readCell env nk).val 245 9 : ℕ) : Fp)
        + ((bitrange (readCell env nk).val 254 1 : ℕ) : Fp) * (2 ^ 9 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [dWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-! ## Config and layout -/

structure Config where
  gate : CommitIvk.Config
  hashConfig : Sinsemilla.HashPiece.Config
  lookupConfig : LookupRangeCheck.Config 10
  mulConfig : Ecc.MulFixed.FullWidth.Config
  addConfig : Ecc.Add.Config

/-- The hash running-sum cell `zs[i][j]`: row `prefixRows ns i + j` of the `bits`
column inside the `hash_to_point` region. -/
def zCell (hcfg : Sinsemilla.HashPiece.Config) (iHash : RegionIndex) (i j : ℕ) :
    AssignedCell Fp :=
  .of iHash (Sinsemilla.Chain.prefixRows ns i + j) hcfg.bits

/-- The piece cells stage 1 hands to the later stages. -/
structure PieceCells where
  a : AssignedCell Fp
  b : AssignedCell Fp
  c : AssignedCell Fp
  d : AssignedCell Fp
  b0 : AssignedCell Fp
  b2 : AssignedCell Fp
  d0 : AssignedCell Fp

@[keygen_norm]
def PieceCells.permutationColumns (cells : PieceCells) : List AnyColumn :=
  [cells.a.cell.column, cells.b.cell.column, cells.c.cell.column,
    cells.d.cell.column, cells.b0.cell.column, cells.b2.cell.column,
    cells.d0.cell.column]

/-- Stage 1 (7 regions): the four message pieces interleaved with the three
sub-piece short checks (`commit_ivk.rs:289-350`). -/
def synthPieces (cfg : Config) (ak nk : AssignedCell Fp) :
    Circuit Fp PieceCells := do
  let a ← witnessMessagePiece cfg.hashConfig (brWit ak 0 250)
  let b0 ← LookupRangeCheck.witnessShortCheck 10 4 cfg.lookupConfig
    (brWit ak 250 4)
  let b2 ← LookupRangeCheck.witnessShortCheck 10 5 cfg.lookupConfig
    (brWit nk 0 5)
  let b ← witnessMessagePiece cfg.hashConfig (bWit ak nk)
  let c ← witnessMessagePiece cfg.hashConfig (brWit nk 5 240)
  let d0 ← LookupRangeCheck.witnessShortCheck 10 9 cfg.lookupConfig
    (brWit nk 245 9)
  let d ← witnessMessagePiece cfg.hashConfig (dWit nk)
  pure { a, b, c, d, b0, b2, d0 }

/-- The full flow: pieces, the 4-region commit, the 3-region canonicity composite.
Output: the extracted `x`-coordinate (`ivk`). -/
def synth (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) : Circuit Fp (Var field Fp) := do
  let i₀ ← currentRegion
  let iHash := i₀ + 9
  let pcs ← synthPieces cfg input.ak input.nk
  let cm ← (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
    (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d], r := input.rivk }
  let _ ← (CommitIvk.Canonicity.circuit (brWit input.ak 254 1) (brWit input.nk 254 1)).call
    (cfg.gate, cfg.lookupConfig)
    { ak := input.ak, a := pcs.a, bWhole := pcs.b, b0 := pcs.b0, b2 := pcs.b2,
      z13A := zCell cfg.hashConfig iHash 0 13,
      nk := input.nk, c := pcs.c, dWhole := pcs.d, d0 := pcs.d0,
      z13C := zCell cfg.hashConfig iHash 2 13 }
  pure cm.x

/-! ## Region counts and stage outputs -/

theorem synthPieces_regionCount (cfg : Config) (ak nk : AssignedCell Fp)
    (i : RegionIndex) :
    Operations.regionCount ((synthPieces cfg ak nk).operations i) = 7 := by
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

/-- The region count of the flow: 7 piece/short regions, the 4-region commit, the
3-region canonicity composite — 14. -/
theorem synth_regionCount (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.regionCount ((synth G R Q hQ cfg input).operations i) = 14 := by
  -- lean explicit set: `circuit_norm`'s dsimp-normalization of op payloads is
  -- kernel-expensive now that call chunks are kernel-transparent (no constructor head)
  simp only [synth, Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    FormalCircuit.nextRegionIndex_call', FormalCircuit.output_call',
    NoteCommit.Main.currentRegion_operations]
  rw [synthPieces_regionCount, Sinsemilla.CommitDomain.commit_call_regionCount, Canonicity.circuit_call_regionCount]

theorem synthPieces_nextRegionIndex (cfg : Config) (ak nk : AssignedCell Fp)
    (i : RegionIndex) :
    (synthPieces cfg ak nk).nextRegionIndex i = i + 7 := by
  rfl

/-- Exact reduced footprint of the seven message-piece regions. -/
def synthPiecesSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  let piece := Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary
    cfg.hashConfig
  let short := LookupRangeCheck.witnessShortCheckSynthesisSummary
    10 cfg.lookupConfig
  [piece, short, short, piece, piece, short, piece].foldr
    FloorPlanner.SynthesisSummary.combine {}

/-- Exact reduced footprint of the complete fourteen-region CommitIvk flow. -/
def synthesisSummary (cfg : Config) : FloorPlanner.SynthesisSummary :=
  (synthPiecesSynthesisSummary cfg).combine
    ((Sinsemilla.CommitDomain.commitSynthesisSummary ns
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)).combine
      (Canonicity.circuitSynthesisSummary cfg.gate cfg.lookupConfig))

@[synthesis_summary_norm]
theorem synthPiecesSynthesisSummary_hasNoFixedWrites (cfg : Config) :
    (synthPiecesSynthesisSummary cfg).HasNoFixedWrites := by
  simp only [synthPiecesSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem synthesisSummary_tableRowExtent_eq (cfg : Config) :
    (synthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthesisSummary, synthPiecesSynthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    Canonicity.circuitSynthesisSummary, List.foldr_cons, List.foldr_nil,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq (cfg : Config) :
    (synthesisSummary cfg).instanceRowExtent = 0 := by
  simp only [synthesisSummary, synthPiecesSynthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    Canonicity.circuitSynthesisSummary, List.foldr_cons, List.foldr_nil,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    CommitIvk.synthesisSummary,
    synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthPieces_synthesisSummary_eq (cfg : Config)
    (ak nk : AssignedCell Fp) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthPieces cfg ak nk).operations region) =
      synthPiecesSynthesisSummary cfg := by
  simp only [synthPiecesSynthesisSummary, synthPieces, circuit_norm,
    synthesis_summary_norm, List.foldr_cons, List.foldr_nil,
    FloorPlanner.SynthesisSummary.combine_empty]

@[synthesis_summary_norm]
theorem synth_synthesisSummary_eq
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synth G R Q hQ cfg input).operations region) =
      synthesisSummary cfg := by
  simp only [synthesisSummary, synth, circuit_norm, synthesis_summary_norm]

@[keygen_output_norm]
theorem synthPieces_output (cfg : Config) (ak nk : AssignedCell Fp)
    (i : RegionIndex) :
    (synthPieces cfg ak nk).output i
      = { a := .of i 0 cfg.hashConfig.witnessPieces,
          b := .of (i + 3) 0 cfg.hashConfig.witnessPieces,
          c := .of (i + 4) 0 cfg.hashConfig.witnessPieces,
          d := .of (i + 6) 0 cfg.hashConfig.witnessPieces,
          b0 := .of (i + 1) 0 cfg.lookupConfig.runningSum,
          b2 := .of (i + 2) 0 cfg.lookupConfig.runningSum,
          d0 := .of (i + 5) 0 cfg.lookupConfig.runningSum } := by
  rfl

@[keygen_output_norm]
theorem synth_output (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    (synth G R Q hQ cfg input).output i =
      AssignedCell.of (i + 10) 1 cfg.addConfig.xQR := by
  simp only [synth, Circuit.output_bind, Circuit.output_pure,
    NoteCommit.Main.currentRegion_output,
    NoteCommit.Main.currentRegion_nextRegionIndex,
    synthPieces_output, synthPieces_nextRegionIndex,
    FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
    Sinsemilla.CommitDomain.commit_output, Nat.add_assoc, Nat.reduceAdd]

/-! ## The bundle contract -/

open Specs.Sinsemilla (hashToPoint hashToPointB SpecOrBreak commitIvkChunks)
open CompElliptic.Fields.Pasta (Fq)

def permutationColumns (cfg : Config) (childColumns : List AnyColumn) :
    List AnyColumn :=
  ([cfg.hashConfig.witnessPieces, cfg.hashConfig.bits,
      cfg.lookupConfig.runningSum] : List AnyColumn) ++
    CommitIvk.permutationColumns cfg.gate ++ childColumns

theorem synthPieces_output_permutationColumns (cfg : Config)
    (ak nk : AssignedCell Fp) (childColumns : List AnyColumn)
    (i : RegionIndex) :
    ∀ column, column ∈ ((synthPieces cfg ak nk).output i).permutationColumns →
      column ∈ permutationColumns cfg childColumns := by
  intro column hcolumn
  simp only [synthPieces_output, PieceCells.permutationColumns,
    AssignedCell.of_cell, Cell.of_column, List.mem_cons,
    List.not_mem_nil, or_false, or_self] at hcolumn
  have : column = cfg.hashConfig.witnessPieces.toAny ∨
      column = cfg.lookupConfig.runningSum.toAny := by
    grind
  rcases this with rfl | rfl <;> simp [permutationColumns]

theorem zCell_column_mem_permutationColumns (cfg : Config)
    (childColumns : List AnyColumn) (iHash : RegionIndex) (i j : ℕ) :
    (zCell cfg.hashConfig iHash i j).cell.column ∈
      permutationColumns cfg childColumns := by
  simp [zCell, AssignedCell.of_cell, Cell.of_column, permutationColumns]

@[keygen_norm]
def keygenRequirements (G : Generators) (R : FixedBase) (Q : Point Fp)
    (hQ : Q.OnCurve) : KeygenRequirements Fp Config (Var Inputs Fp) where
  configLawful cfg :=
    (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).Configured
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
  gates cfg configured :=
    [LookupRangeCheck.bitshiftGate 10 cfg.lookupConfig, CommitIvk.gate cfg.gate] ++
      configured.gates
  lookups cfg configured :=
    [LookupRangeCheck.rangeCheckLookup 10 cfg.lookupConfig] ++ configured.lookups
  fixedColumns _ configured := configured.fixedColumns
  permutationColumns cfg configured :=
    permutationColumns cfg configured.permutationColumns
  inputCells _ _ input :=
    [input.ak.cell, input.nk.cell]

@[keygen_helper]
theorem synthPieces_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthPieces cfg input.ak input.nk).operations self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns
          cfg configured input) := by
  have hRunningSum : cfg.lookupConfig.runningSum.toAny ∈
      (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns
          cfg configured input := by
    simp [keygenRequirements, permutationColumns]
  keygen_registration [synthPieces,
    Sinsemilla.HashToPoint.witnessMessagePiece]

@[keygen_helper]
theorem synth_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synth G R Q hQ cfg input).operations self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns
          cfg configured input) := by
  have hRunningSum : cfg.lookupConfig.runningSum.toAny ∈
      (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns
          cfg configured input := by
    simp [keygenRequirements, permutationColumns]
  have hChild := fun column =>
    show column ∈ configured.permutationColumns →
      column ∈
        (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
          (keygenRequirements G R Q hQ).inputPermutationColumns
            cfg configured input from by
      intro hcolumn
      simp only [keygenRequirements, List.mem_append]
      left
      exact List.mem_append_right _ hcolumn
  have hPieces := synthPieces_output_permutationColumns
    cfg input.ak input.nk configured.permutationColumns
      self
  have hZ := fun i j =>
    zCell_column_mem_permutationColumns
      cfg configured.permutationColumns (self + 9) i j
  have hCanonicity : ∀ column,
      column ∈ CommitIvk.permutationColumns cfg.gate ++
        ([cfg.lookupConfig.runningSum] : List AnyColumn) →
      column ∈
        (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
          (keygenRequirements G R Q hQ).inputPermutationColumns
            cfg configured input := by
    intro column hcolumn
    simp [keygenRequirements, permutationColumns] at hcolumn ⊢
    grind
  simp only [synth, Circuit.operations_bind,
    NoteCommit.Main.currentRegion_operations,
    NoteCommit.Main.currentRegion_nextRegionIndex,
    NoteCommit.Main.currentRegion_output,
    synthPieces_nextRegionIndex, synthPieces_output,
    FormalCircuit.nextRegionIndex_call', FormalCircuit.output_call',
    Circuit.operations_pure, Operations.KeygenRegistered.append,
    Operations.KeygenRegistered.nil, true_and, and_true]
  constructor
  · exact synthPieces_keygenRegistered G R Q hQ cfg input self configured
  constructor
  · apply (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
      |>.call_keygenRegistered
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) configured _ (self + 7)
    case hgates => keygen_registration
    case hlookups => keygen_registration
    case hfixedColumns =>
      intro column hcolumn
      exact hcolumn
    case hpermutationColumns => exact hChild
    case hinputCells =>
      rw [Sinsemilla.CommitDomain.commit_inputCells,
        List.forall_iff_forall_mem]
      intro cell hcell
      simp only [Vector.toList, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hcell
      rcases hcell with rfl | rfl | rfl | rfl <;>
        apply List.mem_append_left <;>
        apply synthPieces_output_permutationColumns cfg input.ak input.nk
          configured.permutationColumns self <;>
        simp [synthPieces_output, PieceCells.permutationColumns]
  · rw [Sinsemilla.CommitDomain.commit_call_regionCount]
    let child := CommitIvk.Canonicity.circuit
      (brWit input.ak 254 1) (brWit input.nk 254 1)
    let childConfigured := FormalCircuit.Configured.ofPure child
      (cfg.gate, cfg.lookupConfig) () (by rfl)
    apply child.call_keygenRegistered
      (cfg.gate, cfg.lookupConfig) childConfigured _ (self + 11)
    case hgates => keygen_registration
    case hlookups => keygen_registration
    case hfixedColumns =>
      intro column hcolumn
      simp only [childConfigured, child,
        FormalCircuit.Configured.ofPure_fixedColumns] at hcolumn
      contradiction
    case hpermutationColumns =>
      intro column hcolumn
      simpa only [childConfigured, child,
        FormalCircuit.Configured.ofPure_permutationColumns] using
          hCanonicity column hcolumn
    case hinputCells => keygen_registration

private theorem synthPieces_copyCellsAssigned
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    ((synthPieces cfg input.ak input.nk).operations self).CopyCellsAssigned self
      [input.ak.cell, input.nk.cell] := by
  simp only [synthPieces, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply Operations.CopyCellsAssignedFrom.append
  · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
  · apply Operations.CopyCellsAssignedFrom.append
    · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
    · apply Operations.CopyCellsAssignedFrom.append
      · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
      · apply Operations.CopyCellsAssignedFrom.append
        · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
        · apply Operations.CopyCellsAssignedFrom.append
          · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
          · apply Operations.CopyCellsAssignedFrom.append
            · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
            · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom

private theorem synthPieces_output_cells_assigned
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    let pcs := (synthPieces cfg input.ak input.nk).output self
    [pcs.a.cell, pcs.b.cell, pcs.c.cell, pcs.d.cell,
      pcs.b0.cell, pcs.b2.cell, pcs.d0.cell].Forall fun cell =>
        cell ∈ Operations.assignedCellsFrom
          ((synthPieces cfg input.ak input.nk).operations self) self := by
  rw [synthPieces_output]
  simp only [synthPieces, Sinsemilla.HashToPoint.witnessMessagePiece,
    LookupRangeCheck.witnessShortCheck, circuit_norm,
    Operations.assignedCellsFrom, RegionOperations.assignedCells,
    RegionOperation.assignedCells, List.flatMap_cons, List.mem_append,
    List.mem_cons, true_or]

private theorem synthPieces_lookupActivationsWellFormed
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    ((synthPieces cfg input.ak input.nk).operations self)
      |>.LookupActivationsWellFormed := by
  simp only [synthPieces, Circuit.operations_bind, Circuit.operations_pure,
    Operations.LookupActivationsWellFormed, List.forall_append,
    List.forall_nil, and_true]
  exact ⟨
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (brWit input.ak 0 250) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 4 cfg.lookupConfig (brWit input.ak 250 4) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 5 cfg.lookupConfig (brWit input.nk 0 5) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (bWit input.ak input.nk) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (brWit input.nk 5 240) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 9 cfg.lookupConfig (brWit input.nk 245 9) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (dWit input.nk) _⟩

private theorem synthPieces_lookupSelectorAssignmentsAgree
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    ((synthPieces cfg input.ak input.nk).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  simp only [synthPieces, Circuit.operations_bind, Circuit.operations_pure,
    keygen_norm, keygen_spine]

private theorem synthPieces_lookupSelectorsAnchoredBy
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied
      (LookupRangeCheck.lookupSelectorAnchorRequirements cfg.lookupConfig) anchor) :
    ((synthPieces cfg input.ak input.nk).operations self)
      |>.LookupSelectorsAnchoredBy anchor := by
  simp only [synthPieces, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply Operations.LookupSelectorsAnchoredBy.append
  · exact Sinsemilla.HashToPoint.witnessMessagePiece_lookupSelectorsAnchoredBy
      cfg.hashConfig _ self anchor
  apply Operations.LookupSelectorsAnchoredBy.append
  · exact LookupRangeCheck.witnessShortCheck_lookupSelectorsAnchoredBy
      10 4 cfg.lookupConfig _ _ anchor hanchor
  apply Operations.LookupSelectorsAnchoredBy.append
  · exact LookupRangeCheck.witnessShortCheck_lookupSelectorsAnchoredBy
      10 5 cfg.lookupConfig _ _ anchor hanchor
  apply Operations.LookupSelectorsAnchoredBy.append
  · exact Sinsemilla.HashToPoint.witnessMessagePiece_lookupSelectorsAnchoredBy
      cfg.hashConfig _ _ anchor
  apply Operations.LookupSelectorsAnchoredBy.append
  · exact Sinsemilla.HashToPoint.witnessMessagePiece_lookupSelectorsAnchoredBy
      cfg.hashConfig _ _ anchor
  apply Operations.LookupSelectorsAnchoredBy.append
  · exact LookupRangeCheck.witnessShortCheck_lookupSelectorsAnchoredBy
      10 9 cfg.lookupConfig _ _ anchor hanchor
  · exact Sinsemilla.HashToPoint.witnessMessagePiece_lookupSelectorsAnchoredBy
      cfg.hashConfig _ _ anchor

private theorem synth_copyCellsAssigned
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synth G R Q hQ cfg input).operations self).CopyCellsAssigned self
      ((keygenRequirements G R Q hQ).inputCells cfg configured input) := by
  simp only [keygenRequirements, synth,
    NoteCommit.Main.currentRegion_operations,
    NoteCommit.Main.currentRegion_nextRegionIndex,
    NoteCommit.Main.currentRegion_output,
    Circuit.operations_bind, Circuit.operations_pure, List.append_nil,
    List.nil_append]
  apply Operations.CopyCellsAssignedFrom.append
  · exact synthPieces_copyCellsAssigned cfg input self
  · apply Operations.CopyCellsAssignedFrom.append
    · rw [synthPieces_regionCount]
      apply (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
        |>.call_copyCellsAssignedFrom _ configured _ _
      rw [Sinsemilla.CommitDomain.commit_inputCells]
      intro cell hcell
      have hpieces := synthPieces_output_cells_assigned cfg input self
      simp only [List.forall_cons, List.forall_nil, and_true] at hpieces
      simp only [Vector.toList, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hcell
      rcases hcell with rfl | rfl | rfl | rfl <;>
        apply List.mem_append_right
      · exact hpieces.1
      · exact hpieces.2.1
      · exact hpieces.2.2.1
      · exact hpieces.2.2.2.1
    · rw [synthPieces_regionCount,
        Sinsemilla.CommitDomain.commit_call_regionCount]
      simp only [synthPieces_nextRegionIndex]
      rw [FormalCircuit.nextRegionIndex_call,
        Sinsemilla.CommitDomain.commit_call_regionCount]
      let pcs := (synthPieces cfg input.ak input.nk).output self
      let commitInput : Var (Sinsemilla.CommitDomain.Input ns.length) Fp :=
        { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d], r := input.rivk }
      let child := CommitIvk.Canonicity.circuit
        (brWit input.ak 254 1) (brWit input.nk 254 1)
      let childConfigured := FormalCircuit.Configured.ofPure child
        (cfg.gate, cfg.lookupConfig) () (by rfl)
      apply child.call_copyCellsAssignedFrom
        (cfg.gate, cfg.lookupConfig) childConfigured _ (self + 7 + 4)
      intro cell hcell
      have hpieces := synthPieces_output_cells_assigned cfg input self
      have hz0 := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
        G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
        commitInput (self + 7) ⟨0, by simp [ns]⟩ ⟨13, by simp [ns]⟩
      have hz2 := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
        G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
        commitInput (self + 7) ⟨2, by simp [ns]⟩ ⟨13, by simp [ns]⟩
      simp only [List.forall_cons, List.forall_nil, and_true] at hpieces
      rw [CommitIvk.Canonicity.circuit_inputCells] at hcell
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
      rcases hcell with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · simp
      · exact List.mem_append_left _ (List.mem_append_right _ hpieces.1)
      · exact List.mem_append_left _ (List.mem_append_right _ hpieces.2.1)
      · exact List.mem_append_left _
          (List.mem_append_right _ hpieces.2.2.2.2.1)
      · exact List.mem_append_left _
          (List.mem_append_right _ hpieces.2.2.2.2.2.1)
      · simpa only [zCell, commitInput, pcs, Nat.add_assoc] using
          List.mem_append_right
            ([input.ak.cell, input.nk.cell] ++
              Operations.assignedCellsFrom
                ((synthPieces cfg input.ak input.nk).operations self) self) hz0
      · simp
      · exact List.mem_append_left _ (List.mem_append_right _ hpieces.2.2.1)
      · exact List.mem_append_left _
          (List.mem_append_right _ hpieces.2.2.2.1)
      · exact List.mem_append_left _
          (List.mem_append_right _ hpieces.2.2.2.2.2.2)
      · simpa only [zCell, commitInput, pcs, Nat.add_assoc] using
          List.mem_append_right
            ([input.ak.cell, input.nk.cell] ++
              Operations.assignedCellsFrom
                ((synthPieces cfg input.ak input.nk).operations self) self) hz2

instance elaborated (G : Generators) (R : FixedBase) (Q : Point Fp)
    (hQ : Q.OnCurve) :
    ElaboratedCircuit Fp Config Config Inputs field
      (fun config => pure config) (synth G R Q hQ) where
  keygenRequirements := keygenRequirements G R Q hQ
  registered configInput _ configured input self := by
    simpa using synth_keygenRegistered
      G R Q hQ configInput input self configured
  copyCellsAssigned cfg _ configured input self :=
    synth_copyCellsAssigned G R Q hQ cfg input self configured
  lookupSelectorAnchorRequirements cfg _ _ :=
    LookupRangeCheck.lookupSelectorAnchorRequirements cfg.lookupConfig
  lookupSelectorsAnchoredBy_of_registered := by
    intro cfg _ hconfig input self anchor hanchor _
    simp only [Configure.output_pure] at hanchor
    simp only [Configure.output_pure, synth,
      NoteCommit.Main.currentRegion_operations, Circuit.operations_bind,
      Circuit.operations_pure, List.append_nil, keygen_norm, keygen_spine]
    exact ⟨synthPieces_lookupSelectorsAnchoredBy cfg input _ anchor hanchor,
      (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
        |>.call_lookupSelectorsAnchoredBy
          (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) hconfig _ _ anchor (by trivial),
      (CommitIvk.Canonicity.circuit
        (brWit input.ak 254 1) (brWit input.nk 254 1))
          |>.call_lookupSelectorsAnchoredBy (cfg.gate, cfg.lookupConfig)
            (FormalCircuit.Configured.ofPure _ _ () rfl) _ _ anchor hanchor⟩
  lookupSelectorAssignmentsAgree_of_registered := by
    intro cfg counts hconfig input self program operations _hregistered
    simp only [operations, program, Configure.output_pure, synth,
      NoteCommit.Main.currentRegion_operations, Circuit.operations_bind,
      Circuit.operations_pure, keygen_norm, keygen_spine]
    exact ⟨synthPieces_lookupSelectorAssignmentsAgree cfg input self,
      (CommitIvk.Canonicity.circuit
        (brWit input.ak 254 1) (brWit input.nk 254 1))
          |>.call_lookupSelectorAssignmentsAgree
            (cfg.gate, cfg.lookupConfig)
            (FormalCircuit.Configured.ofPure _ _ () (by rfl)) _ _⟩
  fixedWritesLawful := by
    intro cfg _ configured input self
    apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
    · simp only [Configure.output_pure, synth, Circuit.operations_bind,
        NoteCommit.Main.currentRegion_operations, Circuit.operations_pure,
        List.forall_append, circuit_norm]
      refine ⟨?_, ?_, ?_⟩
      · have hnoFixed : Operations.HasNoFixedWrites
            ((synthPieces cfg input.ak input.nk).operations self) := by
          apply FloorPlanner.SynthesisSummary.HasNoFixedWrites.hasNoFixedWrites
          rw [synthPieces_synthesisSummary_eq]
          exact synthPiecesSynthesisSummary_hasNoFixedWrites cfg
        exact (hnoFixed.fixedWritesLawful
          (constantColumns := [])).regionAssignmentsAgree
      · exact (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
          |>.call_fixedAssignmentsAgree
            (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) configured _ _
      · exact (CommitIvk.Canonicity.circuit
          (brWit input.ak 254 1) (brWit input.nk 254 1))
            |>.call_fixedAssignmentsAgree
              (cfg.gate, cfg.lookupConfig)
              (FormalCircuit.Configured.ofPure _ _ () (by rfl)) _ _
    · rw [synth_synthesisSummary_eq]
      exact synthesisSummary_tableRowExtent_eq cfg
  lookupActivationsWellFormed cfg input self := by
    simp only [synth, Circuit.operations_bind,
      NoteCommit.Main.currentRegion_operations,
      Circuit.operations_pure, Operations.LookupActivationsWellFormed,
      List.forall_append, List.forall_nil, true_and, and_true]
    exact ⟨synthPieces_lookupActivationsWellFormed cfg input self,
      (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
        |>.call_lookupActivationsWellFormed
          (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) _ _,
      (CommitIvk.Canonicity.circuit
        (brWit input.ak 254 1) (brWit input.nk 254 1))
          |>.call_lookupActivationsWellFormed
            (cfg.gate, cfg.lookupConfig) _ _⟩
  output cfg _ i := AssignedCell.of (i + 10) 1 cfg.addConfig.xQR
  regionCount _ := 14
  synthesisSummary cfg _ _ := synthesisSummary cfg
  output_eq := fun cfg input i => (synth_output G R Q hQ cfg input i).symm
  regionCount_eq cfg input i :=
    (synth_regionCount G R Q hQ cfg input i).symm
  synthesisSummary_eq cfg input region :=
    (synth_synthesisSummary_eq G R Q hQ cfg input region).symm

def EnvAssumptions (G : Generators) (cfg : Config)
    (env : Placed Environment Fp) : Prop :=
  Sinsemilla.GeneratorTableLoaded G cfg.hashConfig.generatorTable env.env ∧
  Ecc.MulFixed.FullWidth.EnvAssumptions cfg.mulConfig env ∧
  LookupRangeCheck.TableLoaded 10 cfg.lookupConfig env.env ∧
  cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

/-- The extracted `rivk` window data: the fixed-base mul's window readings and the
scalar they encode, inside the commit child (regions `i₀+7`/`i₀+8`). -/
def rivkExtract (cfg : Config) (_ : Var Inputs Fp) (i₀ : RegionIndex)
    (env : Placed Environment Fp) : Vector Fp 85 × Fq :=
  Ecc.MulFixed.FullWidth.fwExtract cfg.mulConfig (i₀ + 7) env

/-- Breaks-as-data `Commit^ivk` contract (zcash/ironwood#45): either the Sinsemilla
chain over the canonical `commit_ivk` chunks of `ak`/`nk` is defined and the output
is the extracted short commitment `(B + [rivk]R).x`, or the incomplete-addition
escape is exhibited as a valid break. -/
def Spec (G : Generators) (Q : Point Fp) (R : FixedBase)
    (input : Value Inputs Fp) (output : Value field Fp)
    (rivk : Vector Fp 85 × Fq) : Prop :=
  SpecOrBreak G.S Q
    (fun B => (output : Fp) = (B + (rivk.2 • R : Point Fp)).x)
    (hashToPointB G.S Q
      (commitIvkChunks (show Fp from input.ak).val (show Fp from input.nk).val))

/-- Honest-prover precondition: the canonical message hash is defined. The full-width
child derives and proves the 3-bit bounds for its scalar windows. -/
def ProverAssumptions (G : Generators) (Q : Point Fp)
    (input : ProverValue Inputs Fp) (_ : Vector Fp 85 × Fq)
    (_ : ProverHint Fp) : Prop :=
  ∃ B, hashToPoint G.S Q
    (commitIvkChunks (show Fp from input.ak).val (show Fp from input.nk).val) = some B

end Zcash.Circuits.CommitIvk.Main
