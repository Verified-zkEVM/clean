module

public import Clean.Ironwood.Poseidon.Rounds

@[expose] public section

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `Pow5Chip::permute` (lines 228-266): ONE region `"permute state"`; load the initial
  state (copy_advice ×3 at row 0), then `half_full_rounds = 4` full-round rows, then
  `half_partial_rounds = 28` partial-round rows (each two source rounds,
  `round = 4 + 2r`), then 4 more full-round rows (`round = 60 + r`). 37 rows total; the
  final state is read at row 36.

`Spec` is the donor's `Permute.value` (the 4+28+4 `Fin.foldl` schedule,
`Clean/Orchard/Poseidon/Pow5.lean`), at the ported P128Pow5T3 round constants.
-/

open ProvableStruct.Halo2 (eval_cells_eq_eval)

namespace Zcash.Circuits.Poseidon

open Halo2
open Poseidon
open Poseidon.Permute (State)
open Poseidon.Permute.P128Pow5T3 (mds mdsInv roundConstants)

private theorem fullRound_output_eq (r : ℕ) (cfg : Config) (o : ℕ)
    (input : Var unit Fp) (self : RegionIndex) :
    (fullRound r).output cfg o input self = stateRow cfg (o + 1) self := rfl

private theorem partialRound_output_eq (r : ℕ) (cfg : Config) (o : ℕ)
    (input : Var unit Fp) (self : RegionIndex) :
    (partialRound r).output cfg o input self = stateRow cfg (o + 1) self := rfl

def permuteSynthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  (FloorPlanner.RegionSynthesisSummary.ofColumns
      [.column .advice (cfg.state 0).index,
        .column .advice (cfg.state 1).index,
        .column .advice (cfg.state 2).index]
      (offset + 1) 0).combine
    ((FloorPlanner.RegionSynthesisSummary.repeatColumnsWithSelector cfg.sFull.index
      [.selector cfg.sFull.index,
        .column .fixed (cfg.rcA 0).index,
        .column .fixed (cfg.rcA 1).index,
        .column .fixed (cfg.rcA 2).index,
        .column .advice (cfg.state 0).index,
        .column .advice (cfg.state 1).index,
        .column .advice (cfg.state 2).index]
      offset 1 2 0 4).combine
      ((FloorPlanner.RegionSynthesisSummary.repeatColumnsWithSelector cfg.sPartial.index
        [.selector cfg.sPartial.index,
          .column .fixed (cfg.rcA 0).index,
          .column .fixed (cfg.rcA 1).index,
          .column .fixed (cfg.rcA 2).index,
          .column .advice cfg.partialSbox.index,
          .column .fixed (cfg.rcB 0).index,
          .column .fixed (cfg.rcB 1).index,
          .column .fixed (cfg.rcB 2).index,
          .column .advice (cfg.state 0).index,
          .column .advice (cfg.state 1).index,
          .column .advice (cfg.state 2).index]
        (offset + 4) 1 2 0 28).combine
        (FloorPlanner.RegionSynthesisSummary.repeatColumnsWithSelector cfg.sFull.index
          [.selector cfg.sFull.index,
            .column .fixed (cfg.rcA 0).index,
            .column .fixed (cfg.rcA 1).index,
            .column .fixed (cfg.rcA 2).index,
            .column .advice (cfg.state 0).index,
            .column .advice (cfg.state 1).index,
            .column .advice (cfg.state 2).index]
          (offset + 32) 1 2 0 4)))

@[circuit_norm]
def permuteSynthesize (cfg : Config) (offset : ℕ) (input : Var State Fp) :
    RegionCircuit Fp (Var State Fp) := do
  let _c0 ← copyAdvice input.x0 (cfg.state 0) offset
  let _c1 ← copyAdvice input.x1 (cfg.state 1) offset
  let _c2 ← copyAdvice input.x2 (cfg.state 2) offset
  RegionCircuit.forRange' offset 1 4 (fun r o => do
    let _ ← (fullRound r).call cfg o ()
    pure ())
  RegionCircuit.forRange' (offset + 4) 1 28 (fun r o => do
    let _ ← (partialRound (4 + 2 * r)).call cfg o ()
    pure ())
  RegionCircuit.forRange' (offset + 32) 1 4 (fun r o => do
    let _ ← (fullRound (60 + r)).call cfg o ()
    pure ())
  readStateRow cfg (offset + 36)

private theorem fullRound_state_mem_assignedCells (r : ℕ) (cfg : Config) (o : ℕ)
    (self : RegionIndex) (k : Fin 3) :
    Cell.of self (o + 1) (cfg.state k) ∈
      (((fullRound r).call cfg o ()).operations self).assignedCells self := by
  rw [FormalRegionCircuit.call_operations]
  fin_cases k <;>
    simp [fullRound, fullRoundSynthesize, circuit_norm, RegionOperations.assignedCells,
      RegionOperation.assignedCells]

private theorem partialRound_state_mem_assignedCells (r : ℕ) (cfg : Config) (o : ℕ)
    (self : RegionIndex) (k : Fin 3) :
    Cell.of self (o + 1) (cfg.state k) ∈
      (((partialRound r).call cfg o ()).operations self).assignedCells self := by
  rw [FormalRegionCircuit.call_operations]
  fin_cases k <;>
    simp [partialRound, partialRoundSynthesize, circuit_norm, RegionOperations.assignedCells,
      RegionOperation.assignedCells]

private theorem fullRound_adviceWrites_eq (r : ℕ) (cfg : Config) (o : ℕ) (self : RegionIndex) :
    (((fullRound r).call cfg o ()).operations self).adviceWrites =
      [(cfg.state 0, o + 1), (cfg.state 1, o + 1), (cfg.state 2, o + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  simp [fullRound, fullRoundSynthesize, circuit_norm, RegionOperations.adviceWrites,
    RegionOperation.adviceWrites]

private theorem partialRound_adviceWrites_eq (r : ℕ) (cfg : Config) (o : ℕ) (self : RegionIndex) :
    (((partialRound r).call cfg o ()).operations self).adviceWrites =
      [(cfg.partialSbox, o), (cfg.state 0, o + 1), (cfg.state 1, o + 1), (cfg.state 2, o + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  simp [partialRound, partialRoundSynthesize, circuit_norm, RegionOperations.adviceWrites,
    RegionOperation.adviceWrites]

private theorem fullRoundLoop_consumedCellsAssignedFrom
    (cfg : Config) (hconfig : cfg.FixedColumnsLawful) (base offset count : ℕ)
    (self : RegionIndex) (available : List Cell)
    (hinit : ∀ k : Fin 3, Cell.of self offset (cfg.state k) ∈ available) :
    ((RegionCircuit.forRange' offset 1 count (fun r o => do
      let _ ← (fullRound (base + r)).call cfg o ()
      pure ())).operations self).AssignedFrom RegionOperation.Consumes self available := by
  apply RegionCircuit.forRange'_assignedFrom_of_earlier_rounds
  · intro _
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil]
    apply (fullRound (base + 0)).call_consumedCellsAssignedFrom cfg
      (FormalRegionCircuit.Configured.ofPure (fullRound (base + 0)) cfg hconfig rfl)
    intro cell hcell
    simp only [FormalRegionCircuit.Configured.inputCells,
      FormalRegionCircuit.Configured.readCells,
      FormalRegionCircuit.Configured.readRelativeCellsAt,
      FormalRegionCircuit.Configured.ofPure,
      FormalRegionCircuit.keygenRequirements, ElaboratedRegionCircuit.keygenRequirements,
      fullRound, fullRoundElaborated, KeygenRequirements.readRelativeCellsAt,
      List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, Nat.add_zero] at hcell
    rcases hcell with rfl | rfl | rfl
    · exact hinit 0
    · exact hinit 1
    · exact hinit 2
  · intro i _
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
      Nat.mul_one]
    apply (fullRound (base + (i + 1))).call_consumedCellsAssignedFrom cfg
      (FormalRegionCircuit.Configured.ofPure (fullRound (base + (i + 1))) cfg hconfig rfl)
    intro cell hcell
    simp only [FormalRegionCircuit.Configured.inputCells,
      FormalRegionCircuit.Configured.readCells,
      FormalRegionCircuit.Configured.readRelativeCellsAt,
      FormalRegionCircuit.Configured.ofPure,
      FormalRegionCircuit.keygenRequirements, ElaboratedRegionCircuit.keygenRequirements,
      fullRound, fullRoundElaborated, KeygenRequirements.readRelativeCellsAt,
      List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, Nat.add_zero] at hcell
    rcases hcell with rfl | rfl | rfl
    · exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ i self available _
        (by simpa [Cell.of, RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one] using
          fullRound_state_mem_assignedCells (base + i) cfg (offset + i) self 0)
    · exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ i self available _
        (by simpa [Cell.of, RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one] using
          fullRound_state_mem_assignedCells (base + i) cfg (offset + i) self 1)
    · exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ i self available _
        (by simpa [Cell.of, RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one] using
          fullRound_state_mem_assignedCells (base + i) cfg (offset + i) self 2)

private theorem partialRoundLoop_consumedCellsAssignedFrom
    (cfg : Config) (hconfig : cfg.FixedColumnsLawful) (base offset count : ℕ)
    (self : RegionIndex) (available : List Cell)
    (hinit : ∀ k : Fin 3, Cell.of self offset (cfg.state k) ∈ available) :
    ((RegionCircuit.forRange' offset 1 count (fun r o => do
      let _ ← (partialRound (base + 2 * r)).call cfg o ()
      pure ())).operations self).AssignedFrom RegionOperation.Consumes self available := by
  apply RegionCircuit.forRange'_assignedFrom_of_earlier_rounds
  · intro _
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil]
    apply (partialRound (base + 2 * 0)).call_consumedCellsAssignedFrom cfg
      (FormalRegionCircuit.Configured.ofPure (partialRound (base + 2 * 0)) cfg hconfig rfl)
    intro cell hcell
    simp only [FormalRegionCircuit.Configured.inputCells,
      FormalRegionCircuit.Configured.readCells,
      FormalRegionCircuit.Configured.readRelativeCellsAt,
      FormalRegionCircuit.Configured.ofPure,
      FormalRegionCircuit.keygenRequirements, ElaboratedRegionCircuit.keygenRequirements,
      partialRound, partialRoundElaborated, KeygenRequirements.readRelativeCellsAt,
      List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, Nat.add_zero] at hcell
    rcases hcell with rfl | rfl | rfl
    · exact hinit 0
    · exact hinit 1
    · exact hinit 2
  · intro i _
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
      Nat.mul_one]
    apply (partialRound (base + 2 * (i + 1))).call_consumedCellsAssignedFrom cfg
      (FormalRegionCircuit.Configured.ofPure (partialRound (base + 2 * (i + 1))) cfg hconfig rfl)
    intro cell hcell
    simp only [FormalRegionCircuit.Configured.inputCells,
      FormalRegionCircuit.Configured.readCells,
      FormalRegionCircuit.Configured.readRelativeCellsAt,
      FormalRegionCircuit.Configured.ofPure,
      FormalRegionCircuit.keygenRequirements, ElaboratedRegionCircuit.keygenRequirements,
      partialRound, partialRoundElaborated, KeygenRequirements.readRelativeCellsAt,
      List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, Nat.add_zero] at hcell
    rcases hcell with rfl | rfl | rfl
    · exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ i self available _
        (by simpa [Cell.of, RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one] using
          partialRound_state_mem_assignedCells (base + 2 * i) cfg (offset + i) self 0)
    · exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ i self available _
        (by simpa [Cell.of, RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one] using
          partialRound_state_mem_assignedCells (base + 2 * i) cfg (offset + i) self 1)
    · exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ i self available _
        (by simpa [Cell.of, RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one] using
          partialRound_state_mem_assignedCells (base + 2 * i) cfg (offset + i) self 2)

@[reducible]
def permuteElaborated :
    ElaboratedRegionCircuit Fp Config Config State State pure
      permuteSynthesize :=
  { keygenRequirements :=
      { configLawful cfg := Config.FixedColumnsLawful cfg
        gates cfg _ := [fullRoundGate cfg, partialRoundsGate cfg]
        fixedColumns cfg _ := cfg.fixedColumns
        permutationColumns cfg _ :=
          [cfg.state 0, cfg.state 1, cfg.state 2]
        inputCells _ _ input :=
          [input.x0.cell, input.x1.cell, input.x2.cell] }
    adviceColumnRequirements cfg :=
      ColumnsDistinct [cfg.state 0, cfg.state 1, cfg.state 2, cfg.partialSbox]
    output cfg offset _ self := stateRow cfg (offset + 36) self
    synthesisSummary cfg offset _ _ :=
      permuteSynthesisSummary cfg offset
    synthesisSummary_eq := by
      intro cfg offset input self
      simp only [permuteSynthesisSummary]
      rw [← FloorPlanner.RegionSynthesisSummary.foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector,
        ← FloorPlanner.RegionSynthesisSummary.foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector,
        ← FloorPlanner.RegionSynthesisSummary.foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector]
      apply FloorPlanner.RegionSynthesisSummary.ext
      · simp only [permuteSynthesize, fullRoundSynthesisSummary,
          partialRoundSynthesisSummary, circuit_norm, synthesis_summary_norm,
          Nat.mul_one, FloorPlanner.RegionSynthesisSummary.ofColumns_columns]
      · simp only [permuteSynthesize, fullRoundSynthesisSummary,
          partialRoundSynthesisSummary, circuit_norm, synthesis_summary_norm,
          Nat.mul_one, FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
        omega
      · simp only [permuteSynthesize, fullRoundSynthesisSummary,
          partialRoundSynthesisSummary, circuit_norm, synthesis_summary_norm,
          Nat.mul_one,
          FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]
      · simp only [permuteSynthesize, fullRoundSynthesisSummary,
          partialRoundSynthesisSummary, circuit_norm, synthesis_summary_norm,
          Nat.mul_one]
      · simp only [permuteSynthesize, fullRoundSynthesisSummary,
          partialRoundSynthesisSummary, circuit_norm, synthesis_summary_norm,
          Nat.mul_one]
      · simp only [permuteSynthesize, fullRoundSynthesisSummary,
          partialRoundSynthesisSummary, circuit_norm, synthesis_summary_norm,
          Nat.mul_one]
    output_eq := by
      intro _ _ _ _
      simp only [permuteSynthesize, circuit_norm]
    fixedAssignmentsAgree := by
      intro configInput counts hconfig offset input region
      have hfirst :
          ((RegionCircuit.forRange' offset 1 4 fun r o => do
            let _ ← (fullRound r).call configInput o ()
            pure ()).operations region).FixedAssignmentsAgree := by
        apply RegionCircuit.forRange'_fixedAssignmentsAgree
        · intro i
          simpa only [FormalRegionCircuit.call_operations, fullRound, partialRound, Configure.output_pure,
              RegionCircuit.operations_bind, RegionCircuit.operations_pure,
              List.append_nil]
            using (fullRound i.val).elaborated.fixedAssignmentsAgree
              configInput counts hconfig (offset + i.val * 1) () region
        · intro i column row value hassignment
          simp only [RegionCircuit.operations_bind,
            RegionCircuit.operations_pure, List.append_nil] at hassignment
          exact fullRound_assignFixed_row i.val configInput
            (offset + i.val * 1) () region column row value hassignment
      have hpartial :
          ((RegionCircuit.forRange' (offset + 4) 1 28 fun r o => do
            let _ ← (partialRound (4 + 2 * r)).call configInput o ()
            pure ()).operations region).FixedAssignmentsAgree := by
        apply RegionCircuit.forRange'_fixedAssignmentsAgree
        · intro i
          simpa only [FormalRegionCircuit.call_operations, fullRound, partialRound, Configure.output_pure,
              RegionCircuit.operations_bind, RegionCircuit.operations_pure,
              List.append_nil]
            using (partialRound (4 + 2 * i.val)).elaborated.fixedAssignmentsAgree
              configInput counts hconfig (offset + 4 + i.val * 1) () region
        · intro i column row value hassignment
          simp only [RegionCircuit.operations_bind,
            RegionCircuit.operations_pure, List.append_nil] at hassignment
          exact partialRound_assignFixed_row (4 + 2 * i.val) configInput
            (offset + 4 + i.val * 1) () region column row value hassignment
      have hlast :
          ((RegionCircuit.forRange' (offset + 32) 1 4 fun r o => do
            let _ ← (fullRound (60 + r)).call configInput o ()
            pure ()).operations region).FixedAssignmentsAgree := by
        apply RegionCircuit.forRange'_fixedAssignmentsAgree
        · intro i
          simpa only [FormalRegionCircuit.call_operations, fullRound, partialRound, Configure.output_pure,
              RegionCircuit.operations_bind, RegionCircuit.operations_pure,
              List.append_nil]
            using (fullRound (60 + i.val)).elaborated.fixedAssignmentsAgree
              configInput counts hconfig (offset + 32 + i.val * 1) () region
        · intro i column row value hassignment
          simp only [RegionCircuit.operations_bind,
            RegionCircuit.operations_pure, List.append_nil] at hassignment
          exact fullRound_assignFixed_row (60 + i.val) configInput
            (offset + 32 + i.val * 1) () region column row value hassignment
      have hfirstBounds : ∀ column row value,
          .assignFixed column row value ∈
              (RegionCircuit.forRange' offset 1 4 (fun r o => do
                let _ ← (fullRound r).call configInput o ()
                pure ())).operations region →
            offset ≤ row ∧ row < offset + 4 := by
        apply RegionCircuit.forRange'_assignFixed_row_bounds
        intro i column row value hassignment
        simp only [RegionCircuit.operations_bind,
          RegionCircuit.operations_pure, List.append_nil] at hassignment
        exact fullRound_assignFixed_row i.val configInput
          (offset + i.val * 1) () region column row value hassignment
      have hpartialBounds : ∀ column row value,
          .assignFixed column row value ∈
              (RegionCircuit.forRange' (offset + 4) 1 28 (fun r o => do
                let _ ← (partialRound (4 + 2 * r)).call configInput o ()
                pure ())).operations region →
            offset + 4 ≤ row ∧ row < offset + 32 := by
        intro column row value hassignment
        have hbounds := RegionCircuit.forRange'_assignFixed_row_bounds
          (offset + 4) 28 _ region
          (fun i column row value hassignment => by
            simp only [RegionCircuit.operations_bind,
              RegionCircuit.operations_pure, List.append_nil] at hassignment
            exact partialRound_assignFixed_row (4 + 2 * i.val) configInput
              (offset + 4 + i.val * 1) () region column row value hassignment)
          column row value hassignment
        omega
      have hlastBounds : ∀ column row value,
          .assignFixed column row value ∈
              (RegionCircuit.forRange' (offset + 32) 1 4 (fun r o => do
                let _ ← (fullRound (60 + r)).call configInput o ()
                pure ())).operations region →
            offset + 32 ≤ row ∧ row < offset + 36 := by
        intro column row value hassignment
        have hbounds := RegionCircuit.forRange'_assignFixed_row_bounds
          (offset + 32) 4 _ region
          (fun i column row value hassignment => by
            simp only [RegionCircuit.operations_bind,
              RegionCircuit.operations_pure, List.append_nil] at hassignment
            exact fullRound_assignFixed_row (60 + i.val) configInput
              (offset + 32 + i.val * 1) () region column row value hassignment)
          column row value hassignment
        omega
      unfold RegionOperations.FixedAssignmentsAgree
      intro column row left right hleft hright
      simp only [Configure.output_pure, permuteSynthesize,
        RegionCircuit.operations_bind, operations_copyAdvice] at hleft hright
      rw [operations_readStateRow] at hleft hright
      simp at hleft hright
      rcases hleft with hleft | hleft | hleft <;>
        rcases hright with hright | hright | hright
      · exact hfirst column row left right hleft hright
      · have hleftBounds := hfirstBounds column row left hleft
        have hrightBounds := hpartialBounds column row right hright
        omega
      · have hleftBounds := hfirstBounds column row left hleft
        have hrightBounds := hlastBounds column row right hright
        omega
      · have hleftBounds := hpartialBounds column row left hleft
        have hrightBounds := hfirstBounds column row right hright
        omega
      · exact hpartial column row left right hleft hright
      · have hleftBounds := hpartialBounds column row left hleft
        have hrightBounds := hlastBounds column row right hright
        omega
      · have hleftBounds := hlastBounds column row left hleft
        have hrightBounds := hfirstBounds column row right hright
        omega
      · have hleftBounds := hlastBounds column row left hleft
        have hrightBounds := hpartialBounds column row right hright
        omega
      · exact hlast column row left right hleft hright
    consumedCellsAssigned := by
      intro configInput counts hconfig offset input region
      have hreadOps : ∀ o, @RegionCircuit.operations Fp _ (Var State Fp)
          (readStateRow configInput o) region = [] := fun _ => rfl
      simp only [Configure.output_pure, permuteSynthesize, RegionCircuit.operations_bind,
        operations_copyAdvice, hreadOps,
        RegionOperations.ConsumedCellsAssigned,
        RegionOperations.assignedFrom_append_iff, List.append_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · keygen_registration
      · keygen_registration
      · keygen_registration
      · simpa only [Nat.zero_add] using
          fullRoundLoop_consumedCellsAssignedFrom configInput hconfig 0 offset 4 region _ (by
            intro k
            fin_cases k <;> simp [RegionOperations.assignedCellsAfter, RegionOperation.assignedCells])
      · apply partialRoundLoop_consumedCellsAssignedFrom configInput hconfig 4 (offset + 4) 28 region
        intro k
        exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ 3 region _ _ (by
          simpa [RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one,
            Nat.add_assoc] using fullRound_state_mem_assignedCells 3 configInput (offset + 3) region k)
      · apply fullRoundLoop_consumedCellsAssignedFrom configInput hconfig 60 (offset + 32) 4 region
        intro k
        exact RegionCircuit.mem_assignedCellsAfter_loopAux_succ_of_mem_round _ _ 27 region _ _ (by
          simpa [RegionCircuit.operations_bind, RegionCircuit.operations_pure, Nat.mul_one,
            Nat.add_assoc] using
            partialRound_state_mem_assignedCells (4 + 2 * 27) configInput (offset + 4 + 27) region k)
    adviceWritesConsistent := by
      intro configInput counts hconfig hadvice offset input region
      apply RegionOperations.AdviceWritesDistinct.toConsistent
      have hreadOps : ∀ o, @RegionCircuit.operations Fp _ (Var State Fp)
          (readStateRow configInput o) region = [] := fun _ => rfl
      simp only [Configure.output_pure, ColumnsDistinct, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true,
        List.nodup_nil] at hadvice
      obtain ⟨⟨h01, h02, h0p⟩, ⟨h12, h1p⟩, h2p⟩ := hadvice
      have hfullLoop : ∀ base baseOff cnt,
          ((RegionCircuit.forRange' baseOff 1 cnt (fun r o => do
            let _ ← (fullRound (base + r)).call configInput o ()
            pure ())).operations region).AdviceWritesDistinct := by
        intro base baseOff cnt
        apply RegionCircuit.forRange'_adviceWritesDistinct_of_disjoint
        · intro i
          simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
            RegionOperations.AdviceWritesDistinct, fullRound_adviceWrites_eq, List.nodup_cons,
            List.mem_cons, List.not_mem_nil, Prod.mk.injEq, not_or, List.nodup_nil,
            and_true, not_false_eq_true, or_false]
          exact ⟨⟨h01, h02⟩, h12⟩
        · intro i j hij
          rw [List.disjoint_left]
          intro entry hi hj
          simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
            fullRound_adviceWrites_eq, List.mem_cons, List.not_mem_nil, or_false] at hi hj
          rcases hi with rfl | rfl | rfl <;> rcases hj with h | h | h <;>
            simp only [Prod.mk.injEq] at h <;> omega
      have hfullBounds : ∀ base baseOff cnt col row,
          (col, row) ∈ ((RegionCircuit.forRange' baseOff 1 cnt (fun r o => do
            let _ ← (fullRound (base + r)).call configInput o ()
            pure ())).operations region).adviceWrites →
            baseOff + 1 ≤ row ∧ row ≤ baseOff + cnt ∧ col ≠ configInput.partialSbox := by
        intro base baseOff cnt col row hmem
        obtain ⟨i, hi⟩ := (RegionCircuit.mem_forRange'_adviceWrites_iff baseOff 1 cnt _
          region col row).mp hmem
        have hi_lt := i.isLt
        simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
          fullRound_adviceWrites_eq, List.mem_cons, List.not_mem_nil, or_false,
          Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨by omega, by omega, h0p⟩
        · exact ⟨by omega, by omega, h1p⟩
        · exact ⟨by omega, by omega, h2p⟩
      have hpartLoop :
          ((RegionCircuit.forRange' (offset + 4) 1 28 (fun r o => do
            let _ ← (partialRound (4 + 2 * r)).call configInput o ()
            pure ())).operations region).AdviceWritesDistinct := by
        apply RegionCircuit.forRange'_adviceWritesDistinct_of_disjoint
        · intro i
          simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
            RegionOperations.AdviceWritesDistinct, partialRound_adviceWrites_eq, List.nodup_cons,
            List.mem_cons, List.not_mem_nil, Prod.mk.injEq, not_or, not_and, List.nodup_nil,
            and_true, not_false_eq_true, or_false]
          refine ⟨⟨fun _ h => by omega, fun _ h => by omega, fun _ h => by omega⟩,
            ⟨h01, h02⟩, h12⟩
        · intro i j hij
          rw [List.disjoint_left]
          intro entry hi hj
          simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
            partialRound_adviceWrites_eq, List.mem_cons, List.not_mem_nil, or_false] at hi hj
          rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with h | h | h | h <;>
            simp only [Prod.mk.injEq] at h
          all_goals
            first
            | omega
            | exact h0p h.1
            | exact h1p h.1
            | exact h2p h.1
      have hpartBounds : ∀ col row,
          (col, row) ∈ ((RegionCircuit.forRange' (offset + 4) 1 28 (fun r o => do
            let _ ← (partialRound (4 + 2 * r)).call configInput o ()
            pure ())).operations region).adviceWrites →
            (col = configInput.partialSbox ∧ offset + 4 ≤ row ∧ row ≤ offset + 31) ∨
            (col ≠ configInput.partialSbox ∧ offset + 5 ≤ row ∧ row ≤ offset + 32) := by
        intro col row hmem
        obtain ⟨i, hi⟩ := (RegionCircuit.mem_forRange'_adviceWrites_iff (offset + 4) 1 28 _
          region col row).mp hmem
        have hi_lt := i.isLt
        simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
          partialRound_adviceWrites_eq, List.mem_cons, List.not_mem_nil, or_false,
          Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, by omega, by omega⟩
        · exact Or.inr ⟨h0p, by omega, by omega⟩
        · exact Or.inr ⟨h1p, by omega, by omega⟩
        · exact Or.inr ⟨h2p, by omega, by omega⟩
      simp only [Configure.output_pure, permuteSynthesize, RegionCircuit.operations_bind,
        operations_copyAdvice, hreadOps,
        List.nil_append, List.append_nil, List.cons_append,
        RegionOperations.adviceWritesDistinct_assignAdvice_cons,
        RegionOperations.adviceWritesDistinct_constrainEqual_cons,
        RegionOperations.adviceWritesDistinct_append_iff,
        RegionOperations.adviceWrites_append, RegionOperations.adviceWrites_cons,
        RegionOperation.adviceWrites_assignAdvice,
        RegionOperation.adviceWrites_constrainEqual, List.mem_append, List.mem_cons,
        not_or, Prod.mk.injEq, and_true]
      refine ⟨⟨h01, h02, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩,
        ⟨h12, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩,
        ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_⟩,
        by simpa only [Nat.zero_add] using hfullLoop 0 offset 4,
        ⟨hpartLoop, hfullLoop 60 (offset + 32) 4, ?_⟩, ?_⟩
      · have hb := hfullBounds 0 offset 4 _ _ (by simpa only [Nat.zero_add] using hm); omega
      · rcases hpartBounds _ _ hm with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega
      · have hb := hfullBounds 60 (offset + 32) 4 _ _ hm; omega
      · have hb := hfullBounds 0 offset 4 _ _ (by simpa only [Nat.zero_add] using hm); omega
      · rcases hpartBounds _ _ hm with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega
      · have hb := hfullBounds 60 (offset + 32) 4 _ _ hm; omega
      · have hb := hfullBounds 0 offset 4 _ _ (by simpa only [Nat.zero_add] using hm); omega
      · rcases hpartBounds _ _ hm with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega
      · have hb := hfullBounds 60 (offset + 32) 4 _ _ hm; omega
      · rw [List.disjoint_left]
        rintro ⟨col, row⟩ hp hf
        have hfb := hfullBounds 60 (offset + 32) 4 col row hf
        rcases hpartBounds col row hp with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> omega
      · rw [List.disjoint_left]
        rintro ⟨col, row⟩ hf1 hrest
        have hb1 := hfullBounds 0 offset 4 col row (by simpa only [Nat.zero_add] using hf1)
        rw [List.mem_append] at hrest
        rcases hrest with hp | hf2
        · rcases hpartBounds col row hp with ⟨heq, _, _⟩ | ⟨_, hlo, _⟩
          · exact hb1.2.2 heq
          · omega
        · have hb2 := hfullBounds 60 (offset + 32) 4 col row hf2
          omega }

/-- Chain a per-row step family into a `Fin.foldl` (the donor `Permute.value` shape). -/
private theorem foldl_of_steps (f : ℕ → State Fp → State Fp) (st : ℕ → State Fp)
    (base : ℕ) : ∀ n : ℕ,
    (∀ i : ℕ, i < n → st (base + i + 1) = f i (st (base + i))) →
    st (base + n) = Fin.foldl n (fun s (i : Fin n) => f ↑i s) (st base)
  | 0, _ => by simp
  | n + 1, h => by
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← foldl_of_steps f st base n (fun i hi => h i (by omega)),
      show base + (n + 1) = base + n + 1 from rfl]
    exact h n (by omega)

/-- Rust `Pow5Chip::permute`'s region body (`pow5.rs:235-265`): load the state, 4 full
rounds, 28 double partial rounds, 4 full rounds. `Spec`: the outgoing state is the donor
`Permute.value` of the incoming one. -/
def permuteRegion : FormalRegionCircuit Fp Config Config State State where
  configure := pure
  synthesize := permuteSynthesize
  elaborated := permuteElaborated

  Spec input output _ := output = Permute.value roundConstants input

  ProverSpec input output _ _ := output = Permute.value roundConstants input

  soundness := by
    circuit_proof_start
    obtain ⟨hcp0, hcp1, hcp2, hfullA, hpart, hfullB⟩ := hc
    simp only [fullRound_envAssumptions_eq, fullRound_assumptions_eq, fullRound_spec_eq,
      fullRound_extract_eq, fullRound_output_eq, partialRound_envAssumptions_eq,
      partialRound_assumptions_eq, partialRound_spec_eq, partialRound_extract_eq,
      partialRound_output_eq, eval_cells_eq_eval, forall_const,
      mul_one] at hfullA hpart hfullB
    -- the row-value family
    set st : ℕ → State Fp := fun k =>
      ProvableStruct.Halo2.eval place env (stateRow cfg (offset + k) self) with hst
    -- per-phase step facts on the family
    have hstepA : ∀ i : ℕ, i < 4 →
        st (0 + i + 1) = FullRound.value (FullRound.params roundConstants mds i)
          (st (0 + i)) := by
      intro i hi
      have h := hfullA ⟨i, hi⟩
      simp only [hst, Nat.zero_add]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepB : ∀ i : ℕ, i < 28 →
        st (4 + i + 1) = PartialRounds.value
          (PartialRounds.paramsP128 roundConstants (4 + 2 * i)) (st (4 + i)) := by
      intro i hi
      have h := hpart ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepC : ∀ i : ℕ, i < 4 →
        st (32 + i + 1) = FullRound.value
          (FullRound.params roundConstants mds (60 + i)) (st (32 + i)) := by
      intro i hi
      have h := hfullB ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    -- endpoints
    have h0 : st 0 = { x0 := input_x0, x1 := input_x1, x2 := input_x2 } := by
      simp only [hst, Nat.add_zero]
      rw [show (ProvableStruct.Halo2.eval place env (stateRow cfg offset self)
          : State Fp)
        = { x0 := env.advice (cfg.state 0) ((place self + offset : ℕ) : ℤ),
            x1 := env.advice (cfg.state 1) ((place self + offset : ℕ) : ℤ),
            x2 := env.advice (cfg.state 2) ((place self + offset : ℕ) : ℤ) }
        from by simp only [stateRow, circuit_norm]]
      rw [hcp0, hcp1, hcp2]
    have h36 : st 36 = { x0 := output_x0, x1 := output_x1, x2 := output_x2 } := h_output
    -- assemble the three folds
    have hA := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds i)) st 0 4 hstepA
    have hB := foldl_of_steps
      (fun i => PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i)))
      st 4 28 hstepB
    have hC := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds (60 + i))) st 32 4
      hstepC
    rw [← h36, ← h0]
    show st (32 + 4) = Permute.value roundConstants (st 0)
    rw [hC, show (32 : ℕ) = 4 + 28 from rfl, hB, show (4 : ℕ) = 0 + 4 from rfl, hA]
    rfl

  completeness := by
    circuit_proof_start
    obtain ⟨hw0, hw1, hw2, hwA, hwB, hwC⟩ := hwit
    -- per-chunk derived contracts (verifier-view Spec is all we need for the chain)
    have hdA := fun i : Fin 4 => (SubcircuitRw.region_completeness_derived
      (fullRound ↑i) cfg (offset + ↑i * 1) self place env () (hwA i)
      trivial trivial trivial).1
    have hdB := fun i : Fin 28 => (SubcircuitRw.region_completeness_derived
      (partialRound (4 + 2 * ↑i)) cfg (offset + 4 + ↑i * 1) self place env ()
      (hwB i) trivial trivial trivial).1
    have hdC := fun i : Fin 4 => (SubcircuitRw.region_completeness_derived
      (fullRound (60 + ↑i)) cfg (offset + 32 + ↑i * 1) self place env ()
      (hwC i) trivial trivial trivial).1
    simp only [fullRound_spec_eq, fullRound_extract_eq, fullRound_output_eq,
      partialRound_spec_eq, partialRound_extract_eq, partialRound_output_eq,
      eval_cells_eq_eval, mul_one] at hdA hdB hdC
    -- the row-value family (verifier view of the honest environment)
    set st : ℕ → State Fp := fun k =>
      ProvableStruct.Halo2.eval place env.toEnvironment (stateRow cfg (offset + k) self)
      with hst
    have hstepA : ∀ i : ℕ, i < 4 →
        st (0 + i + 1) = FullRound.value (FullRound.params roundConstants mds i)
          (st (0 + i)) := by
      intro i hi
      have h := hdA ⟨i, hi⟩
      simp only [hst, Nat.zero_add]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepB : ∀ i : ℕ, i < 28 →
        st (4 + i + 1) = PartialRounds.value
          (PartialRounds.paramsP128 roundConstants (4 + 2 * i)) (st (4 + i)) := by
      intro i hi
      have h := hdB ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepC : ∀ i : ℕ, i < 4 →
        st (32 + i + 1) = FullRound.value
          (FullRound.params roundConstants mds (60 + i)) (st (32 + i)) := by
      intro i hi
      have h := hdC ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    have h0 : st 0 = { x0 := input_x0, x1 := input_x1, x2 := input_x2 } := by
      simp only [hst, Nat.add_zero]
      rw [show (ProvableStruct.Halo2.eval place env.toEnvironment
          (stateRow cfg offset self) : State Fp)
        = { x0 := env.advice (cfg.state 0) ((place self + offset : ℕ) : ℤ),
            x1 := env.advice (cfg.state 1) ((place self + offset : ℕ) : ℤ),
            x2 := env.advice (cfg.state 2) ((place self + offset : ℕ) : ℤ) }
        from by simp only [stateRow, circuit_norm]]
      rw [hw0, hw1, hw2]
    have h36 : st 36 = { x0 := output_x0, x1 := output_x1, x2 := output_x2 } := h_output
    have hA := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds i)) st 0 4 hstepA
    have hB := foldl_of_steps
      (fun i => PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i)))
      st 4 28 hstepB
    have hC := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds (60 + i))) st 32 4
      hstepC
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      have hleaf := SubcircuitRw.region_completeness_leaf_placed (fullRound ↑i) cfg
        (offset + ↑i * 1) self (⟨place, env⟩ : Placed ProverEnvironment Fp) () (hwA i)
      rw [fullRound_envAssumptions_eq, fullRound_assumptions_eq,
        fullRound_proverAssumptions_eq] at hleaf
      exact hleaf ⟨trivial, trivial, trivial⟩
    · intro i
      have hleaf := SubcircuitRw.region_completeness_leaf_placed
        (partialRound (4 + 2 * ↑i)) cfg (offset + 4 + ↑i * 1) self (⟨place, env⟩ : Placed ProverEnvironment Fp) () (hwB i)
      rw [partialRound_envAssumptions_eq, partialRound_assumptions_eq,
        partialRound_proverAssumptions_eq] at hleaf
      exact hleaf ⟨trivial, trivial, trivial⟩
    · intro i
      have hleaf := SubcircuitRw.region_completeness_leaf_placed (fullRound (60 + ↑i))
        cfg (offset + 32 + ↑i * 1) self (⟨place, env⟩ : Placed ProverEnvironment Fp) () (hwC i)
      rw [fullRound_envAssumptions_eq, fullRound_assumptions_eq,
        fullRound_proverAssumptions_eq] at hleaf
      exact hleaf ⟨trivial, trivial, trivial⟩
    rw [← h36, ← h0]
    show st (32 + 4) = Permute.value roundConstants (st 0)
    rw [hC, show (32 : ℕ) = 4 + 28 from rfl, hB, show (4 : ℕ) = 0 + 4 from rfl, hA]
    rfl

/-- The permutation bundle exposes its already-reduced synthesis footprint. -/
@[synthesis_summary_norm]
theorem permuteRegion_synthesisSummary (cfg : Config) (offset : ℕ)
    (input : Var State Fp) (self : RegionIndex) :
    permuteRegion.elaborated.synthesisSummary cfg offset input self =
      permuteSynthesisSummary cfg offset := rfl

@[keygen_norm]
theorem permuteRegion_inputCells (cfg : Config)
    (hconfigured : permuteRegion.Configured cfg) (input : Var State Fp) :
    FormalRegionCircuit.Configured.inputCells hconfigured input =
      [input.x0.cell, input.x1.cell, input.x2.cell] := rfl

/-- Every coordinate returned by the Poseidon permutation is assigned by its final
full round. The proof only opens the four-round tail, not the 28-round middle loop. -/
theorem permuteRegion_output_cells_assigned (cfg : Config) (offset : ℕ)
    (input : Var State Fp) (self : RegionIndex) (available : List Cell) :
    let output := permuteRegion.output cfg offset input self
    output.x0.cell ∈
        ((permuteRegion.call cfg offset input).operations self
          |>.assignedCellsAfter self available) ∧
      output.x1.cell ∈
        ((permuteRegion.call cfg offset input).operations self
          |>.assignedCellsAfter self available) ∧
      output.x2.cell ∈
        ((permuteRegion.call cfg offset input).operations self
          |>.assignedCellsAfter self available) := by
  rw [show permuteRegion.output cfg offset input self =
      stateRow cfg (offset + 36) self from rfl]
  rw [FormalRegionCircuit.call_operations]
  simp only [permuteRegion, permuteSynthesize, RegionCircuit.operations_bind,
    circuit_norm, RegionOperations.mem_assignedCellsAfter_iff,
    RegionOperations.assignedCells, List.flatMap_append, List.flatMap_cons,
    RegionOperation.assignedCells, List.singleton_append, List.mem_append,
    List.mem_cons]
  repeat' apply And.intro
  all_goals right
  all_goals right
  all_goals right
  all_goals right
  all_goals right
  all_goals right
  all_goals rw [RegionCircuit.forRange'_operations]
  all_goals simp only [List.ofFn, Fin.foldr_succ, Fin.foldr_zero,
    List.flatten_cons, List.flatten_nil, List.append_nil,
    List.flatMap_append, List.mem_append]
  all_goals right
  all_goals right
  all_goals right
  all_goals
    have h := fullRound_output_cells_assigned 63 cfg (offset + 35) () self []
    simp only [RegionOperations.mem_assignedCellsAfter_iff, List.nil_append] at h
    first
      | simpa only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
          Nat.mul_one, Nat.add_assoc, Fin.val_succ, Fin.val_zero, Nat.reduceAdd,
          fullRound_output_eq, RegionOperations.assignedCells, RegionCircuit.operations,
          FormalRegionCircuit.call, Bind.bind, Pure.pure, Var, CircuitTypeOver.Var,
          ProvableType.Halo2.toCircuitType, explicit_provable_type] using h.1
      | simpa only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
          Nat.mul_one, Nat.add_assoc, Fin.val_succ, Fin.val_zero, Nat.reduceAdd,
          fullRound_output_eq, RegionOperations.assignedCells, RegionCircuit.operations,
          FormalRegionCircuit.call, Bind.bind, Pure.pure, Var, CircuitTypeOver.Var,
          ProvableType.Halo2.toCircuitType, explicit_provable_type] using h.2.1
      | simpa only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil,
          Nat.mul_one, Nat.add_assoc, Fin.val_succ, Fin.val_zero, Nat.reduceAdd,
          fullRound_output_eq, RegionOperations.assignedCells, RegionCircuit.operations,
          FormalRegionCircuit.call, Bind.bind, Pure.pure, Var, CircuitTypeOver.Var,
          ProvableType.Halo2.toCircuitType, explicit_provable_type] using h.2.2

derive_contract_bridges permuteRegion := permuteRegion

end Zcash.Circuits.Poseidon
