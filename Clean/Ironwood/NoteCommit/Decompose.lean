import Clean.Ironwood.NoteCommit.Gates
import Clean.Ironwood.NoteCommit.DecomposeTheorems

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/note_commit.rs` — the five `Decompose*::assign` regions
(`"NoteCommit MessagePiece b"` 179-215, `d` 297-340, `e` 418-448, `g` 540-575,
`h` 660-694): enable the gate at row 0, copy the piece and the externally-constrained
subpieces in, assign the in-gate boolean subpiece (returned; `e` assigns nothing).

The semantic contracts are the phase-1 gate specs
(`Clean/Orchard/Action/Decompose.lean`, `Decompose{B,D,E,G,H}.Gate.Spec`) verbatim: the
booleanity of the in-gate bits plus the piece decomposition identity. Externally-provided
range facts stay OUT of these bundles (they are the callers' rely-conditions, threaded at
the composite level exactly as in phase 1).
-/

namespace Zcash.Circuits.NoteCommit

open Halo2

/-- `v·(1−v) = 0` pins a boolean. -/
private theorem isBool_of_boolCheck {v : Fp} (h : v * (1 - v) = 0) : IsBool v := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination -h1)

namespace DecomposeB

/-- The copied-in cells: the piece and the externally-constrained subpieces. -/
structure Inputs (F : Type) where
  b : F
  b0 : F
  b2 : F
  b3 : F
deriving ProvableStruct

def synthesisSummary (config : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector config.qNotecommitB.index,
      .column .advice config.colL.index,
      .column .advice config.colM.index,
      .column .advice config.colR.index,
      .column .advice config.colM.index,
      .column .advice config.colR.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (config : Config) (offset : ℕ) :
    (synthesisSummary config offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

/-- Rust `DecomposeB::assign` (`note_commit.rs:179-215`), parameterized by the `b_1`
witness program (Rust: `RangeConstrained::bitrange_of(gd_x, 254..255)`). Output is the
witnessed `b_1` cell; `Spec` is the donor `DecomposeB.Gate.Spec`. -/
def bundle (wb1 : WitgenIR Fp 1) : FormalRegionCircuit Fp Config Config Inputs field where
  configure := pure
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR]
          inputCells _ _ input :=
            [input.b.cell, input.b0.cell, input.b2.cell, input.b3.cell] }
      synthesisSummary config offset _ _ :=
        synthesisSummary config offset
      synthesisSummary_eq := by
        intro _ _ _ _
        unfold synthesisSummary
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [circuit_norm, gate, List.flatMap_cons, List.flatMap_nil,
            FloorPlanner.regionOperationShapeColumns, List.append_nil,
            List.nil_append, List.singleton_append]
        · simp only [circuit_norm]
          omega
        · simp only [circuit_norm]
        · simp only [circuit_norm, synthesis_summary_norm]
        · simp only [circuit_norm, synthesis_summary_norm] }

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    (gate cfg).enable offset
    let _b ← copyAdvice input.b cfg.colL offset
    let _b0 ← copyAdvice input.b0 cfg.colM offset
    let b1 ← assignAdvice cfg.colR offset wb1
    let _b2 ← copyAdvice input.b2 cfg.colM (offset + 1)
    let _b3 ← copyAdvice input.b3 cfg.colR (offset + 1)
    pure b1

  Witness := field
  extract cfg offset _ self env :=
    eval env (AssignedCell.of self offset cfg.colR : Var field Fp)

  Spec := fun input (out : Fp) _ => IsBool out ∧ IsBool input.b2 ∧
    input.b = input.b0 + out * 16 + input.b2 * 32 + input.b3 * 64

  ProverAssumptions := fun input (wit : Fp) _ => IsBool wit ∧ IsBool input.b2 ∧
    input.b = input.b0 + wit * 16 + input.b2 * 32 + input.b3 * 64

  ProverSpec := fun _ (out : Fp) (wit : Fp) _ => out = wit

  soundness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨⟨hb1, hb2, hdec⟩, hcb, hcb0, hcb2, hcb3⟩ := hc
    rw [hcb2] at hb2
    rw [hcb, hcb0, hcb2, hcb3] at hdec
    exact ⟨isBool_of_boolCheck hb1, isBool_of_boolCheck hb2,
      by linear_combination hdec⟩

  completeness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨hpa1, hpa2, hpa3⟩ := hPA
    refine ⟨⟨?_, ?_, ?_⟩, h_output.symm⟩
    · rcases hpa1 with h | h <;> rw [h] <;> ring
    · rcases hpa2 with h | h <;> rw [h] <;> ring
    · linear_combination hpa3

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (wb1 : WitgenIR Fp 1) (cfg : Config)
    (offset : ℕ) (input : Var Inputs Fp) (region : RegionIndex) :
    (bundle wb1).elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle (wb1 : WitgenIR Fp 1) := bundle wb1

/-- The returned `b₁` cell is assigned by the enclosing call. -/
theorem bundle_call_output_cell_assigned (wb1 : WitgenIR Fp 1)
    (name : String) (cfg : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    (((bundle wb1).toFormal name).output cfg input self).cell ∈
      Operations.assignedCellsFrom
        ((((bundle wb1).toFormal name).call cfg input).operations self) self := by
  have houtput : ((bundle wb1).toFormal name).output cfg input self =
      AssignedCell.of self 0 cfg.colR := by
    show ((bundle wb1).synthesize cfg 0 input).output self = _
    simp only [bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]
  rw [houtput, FormalCircuit.call_operations]
  simp only [FormalRegionCircuit.toFormal, bundle, circuit_norm,
    Operations.assignedCellsFrom, RegionOperations.assignedCells,
    List.flatMap_cons, RegionOperation.assignedCells, List.mem_cons,
    AssignedCell.of_cell]

end DecomposeB

namespace DecomposeD

structure Inputs (F : Type) where
  d : F
  d1 : F
  d2 : F
  d3 : F
deriving ProvableStruct

def synthesisSummary (config : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector config.qNotecommitD.index,
      .column .advice config.colL.index,
      .column .advice config.colM.index,
      .column .advice config.colR.index,
      .column .advice config.colM.index,
      .column .advice config.colR.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (config : Config) (offset : ℕ) :
    (synthesisSummary config offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

/-- Rust `DecomposeD::assign` (`note_commit.rs:297-340`), parameterized by the `d_0`
witness program (bit 254 of `x(pk_d)`). Output is the witnessed `d_0` cell; `Spec` is
the donor `DecomposeD.Gate.Spec`. -/
def bundle (wd0 : WitgenIR Fp 1) : FormalRegionCircuit Fp Config Config Inputs field where
  configure := pure
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR]
          inputCells _ _ input :=
            [input.d.cell, input.d1.cell, input.d2.cell, input.d3.cell] }
      synthesisSummary config offset _ _ :=
        synthesisSummary config offset
      synthesisSummary_eq := by
        intro _ _ _ _
        unfold synthesisSummary
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [circuit_norm, gate, List.flatMap_cons, List.flatMap_nil,
            FloorPlanner.regionOperationShapeColumns, List.append_nil,
            List.nil_append, List.singleton_append]
        · simp only [circuit_norm]
          omega
        · simp only [circuit_norm]
        · simp only [circuit_norm, synthesis_summary_norm]
        · simp only [circuit_norm, synthesis_summary_norm] }

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    (gate cfg).enable offset
    let _d ← copyAdvice input.d cfg.colL offset
    let d0 ← assignAdvice cfg.colM offset wd0
    let _d1 ← copyAdvice input.d1 cfg.colR offset
    let _d2 ← copyAdvice input.d2 cfg.colM (offset + 1)
    let _d3 ← copyAdvice input.d3 cfg.colR (offset + 1)
    pure d0

  Witness := field
  extract cfg offset _ self env :=
    eval env (AssignedCell.of self offset cfg.colM : Var field Fp)

  Spec := fun input (out : Fp) _ => IsBool out ∧ IsBool input.d1 ∧
    input.d = out + input.d1 * 2 + input.d2 * 4 + input.d3 * 1024

  ProverAssumptions := fun input (wit : Fp) _ => IsBool wit ∧ IsBool input.d1 ∧
    input.d = wit + input.d1 * 2 + input.d2 * 4 + input.d3 * 1024

  ProverSpec := fun _ (out : Fp) (wit : Fp) _ => out = wit

  soundness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨⟨hd0, hd1, hdec⟩, hcd, hcd1, hcd2, hcd3⟩ := hc
    rw [hcd1] at hd1
    rw [hcd, hcd1, hcd2, hcd3] at hdec
    exact ⟨isBool_of_boolCheck hd0, isBool_of_boolCheck hd1,
      by linear_combination hdec⟩

  completeness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨hpa1, hpa2, hpa3⟩ := hPA
    refine ⟨⟨?_, ?_, ?_⟩, h_output.symm⟩
    · rcases hpa1 with h | h <;> rw [h] <;> ring
    · rcases hpa2 with h | h <;> rw [h] <;> ring
    · linear_combination hpa3

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (wd0 : WitgenIR Fp 1) (cfg : Config)
    (offset : ℕ) (input : Var Inputs Fp) (region : RegionIndex) :
    (bundle wd0).elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle (wd0 : WitgenIR Fp 1) := bundle wd0

/-- The returned `d₀` cell is assigned by the enclosing call. -/
theorem bundle_call_output_cell_assigned (wd0 : WitgenIR Fp 1)
    (name : String) (cfg : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    (((bundle wd0).toFormal name).output cfg input self).cell ∈
      Operations.assignedCellsFrom
        ((((bundle wd0).toFormal name).call cfg input).operations self) self := by
  have houtput : ((bundle wd0).toFormal name).output cfg input self =
      AssignedCell.of self 0 cfg.colM := by
    show ((bundle wd0).synthesize cfg 0 input).output self = _
    simp only [bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]
  rw [houtput, FormalCircuit.call_operations]
  simp only [FormalRegionCircuit.toFormal, bundle, circuit_norm,
    Operations.assignedCellsFrom, RegionOperations.assignedCells,
    List.flatMap_cons, RegionOperation.assignedCells, List.mem_cons,
    AssignedCell.of_cell]

end DecomposeD

namespace DecomposeE

structure Inputs (F : Type) where
  e : F
  e0 : F
  e1 : F
deriving ProvableStruct

def synthesisSummary (config : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector config.qNotecommitE.index,
      .column .advice config.colL.index,
      .column .advice config.colM.index,
      .column .advice config.colR.index]
    (offset + 1) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (config : Config) (offset : ℕ) :
    (synthesisSummary config offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

/-- Rust `DecomposeE::assign` (`note_commit.rs:418-448`): pure copies, no in-gate
witness. `Spec` is the donor `DecomposeE.Gate.Spec`. -/
def bundle : FormalRegionCircuit Fp Config Config Inputs unit where
  configure := pure
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR]
          inputCells _ _ input :=
            [input.e.cell, input.e0.cell, input.e1.cell] }
      synthesisSummary config offset _ _ :=
        synthesisSummary config offset
      synthesisSummary_eq := by
        intro _ _ _ _
        unfold synthesisSummary
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [circuit_norm, gate, List.flatMap_cons, List.flatMap_nil,
            FloorPlanner.regionOperationShapeColumns, List.append_nil,
            List.nil_append, List.singleton_append]
        · simp only [circuit_norm]
          omega
        · simp only [circuit_norm]
        · simp only [circuit_norm, synthesis_summary_norm]
        · simp only [circuit_norm, synthesis_summary_norm] }

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    (gate cfg).enable offset
    let _e ← copyAdvice input.e cfg.colL offset
    let _e0 ← copyAdvice input.e0 cfg.colM offset
    let _e1 ← copyAdvice input.e1 cfg.colR offset
    pure ()

  Spec input _ _ := input.e = input.e0 + input.e1 * 64

  ProverAssumptions input _ _ := input.e = input.e0 + input.e1 * 64

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hdec, hce, hce0, hce1⟩ := hc
    rw [hce, hce0, hce1] at hdec
    linear_combination hdec

  completeness := by
    circuit_proof_start [gate]
    linear_combination hPA

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Inputs Fp) (region : RegionIndex) :
    bundle.elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle := bundle

end DecomposeE

namespace DecomposeG

structure Inputs (F : Type) where
  g : F
  g1 : F
  g2 : F
deriving ProvableStruct

def synthesisSummary (config : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector config.qNotecommitG.index,
      .column .advice config.colL.index,
      .column .advice config.colM.index,
      .column .advice config.colL.index,
      .column .advice config.colM.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (config : Config) (offset : ℕ) :
    (synthesisSummary config offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

/-- Rust `DecomposeG::assign` (`note_commit.rs:540-575`), parameterized by the `g_0`
witness program (bit 254 of `rho`). Output is the witnessed `g_0` cell; `Spec` is the
donor `DecomposeG.Gate.Spec`. -/
def bundle (wg0 : WitgenIR Fp 1) : FormalRegionCircuit Fp Config Config Inputs field where
  configure := pure
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ := [cfg.colL, cfg.colM]
          inputCells _ _ input :=
            [input.g.cell, input.g1.cell, input.g2.cell] }
      synthesisSummary config offset _ _ :=
        synthesisSummary config offset
      synthesisSummary_eq := by
        intro _ _ _ _
        unfold synthesisSummary
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [circuit_norm, gate, List.flatMap_cons, List.flatMap_nil,
            FloorPlanner.regionOperationShapeColumns, List.append_nil,
            List.nil_append, List.singleton_append]
        · simp only [circuit_norm]
          omega
        · simp only [circuit_norm]
        · simp only [circuit_norm, synthesis_summary_norm]
        · simp only [circuit_norm, synthesis_summary_norm] }

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    (gate cfg).enable offset
    let _g ← copyAdvice input.g cfg.colL offset
    let g0 ← assignAdvice cfg.colM offset wg0
    let _g1 ← copyAdvice input.g1 cfg.colL (offset + 1)
    let _g2 ← copyAdvice input.g2 cfg.colM (offset + 1)
    pure g0

  Witness := field
  extract cfg offset _ self env :=
    eval env (AssignedCell.of self offset cfg.colM : Var field Fp)

  Spec := fun input (out : Fp) _ => IsBool out ∧
    input.g = out + input.g1 * 2 + input.g2 * 1024

  ProverAssumptions := fun input (wit : Fp) _ => IsBool wit ∧
    input.g = wit + input.g1 * 2 + input.g2 * 1024

  ProverSpec := fun _ (out : Fp) (wit : Fp) _ => out = wit

  soundness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨⟨hg0, hdec⟩, hcg, hcg1, hcg2⟩ := hc
    rw [hcg, hcg1, hcg2] at hdec
    exact ⟨isBool_of_boolCheck hg0, by linear_combination hdec⟩

  completeness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨hpa1, hpa2⟩ := hPA
    refine ⟨⟨?_, ?_⟩, h_output.symm⟩
    · rcases hpa1 with h | h <;> rw [h] <;> ring
    · linear_combination hpa2

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (wg0 : WitgenIR Fp 1) (cfg : Config)
    (offset : ℕ) (input : Var Inputs Fp) (region : RegionIndex) :
    (bundle wg0).elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle (wg0 : WitgenIR Fp 1) := bundle wg0

/-- The returned `g₀` cell is assigned by the enclosing call. -/
theorem bundle_call_output_cell_assigned (wg0 : WitgenIR Fp 1)
    (name : String) (cfg : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    (((bundle wg0).toFormal name).output cfg input self).cell ∈
      Operations.assignedCellsFrom
        ((((bundle wg0).toFormal name).call cfg input).operations self) self := by
  have houtput : ((bundle wg0).toFormal name).output cfg input self =
      AssignedCell.of self 0 cfg.colM := by
    show ((bundle wg0).synthesize cfg 0 input).output self = _
    simp only [bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]
  rw [houtput, FormalCircuit.call_operations]
  simp only [FormalRegionCircuit.toFormal, bundle, circuit_norm,
    Operations.assignedCellsFrom, RegionOperations.assignedCells,
    List.flatMap_cons, RegionOperation.assignedCells, List.mem_cons,
    AssignedCell.of_cell]

end DecomposeG

namespace DecomposeH

structure Inputs (F : Type) where
  h : F
  h0 : F
deriving ProvableStruct

def synthesisSummary (config : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector config.qNotecommitH.index,
      .column .advice config.colL.index,
      .column .advice config.colM.index,
      .column .advice config.colR.index]
    (offset + 1) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (config : Config) (offset : ℕ) :
    (synthesisSummary config offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

/-- Rust `DecomposeH::assign` (`note_commit.rs:660-694`), parameterized by the `h_1`
witness program (bit 254 of `psi`). Output is the witnessed `h_1` cell; `Spec` is the
donor `DecomposeH.Gate.Spec`. -/
def bundle (wh1 : WitgenIR Fp 1) : FormalRegionCircuit Fp Config Config Inputs field where
  configure := pure
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR]
          inputCells _ _ input :=
            [input.h.cell, input.h0.cell] }
      synthesisSummary config offset _ _ :=
        synthesisSummary config offset
      synthesisSummary_eq := by
        intro _ _ _ _
        unfold synthesisSummary
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [circuit_norm, gate, List.flatMap_cons, List.flatMap_nil,
            FloorPlanner.regionOperationShapeColumns, List.append_nil,
            List.nil_append, List.singleton_append]
        · simp only [circuit_norm]
          omega
        · simp only [circuit_norm]
        · simp only [circuit_norm, synthesis_summary_norm]
        · simp only [circuit_norm, synthesis_summary_norm] }

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    (gate cfg).enable offset
    let _h ← copyAdvice input.h cfg.colL offset
    let _h0 ← copyAdvice input.h0 cfg.colM offset
    let h1 ← assignAdvice cfg.colR offset wh1
    pure h1

  Witness := field
  extract cfg offset _ self env :=
    eval env (AssignedCell.of self offset cfg.colR : Var field Fp)

  Spec := fun input (out : Fp) _ => IsBool out ∧ input.h = input.h0 + out * 32

  ProverAssumptions := fun input (wit : Fp) _ => IsBool wit ∧ input.h = input.h0 + wit * 32

  ProverSpec := fun _ (out : Fp) (wit : Fp) _ => out = wit

  soundness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨⟨hh1, hdec⟩, hch, hch0⟩ := hc
    rw [hch, hch0] at hdec
    exact ⟨isBool_of_boolCheck hh1, by linear_combination hdec⟩

  completeness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨hpa1, hpa2⟩ := hPA
    refine ⟨⟨?_, ?_⟩, h_output.symm⟩
    · rcases hpa1 with h | h <;> rw [h] <;> ring
    · linear_combination hpa2

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (wh1 : WitgenIR Fp 1) (cfg : Config)
    (offset : ℕ) (input : Var Inputs Fp) (region : RegionIndex) :
    (bundle wh1).elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle (wh1 : WitgenIR Fp 1) := bundle wh1

/-- The returned `h₁` cell is assigned by the enclosing call. -/
theorem bundle_call_output_cell_assigned (wh1 : WitgenIR Fp 1)
    (name : String) (cfg : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    (((bundle wh1).toFormal name).output cfg input self).cell ∈
      Operations.assignedCellsFrom
        ((((bundle wh1).toFormal name).call cfg input).operations self) self := by
  have houtput : ((bundle wh1).toFormal name).output cfg input self =
      AssignedCell.of self 0 cfg.colR := by
    show ((bundle wh1).synthesize cfg 0 input).output self = _
    simp only [bundle, circuit_norm, RegionCircuit.output_bind]
  rw [houtput, FormalCircuit.call_operations]
  simp only [FormalRegionCircuit.toFormal, bundle, circuit_norm,
    Operations.assignedCellsFrom, RegionOperations.assignedCells,
    List.flatMap_cons, RegionOperation.assignedCells, List.mem_cons,
    AssignedCell.of_cell]

end DecomposeH

@[synthesis_summary_norm]
theorem DecomposeB.synthesisSummary_lookupActivationCount
    (cfg : DecomposeB.Config) (offset : ℕ) :
    (DecomposeB.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [DecomposeB.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem DecomposeD.synthesisSummary_lookupActivationCount
    (cfg : DecomposeD.Config) (offset : ℕ) :
    (DecomposeD.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [DecomposeD.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem DecomposeE.synthesisSummary_lookupActivationCount
    (cfg : DecomposeE.Config) (offset : ℕ) :
    (DecomposeE.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [DecomposeE.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem DecomposeG.synthesisSummary_lookupActivationCount
    (cfg : DecomposeG.Config) (offset : ℕ) :
    (DecomposeG.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [DecomposeG.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem DecomposeH.synthesisSummary_lookupActivationCount
    (cfg : DecomposeH.Config) (offset : ℕ) :
    (DecomposeH.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [DecomposeH.synthesisSummary, synthesis_summary_norm]

end Zcash.Circuits.NoteCommit
