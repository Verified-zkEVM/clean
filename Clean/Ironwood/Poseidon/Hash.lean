import Clean.Ironwood.Poseidon.Permute

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `initial_state` (lines 277-308): a region assigning the domain's initial state from
  constants (`assign_advice_from_constant`: zeros on the rate words, the capacity element
  on the last).
- `add_input` (lines 310-396): a region enabling `s_pad_and_add` at row 1, copying the
  initial state at row 0, the (already-padded) input words at row 1, and assigning the
  summed output state at row 2. For `ConstantLength<2>` both words are `Message` cells —
  no fixed padding.
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon.rs`
- `Hash::hash` for `ConstantLength<2>` (lines 269-286 + the sponge, 100-228): absorb both
  words (buffered), `finish_absorbing` = `add_input` + `permute`, `squeeze` returns
  `state[0]` with no further region. Region sequence: `"initial state for domain
  ConstantLength<2>"`, `"add input for domain ConstantLength<2>"`, `"permute state"`.

The value-level contract is the donor `Hash.HashPaddedBlock.value`
(`Clean/Orchard/Poseidon/Hash.lean`) at capacity `ConstantLength.capacity 2 = 2·2⁶⁴`.
-/

namespace Zcash.Circuits.Poseidon

open Halo2
open Poseidon
open Poseidon.Permute (State)
open Poseidon.Permute.P128Pow5T3 (roundConstants)

/-- A constant witness program. -/
def constWit (c : Fp) : WitgenIR Fp 1 := .native fun _ => #v[c]

@[circuit_norm]
theorem constWit_eval (c : Fp) (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((constWit c).eval env)[j] = c := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [constWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The sum of two read cells. -/
def addWit (a b : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env a + readCell env b]

@[circuit_norm]
theorem addWit_eval (a b : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((addWit a b).eval env)[j] = readCell env a + readCell env b := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [addWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- A copy of one read cell. -/
def readCellWit (a : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env a]

@[circuit_norm]
theorem readCellWit_eval (a : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((readCellWit a).eval env)[j] = readCell env a := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [readCellWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Reduced synthesis footprint of the initial-state region. -/
def initRegionSynthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.column .advice (cfg.state 0).index,
      .column .advice (cfg.state 1).index,
      .column .advice (cfg.state 2).index]
    (offset + 1) 3

/-- Rust `Pow5Chip::initial_state`'s region body (`pow5.rs:277-308`): the domain's
initial state from constrained constants. -/
def initRegion (capacity : Fp) : FormalRegionCircuit Fp Config Config unit State where
  configure := pure
  elaborated :=
    { keygenRequirements :=
        { permutationColumns cfg _ :=
            [cfg.state 0, cfg.state 1, cfg.state 2] }
      output cfg offset _ self :=
        { x0 := .of self offset (cfg.state 0)
          x1 := .of self offset (cfg.state 1)
          x2 := .of self offset (cfg.state 2) }
      synthesisSummary cfg offset _ _ :=
        initRegionSynthesisSummary cfg offset
      synthesisSummary_eq := by
        intro _ _ _ _
        apply FloorPlanner.RegionSynthesisSummary.ext
        · simp only [initRegionSynthesisSummary, circuit_norm,
            synthesis_summary_norm]
        · simp only [initRegionSynthesisSummary, circuit_norm,
            synthesis_summary_norm]
        · simp only [initRegionSynthesisSummary, circuit_norm,
            synthesis_summary_norm]
        · simp only [initRegionSynthesisSummary, circuit_norm,
            synthesis_summary_norm]
        · simp only [initRegionSynthesisSummary, circuit_norm,
            synthesis_summary_norm]
      output_eq := by
        intro cfg _ _ _
        rfl }

  synthesize cfg offset _ := do
    let x0 ← assignAdvice (cfg.state 0) offset (constWit 0)
    constrainConstant x0 0
    let x1 ← assignAdvice (cfg.state 1) offset (constWit 0)
    constrainConstant x1 0
    let x2 ← assignAdvice (cfg.state 2) offset (constWit capacity)
    constrainConstant x2 capacity
    pure { x0, x1, x2 }

  Spec _ out _ := out = ({ x0 := 0, x1 := 0, x2 := capacity } : State Fp)
  ProverSpec _ out _ _ := out = ({ x0 := 0, x1 := 0, x2 := capacity } : State Fp)

  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm]
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm]
    rw [← h_output.1, ← h_output.2.1]

/-- The initial-state bundle exposes its already-reduced synthesis footprint. -/
@[synthesis_summary_norm]
theorem initRegion_synthesisSummary (capacity : Fp) (cfg : Config)
    (offset : ℕ) (input : Var unit Fp) (self : RegionIndex) :
    (initRegion capacity).elaborated.synthesisSummary cfg offset input self =
      initRegionSynthesisSummary cfg offset := rfl

/-- Reduced synthesis footprint of the pad-and-add region. -/
def addInputRegionSynthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.sPadAndAdd.index,
      .column .advice (cfg.state 0).index,
      .column .advice (cfg.state 1).index,
      .column .advice (cfg.state 2).index]
    (offset + 3) 0

def addInputRegionSynthesize (cfg : Config) (offset : ℕ)
    (input : Var Sponge.AddInputInput Fp) : RegionCircuit Fp (Var State Fp) := do
  (padAndAddGate cfg).enable (offset + 1)
  let i0 ← copyAdvice input.initialState.x0 (cfg.state 0) offset
  let i1 ← copyAdvice input.initialState.x1 (cfg.state 1) offset
  let i2 ← copyAdvice input.initialState.x2 (cfg.state 2) offset
  let w0 ← assignAdvice (cfg.state 0) (offset + 1) (readCellWit input.input.x0)
  constrainEqual input.input.x0 w0
  let w1 ← assignAdvice (cfg.state 1) (offset + 1) (readCellWit input.input.x1)
  constrainEqual input.input.x1 w1
  let o0 ← assignAdvice (cfg.state 0) (offset + 2) (addWit i0 w0)
  let o1 ← assignAdvice (cfg.state 1) (offset + 2) (addWit i1 w1)
  let o2 ← assignAdvice (cfg.state 2) (offset + 2) (readCellWit i2)
  pure { x0 := o0, x1 := o1, x2 := o2 }

@[implicit_reducible]
def addInputRegionElaborated : ElaboratedRegionCircuit Fp Config Config
    Sponge.AddInputInput State pure addInputRegionSynthesize where
  keygenRequirements :=
    { gates cfg _ := [padAndAddGate cfg]
      permutationColumns cfg _ :=
        [cfg.state 0, cfg.state 1, cfg.state 2]
      inputCells _ _ input :=
        [input.initialState.x0.cell, input.initialState.x1.cell,
          input.initialState.x2.cell, input.input.x0.cell,
          input.input.x1.cell] }
  output cfg offset _ self :=
    { x0 := .of self (offset + 2) (cfg.state 0)
      x1 := .of self (offset + 2) (cfg.state 1)
      x2 := .of self (offset + 2) (cfg.state 2) }
  synthesisSummary cfg offset _ _ :=
    addInputRegionSynthesisSummary cfg offset
  copyCellsAssigned := by
    keygen_registration [addInputRegionSynthesize]
  lookupActivationsWellFormed := by
    keygen_registration [addInputRegionSynthesize]
  synthesisSummary_eq := by
    intro cfg _ _ _
    apply FloorPlanner.RegionSynthesisSummary.ext
    · simp only [addInputRegionSynthesize, addInputRegionSynthesisSummary, circuit_norm,
        synthesis_summary_norm, configure_selector_norm]
      refine (FloorPlanner.unionColumns_normalize_append_redundant
        [.selector cfg.sPadAndAdd.index,
          .column .advice (cfg.state 0).index,
          .column .advice (cfg.state 1).index,
          .column .advice (cfg.state 2).index]
        [.column .advice (cfg.state 0).index,
          .column .advice (cfg.state 1).index,
          .column .advice (cfg.state 0).index,
          .column .advice (cfg.state 1).index,
          .column .advice (cfg.state 2).index] ?_).symm
      intro column hcolumn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn ⊢
      tauto
    · simp only [addInputRegionSynthesize, addInputRegionSynthesisSummary, circuit_norm,
        synthesis_summary_norm, configure_selector_norm]
      omega
    · simp only [addInputRegionSynthesize, addInputRegionSynthesisSummary, circuit_norm,
        synthesis_summary_norm, configure_selector_norm]
    · simp only [addInputRegionSynthesize, addInputRegionSynthesisSummary, circuit_norm,
        synthesis_summary_norm, configure_selector_norm]
    · simp only [addInputRegionSynthesize, addInputRegionSynthesisSummary, circuit_norm,
        synthesis_summary_norm, configure_selector_norm]
  output_eq := by
    intro _ _ _ _
    rfl

/-- Rust `Pow5Chip::add_input`'s region body (`pow5.rs:310-396`), `ConstantLength<2>`
shape (both rate words are `Message` cells): `s_pad_and_add` at row 1, the initial state
copied at row 0, the input words copied at row 1, the summed output at row 2. `Spec` is
the donor `Sponge.AddInput.value`. -/
def addInputRegion : FormalRegionCircuit Fp Config Config Sponge.AddInputInput State where
  configure := pure
  elaborated := addInputRegionElaborated

  synthesize := addInputRegionSynthesize

  Spec input out _ := out = Sponge.AddInput.value input
  ProverSpec input out _ _ := out = Sponge.AddInput.value input

  soundness := by
    circuit_proof_start [addInputRegionElaborated, addInputRegionSynthesize,
      padAndAddGate, Sponge.AddInput.value]
    obtain ⟨⟨g0, g1, g2⟩, c0, c1, c2, c3, c4⟩ := hc
    rw [c0, ← c3] at g0
    rw [c1, ← c4] at g1
    rw [c2] at g2
    exact ⟨by linear_combination -g0, by linear_combination -g1, by linear_combination -g2⟩
  completeness := by
    circuit_proof_start [addInputRegionElaborated, addInputRegionSynthesize, padAndAddGate,
      Sponge.AddInput.value, readCell]
    exact ⟨⟨by ring, by ring, by ring⟩,
      h_output.1.symm, h_output.2.1.symm, h_output.2.2.symm⟩

/-- The pad-and-add bundle exposes its already-reduced synthesis footprint. -/
@[synthesis_summary_norm]
theorem addInputRegion_synthesisSummary (cfg : Config) (offset : ℕ)
    (input : Var Sponge.AddInputInput Fp) (self : RegionIndex) :
    addInputRegion.elaborated.synthesisSummary cfg offset input self =
      addInputRegionSynthesisSummary cfg offset := rfl

@[keygen_norm]
theorem addInputRegion_inputCells (cfg : Config)
    (hconfigured : addInputRegion.Configured cfg)
    (input : Var Sponge.AddInputInput Fp) :
    FormalRegionCircuit.Configured.inputCells hconfigured input =
      [input.initialState.x0.cell, input.initialState.x1.cell,
        input.initialState.x2.cell, input.input.x0.cell,
        input.input.x1.cell] := rfl

derive_contract_bridges initRegion (capacity : Fp) := initRegion capacity

derive_contract_bridges addInputRegion := addInputRegion

theorem initRegion_output_cells_assigned (capacity : Fp) (cfg : Config)
    (offset : ℕ) (region : RegionIndex) (available : List Cell) :
    let output := (initRegion capacity).output cfg offset () region
    output.x0.cell ∈
        (((initRegion capacity).call cfg offset ()).operations region
          |>.assignedCellsAfter region available) ∧
      output.x1.cell ∈
        (((initRegion capacity).call cfg offset ()).operations region
          |>.assignedCellsAfter region available) ∧
      output.x2.cell ∈
        (((initRegion capacity).call cfg offset ()).operations region
          |>.assignedCellsAfter region available) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [initRegion_output, RegionOperations.mem_assignedCellsAfter_iff,
    List.mem_append]
  repeat' apply And.intro
  all_goals right
  all_goals simp only [initRegion, circuit_norm, RegionOperations.assignedCells,
    List.flatMap_cons, RegionOperation.assignedCells, List.singleton_append,
    List.mem_cons, true_or]

theorem addInputRegion_output_cells_assigned (cfg : Config) (offset : ℕ)
    (input : Var Sponge.AddInputInput Fp) (region : RegionIndex)
    (available : List Cell) :
    let output := addInputRegion.output cfg offset input region
    output.x0.cell ∈
        ((addInputRegion.call cfg offset input).operations region
          |>.assignedCellsAfter region available) ∧
      output.x1.cell ∈
        ((addInputRegion.call cfg offset input).operations region
          |>.assignedCellsAfter region available) ∧
      output.x2.cell ∈
        ((addInputRegion.call cfg offset input).operations region
          |>.assignedCellsAfter region available) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [addInputRegion_output,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  repeat' apply And.intro
  all_goals right
  all_goals simp only [addInputRegion, addInputRegionSynthesize, circuit_norm,
    RegionOperations.assignedCells, List.flatMap_cons,
    RegionOperation.assignedCells, List.singleton_append,
    List.mem_cons, true_or]

/-- The region count of `hash`: three regions. -/
private theorem hash_regionCount (capacity : Fp) (cfg : Config)
    (input : Var Sponge.Rate2 Fp) (i : RegionIndex) :
    Operations.regionCount
      (((do
        let init ← assignRegion "initial state for domain ConstantLength<2>"
          ((initRegion capacity).call cfg 0 ())
        let absorbed ← assignRegion "add input for domain ConstantLength<2>"
          (addInputRegion.call cfg 0 { initialState := init, input := input })
        let permuted ← assignRegion "permute state"
          (permuteRegion.call cfg 0 absorbed)
        pure permuted.x0) : Circuit Fp (Var field Fp)).operations i)
      = 3 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount]

/-- The three layouter regions of the one-block Poseidon hash. -/
def synthesize (capacity : Fp) (cfg : Config)
    (input : Var Sponge.Rate2 Fp) : Circuit Fp (AssignedCell Fp) := do
    let init ← assignRegion "initial state for domain ConstantLength<2>"
      ((initRegion capacity).call cfg 0 ())
    let absorbed ← assignRegion "add input for domain ConstantLength<2>"
      (addInputRegion.call cfg 0 { initialState := init, input := input })
    let permuted ← assignRegion "permute state"
      (permuteRegion.call cfg 0 absorbed)
    pure permuted.x0

/-- Reduced layouter-level synthesis footprint of the three hash regions. -/
def hashSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  (FloorPlanner.SynthesisSummary.ofRegion
      (initRegionSynthesisSummary cfg 0)).combine
    ((FloorPlanner.SynthesisSummary.ofRegion
        (addInputRegionSynthesisSummary cfg 0)).combine
      (FloorPlanner.SynthesisSummary.ofRegion
        (permuteSynthesisSummary cfg 0)))

@[synthesis_summary_norm]
theorem hashSynthesisSummary_lookupActivationCount (cfg : Config) :
    (hashSynthesisSummary cfg).lookupActivationCount = 0 := by
  simp only [hashSynthesisSummary, initRegionSynthesisSummary,
    addInputRegionSynthesisSummary, permuteSynthesisSummary,
    synthesis_summary_norm]

@[synthesis_summary_norm]
theorem hashSynthesisSummary_tableRowExtent_eq (cfg : Config) :
    (hashSynthesisSummary cfg).tableRowExtent = 0 := by
  simp only [hashSynthesisSummary, synthesis_summary_norm]

/-- Rust `Hash::<ConstantLength<2>>::hash` (`poseidon.rs:269-286`) on the Pow5 chip:
initial state, pad-and-add, one permutation; the digest is `state[0]`. `Spec` is the
donor one-block hash value `HashPaddedBlock.value`. -/
def hash (capacity : Fp) :
    FormalCircuit Fp Config Config Sponge.Rate2 field where
  name := "poseidon hash ConstantLength<2>"
  configure := pure

  synthesize := synthesize capacity

  elaborated :=
    { keygenRequirements :=
        { configLawful cfg := Config.FixedColumnsLawful cfg
          gates cfg _ :=
            [padAndAddGate cfg, fullRoundGate cfg, partialRoundsGate cfg]
          fixedColumns cfg _ := cfg.fixedColumns
          permutationColumns cfg _ :=
            [cfg.state 0, cfg.state 1, cfg.state 2]
          inputCells _ _ input :=
            [input.x0.cell, input.x1.cell] }
      output cfg _ i := .of (i + 2) 36 (cfg.state 0)
      regionCount _ := 3
      synthesisSummary cfg _ _ := hashSynthesisSummary cfg
      registered := by
        keygen_registration [synthesize]
        case left =>
          apply FormalRegionCircuit.callPacked_keygenRegistered
            (self := addInputRegion) (hconfigured := by
              apply FormalRegionCircuit.Configured.ofPure
              · exact ()
              · rfl)
          all_goals keygen_registration
        case right =>
          apply FormalRegionCircuit.callPacked_keygenRegistered
            (self := permuteRegion) (hconfigured := by
              apply FormalRegionCircuit.Configured.ofPure
              · assumption
              · rfl)
          all_goals keygen_registration
      copyCellsAssigned := by
        intro configInput counts hconfig input i
        keygen_registration [synthesize]
        case left =>
          apply FormalRegionCircuit.callPacked_copyCellsAssignedFrom
            (self := addInputRegion) (hconfigured := by
              apply FormalRegionCircuit.Configured.ofPure
              · exact ()
              · rfl)
          intro cell hcell
          rw [addInputRegion_inputCells] at hcell
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
          have hinit := initRegion_output_cells_assigned capacity configInput 0 i
            [input.x0.cell, input.x1.cell]
          rcases hcell with rfl | rfl | rfl | rfl | rfl
          · simpa only [FormalRegionCircuit.callPacked_operations] using hinit.1
          · simpa only [FormalRegionCircuit.callPacked_operations] using hinit.2.1
          · simpa only [FormalRegionCircuit.callPacked_operations] using hinit.2.2
          · apply RegionOperations.mem_assignedCellsAfter_of_mem
            simp
          · apply RegionOperations.mem_assignedCellsAfter_of_mem
            simp
        case right =>
          simp only [nextRegionIndex_assignRegion]
          apply FormalRegionCircuit.callPacked_copyCellsAssignedFrom
            (self := permuteRegion) (hconfigured := by
              apply FormalRegionCircuit.Configured.ofPure
              · assumption
              · rfl)
          intro cell hcell
          rw [permuteRegion_inputCells] at hcell
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
          let initial := [input.x0.cell, input.x1.cell]
          let initOutput := (initRegion capacity).output configInput 0 () i
          let afterInit :=
            ((initRegion capacity).call configInput 0 ()).operations i
              |>.assignedCellsAfter i initial
          have hadd := addInputRegion_output_cells_assigned configInput 0
            { initialState := initOutput, input := input } (i + 1) afterInit
          rcases hcell with rfl | rfl | rfl
          · simpa only [afterInit, initial,
              FormalRegionCircuit.callPacked_operations] using hadd.1
          · simpa only [afterInit, initial,
              FormalRegionCircuit.callPacked_operations] using hadd.2.1
          · simpa only [afterInit, initial,
              FormalRegionCircuit.callPacked_operations] using hadd.2.2
      fixedWritesLawful := by
        intro cfg _ hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simp only [synthesize, Circuit.operations_bind,
            operations_assignRegion, Circuit.operations_pure,
            circuit_norm]
          exact ⟨(initRegion capacity).call_fixedAssignmentsAgree cfg
              (FormalRegionCircuit.Configured.ofPure
                (initRegion capacity) cfg () rfl) 0 () self,
            addInputRegion.call_fixedAssignmentsAgree cfg
              (FormalRegionCircuit.Configured.ofPure
                addInputRegion cfg () rfl) 0
              { initialState := (initRegion capacity).output cfg 0 () self,
                input := input }
              (self + 1),
            permuteRegion.call_fixedAssignmentsAgree cfg
              (FormalRegionCircuit.Configured.ofPure
                permuteRegion cfg hconfig rfl) 0
              (addInputRegion.output cfg 0
                { initialState := (initRegion capacity).output cfg 0 () self,
                  input := input }
                (self + 1))
              (self + 2)⟩
        · simp only [synthesize, circuit_norm, synthesis_summary_norm]
      output_eq := by
        intro _ _ _
        simp only [synthesize, circuit_norm, keygen_output_norm, stateRow]
      regionCount_eq := fun cfg input i => (hash_regionCount capacity cfg input i).symm
      synthesisSummary_eq := by
        intro _ _ _
        simp only [hashSynthesisSummary, synthesize, circuit_norm,
          synthesis_summary_norm]
      lookupActivationsWellFormed := by
        keygen_registration [synthesize]
        all_goals first
          | exact FormalRegionCircuit.callPacked_lookupActivationsWellFormed
              addInputRegion _ 0 _ _
          | exact FormalRegionCircuit.callPacked_lookupActivationsWellFormed
              permuteRegion _ 0 _ _ }

  Spec input output _ :=
    output = Hash.HashPaddedBlock.value roundConstants capacity input

  ProverSpec input output _ _ :=
    output = Hash.HashPaddedBlock.value roundConstants capacity input

  soundness := by
    circuit_proof_start
    obtain ⟨hInit, hAdd, hPerm⟩ := hc
    have h0 := hInit trivial trivial
    simp only [initRegion_spec_eq] at h0
    have h1 := hAdd trivial trivial
    simp only [addInputRegion_spec_eq] at h1
    have h2 := hPerm trivial trivial
    simp only [permuteRegion_spec_eq] at h2
    rw [h0] at h1
    rw [h1] at h2
    rw [← h_output]
    rw [show env.advice (cfg.state 0) ((place (i₀ + 2) + 36 : ℕ) : ℤ) =
      (ProvableStruct.Halo2.eval place env
        (permuteRegion.output cfg 0 x_gen_out_1 (i₀ + 2)) : State Fp).x0 from by
        simp only [keygen_output_norm, stateRow, circuit_norm]]
    rw [h2]
    rfl

  completeness := by
    circuit_proof_start
    have h0 := (h_spec_0 trivial trivial trivial).1
    simp only [initRegion_spec_eq] at h0
    have h1 := (h_spec_1 trivial trivial trivial).1
    simp only [addInputRegion_spec_eq] at h1
    have h2 := (h_spec_2 trivial trivial trivial).1
    simp only [permuteRegion_spec_eq] at h2
    rw [h0] at h1
    rw [h1] at h2
    refine ⟨⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      trivial, trivial, trivial⟩, ?_⟩
    rw [← h_output]
    rw [show env.advice (cfg.state 0) ((place (i₀ + 2) + 36 : ℕ) : ℤ) =
      (ProvableStruct.Halo2.eval place env.toEnvironment
        (permuteRegion.output cfg 0 x_gen_out_1 (i₀ + 2)) : State Fp).x0 from by
        simp only [keygen_output_norm, stateRow, circuit_norm]]
    rw [h2]
    rw [h_input.1, h_input.2]
    rfl

/-- The digest returned by the one-block hash is assigned by its final permutation
region. -/
theorem hash_call_output_cell_assigned (capacity : Fp) (cfg : Config)
    (input : Var Sponge.Rate2 Fp) (self : RegionIndex) :
    ((hash capacity).output cfg input self).cell ∈
      Operations.assignedCellsFrom
        (((hash capacity).call cfg input).operations self) self := by
  rw [show (hash capacity).output cfg input self =
      .of (self + 2) 36 (cfg.state 0) from rfl]
  rw [FormalCircuit.call_operations]
  simp only [hash, synthesize, circuit_norm, Operations.assignedCellsFrom,
    List.mem_append]
  right
  right
  let initOutput := (initRegion capacity).output cfg 0 () self
  let absorbed := addInputRegion.output cfg 0
    { initialState := initOutput, input := input } (self + 1)
  have h := permuteRegion_output_cells_assigned cfg 0 absorbed (self + 2) []
  simp only [RegionOperations.mem_assignedCellsAfter_iff, List.nil_append] at h
  simpa only [absorbed, initOutput, FormalRegionCircuit.output_call,
    Nat.zero_add] using h.1

@[keygen_norm]
theorem hash_inputCells (capacity : Fp) (cfg : Config)
    (configured : (hash capacity).Configured cfg)
    (input : Var Sponge.Rate2 Fp) :
    configured.inputCells input = [input.x0.cell, input.x1.cell] := rfl

/-- The hash circuit exposes its reduced three-region footprint directly. -/
@[synthesis_summary_norm]
theorem hash_synthesisSummary_eq (capacity : Fp) (cfg : Config)
    (input : Var Sponge.Rate2 Fp) (region : RegionIndex) :
    (hash capacity).elaborated.synthesisSummary cfg input region =
      hashSynthesisSummary cfg := rfl

/-- The hash capability exported by one aggregate Poseidon configure run. -/
def hashConfigureCertificate (capacity : Fp)
    (state : Fin 3 → Column .advice) (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) (counts : ConfigureCounts)
    (hfixedColumns :
      ((configure state partialSbox rcA rcB).output counts).FixedColumnsLawful) :
    (hash capacity).ConfigurationCertificate
      ((configure state partialSbox rcA rcB).output counts)
      { gates := ((configure state partialSbox rcA rcB).delta counts).gates
        lookups := ((configure state partialSbox rcA rcB).delta counts).lookups
        fixedColumns :=
          ((configure state partialSbox rcA rcB).output counts).fixedColumns
        permutationColumns :=
          ((configure state partialSbox rcA rcB).delta counts).permutationRequests } := by
  let cfg := (configure state partialSbox rcA rcB).output counts
  apply ((hash capacity).configureCertificate cfg {} hfixedColumns).mono
  · intro gate hgate
    simp only [hash, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with rfl | rfl | rfl <;> simp [cfg, configure]
  · intro argument hargument
    simp only [hash, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil] at hargument
    exact False.elim (List.not_mem_nil hargument)
  · intro column hcolumn
    simpa only [hash, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Configure.fixedColumns_pure,
      List.append_nil] using hcolumn
  · intro column hcolumn
    simp only [hash, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hcolumn
    rcases hcolumn with rfl | rfl | rfl
    · exact state_mem_configure_permutationRequests
        state partialSbox rcA rcB counts 0
    · exact state_mem_configure_permutationRequests
        state partialSbox rcA rcB counts 1
    · exact state_mem_configure_permutationRequests
        state partialSbox rcA rcB counts 2

derive_contract_bridges hash (capacity : Fp) := hash capacity

end Zcash.Circuits.Poseidon
