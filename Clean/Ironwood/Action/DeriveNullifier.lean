import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem
import Clean.Ironwood.Poseidon.Hash
import Clean.Ironwood.Utilities.AddChip

/-!
# Orchard-protocol nullifier derivation

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/gadget.rs::derive_nullifier` (lines 154-206):
`nf = extract_p(cm + (poseidon_hash(nk, rho) + psi) • NullifierK)` — four layouter pieces
in source order:
1. `PoseidonHash::init` + `hash([nk, rho])` (`ConstantLength<2>` on the Pow5 chip; the
   Orchard-protocol `Poseidon.hash` bundle at capacity `2·2^{64}`);
2. `add_chip.add(hash, psi)` (region `"c = a + b"`, `add_chip.rs:71-91`);
3. `FixedPointBaseField::from_inner(NullifierK).mul(scalar)` (the
   `Ecc.MulFixed.BaseFieldElem` bundle);
4. `cm.add(product)` (region `"complete point addition"`, `ecc/chip.rs:582-595`); the
   returned nullifier is `.extract_p()` — the x-coordinate.

Phase-1 donor: `Clean/Orchard/Action/DeriveNullifier.lean`.
-/

namespace Zcash.Circuits.Action.DeriveNullifier

open Halo2
open Ecc.MulFixed (FixedBase)
open Poseidon
open Poseidon.Permute.P128Pow5T3 (roundConstants)

/-- The inputs of `derive_nullifier`: the already-assigned cells `nk`, `rho`, `psi`, and
the note commitment point `cm`. -/
structure Input (F : Type) where
  nk : F
  rho : F
  psi : F
  cm : Point F
deriving ProvableStruct

/-- The `ConstantLength<2>` hash value is the one-padded-block hash at capacity
`2·2^{64}`: the message is exactly one rate-2 block, so the donor scheduler's fold
is a single absorb/permute step — the value-level bridge onto the Orchard-protocol
`Poseidon.hash` bundle's `HashPaddedBlock` contract. -/
theorem constantLength_value_two (a b : Fp) :
    Hash.ConstantLength.value #v[a, b]
      = Hash.HashPaddedBlock.value roundConstants (Hash.ConstantLength.capacity 2)
          { x0 := a, x1 := b } := by
  simp [Hash.ConstantLength.value, Hash.HashPaddedBlock.value,
    Hash.ConstantLength.blockCount, Hash.ConstantLength.stepValueAt,
    Hash.ConstantLength.absorbPermuteValue, Permute.concreteValue,
    Hash.ConstantLength.blockValue, Hash.ConstantLength.paddedWord,
    Fin.foldl_succ, Fin.foldl_zero]

/-! ## Region counts -/

/-- The region count of `derive_nullifier`: the Poseidon child's three regions, the
add-chip region, the fixed-base mul's four regions, the final complete addition. -/
private theorem deriveNullifier_regionCount (K : FixedBase)
    (pcfg : Poseidon.Config) (acfg : AddChip.Config)
    (bcfg : Ecc.MulFixed.BaseFieldElem.Config) (ecfg : Ecc.Add.Config)
    (input : Var Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let hash ← (Poseidon.hash (Hash.ConstantLength.capacity 2)).call pcfg
          { x0 := input.nk, x1 := input.rho }
        let scalar ← AddChip.addFormal.call acfg
          { a := hash, b := input.psi }
        let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg scalar
        let nf ← Ecc.Add.addFormal.call ecfg
          { p := input.cm, q := product }
        pure nf.x : Circuit Fp (Var field Fp)).operations i)
      = 9 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    FormalCircuit.call_regionCount]
  rfl

/-! ## The `derive_nullifier` bundle -/

@[keygen_norm]
def keygenRequirements (K : FixedBase) : KeygenRequirements Fp
    (Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config) (Var Input Fp) where
  configLawful cfg :=
    (Poseidon.hash (Hash.ConstantLength.capacity 2)).Configured cfg.1 ×
      AddChip.addFormal.Configured cfg.2.1 ×
        (Ecc.MulFixed.BaseFieldElem.circuit K).Configured cfg.2.2.1 ×
          Ecc.Add.addFormal.Configured cfg.2.2.2
  gates _ configured :=
    configured.1.gates ++ configured.2.1.gates ++
      configured.2.2.1.gates ++ configured.2.2.2.gates
  lookups _ configured :=
    configured.1.lookups ++ configured.2.1.lookups ++
      configured.2.2.1.lookups ++ configured.2.2.2.lookups
  fixedColumns _ configured :=
    configured.1.fixedColumns ++ configured.2.1.fixedColumns ++
      configured.2.2.1.fixedColumns ++ configured.2.2.2.fixedColumns
  permutationColumns cfg configured :=
    configured.1.permutationColumns ++ configured.2.1.permutationColumns ++
      configured.2.2.1.permutationColumns ++ configured.2.2.2.permutationColumns ++
        ([cfg.1.state 0, cfg.2.1.c,
          cfg.2.2.1.superConfig.addConfig.xQR,
          cfg.2.2.1.superConfig.addConfig.yQR] : List AnyColumn)
  inputCells _ _ input :=
    [input.nk.cell, input.rho.cell, input.psi.cell,
      input.cm.x.cell, input.cm.y.cell]

def synthesisSummary
    (cfg : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config) :
    FloorPlanner.SynthesisSummary :=
  (Poseidon.hashSynthesisSummary cfg.1).combine
    ((FloorPlanner.SynthesisSummary.ofRegion
      (AddChip.synthesisSummary cfg.2.1 0)).combine
      ((Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary cfg.2.2.1).combine
        (FloorPlanner.SynthesisSummary.ofRegion
          (Ecc.Add.synthesisSummary cfg.2.2.2 0))))

@[synthesis_summary_norm]
theorem synthesisSummary_lookupActivationCount
    (cfg : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config) :
    (synthesisSummary cfg).lookupActivationCount = 13 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_tableRowExtent_eq
    (cfg : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config) :
    (synthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthesisSummary, Poseidon.hashSynthesisSummary,
    synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq
    (cfg : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config) :
    (synthesisSummary cfg).instanceRowExtent = 0 := by
  simp only [synthesisSummary, Poseidon.hashSynthesisSummary,
    Poseidon.initRegionSynthesisSummary,
    Poseidon.addInputRegionSynthesisSummary,
    Poseidon.permuteSynthesisSummary,
    AddChip.synthesisSummary, synthesis_summary_norm]
  simp

def synthesize (K : FixedBase)
    (cfg : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  let hash ← (Poseidon.hash (Hash.ConstantLength.capacity 2)).call cfg.1
    { x0 := input.nk, x1 := input.rho }
  let scalar ← AddChip.addFormal.call cfg.2.1
    { a := hash, b := input.psi }
  let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call cfg.2.2.1 scalar
  let nf ← Ecc.Add.addFormal.call cfg.2.2.2
    { p := input.cm, q := product }
  pure nf.x

/-- Rust `gadget.rs::derive_nullifier`: the Poseidon hash of `(nk, rho)`, the add-chip
sum with `psi`, the `scalar • NullifierK` base-field-element fixed-base mul, and the
complete addition with `cm`. `Spec` is the donor contract: the nullifier is
`extract_p(cm + (poseidon_hash(nk, rho) + psi) • NullifierK)` — the x-coordinate of the
complete sum. -/
def circuit (K : FixedBase) : FormalCircuit Fp
    (Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config)
    (Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config)
    Input field where
  name := "derive nullifier"
  configure := pure

  synthesize := synthesize K

  elaborated :=
    { keygenRequirements := keygenRequirements K
      registered := by
        intro cfg counts hconfig input self
        simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
          Operations.KeygenRegistered.append, circuit_norm]
        exact ⟨by
          apply (Poseidon.hash (Hash.ConstantLength.capacity 2))
              |>.call_keygenRegistered cfg.1 hconfig.1 _ self <;>
            keygen_registration,
          by
            apply AddChip.addFormal.call_keygenRegistered cfg.2.1
                hconfig.2.1 _ (self + 3) <;>
              keygen_registration,
          by
            apply (Ecc.MulFixed.BaseFieldElem.circuit K)
                |>.call_keygenRegistered cfg.2.2.1 hconfig.2.2.1 _
                  (self + 4) <;>
              keygen_registration,
          by
            apply Ecc.Add.addFormal.call_keygenRegistered cfg.2.2.2
                hconfig.2.2.2 _ (self + 8) <;>
              keygen_registration⟩
      lookupSelectorAssignmentsAgree_of_registered := by
        intro cfg counts hconfig input self program operations _hregistered
        simp only [operations, program, Configure.output_pure, synthesize,
          Circuit.operations_bind, Circuit.operations_pure,
          keygen_norm, keygen_spine]
        exact ⟨AddChip.addFormal.call_lookupSelectorAssignmentsAgree
            cfg.2.1 hconfig.2.1 _ _,
          (Ecc.MulFixed.BaseFieldElem.circuit K)
            |>.call_lookupSelectorAssignmentsAgree
              cfg.2.2.1 hconfig.2.2.1 _ _,
          Ecc.Add.addFormal.call_lookupSelectorAssignmentsAgree
            cfg.2.2.2 hconfig.2.2.2 _ _⟩
      lookupSelectorAnchorRequirements cfg _ _ :=
        LookupRangeCheck.lookupSelectorAnchorRequirements
          cfg.2.2.1.lookupConfig
      lookupSelectorsAnchoredBy_of_registered := by
        intro cfg _ hconfig input self anchor hanchor _
        simp only [synthesize, Circuit.operations_bind,
          Circuit.operations_pure, List.append_nil, circuit_norm]
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact (Poseidon.hash (Hash.ConstantLength.capacity 2))
            |>.call_lookupSelectorsAnchoredBy
              cfg.1 hconfig.1 _ self anchor (by trivial)
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact AddChip.addFormal.call_lookupSelectorsAnchoredBy
            cfg.2.1 hconfig.2.1 _ (self + 3) anchor (by trivial)
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact (Ecc.MulFixed.BaseFieldElem.circuit K)
            |>.call_lookupSelectorsAnchoredBy cfg.2.2.1 hconfig.2.2.1 _
              (self + 4) anchor (by
                simpa only [Ecc.MulFixed.BaseFieldElem.circuit_lookupSelectorAnchorRequirements]
                  using hanchor)
        · exact Ecc.Add.addFormal.call_lookupSelectorsAnchoredBy
            cfg.2.2.2 hconfig.2.2.2 _ (self + 8) anchor (by trivial)
      fixedWritesLawful := by
        intro cfg _ hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simp only [Configure.output_pure, synthesize,
            Circuit.operations_bind, Circuit.operations_pure,
            List.forall_append, circuit_norm]
          constructor
          · exact (Poseidon.hash (Hash.ConstantLength.capacity 2))
              |>.call_fixedAssignmentsAgree cfg.1 hconfig.1 _ self
          constructor
          · exact AddChip.addFormal.call_fixedAssignmentsAgree
              cfg.2.1 hconfig.2.1 _ (self + 3)
          constructor
          · exact (Ecc.MulFixed.BaseFieldElem.circuit K)
              |>.call_fixedAssignmentsAgree cfg.2.2.1 hconfig.2.2.1 _
                (self + 4)
          · exact Ecc.Add.addFormal.call_fixedAssignmentsAgree
              cfg.2.2.2 hconfig.2.2.2 _ (self + 8)
        · simp only [synthesize, circuit_norm, synthesis_summary_norm]
      copyCellsAssigned := by
        intro cfg counts hconfig input self
        simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
          List.append_nil, Configure.output_pure, circuit_norm]
        apply Operations.CopyCellsAssignedFrom.append
        · apply (Poseidon.hash (Hash.ConstantLength.capacity 2))
            |>.call_copyCellsAssignedFrom cfg.1 hconfig.1 _ self
          intro cell hcell
          rw [Poseidon.hash_inputCells] at hcell
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
          rcases hcell with rfl | rfl
          · simp only [keygenRequirements, List.mem_cons, true_or]
          · simp only [keygenRequirements, List.mem_cons, true_or, or_true]
        · apply Operations.CopyCellsAssignedFrom.append
          · simp only [circuit_norm]
            apply AddChip.addFormal.call_copyCellsAssignedFrom
              cfg.2.1 hconfig.2.1 _ _
            intro cell hcell
            rw [AddChip.addFormal_inputCells] at hcell
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
            simp only [keygenRequirements, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at ⊢
            rcases hcell with rfl | rfl
            · exact Or.inr (Poseidon.hash_call_output_cell_assigned
                (Hash.ConstantLength.capacity 2) cfg.1 _ self)
            · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · simp only [circuit_norm, Nat.add_assoc]
            apply Operations.CopyCellsAssignedFrom.append
            · apply (Ecc.MulFixed.BaseFieldElem.circuit K)
                |>.call_copyCellsAssignedFrom cfg.2.2.1 hconfig.2.2.1 _ _
              intro cell hcell
              rw [Ecc.MulFixed.BaseFieldElem.circuit_inputCells_eq] at hcell
              simp only [List.mem_singleton] at hcell
              subst cell
              simp only [keygenRequirements, List.mem_append, List.mem_cons,
                List.not_mem_nil, or_false] at ⊢
              exact Or.inr (Or.inr
                (AddChip.addFormal_call_output_cell_assigned cfg.2.1 _ _))
            · simp only [circuit_norm, Nat.add_assoc]
              apply Ecc.Add.addFormal.call_copyCellsAssignedFrom
                cfg.2.2.2 hconfig.2.2.2 _ _
              intro cell hcell
              rw [Ecc.Add.addFormal_inputCells] at hcell
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
              simp only [keygenRequirements, List.mem_append, List.mem_cons,
                List.not_mem_nil, or_false] at ⊢
              rcases hcell with rfl | rfl | rfl | rfl
              · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
              · exact Or.inr (Or.inr (Or.inr
                  (Ecc.MulFixed.BaseFieldElem.circuit_call_output_cells_assigned
                    K cfg.2.2.1 _ _).1))
              · exact Or.inr (Or.inr (Or.inr
                  (Ecc.MulFixed.BaseFieldElem.circuit_call_output_cells_assigned
                    K cfg.2.2.1 _ _).2))
      lookupActivationsWellFormed := by
        intro cfg input self
        simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
          Operations.LookupActivationsWellFormed, List.forall_append,
          circuit_norm]
        exact ⟨(Poseidon.hash (Hash.ConstantLength.capacity 2))
            |>.call_lookupActivationsWellFormed cfg.1 _ self,
          AddChip.addFormal.call_lookupActivationsWellFormed
            cfg.2.1 _ (self + 3),
          (Ecc.MulFixed.BaseFieldElem.circuit K)
            |>.call_lookupActivationsWellFormed cfg.2.2.1 _ (self + 4),
          Ecc.Add.addFormal.call_lookupActivationsWellFormed
            cfg.2.2.2 _ (self + 8)⟩
      output cfg input i :=
        .of (i + 8) 1 cfg.2.2.2.xQR
      regionCount _ := 9
      synthesisSummary cfg _ _ := synthesisSummary cfg
      synthesisSummary_eq := by
        intro cfg input region
        simp only [synthesize, synthesisSummary, circuit_norm, synthesis_summary_norm]
      output_eq := by
        intro cfg input i
        simp only [synthesize, Circuit.output_bind, Circuit.output_pure,
          FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
          FormalCircuit.call_regionCount', circuit_norm,
          Ecc.Add.addFormal_output_cells]
      regionCount_eq := fun (pcfg, acfg, bcfg, ecfg) input i => by
        unfold synthesize
        exact (deriveNullifier_regionCount K pcfg acfg bcfg ecfg input i).symm }

  EnvAssumptions := fun (_, _, bcfg, _) env =>
    Ecc.MulFixed.BaseFieldElem.EnvAssumptions bcfg env

  -- `cm` is an already-assigned valid point
  Assumptions input := input.cm.Valid

  Spec input output _ :=
    output = ((input.cm +
      ((Hash.ConstantLength.value #v[input.nk, input.rho] + input.psi).val : Fq) • K
      : Point Fp)).x

  soundness := by
    circuit_proof_start
    obtain ⟨hHash, hScalar, hBfe, hAdd⟩ := hc
    -- the Poseidon child: the output cell is the one-block hash of `(nk, rho)`
    have hH := hHash trivial trivial
    rw [Poseidon.hash_spec_eq] at hH
    -- the add-chip child: the scalar cell is `hash + psi`
    have hS := hScalar trivial trivial
    rw [AddChip.addFormal_spec_eq] at hS
    -- the fixed-base mul child: the product is `scalar • K`
    have hB := hBfe (by rw [Ecc.MulFixed.BaseFieldElem.circuit_envAssumptions_eq]; exact _hE)
      (by rw [Ecc.MulFixed.BaseFieldElem.circuit_assumptions_eq]; trivial)
    rw [Ecc.MulFixed.BaseFieldElem.circuit_spec_eq] at hB
    simp only [Ecc.MulFixed.BaseFieldElem.Spec] at hB
    -- the complete addition: `nf = cm + product` (both summands valid)
    have hAddS := hAdd trivial (by
      rw [Ecc.Add.addFormal_assumptions_eq]
      exact ⟨hA, by rw [hB]; exact K.smul_valid _⟩)
    rw [Ecc.Add.addFormal_spec_eq] at hAddS
    rw [Ecc.Add.addFormal_output_cells] at hAddS
    have hSum := congrArg Point.x hAddS.2
    simp only [Point.eval_eq, circuit_norm] at hSum
    simp only [Point.eval_eq, circuit_norm] at hB
    rw [← h_output, hSum, hB, hS, hH, constantLength_value_two]

  completeness := by
    circuit_proof_start
    -- the fixed-base mul child's honest contract: the product is `scalar • K`
    have hB := (h_spec_2 (by rw [Ecc.MulFixed.BaseFieldElem.circuit_envAssumptions_eq]; exact _hE) trivial trivial).1
    rw [Ecc.MulFixed.BaseFieldElem.circuit_spec_eq] at hB
    simp only [Ecc.MulFixed.BaseFieldElem.Spec] at hB
    refine ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      ⟨by rw [Ecc.MulFixed.BaseFieldElem.circuit_envAssumptions_eq]; exact _hE, trivial, trivial⟩,
      trivial, ?_, trivial⟩
    rw [Ecc.Add.addFormal_assumptions_eq]
    exact ⟨hA, by rw [hB]; exact K.smul_valid _⟩

@[keygen_norm]
theorem circuit_inputCells_eq (K : FixedBase) {config}
    (configured : (circuit K).Configured config) (input : Var Input Fp) :
    configured.inputCells input =
      [input.nk.cell, input.rho.cell, input.psi.cell,
        input.cm.x.cell, input.cm.y.cell] := by
  rfl

/-- The nullifier cell returned by the call is assigned by its final complete
addition region. -/
theorem circuit_call_output_cell_assigned
    (K : FixedBase)
    (config : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    ((circuit K).output config input region).cell ∈
      (((circuit K).call config input).operations region).assignedCellsFrom region := by
  have houtput : (circuit K).output config input region =
      .of (region + 8) 1 config.2.2.2.xQR := rfl
  rw [houtput]
  rw [FormalCircuit.call_operations]
  let hash := (Poseidon.hash (Hash.ConstantLength.capacity 2)).output
    config.1 { x0 := input.nk, x1 := input.rho } region
  let scalar := AddChip.addFormal.output config.2.1
    { a := hash, b := input.psi } (region + 3)
  let product := (Ecc.MulFixed.BaseFieldElem.circuit K).output config.2.2.1
    scalar (region + 4)
  have hadd := Ecc.Add.addFormal_call_output_cells_assigned config.2.2.2
    { p := input.cm, q := product } (region + 8)
  simp only [circuit, synthesize, Circuit.operations_bind,
    Circuit.operations_pure, FormalCircuit.output_call',
    FormalCircuit.nextRegionIndex_call', FormalCircuit.call_regionCount',
    Operations.assignedCellsFrom_append, circuit_norm,
    Ecc.Add.addFormal_output_cells, List.mem_append, AssignedCell.of_cell,
    Nat.add_assoc, Nat.reduceAdd, hash, scalar, product] at hadd ⊢
  exact Or.inr (Or.inr (Or.inr hadd.1))

@[keygen_norm]
theorem circuit_lookupSelectorAnchorRequirements
    (K : FixedBase)
    (config : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    (circuit K).elaborated.lookupSelectorAnchorRequirements config input region =
      LookupRangeCheck.lookupSelectorAnchorRequirements
        config.2.2.1.lookupConfig := rfl

@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq (K : FixedBase)
    (config : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    (circuit K).elaborated.synthesisSummary config input region =
      synthesisSummary config := rfl

derive_contract_bridges circuit (K : FixedBase) := circuit K

end Zcash.Circuits.Action.DeriveNullifier
