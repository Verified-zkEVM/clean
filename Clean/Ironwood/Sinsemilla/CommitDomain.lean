import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Specs.Sinsemilla
import Clean.Ironwood.Ecc.MulFixed.ShortTheorems
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.FullWidth
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece
import Clean.Ironwood.Sinsemilla.Chain
import Clean.Ironwood.Sinsemilla.HashToPoint
import Clean.Halo2.CircuitTypeDeriving

/-!
# Sinsemilla commit domain

`commit(msg, r) = hash_to_point(Q, msg) + [r]·R`, keeping the per-piece running sums `zs`
(`NoteCommit`/`CommitIvk` read individual `zs[i][j]` cells). The `[r]·R` leg is full-width
fixed-base scalar mul (`Ecc.MulFixed.FullWidth.circuit R`): the blinding scalar enters as the
input's nat-valued reading program `r`, the child derives its 85 window witnesses from it, and the
scalar it encodes is extraction data, so the commitment `Spec` is stated at the extracted scalar.

The `Chain.circuit` enters at an accumulator seeded from the domain point `Q`: the wrapper assigns
`Q`'s coordinates into the entering cells as constrained constants, so soundness pins `A = Q`.

Reference: `halo2_gadgets/src/sinsemilla.rs`.
-/

open ProvableType.Halo2 (eval_cells eval_var eval_var_prover)

namespace Zcash.Circuits.Sinsemilla.CommitDomain

open Halo2
open Ecc (DoubleAndAddRow)
open Ecc.MulFixed (FixedBase)
open Specs.Sinsemilla (Generators hashToPoint)
open Specs (K)
open Sinsemilla (HVec)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)
open Sinsemilla
  (GeneratorTableConfig GeneratorTableLoaded)
open Sinsemilla.Chain
  (zLengths PieceChunks ZsFacts honestChunks PieceBounds ZsHonest pieceChunks_bound
   pieceChunks_honestChunks)

/-! ## Config

The parent config bundles the shared `Chain`/`HashPiece.Config` (the hash leg), the `Ecc.Add`
child config (the final sum), the blinding child's config `BCfg`, and the constant-seed columns
for `Q`. -/

/-- The `commit` config, parameterized by the blinding child's config type `BCfg`. -/
structure Config (BCfg : Type) where
  -- The hash leg's config.
  hashConfig : HashPiece.Config
  -- The final complete-addition child's config.
  addConfig : Ecc.Add.Config
  -- The blinding child's config.
  blindConfig : BCfg

/-! ## Inputs / Output -/

/-- The message pieces and the blinding scalar's nat-valued reading program `r` (a prover hint —
Rust `Value<pallas::Scalar>`; the full-width child derives its 85 window witnesses from it and the
scalar it encodes is the child's extraction data). -/
structure Input (k : ℕ) (F : Type) where
  -- The message pieces (the whole `k`-piece message).
  pieces : Vector F k
  -- The blinding scalar's nat-valued reading program (prover hint).
  r : UnconstrainedNat F
deriving CircuitType

structure Output (ns : List ℕ) (F : Type) where
  -- The commitment point.
  point : Point F
  -- The hash running sums.
  zs : HVec (zLengths ns) F
deriving ProvableStruct

/-! ## The commit body

`commit = hash_to_point(Q, msg) + [r]R` on the `hash_message` bundle (Q-init inside its region);
the `[r]R` leg is the `Ecc.MulFixed.FullWidth` bundle. -/

/-- `CommitDomain::blinding_factor` is the bare `[r]R` — exactly the full-width fixed-base
mul bundle, whose input is the blinding scalar's nat-valued reading program. -/
def blindingFactor (R : FixedBase) :
    FormalCircuit Fp Ecc.MulFixed.Config Ecc.MulFixed.FullWidth.Config UnconstrainedNat Point :=
  Ecc.MulFixed.FullWidth.circuit R

/-! ## The `commit` bundle -/

open Specs.Sinsemilla (hashToPoint)

/-- The region count of `commit`: the blinding child's two regions, the hash region, the
final complete addition. -/
private theorem commit_regionCount
    (G : Generators) (ns : List ℕ)
    (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ [])
    (bcfg : Ecc.MulFixed.FullWidth.Config) (hcfg : HashPiece.Config)
    (acfg : Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let blindOut ← (Ecc.MulFixed.FullWidth.circuit R).call bcfg input.r
        let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns).call hcfg
          { pieces := input.pieces }
        let result ← Ecc.Add.addFormal.call acfg
          { p := hashOut.point, q := blindOut }
        pure result).operations i)
      = 4 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount]
  rw [show ∀ (j : RegionIndex) (inp : Var (Sinsemilla.Chain.Inputs ns.length) Fp),
      Operations.regionCount
        (((HashToPoint.hashCircuit G ns Q hQ hns).call hcfg inp).operations j) = 1
    from fun j inp => by
      rw [FormalCircuit.call_operations]
      simp only [Circuit.operations]
      rw [show ((HashToPoint.hashCircuit G ns Q hQ hns).synthesize hcfg inp j).2.1
          = ((assignRegion (HashToPoint.hashRegion G ns Q hQ hns).name
              ((HashToPoint.hashRegion G ns Q hQ hns).synthesize hcfg 0
                inp)).operations j) from rfl,
        operations_assignRegion]
      simp only [Operations.regionCount]]
  rw [show ∀ (j : RegionIndex) (inp : Var Ecc.Add.Inputs Fp),
      Operations.regionCount
        ((Ecc.Add.addFormal.call acfg inp).operations j) = 1
    from fun j inp => by
      rw [FormalCircuit.call_operations]
      simp only [Circuit.operations]
      rw [show (Ecc.Add.addFormal.synthesize acfg inp j).2.1
          = ((assignRegion "complete point addition"
              (Ecc.Add.add.synthesize acfg 0 inp)).operations j) from rfl,
        operations_assignRegion]
      simp only [Operations.regionCount]]
  rw [Ecc.MulFixed.FullWidth.circuit_call_regionCount R bcfg input.r i]

@[keygen_norm]
def keygenRequirements (G : Generators) (ns : List ℕ)
    (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ []) :
    KeygenRequirements Fp
      (Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
      (Var (Input ns.length) Fp) where
  configLawful cfg :=
    (Ecc.MulFixed.FullWidth.circuit R).Configured cfg.1 ×
      (HashToPoint.hashCircuit G ns Q hQ hns).Configured cfg.2.1 ×
        Ecc.Add.addFormal.Configured cfg.2.2
  gates _ configured :=
    configured.1.gates ++ configured.2.1.gates ++ configured.2.2.gates
  lookups _ configured :=
    configured.1.lookups ++ configured.2.1.lookups ++
      configured.2.2.lookups
  fixedColumns _ configured :=
    configured.1.fixedColumns ++ configured.2.1.fixedColumns ++
      configured.2.2.fixedColumns
  permutationColumns _ configured :=
    configured.1.permutationColumns ++ configured.2.1.permutationColumns ++
      configured.2.2.permutationColumns
  inputCells _ _ input :=
    input.pieces.toList.map (·.cell)

def commitSynthesisSummary (ns : List ℕ)
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config) :
    FloorPlanner.SynthesisSummary :=
  (Ecc.MulFixed.FullWidth.circuitSynthesisSummary cfg.1).combine
    ((HashToPoint.hashCircuitSynthesisSummary ns cfg.2.1).combine
      (FloorPlanner.SynthesisSummary.ofRegion
        (Ecc.Add.synthesisSummary cfg.2.2 0)))

@[synthesis_summary_norm]
theorem commitSynthesisSummary_lookupActivationCount
    (ns : List ℕ)
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config) :
    (commitSynthesisSummary ns cfg).lookupActivationCount =
      (List.ofFn fun i : Fin ns.length => ns.getD i.val 0 + 1).sum := by
  simp only [commitSynthesisSummary, synthesis_summary_norm, Nat.zero_add,
    Nat.add_zero]

@[synthesis_summary_norm]
theorem commitSynthesisSummary_tableRowExtent_eq (ns : List ℕ)
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config) :
    (commitSynthesisSummary ns cfg).tableRowExtent = 0 := by
  simp only [commitSynthesisSummary, synthesis_summary_norm]

def synthesize (G : Generators) (ns : List ℕ) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) : Circuit Fp (Var Point Fp) := do
  let blindOut ← (Ecc.MulFixed.FullWidth.circuit R).call cfg.1 input.r
  let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns).call cfg.2.1
    { pieces := input.pieces }
  let result ← Ecc.Add.addFormal.call cfg.2.2
    { p := hashOut.point, q := blindOut }
  pure result

/-- `CommitDomain::commit`: `[r]R` (the `Ecc.MulFixed.FullWidth` bundle), `hash_to_point(Q, msg)`
(the hash bundle), and the final complete addition `M + [r]R`. `Spec`: the commitment is
`SinsemillaHashToPoint(Q, chunks) + s·R` at the extracted window scalar `s`, whenever the
hash is defined, with the message chunking and running-sum facts exposed. -/
def commit (G : Generators) (ns : List ℕ)
    (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) :
    FormalCircuit Fp
      (Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
      (Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
      (Input ns.length) Point where
  name := "sinsemilla commit"
  configure := pure

  synthesize := synthesize G ns R Q hQ hns

  elaborated :=
    { keygenRequirements := keygenRequirements G ns R Q hQ hns
      registered configInput counts configured input self := by
        have hmulAdd := Ecc.MulFixed.FullWidth.Configured.addPermutationColumns_subset
          R configured.1
        simp only [synthesize, Circuit.operations_bind,
          Operations.KeygenRegistered.append, circuit_norm]
        constructor
        · apply (Ecc.MulFixed.FullWidth.circuit R)
            |>.call_keygenRegistered configInput.1 configured.1 input.r self <;>
              keygen_registration
        constructor
        · apply (HashToPoint.hashCircuit G ns Q hQ hns)
            |>.call_keygenRegistered configInput.2.1 configured.2.1 _ (self + 2)
          · intro gate hgate
            simp only [keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            exact Or.inl (Or.inr hgate)
          · intro lookup hlookup
            simp only [keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            exact Or.inl (Or.inr hlookup)
          · intro column hcolumn
            simp only [keygenRequirements, Configure.fixedColumns_pure,
              List.append_nil, List.mem_append]
            exact Or.inl (Or.inr hcolumn)
          · intro column hcolumn
            simp only [keygenRequirements, Configure.delta_pure,
              KeygenRequirements.inputPermutationColumns,
              List.nil_append, List.mem_append]
            exact Or.inl (Or.inl (Or.inr hcolumn))
          · rw [HashToPoint.hashCircuit_inputCells,
              List.forall_iff_forall_mem]
            intro cell hcell
            simp only [keygenRequirements, Configure.delta_pure,
              KeygenRequirements.inputPermutationColumns,
              List.nil_append, List.mem_append, List.mem_map]
            rcases List.mem_map.mp hcell with ⟨assigned, hassigned, rfl⟩
            exact Or.inr ⟨assigned.cell, ⟨assigned, hassigned, rfl⟩, rfl⟩
        · apply Ecc.Add.addFormal.call_keygenRegistered
            configInput.2.2 configured.2.2 _ (self + 3) <;>
              keygen_registration
      lookupSelectorAssignmentsAgree_of_registered := by
        intro cfg counts hconfig input self program operations _hregistered
        simp only [operations, program, Configure.output_pure, synthesize,
          Circuit.operations_bind, Circuit.operations_pure,
          keygen_norm, keygen_spine]
        exact ⟨(HashToPoint.hashCircuit G ns Q hQ hns)
            |>.call_lookupSelectorAssignmentsAgree
              cfg.2.1 hconfig.2.1 _ _,
          Ecc.Add.addFormal.call_lookupSelectorAssignmentsAgree
            cfg.2.2 hconfig.2.2 _ _⟩
      lookupSelectorsAnchoredBy_of_registered := by
        intro cfg _ hconfig input self anchor _ _
        simp only [synthesize, Circuit.operations_bind,
          Circuit.operations_pure, List.append_nil, circuit_norm]
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact (Ecc.MulFixed.FullWidth.circuit R)
            |>.call_lookupSelectorsAnchoredBy
              cfg.1 hconfig.1 input.r self anchor (by trivial)
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact (HashToPoint.hashCircuit G ns Q hQ hns)
            |>.call_lookupSelectorsAnchoredBy
              cfg.2.1 hconfig.2.1 _ (self + 2) anchor (by trivial)
        · exact Ecc.Add.addFormal.call_lookupSelectorsAnchoredBy
            cfg.2.2 hconfig.2.2 _ (self + 3) anchor (by trivial)
      copyCellsAssigned := by
        intro cfg counts configured input self
        simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
          List.append_nil, Configure.output_pure, circuit_norm]
        apply Operations.CopyCellsAssignedFrom.append
        · apply (Ecc.MulFixed.FullWidth.circuit R)
            |>.call_copyCellsAssignedFrom cfg.1 configured.1 input.r self
          intro cell hcell
          rw [Ecc.MulFixed.FullWidth.circuit_inputCells_eq] at hcell
          contradiction
        · apply Operations.CopyCellsAssignedFrom.append
          · rw [Ecc.MulFixed.FullWidth.circuit_call_regionCount]
            apply (HashToPoint.hashCircuit G ns Q hQ hns)
              |>.call_copyCellsAssignedFrom cfg.2.1 configured.2.1 _ _
            intro cell hcell
            rw [HashToPoint.hashCircuit_inputCells] at hcell
            simp only [keygenRequirements]
            exact List.mem_append_left _ hcell
          · simp only [circuit_norm, Nat.add_assoc]
            apply Ecc.Add.addFormal.call_copyCellsAssignedFrom
              cfg.2.2 configured.2.2 _ _
            intro cell hcell
            rw [Ecc.Add.addFormal_inputCells] at hcell
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
            simp only [keygenRequirements, List.mem_append] at ⊢
            rcases hcell with rfl | rfl | rfl | rfl
            · exact Or.inr (Or.inr
                (HashToPoint.hashCircuit_call_output_point_cells_assigned
                  G ns Q hQ hns cfg.2.1 _ _).1)
            · exact Or.inr (Or.inr
                (HashToPoint.hashCircuit_call_output_point_cells_assigned
                  G ns Q hQ hns cfg.2.1 _ _).2)
            · exact Or.inr (Or.inl
                (Ecc.MulFixed.FullWidth.circuit_call_output_cells_assigned
                  R cfg.1 input.r self).1)
            · exact Or.inr (Or.inl
                (Ecc.MulFixed.FullWidth.circuit_call_output_cells_assigned
                  R cfg.1 input.r self).2)
      fixedWritesLawful := by
        intro cfg _ hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simpa only [Configure.output_pure, synthesize,
            Circuit.operations_bind, Circuit.operations_pure,
            List.forall_append, circuit_norm, Nat.add_assoc] using
            And.intro
              ((Ecc.MulFixed.FullWidth.circuit R).call_fixedAssignmentsAgree
                cfg.1 hconfig.1 input.r self)
              (And.intro
                ((HashToPoint.hashCircuit G ns Q hQ hns)
                  |>.call_fixedAssignmentsAgree cfg.2.1 hconfig.2.1
                    { pieces := input.pieces } (self + 2))
                (Ecc.Add.addFormal.call_fixedAssignmentsAgree
                  cfg.2.2 hconfig.2.2
                    { p := (HashToPoint.hashCircuit G ns Q hQ hns).output
                        cfg.2.1 { pieces := input.pieces } (self + 2) |>.point,
                      q := (Ecc.MulFixed.FullWidth.circuit R).output
                        cfg.1 input.r self }
                    (self + 3)))
        · simp only [synthesize, circuit_norm, synthesis_summary_norm]
      lookupActivationsWellFormed := by
        intro cfg input self
        simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
          Operations.LookupActivationsWellFormed, List.forall_append,
          circuit_norm]
        exact ⟨(Ecc.MulFixed.FullWidth.circuit R)
            |>.call_lookupActivationsWellFormed cfg.1 input.r self,
          (HashToPoint.hashCircuit G ns Q hQ hns)
            |>.call_lookupActivationsWellFormed cfg.2.1 _ (self + 2),
          Ecc.Add.addFormal.call_lookupActivationsWellFormed
            cfg.2.2 _ (self + 3)⟩
      output cfg _ i :=
        { x := .of (i + 3) 1 cfg.2.2.xQR
          y := .of (i + 3) 1 cfg.2.2.yQR }
      regionCount _ := 4
      synthesisSummary cfg _ _ := commitSynthesisSummary ns cfg
      synthesisSummary_eq := by
        intro cfg input region
        simp only [synthesize, commitSynthesisSummary, circuit_norm, synthesis_summary_norm]
      output_eq := by
        intro _ _ _
        simp only [synthesize, circuit_norm, keygen_output_norm]
      regionCount_eq := fun (bcfg, hcfg, acfg) input i =>
        by
          unfold synthesize
          exact (commit_regionCount G ns R Q hQ hns bcfg hcfg acfg input i).symm }

  EnvAssumptions := fun (bcfg, hcfg, _) env =>
    Sinsemilla.GeneratorTableLoaded G hcfg.generatorTable env.env ∧
    Ecc.MulFixed.FullWidth.EnvAssumptions bcfg env

  Assumptions _ := True

  Witness := fun F => Sinsemilla.Chain.ChainWit ns F × (Vector F 85 × Fq)
  extract := fun (bcfg, hcfg, _) input i₀ env =>
    ((HashToPoint.hashCircuit G ns Q hQ hns).extract hcfg
      { pieces := input.pieces } (i₀ + 2) env,
     Ecc.MulFixed.FullWidth.fwExtract bcfg i₀ env)

  Spec input output wit :=
    ∃ chunks : List ℕ,
      Sinsemilla.Chain.PieceChunks ns (input.pieces) chunks ∧
      Sinsemilla.Chain.ZsFacts ns chunks wit.1.zs ∧
      ∀ B, hashToPoint G.S Q chunks = some B →
        output.Valid ∧ output = B + wit.2.2 • R

  ProverAssumptions input _ _ :=
    Sinsemilla.Chain.PieceBounds ns (input.pieces) ∧
    (∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns (input.pieces)) = some B)

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start2
    obtain ⟨hTableE, hMulE⟩ := env_assumptions
    -- the blind child's contract: the output is the extracted window scalar times `R`
    rw [Ecc.MulFixed.FullWidth.circuit_extract_eq] at wit_blindOut_eq
    have hBl := blindOut_spec
      (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hMulE)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq, ← wit_blindOut_eq] at hBl
    -- the hash child's contract
    have hHashS := hashOut_spec
      (by rw [HashToPoint.hashCircuit_envAssumptions_eq]; exact hTableE) trivial
    rw [HashToPoint.hashCircuit_spec_eq] at hHashS
    obtain ⟨chunks, hPC, hZs, -, hContract⟩ := hHashS
    -- input eval landing: bridge to the whole-struct `input_eq`
    have hPC' : PieceChunks ns input.pieces chunks := by
      rw [← input_eq]
      exact hPC
    refine ⟨chunks, hPC', hZs, ?_⟩
    intro B hB
    have hcoords := hContract B hB
    -- the hash output point value IS the eval'd point (projection commute; go through
    -- the componentwise `ProvableStruct.Halo2.eval` — the flat eval of the whole symbolic-size
    -- Output struct is a whnf wall)
    have hpoint : (ProvableStruct.Halo2.eval place env hashOut).point
        = (eval (⟨place, env⟩ : Placed Environment Fp) hashOut.point
          : Value Point Fp) := by
      rw [ProvableType.Halo2.eval_cells]; rfl
    -- the hash point equals B
    have hPB : (eval (⟨place, env⟩ : Placed Environment Fp) hashOut.point
        : Value Point Fp) = B := by
      obtain ⟨bx, byv⟩ := B
      have hx : (eval (⟨place, env⟩ : Placed Environment Fp) hashOut.point
          : Value Point Fp).x = bx := by
        rw [← hpoint]; exact hcoords.1
      have hy : (eval (⟨place, env⟩ : Placed Environment Fp) hashOut.point
          : Value Point Fp).y = byv := by
        rw [← hpoint]; exact hcoords.2
      rw [← hx, ← hy]
    -- B is a valid point (the chunks are generator indices)
    have hBvalid : B.Valid :=
      Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ)
        (Sinsemilla.Chain.pieceChunks_bound hPC) hB
    -- the complete addition's contract (input literal already eval'd componentwise)
    have hAddS := result_spec trivial (by
      show (eval (⟨place, env⟩ : Placed Environment Fp) hashOut.point
          : Value Point Fp).Valid ∧
        (eval (⟨place, env⟩ : Placed Environment Fp) blindOut
          : Value Point Fp).Valid
      constructor
      · rw [hPB]; exact hBvalid
      · rw [hBl]; exact R.smul_valid _)
    obtain ⟨hVout, hSum⟩ := hAddS
    have hresult : (eval (⟨place, env⟩ : Placed Environment Fp) result
        : Value Point Fp) = { x := output_x, y := output_y } := by
      rw [← result_eq]
      rw [Ecc.Add.addFormal_output, Ecc.Add.add_output_cells]
      rw [ProvableType.Halo2.eval_cells, Sinsemilla.Chain.point_eval_literal]
      congr 1
      · exact output_eq.1
      · exact output_eq.2
    rw [← hresult]
    exact ⟨hVout, by rw [hSum, hPB, hBl]⟩

  completeness := by
    circuit_proof_start2
    obtain ⟨hTableE, hMulE⟩ := env_assumptions
    obtain ⟨hPBounds, B0, hB0⟩ := prover_assumptions
    obtain ⟨bx, byv⟩ := B0
    -- the blind child's contract
    have hBl := (blindOut_spec (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hMulE)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
      (by rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq]; trivial)).1
    rw [Ecc.MulFixed.FullWidth.circuit_extract_eq] at wit_blindOut_eq
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq, ← wit_blindOut_eq] at hBl
    -- the pieces value bridge: the hint-erased eval of the message-piece cells equals
    -- the prover-view piece value (`input_eq` lands the whole struct; the hint-erased
    -- and prover-view evals of a pure-provable var agree up to defeq)
    have hpe : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) input_var.pieces
        : Value (fields ns.length) Fp) = input.pieces := by
      rw [← input_eq, ProvableType.Halo2.eval_var, ProvableType.Halo2.eval_var_prover]
    -- the hash child's honest-prover precondition, transported to the minted witness
    have hPAhash : (HashToPoint.hashCircuit G ns Q hQ hns).ProverAssumptions
        ({ pieces := eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) input_var.pieces }
          : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
        wit_hashOut env.hint := by
      rw [← wit_hashOut_eq, HashToPoint.hashCircuit_proverAssumptions_eq]
      simp only [hpe]
      exact ⟨hns, hPBounds, ⟨bx, byv⟩, hB0⟩
    -- the hash child's honest contract (prover side: the output point IS the honest hash)
    have hPSHash := (hashOut_spec (by rw [HashToPoint.hashCircuit_envAssumptions_eq]; exact hTableE)
      trivial hPAhash).2
    rw [HashToPoint.hashCircuit_proverSpec_eq] at hPSHash
    have hres := hPSHash ⟨bx, byv⟩ (by
      simp only [hpe]; exact hB0)
    -- projection commute through the componentwise `ProvableStruct.Halo2.eval` (the flat
    -- eval of the whole symbolic-size Output struct is a whnf wall)
    have hpointP : (ProvableStruct.Halo2.eval place env.toEnvironment hashOut).point
        = (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) hashOut.point
          : Value Point Fp) := by
      rw [ProvableType.Halo2.eval_cells]; rfl
    -- the hash point equals the honest B0
    have hPB0 : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) hashOut.point : Value Point Fp)
        = (⟨bx, byv⟩ : Point Fp) := by
      have hx : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) hashOut.point : Value Point Fp).x = bx := by
        rw [← hpointP]; exact hres.1
      have hy : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) hashOut.point : Value Point Fp).y = byv := by
        rw [← hpointP]; exact hres.2
      rw [← hx, ← hy]
    have hB0valid : (⟨bx, byv⟩ : Point Fp).Valid :=
      Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ)
        (Sinsemilla.Chain.pieceChunks_bound
          (Sinsemilla.Chain.pieceChunks_honestChunks ns input.pieces hPBounds)) hB0
    refine ⟨⟨by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hMulE,
      by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial,
      by rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq]; trivial⟩,
      ⟨by rw [HashToPoint.hashCircuit_envAssumptions_eq]; exact hTableE, trivial,
        hPAhash⟩,
      trivial, ?_, trivial⟩
    show (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) hashOut.point
        : Value Point Fp).Valid ∧
      (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) blindOut
        : Value Point Fp).Valid
    constructor
    · rw [hPB0]; exact hB0valid
    · rw [hBl]; exact R.smul_valid _

/-- Assemble a Sinsemilla commitment capability from its three direct children. -/
def configurationCertificate (G : Generators) (ns : List ℕ)
    (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    {bcfg : Ecc.MulFixed.FullWidth.Config} {hcfg : HashPiece.Config}
    {acfg : Ecc.Add.Config} {context : KeygenContext Fp}
    (mul : (Ecc.MulFixed.FullWidth.circuit R).ConfigurationCertificate bcfg context)
    (hash : (HashToPoint.hashCircuit G ns Q hQ hns).ConfigurationCertificate
      hcfg context)
    (add : Ecc.Add.addFormal.ConfigurationCertificate acfg context) :
    (commit G ns R Q hQ hns).ConfigurationCertificate
      (bcfg, hcfg, acfg) context := by
  let lawful : (keygenRequirements G ns R Q hQ hns).configLawful
      (bcfg, hcfg, acfg) := ⟨mul.configured, hash.configured, add.configured⟩
  apply ((commit G ns R Q hQ hns).configureCertificate
    (bcfg, hcfg, acfg) {} lawful).mono
  · intro required hrequired
    simp only [commit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with (hrequired | hrequired) | hrequired
    · exact mul.gates_of_configured required hrequired
    · exact hash.gates_of_configured required hrequired
    · exact add.gates_of_configured required hrequired
  · intro required hrequired
    simp only [commit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with (hrequired | hrequired) | hrequired
    · exact mul.lookups_of_configured required hrequired
    · exact hash.lookups_of_configured required hrequired
    · exact add.lookups_of_configured required hrequired
  · intro column hcolumn
    simp only [commit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.fixedColumns_pure, List.append_nil, List.mem_append] at hcolumn
    rcases hcolumn with (hmul | hhash) | hadd
    · exact mul.fixedColumns_of_configured column hmul
    · exact hash.fixedColumns_of_configured column hhash
    · exact add.fixedColumns_of_configured column hadd
  · intro column hcolumn
    simp only [commit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hcolumn
    rcases hcolumn with (hmul | hhash) | hadd
    · exact mul.permutationColumns_of_configured column hmul
    · exact hash.permutationColumns_of_configured column hhash
    · exact add.permutationColumns_of_configured column hadd

@[synthesis_summary_norm]
theorem commit_synthesisSummary_eq
    (G : Generators) (ns : List ℕ) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (region : RegionIndex) :
    (commit G ns R Q hQ hns).elaborated.synthesisSummary cfg input region =
      commitSynthesisSummary ns cfg := rfl

derive_contract_bridges commit (G : Generators) (ns : List ℕ) (R : FixedBase)
  (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ []) := commit G ns R Q hQ hns

/-- The commitment result occupies the complete-addition output columns. -/
theorem commit_output_cells (G : Generators) (ns : List ℕ) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (i : RegionIndex) :
    (commit G ns R Q hQ hns).output cfg input i =
      { x := .of (i + 3) 1 cfg.2.2.xQR,
        y := .of (i + 3) 1 cfg.2.2.yQR } := by
  rfl

/-- Both commitment coordinates are assigned by the final addition call. -/
theorem commit_call_output_cells_assigned
    (G : Generators) (ns : List ℕ) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (region : RegionIndex) :
    let output := (commit G ns R Q hQ hns).output cfg input region
    output.x.cell ∈
        Operations.assignedCellsFrom
          (((commit G ns R Q hQ hns).call cfg input).operations region) region ∧
      output.y.cell ∈
        Operations.assignedCellsFrom
          (((commit G ns R Q hQ hns).call cfg input).operations region) region := by
  rw [commit_output_cells, FormalCircuit.call_operations]
  let blind := (Ecc.MulFixed.FullWidth.circuit R).output cfg.1 input.r region
  let hash := (HashToPoint.hashCircuit G ns Q hQ hns).output cfg.2.1
    { pieces := input.pieces } (region + 2)
  have hadd := Ecc.Add.addFormal_call_output_cells_assigned cfg.2.2
    { p := hash.point, q := blind } (region + 3)
  simp only [commit, synthesize, Circuit.operations_bind, Circuit.operations_pure,
    FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
    FormalCircuit.call_regionCount', Operations.assignedCellsFrom_append,
    circuit_norm, Ecc.Add.addFormal_output_cells, List.mem_append,
    AssignedCell.of_cell, Nat.add_assoc, Nat.reduceAdd, blind, hash] at hadd ⊢
  constructor
  · exact Or.inr (Or.inr hadd.1)
  · exact Or.inr (Or.inr hadd.2)

/-- A running-sum cell assigned by the hash child remains assigned in the
enclosing commitment call. -/
theorem commit_call_hash_z_cell_assigned
    (G : Generators) (ns : List ℕ) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (self : RegionIndex)
    (i : Fin ns.length) (r : Fin (ns.getD i.val 0 + 1)) :
    Cell.of (self + 2) (Sinsemilla.Chain.prefixRows ns i.val + r.val)
        cfg.2.1.bits ∈
      Operations.assignedCellsFrom
        (((commit G ns R Q hQ hns).call cfg input).operations self) self := by
  have hhash := HashToPoint.hashCircuit_call_z_cell_assigned
    G ns Q hQ hns cfg.2.1 { pieces := input.pieces } (self + 2) i r
  have hmul := Ecc.MulFixed.FullWidth.circuit_call_regionCount
    R cfg.1 input.r self
  rw [FormalCircuit.call_operations]
  simp only [commit, synthesize, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil,
    Operations.assignedCellsFrom_append,
    FormalCircuit.nextRegionIndex_call',
    hmul,
    HashToPoint.hashCircuit_call_regionCount, Nat.add_assoc]
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inl hhash)))

/-- A `z₁` cell assigned by the hash child remains assigned in the enclosing
commitment call. -/
theorem commit_call_hash_z1_cell_assigned
    (G : Generators) (ns : List ℕ) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (self : RegionIndex)
    (i : Fin ns.length) (hi : 0 < ns.getD i.val 0) :
    ((HashToPoint.hashCircuit G ns Q hQ hns).output cfg.2.1
        { pieces := input.pieces } (self + 2)).z1s[i].cell ∈
      Operations.assignedCellsFrom
        (((commit G ns R Q hQ hns).call cfg input).operations self) self := by
  rw [HashToPoint.hashCircuit_output_z1s]
  simpa only [Fin.getElem_fin, Vector.getElem_ofFn, AssignedCell.of_cell,
    Nat.zero_add] using commit_call_hash_z_cell_assigned
      G ns R Q hQ hns cfg input self i ⟨1, by omega⟩

@[keygen_norm]
theorem commit_inputCells (G : Generators) (ns : List ℕ) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ []) {cfg}
    (configured : (commit G ns R Q hQ hns).Configured cfg)
    (input : Var (Input ns.length) Fp) :
    configured.inputCells input = input.pieces.toList.map fun assigned => assigned.cell := by
  rfl

end Zcash.Circuits.Sinsemilla.CommitDomain
