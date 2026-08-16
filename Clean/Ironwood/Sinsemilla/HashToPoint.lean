import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Specs.Sinsemilla
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece
import Clean.Ironwood.Sinsemilla.Chain

/-!
# Sinsemilla `hash_message` — the layouter-level hash region

`hash_message` is `public_q_initialization` + `hash_all_pieces` in one `"hash_to_point"` region;
each message piece is witnessed in its own `"witness message piece"` region.

`public_q_initialization` (public `Q`, the Orchard branch): enable `q_sinsemilla4` on the first
row, load `y_Q` into the `fixed_y_q` column there, and assign `x_Q` into `x_a` from a constant.
The hash (`Chain.circuit`) starts at the same offset: the init row is the first word row, and the
`Initial y_Q` gate checks `2·y_Q = Y_A(row 0)` against the first word's slopes.

Reference: `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`.
-/

open ProvableStruct.Halo2 (eval_cells_eq_eval eval_cells_eq_eval_prover)

namespace Zcash.Circuits.Sinsemilla.HashToPoint

open Halo2
open Specs.Sinsemilla (Generators)

/-- Constant single-cell witness program. -/
def constWit (c : Fp) : WitgenIR Fp 1 := .native fun _ => #v[c]

@[circuit_norm]
theorem constWit_eval (c : Fp) (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((constWit c).eval env)[j] = c := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [constWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Rust `witness_message_piece`: one piece witnessed at `(witness_pieces, 0)` of its own
region, from the caller-supplied witness program. -/
def witnessMessagePiece (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp) :=
  assignRegion "witness message piece" (assignAdvice cfg.witnessPieces 0 w)

def witnessMessagePieceSynthesisSummary
    (cfg : Sinsemilla.HashPiece.Config) : FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (FloorPlanner.RegionSynthesisSummary.ofColumns
      [.column .advice cfg.witnessPieces.index] 1 0)

@[synthesis_summary_norm]
theorem witnessMessagePiece_synthesisSummary
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    FloorPlanner.synthesisSummary
      ((witnessMessagePiece cfg w).operations region) =
        witnessMessagePieceSynthesisSummary cfg := by
  simp only [witnessMessagePieceSynthesisSummary, witnessMessagePiece,
    operations_assignRegion, circuit_norm, synthesis_summary_norm]

@[circuit_norm]
theorem witnessMessagePiece_nextRegionIndex
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    (witnessMessagePiece cfg w).nextRegionIndex region = region + 1 := by
  simp only [witnessMessagePiece, circuit_norm]

@[circuit_norm]
theorem witnessMessagePiece_regionCount
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    ((witnessMessagePiece cfg w).operations region).regionCount = 1 := by
  simp only [witnessMessagePiece, operations_assignRegion,
    Operations.regionCount]

/-- Assigning a message piece has no keygen requirements. -/
@[keygen_norm, keygen_helper]
theorem witnessMessagePiece_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    ((witnessMessagePiece cfg w).operations region).KeygenRegistered
      gates lookups fixedColumns permutationColumns := by
  unfold witnessMessagePiece
  keygen_registration

/-- Witnessing a message piece introduces no copy endpoints. -/
theorem witnessMessagePiece_copyCellsAssignedFrom
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (region : RegionIndex) (available : List Cell) :
    ((witnessMessagePiece cfg w).operations region)
      |>.CopyCellsAssignedFrom region available := by
  simp only [witnessMessagePiece, circuit_norm, keygen_spine]

/-- Witnessing a message piece does not introduce malformed lookup
activations. -/
theorem witnessMessagePiece_lookupActivationsWellFormed
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    ((witnessMessagePiece cfg w).operations region)
      |>.LookupActivationsWellFormed := by
  simp only [witnessMessagePiece, circuit_norm, keygen_spine]

/-- Witnessing a message piece requests no deferred constants. -/
@[synthesis_summary_norm]
theorem witnessMessagePiece_synthesisSummary_constantSiteCount
    (config : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    (FloorPlanner.synthesisSummary
      ((witnessMessagePiece config w).operations region)).constantSiteCount = 0 := by
  rw [witnessMessagePiece_synthesisSummary]
  simp only [witnessMessagePieceSynthesisSummary, synthesis_summary_norm]

/-- A witnessed message piece stays in the chip's witness-piece column. -/
@[keygen_norm, keygen_output_norm]
theorem witnessMessagePiece_output_column (cfg : Sinsemilla.HashPiece.Config)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    ((witnessMessagePiece cfg w).output i).cell.column = cfg.witnessPieces := by
  simp only [witnessMessagePiece, circuit_norm]

/-- The cell returned by a message-piece witness was assigned in its region. -/
theorem witnessMessagePiece_output_cell_assigned
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    ((witnessMessagePiece cfg w).output i).cell ∈
      Operations.assignedCellsFrom ((witnessMessagePiece cfg w).operations i) i := by
  simp only [witnessMessagePiece, circuit_norm, Operations.assignedCellsFrom,
    RegionOperations.assignedCells, List.flatMap_cons,
    RegionOperation.assignedCells, List.singleton_append, List.mem_cons, true_or]

/-! ## The layouter-level `hash_message`

The formal wrapper is `(hashRegion …).toFormal` (below); `hashMessage` is its `.call`. -/

/-! ## The formal `hash_message` bundle

The region-level Q-pin wrapper over `Chain.circuit`: the `public_q_initialization` ops pin
the entering accumulator to the public `Q` (the constant copy fixes `x_a(0) = Q.x`; the
`Initial y_Q` gate fixes `Y_A(0) = 2·Q.y`), so the chain's `∀ A`-quantified contract
collapses to the hash from `Q`. `toFormal "hash_to_point"` lifts it to the layouter level
(one region — the Rust `hash_to_point` `assign_region`). -/

open Sinsemilla.Chain in
/-- The per-piece `z_1` values off the chain's running-sum extraction data (`HVec` is
stored flat; piece `i`'s `z_1` sits at flat index `prefixRows ns i + 1`). -/
def z1View (ns : List ℕ) (zs : Sinsemilla.HVec (zLengths ns) Fp) :
    Vector Fp ns.length :=
  Vector.ofFn fun i : Fin ns.length => zs.elems[prefixRows ns ↑i + 1]!

open Sinsemilla.Chain in
/-- The flat contents of the abstract running-sum family. -/
private theorem zsFam_elems (f : ℕ → Fp) : ∀ (ns : List ℕ) (off : ℕ),
    (zsFam f ns off).elems
      = Vector.ofFn (fun k : Fin (zLengths ns).sum => f (off + k.val))
  | [], _ => rfl
  | n :: rest, off => by
    show (Vector.ofFn fun r : Fin (n + 1) => f (off + r.val))
        ++ (zsFam f rest (off + (n + 1))).elems = _
    rw [zsFam_elems f rest (off + (n + 1))]
    ext j hj
    have hjs : j < (zLengths (n :: rest)).sum := by
      have h := hj
      simp only [zLengths, List.map_cons, List.sum_cons] at h ⊢
      omega
    simp only [Vector.getElem_append, Vector.getElem_ofFn]
    split
    · exact (Vector.getElem_ofFn
        (f := fun k : Fin (n + 1 + (zLengths rest).sum) => f (off + (k : ℕ))) hj).symm
    · next h =>
      rw [show f (off + (n + 1) + (j - (n + 1))) = f (off + j) from by congr 1; omega]
      exact (Vector.getElem_ofFn
        (f := fun k : Fin (n + 1 + (zLengths rest).sum) => f (off + (k : ℕ))) hj).symm

open Sinsemilla.Chain in
/-- `z1View` over the abstract running-sum family: the per-piece `base + 1` reads
(each piece must have ≥ 2 words — `z_1` exists). -/
private theorem z1View_zsFam (f : ℕ → Fp) (ns : List ℕ) (off : ℕ)
    (hpos : ∀ x ∈ ns, 0 < x) :
    z1View ns (zsFam f ns off)
      = Vector.ofFn (fun i : Fin ns.length => f (off + (prefixRows ns ↑i + 1))) := by
  have hsum : (zLengths ns).sum = prefixRows ns ns.length := by
    simp [zLengths, prefixRows, List.take_length]
  have hidx : ∀ i : Fin ns.length, prefixRows ns ↑i + 1 < (zLengths ns).sum := by
    intro i
    have hstep := prefixRows_step ns ↑i i.isLt
    have hpos_i : 0 < ns.getD ↑i 0 := by
      rw [List.getD_eq_getElem ns 0 i.isLt]
      exact hpos _ (ns.getElem_mem i.isLt)
    have hmono : prefixRows ns (↑i + 1) ≤ (zLengths ns).sum := by
      show ((ns.take (↑i + 1)).map (· + 1)).sum ≤ _
      rw [List.map_take]
      conv_rhs => rw [show (zLengths ns) = (ns.map (· + 1)) from rfl,
        ← List.take_append_drop (↑i + 1) (ns.map (· + 1))]
      rw [List.sum_append]
      omega
    omega
  ext j hj
  simp only [z1View, Vector.getElem_ofFn]
  rw [zsFam_elems,
    getElem!_pos (Vector.ofFn fun k : Fin (zLengths ns).sum => f (off + k.val))
      (prefixRows ns j + 1) (hidx ⟨j, hj⟩)]
  simp [Vector.getElem_ofFn]

/-- The hash output: the point and the per-piece `z_1` cells (`zs[i][1]` — what Merkle's
decomposition gate reads). -/
structure Output (k : ℕ) (F : Type) where
  point : Point F
  z1s : Vector F k
deriving ProvableStruct

/-- The verifier contract: the pieces decompose into `K`-bit chunks (with the running-sum
facts on the extraction data and the `z_1` view exposed on the output), and the output
point is `SinsemillaHashToPoint(Q, chunks)` whenever defined. -/
def Spec (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp) (output : Value (Output ns.length) Fp)
    (wit : Sinsemilla.Chain.ChainWit ns Fp) : Prop :=
  ∃ chunks : List ℕ, Sinsemilla.Chain.PieceChunks ns input.pieces chunks ∧
    Sinsemilla.Chain.ZsFacts ns chunks wit.zs ∧
    ((∀ x ∈ ns, 0 < x) → output.z1s = z1View ns wit.zs) ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output.point.x = B.x ∧ output.point.y = B.y

/-- The honest-prover precondition: nonempty message, pieces in range, honest hash defined. -/
def ProverAssumptions (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp) : Prop :=
  ns ≠ [] ∧ Sinsemilla.Chain.PieceBounds ns input.pieces ∧
  ∃ B, Specs.Sinsemilla.hashToPoint G.S Q
    (Sinsemilla.Chain.honestChunks ns input.pieces) = some B

/-- The honest-prover contract: the output point is the honest hash. -/
def ProverSpec (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
    (output : Value (Output ns.length) Fp) : Prop :=
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q
    (Sinsemilla.Chain.honestChunks ns input.pieces) = some B →
    output.point.x = B.x ∧ output.point.y = B.y

derive_contract_bridges chainC (G : Generators) (ns : List ℕ) (Q : Point Fp) :=
  Sinsemilla.Chain.circuit G ns (fun _ => Q.y)

/-- Literal-eval bridge for the output record. -/
private theorem out_eval_lit {k : ℕ} (env : Placed Environment Fp)
    (p : Point (AssignedCell Fp)) (v : Vector (AssignedCell Fp) k) :
    (eval env ({ point := p, z1s := v } : Output k (AssignedCell Fp)) : Value (Output k) Fp)
      = { point := { x := AssignedCell.eval env.place env.env p.x,
                     y := AssignedCell.eval env.place env.env p.y },
          z1s := v.map (AssignedCell.eval env.place env.env) } := by
  rw [ProvableStruct.Halo2.eval_cells_eq_eval]
  rw [show ProvableStruct.Halo2.eval env.place env.env
      ({ point := p, z1s := v } : Output k (AssignedCell Fp))
    = ({ point := ProvableType.Halo2.eval env.place env.env p,
         z1s := ProvableType.Halo2.eval (M := fields k) env.place env.env v }
        : Value (Output k) Fp) from by rfl]
  rw [show p = ({ x := p.x, y := p.y } : Point (AssignedCell Fp)) from rfl,
    Sinsemilla.Chain.point_eval_literal, Sinsemilla.Chain.eval_fields_eq_map]

/-- Literal-eval bridge for the output record, prover view. -/
private theorem out_eval_lit_prover {k : ℕ} (env : Placed ProverEnvironment Fp)
    (p : Point (AssignedCell Fp)) (v : Vector (AssignedCell Fp) k) :
    (eval env ({ point := p, z1s := v } : Output k (AssignedCell Fp)) : Value (Output k) Fp)
      = { point := { x := AssignedCell.eval env.place env.env.toEnvironment p.x,
                     y := AssignedCell.eval env.place env.env.toEnvironment p.y },
          z1s := v.map (AssignedCell.eval env.place env.env.toEnvironment) } := by
  rw [ProvableStruct.Halo2.eval_cells_eq_eval_prover]
  rw [show ProvableStruct.Halo2.eval env.place env.env.toEnvironment
      ({ point := p, z1s := v } : Output k (AssignedCell Fp))
    = ({ point := ProvableType.Halo2.eval env.place env.env.toEnvironment p,
         z1s := ProvableType.Halo2.eval (M := fields k) env.place env.env.toEnvironment v }
        : Value (Output k) Fp) from by rfl]
  rw [show p = ({ x := p.x, y := p.y } : Point (AssignedCell Fp)) from rfl,
    Sinsemilla.Chain.point_eval_literal, Sinsemilla.Chain.eval_fields_eq_map]

def z1Cells (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (offset : ℕ) : RegionCircuit Fp (Var (fields ns.length) Fp) :=
  fun self =>
    (Vector.ofFn (fun i : Fin ns.length =>
      AssignedCell.of self (offset + Sinsemilla.Chain.prefixRows ns ↑i + 1) cfg.bits),
     [])

@[circuit_norm]
theorem z1Cells_operations (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (offset : ℕ) (self : RegionIndex) :
    (z1Cells ns cfg offset).operations self = [] := rfl

@[circuit_norm]
theorem z1Cells_output (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (offset : ℕ) (self : RegionIndex) :
    (z1Cells ns cfg offset).output self =
      Vector.ofFn (fun i : Fin ns.length =>
        AssignedCell.of self
          (offset + Sinsemilla.Chain.prefixRows ns ↑i + 1) cfg.bits) := rfl

def hashRegionSynthesize (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (cfg : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) :
    RegionCircuit Fp (Var (Output ns.length) Fp) := do
  (Sinsemilla.HashPiece.initialYQGate cfg).enable offset
  let _yq ← assignFixed cfg.fixedYQ offset Q.y
  let xa ← assignAdvice cfg.xA offset (constWit Q.x)
  constrainConstant xa Q.x
  let out ← (Sinsemilla.Chain.circuit G ns (fun _ => Q.y)).call cfg offset pieces
  let z1s ← z1Cells ns cfg offset
  pure ({ point := out.point, z1s := z1s } : Output ns.length (AssignedCell Fp))

@[circuit_norm]
theorem hashRegionSynthesize_output (G : Generators) (ns : List ℕ)
    (Q : Point Fp) (cfg : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) :
    (hashRegionSynthesize G ns Q cfg offset input).output self =
      { point :=
          { x := AssignedCell.of self
              (offset + Sinsemilla.Chain.prefixRows ns ns.length) cfg.xA,
            y := AssignedCell.of self
              (offset + Sinsemilla.Chain.prefixRows ns ns.length) cfg.lambda1 },
        z1s := Vector.ofFn (fun i : Fin ns.length =>
          AssignedCell.of self
            (offset + Sinsemilla.Chain.prefixRows ns ↑i + 1) cfg.bits) } := by
  simp only [hashRegionSynthesize, circuit_norm, keygen_output_norm]
  exact ⟨rfl, rfl⟩

theorem hashRegionSynthesize_assignFixed_mem_iff
    (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (cfg : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) (column : Column .fixed) (row : ℕ) (value : Fp) :
    .assignFixed column row value ∈
        (hashRegionSynthesize G ns Q cfg offset input).operations self ↔
      (column = cfg.fixedYQ ∧ row = offset ∧ value = Q.y) ∨
        .assignFixed column row value ∈
          ((Sinsemilla.Chain.circuit G ns fun _ => Q.y).call
            cfg offset input).operations self := by
  simp only [hashRegionSynthesize, circuit_norm, List.mem_append]
  rw [z1Cells_operations]
  simp

def hashRegionSynthesisSummary (ns : List ℕ)
    (cfg : Sinsemilla.HashPiece.Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  (FloorPlanner.RegionSynthesisSummary.ofColumns
    [.selector (Sinsemilla.HashPiece.initialYQGate cfg).selector.index,
      .column .fixed cfg.fixedYQ.index,
      .column .advice cfg.xA.index]
    (offset + 1) 1).combine
      (Sinsemilla.Chain.circuitSynthesisSummary ns cfg offset)

/-- The `hash_message` region bundle (public `Q`): `public_q_initialization` + the chain.
`hns`: a Sinsemilla message is nonempty (for `ns = []` the trailing dummy row's `λ₁` is
unconstrained, so the exit `y` would be unpinned). -/
def hashRegion (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) :
    FormalRegionCircuit Fp Sinsemilla.HashPiece.Config Sinsemilla.HashPiece.Config
      (Sinsemilla.Chain.Inputs ns.length) (Output ns.length) where
  name := "hash_to_point"
  configure := pure

  synthesize := hashRegionSynthesize G ns Q

  elaborated :=
    { keygenRequirements :=
        { configLawful cfg := Sinsemilla.HashPiece.Config.FixedColumnsLawful cfg
          gates cfg _ :=
            [Sinsemilla.HashPiece.initialYQGate cfg,
              Sinsemilla.HashPiece.sinsemillaGate cfg]
          lookups cfg _ := [Sinsemilla.HashPiece.generatorLookup G cfg]
          fixedColumns cfg _ := [cfg.fixedYQ, cfg.qS2]
          permutationColumns cfg _ := [cfg.xA, cfg.lambda1, cfg.bits]
          inputCells _ _ input :=
            input.pieces.toList.map (·.cell) }
      registered := by
        intro cfg counts hconfig offset input region
        let hchain : (Sinsemilla.Chain.circuit G ns fun _ => Q.y).Configured cfg :=
          FormalRegionCircuit.Configured.ofPure _ cfg () rfl
        keygen_registration [hashRegionSynthesize]
        apply (Sinsemilla.Chain.circuit G ns fun _ => Q.y)
          |>.callPacked_keygenRegistered cfg hchain offset input region
        · simp only [hchain, FormalRegionCircuit.Configured.ofPure_gates,
            FormalRegionCircuit.keygenRequirements,
            Sinsemilla.Chain.circuit, ElaboratedRegionCircuit.keygenRequirements,
            List.mem_cons] at *
          aesop
        · simp only [hchain, FormalRegionCircuit.Configured.ofPure_lookups,
            FormalRegionCircuit.keygenRequirements,
            Sinsemilla.Chain.circuit, ElaboratedRegionCircuit.keygenRequirements,
            List.mem_cons] at *
          aesop
        · simp only [hchain,
            FormalRegionCircuit.Configured.ofPure_fixedColumns,
            FormalRegionCircuit.keygenRequirements,
            Sinsemilla.Chain.circuit, ElaboratedRegionCircuit.keygenRequirements,
            List.mem_singleton] at *
          simp_all
        · simp only [hchain,
            FormalRegionCircuit.Configured.ofPure_permutationColumns,
            FormalRegionCircuit.keygenRequirements,
            Sinsemilla.Chain.circuit, ElaboratedRegionCircuit.keygenRequirements,
            List.mem_cons, List.mem_append, List.mem_map] at *
          aesop
        · simp only [hchain, FormalRegionCircuit.Configured.ofPure_inputCells,
            FormalRegionCircuit.keygenRequirements,
            Sinsemilla.Chain.circuit, ElaboratedRegionCircuit.keygenRequirements,
            List.forall_iff_forall_mem]
          intro cell hcell
          simp only [List.mem_append, List.mem_cons, List.mem_map]
          right
          rcases List.mem_map.mp hcell with ⟨assigned, hassigned, rfl⟩
          exact ⟨assigned.cell, ⟨assigned, hassigned, rfl⟩, rfl⟩
      copyCellsAssigned := by
        intro cfg counts hconfig offset input region
        let hchain : (Sinsemilla.Chain.circuit G ns fun _ => Q.y).Configured cfg :=
          FormalRegionCircuit.Configured.ofPure _ cfg () rfl
        keygen_registration [hashRegionSynthesize, z1Cells]
        · apply (Sinsemilla.Chain.circuit G ns fun _ => Q.y)
            |>.callPacked_copyCellsAssignedFrom cfg hchain offset input region
          intro cell hcell
          simp only [hchain, FormalRegionCircuit.Configured.ofPure_inputCells,
            FormalRegionCircuit.keygenRequirements,
            Sinsemilla.Chain.circuit, ElaboratedRegionCircuit.keygenRequirements,
            List.mem_map] at hcell
          simp only [List.mem_cons]
          exact Or.inr (Or.inr (List.mem_map.mpr hcell))
        · exact RegionOperations.CopyCellsAssignedFrom.nil _
      fixedAssignmentsAgree := by
        intro cfg counts hconfig offset input region
        let child := Sinsemilla.Chain.circuit G ns fun _ => Q.y
        let hchain : child.Configured cfg :=
          FormalRegionCircuit.Configured.ofPure _ cfg () rfl
        have hchild := child.call_fixedAssignmentsAgree
          cfg hchain offset input region
        unfold RegionOperations.FixedAssignmentsAgree at hchild ⊢
        intro column row left right hleft hright
        rw [hashRegionSynthesize_assignFixed_mem_iff] at hleft hright
        rcases hleft with hleft | hleft <;>
          rcases hright with hright | hright
        · exact hleft.2.2.trans hright.2.2.symm
        · have hcolumn : column = cfg.qS2 := by
            have := child.fixedColumn_mem_of_mem_call
              cfg hchain offset input region column row right hright
            simpa only [hchain,
              FormalRegionCircuit.Configured.ofPure_fixedColumns,
              FormalRegionCircuit.keygenRequirements, child,
              Sinsemilla.Chain.circuit,
              ElaboratedRegionCircuit.keygenRequirements,
              List.mem_singleton] using this
          exact False.elim (hconfig.qS2_ne_fixedYQ
            (hcolumn.symm.trans hleft.1))
        · have hcolumn : column = cfg.qS2 := by
            have := child.fixedColumn_mem_of_mem_call
              cfg hchain offset input region column row left hleft
            simpa only [hchain,
              FormalRegionCircuit.Configured.ofPure_fixedColumns,
              FormalRegionCircuit.keygenRequirements, child,
              Sinsemilla.Chain.circuit,
              ElaboratedRegionCircuit.keygenRequirements,
              List.mem_singleton] using this
          exact False.elim (hconfig.qS2_ne_fixedYQ
            (hcolumn.symm.trans hright.1))
        · exact hchild column row left right hleft hright
      output cfg offset input self :=
        { point :=
            { x := AssignedCell.of self
                (offset + Sinsemilla.Chain.prefixRows ns ns.length) cfg.xA
              y := AssignedCell.of self
                (offset + Sinsemilla.Chain.prefixRows ns ns.length) cfg.lambda1 }
          z1s := Vector.ofFn (fun i : Fin ns.length =>
            AssignedCell.of self
              (offset + Sinsemilla.Chain.prefixRows ns ↑i + 1) cfg.bits) }
      synthesisSummary cfg offset _ _ := hashRegionSynthesisSummary ns cfg offset
      synthesisSummary_eq := by
        intro cfg offset input self
        apply FloorPlanner.RegionSynthesisSummary.ext
        all_goals
          simp only [hashRegionSynthesisSummary, hashRegionSynthesize,
            circuit_norm, synthesis_summary_norm]
          rw [z1Cells_operations]
          simp only [synthesis_summary_norm, Nat.max_zero]
        rw [← max_assoc, max_self, ← max_assoc, max_self]
      output_eq := by
        intro config offset input self
        exact (hashRegionSynthesize_output G ns Q config offset input self).symm }

  Witness := Sinsemilla.Chain.ChainWit ns
  extract cfg offset input self env :=
    (Sinsemilla.Chain.circuit G ns (fun _ => Q.y)).extract cfg offset input self env

  EnvAssumptions cfg env :=
    Sinsemilla.GeneratorTableLoaded G cfg.generatorTable env.env

  Spec input output wit := Spec G ns Q input output wit
  ProverAssumptions input _ _ := ProverAssumptions G ns Q input
  ProverSpec input output _ _ := ProverSpec G ns Q input output

  soundness := by
    circuit_proof_start2 [Sinsemilla.HashPiece.initialYQGate,
      Sinsemilla.HashPiece.yAExpr, Sinsemilla.HashPiece.xRExpr]
    -- the raw z1s-naming step: no ops, output = the named cell vector
    simp only [RegionCircuit.operations, circuit_norm]
      at region_3 output_eq
    clear region_3
    obtain ⟨⟨ho_x, ho_y⟩, ho_z1s⟩ := output_eq
    -- the chain's contract
    have hSpec := out_spec env_assumptions trivial
    -- fold the destructured `Q` atoms back into the point literal, so the Q-generic
    -- bridge pattern (`fun _ => ?Q.y`) matches
    rw [show (fun _ : Placed Environment Fp => Q_y)
        = (fun _ : Placed Environment Fp => ({ x := Q_x, y := Q_y } : Point Fp).y)
      from rfl] at hSpec
    rw [chainC_spec_eq] at hSpec
    obtain ⟨chunks, hPC, hZs, hContract⟩ := hSpec
    simp only [Spec]
    refine ⟨chunks, hPC, hZs, ?_, ?_⟩
    · -- the z_1 view of the running sums
      intro hpos
      rw [← ho_z1s, ← wit_out_eq]
      rw [show ((Sinsemilla.Chain.circuit G ns fun _ => Q_y).extract cfg offset
            input_var self (⟨place, env⟩ : Placed Environment Fp)).zs
          = eval (⟨place, env⟩ : Placed Environment Fp)
              (Sinsemilla.Chain.zsCellsVal cfg self ns offset) from rfl,
        Sinsemilla.Chain.eval_zsCellsVal, z1View_zsFam _ _ _ hpos]
      ext j hj
      simp only [circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
        AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
        Environment.get_advice]
      congr 2
    · -- the hash from `Q`
      intro B hB
      have hout := Sinsemilla.Chain.circuit_output_eval G ns (fun _ => Q_y)
        cfg offset input_var self (⟨place, env⟩ : Placed Environment Fp)
      rw [eval_cells_eq_eval, out_eq] at hout
      have hfirst : (ProvableStruct.Halo2.eval place env out).first
          = ({ xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
               xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
               lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
               lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) }
             : Ecc.DoubleAndAddRow Fp) :=
        congrArg (fun output : Value Sinsemilla.Chain.Output Fp => output.first) hout
      have hres := hContract ({ x := Q_x, y := Q_y } : Point Fp) hQ
        (by show Q_x = _; rw [hfirst]; exact region_2.symm) (by
        rw [show ns.isEmpty = false from by
          cases ns with
          | nil => exact absurd rfl hns
          | cons a l => rfl]
        show 2 * ({ x := Q_x, y := Q_y } : Point Fp).y
          = Ecc.DoubleAndAdd.yA _
        rw [hfirst]
        simp only [Ecc.DoubleAndAdd.yA,
          Ecc.DoubleAndAdd.xR]
        linear_combination region_0 - 2 * region_1) B hB
      exact ⟨calc
          output_point_x = env.advice cfg.xA ((place self +
              (offset + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ) := ho_x.symm
          _ = (ProvableStruct.Halo2.eval place env out).point.x :=
            (congrArg (fun output : Value Sinsemilla.Chain.Output Fp => output.point.x) hout).symm
          _ = B.x := hres.1,
        calc
          output_point_y = env.advice cfg.lambda1 ((place self +
              (offset + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ) := ho_y.symm
          _ = (ProvableStruct.Halo2.eval place env out).point.y :=
            (congrArg (fun output : Value Sinsemilla.Chain.Output Fp => output.point.y) hout).symm
          _ = B.y := hres.2⟩

  completeness := by
    circuit_proof_start2 [Sinsemilla.HashPiece.initialYQGate,
      Sinsemilla.HashPiece.yAExpr, Sinsemilla.HashPiece.xRExpr]
    obtain ⟨-, hbounds, B0, hchain0⟩ := prover_assumptions
    -- the raw z1s-naming step: no ops, output = the named cell vector
    simp only [RegionCircuit.operations, circuit_norm]
      at region_2 output_eq
    clear region_2
    obtain ⟨⟨ho_x, ho_y⟩, ho_z1s⟩ := output_eq
    -- fold the destructured `Q` atoms back into the point literal ONCE, so the
    -- Q-generic bridge patterns (`fun _ => ?Q.y`) match everywhere
    rw [show (fun _ : Placed Environment Fp => Q_y)
        = (fun _ : Placed Environment Fp => ({ x := Q_x, y := Q_y } : Point Fp).y)
      from rfl] at out_spec wit_out_eq ⊢
    -- the chain's honest-prover precondition, transported to the minted witness
    have hPAchain : (Sinsemilla.Chain.circuit G ns
          fun _ => ({ x := Q_x, y := Q_y } : Point Fp).y).ProverAssumptions
        input wit_out env.hint := by
      rw [← wit_out_eq, chainC_proverAssumptions_eq]
      show Sinsemilla.Chain.ProverAssumptions G ns input _
      refine ⟨hns, hbounds, { x := Q_x, y := Q_y }, B0, hQ, ?_, rfl, hchain0⟩
      show Q_x = (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        (AssignedCell.of self offset cfg.xA : Var field Fp) : Fp)
      simp only [circuit_norm, AssignedCell.eval, AssignedCell.of_cell,
        Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice]
      exact region_1.symm
    -- the chain's honest contract
    have hsp := out_spec (by rw [chainC_envAssumptions_eq]; exact env_assumptions)
      trivial hPAchain
    have hPSchain := hsp.2
    rw [← wit_out_eq, chainC_proverSpec_eq] at hPSchain
    have hfacts := hPSchain ({ x := Q_x, y := Q_y } : Point Fp) B0 (by
        show Q_x = (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
          (AssignedCell.of self offset cfg.xA : Var field Fp) : Fp)
        simp only [circuit_norm, AssignedCell.eval, AssignedCell.of_cell,
          Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
          Environment.get_advice]
        exact region_1.symm) rfl hchain0
    obtain ⟨hpx, hpy, henter⟩ := hfacts
    have hout := Sinsemilla.Chain.circuit_output_eval G ns (fun _ => Q_y)
      cfg offset input_var self (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
    rw [eval_cells_eq_eval, out_eq] at hout
    refine ⟨⟨?_, region_0, region_1,
      ⟨by rw [chainC_envAssumptions_eq]; exact env_assumptions, trivial, hPAchain⟩,
      ?_⟩, ?_⟩
    · -- the Initial y_Q gate at the entering row
      rw [show ns.isEmpty = false from by
          cases ns with
          | nil => exact absurd rfl hns
          | cons a l => rfl] at henter
      simp only [Sinsemilla.Chain.enterYA, Bool.false_eq_true, if_false,
        Ecc.DoubleAndAdd.yA, Ecc.DoubleAndAdd.xR] at henter
      have hfirst : (ProvableStruct.Halo2.eval place env.toEnvironment out).first
          = ({ xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
               xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
               lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
               lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) }
             : Ecc.DoubleAndAddRow Fp) :=
        congrArg (fun output : Value Sinsemilla.Chain.Output Fp => output.first) hout
      rw [hfirst] at henter
      linear_combination 2 * region_0 - henter
    · -- the raw z1s-naming step emits no constraints
      show True
      trivial
    · -- the honest-prover contract
      simp only [ProverSpec]
      intro B hB
      have hBB : B0 = B := Option.some.inj (hchain0.symm.trans hB)
      rw [← hBB]
      exact ⟨calc
          output_point_x = env.advice cfg.xA ((place self +
              (offset + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ) := ho_x.symm
          _ = (ProvableStruct.Halo2.eval place env.toEnvironment out).point.x :=
            (congrArg (fun output : Value Sinsemilla.Chain.Output Fp => output.point.x) hout).symm
          _ = B0.x := hpx,
        calc
          output_point_y = env.advice cfg.lambda1 ((place self +
              (offset + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ) := ho_y.symm
          _ = (ProvableStruct.Halo2.eval place env.toEnvironment out).point.y :=
            (congrArg (fun output : Value Sinsemilla.Chain.Output Fp => output.point.y) hout).symm
          _ = B0.y := hpy⟩

@[synthesis_summary_norm]
theorem hashRegion_synthesisSummary
    (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    (hashRegion G ns Q hQ hns).elaborated.synthesisSummary
      config offset input region =
        hashRegionSynthesisSummary ns config offset := rfl

/-- A hash-to-point region requests one deferred constant cell for the public
initial point's x-coordinate. -/
@[synthesis_summary_norm]
theorem hashRegion_synthesisSummary_constantSiteCount
    (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    ((hashRegion G ns Q hQ hns).elaborated.synthesisSummary
      config 0 input region).constantSiteCount = 1 := by
  rw [hashRegion_synthesisSummary]
  simp only [hashRegionSynthesisSummary, synthesis_summary_norm]

/-- The layouter-level `hash_message` bundle: the `"hash_to_point"` region (Rust
`SinsemillaChip::hash_to_point`). -/
def hashCircuit (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) :
    FormalCircuit Fp Sinsemilla.HashPiece.Config Sinsemilla.HashPiece.Config
      (Sinsemilla.Chain.Inputs ns.length) (Output ns.length) :=
  (hashRegion G ns Q hQ hns).toFormal

/-- Fully reduced layouter summary of a hash-to-point call. -/
def hashCircuitSynthesisSummary (ns : List ℕ)
    (config : Sinsemilla.HashPiece.Config) : FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (hashRegionSynthesisSummary ns config 0)

@[synthesis_summary_norm]
theorem hashCircuitSynthesisSummary_tableRowExtent_eq (ns : List ℕ)
    (config : Sinsemilla.HashPiece.Config) :
    (hashCircuitSynthesisSummary ns config).tableRowExtent = 0 := by
  simp only [hashCircuitSynthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem hashCircuitSynthesisSummary_instanceRowExtent_eq (ns : List ℕ)
    (config : Sinsemilla.HashPiece.Config) :
    (hashCircuitSynthesisSummary ns config).instanceRowExtent = 0 := by
  simp only [hashCircuitSynthesisSummary, hashRegionSynthesisSummary,
    synthesis_summary_norm]

private opaque hashPhysicalShapePacked :
    { shape : List ℕ → Sinsemilla.HashPiece.Config →
        FloorPlanner.RegionShapeSummary //
      ∀ ns config,
        shape ns config =
          (hashRegionSynthesisSummary ns config 0
            |>.toRegionShapeSummary).withoutSelectors } :=
  ⟨fun ns config =>
      (hashRegionSynthesisSummary ns config 0
        |>.toRegionShapeSummary).withoutSelectors,
    by intros; rfl⟩

/-- The selector-free physical shape of one hash-to-point region. The reduction
barrier keeps concrete planner proofs from unfolding the full hash stack
accidentally; `hashPhysicalShape_eq` opens it deliberately. -/
def hashPhysicalShape (ns : List ℕ)
    (config : Sinsemilla.HashPiece.Config) : FloorPlanner.RegionShapeSummary :=
  hashPhysicalShapePacked.val ns config

theorem hashPhysicalShape_eq (ns : List ℕ)
    (config : Sinsemilla.HashPiece.Config) :
    hashPhysicalShape ns config =
      (hashRegionSynthesisSummary ns config 0
        |>.toRegionShapeSummary).withoutSelectors :=
  hashPhysicalShapePacked.property ns config

@[synthesis_summary_norm]
theorem hashCircuitSynthesisSummary_physicalShapes_eq
    (ns : List ℕ) (config : Sinsemilla.HashPiece.Config) :
    (hashCircuitSynthesisSummary ns config).physicalRegionShapes =
      [hashPhysicalShape ns config] := by
  simp only [hashCircuitSynthesisSummary,
    FloorPlanner.SynthesisSummary.ofRegion_physicalRegionShapes,
    hashPhysicalShape_eq]

@[synthesis_summary_norm]
theorem hashCircuit_synthesisSummary
    (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    (hashCircuit G ns Q hQ hns).elaborated.synthesisSummary
      config input region = hashCircuitSynthesisSummary ns config := rfl

/-- Lifting hash-to-point to a layouter region preserves its one deferred
constant request. -/
@[synthesis_summary_norm]
theorem hashCircuit_synthesisSummary_constantSiteCount
    (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    ((hashCircuit G ns Q hQ hns).elaborated.synthesisSummary
      config input region).constantSiteCount = 1 := by
  simpa only [hashCircuit, hashRegion_synthesisSummary_constantSiteCount] using
    FormalRegionCircuit.toFormal_synthesisSummary_constantSiteCount
      (hashRegion G ns Q hQ hns) (hashRegion G ns Q hQ hns).name
      config input region

attribute [keygen_metadata_projection] hashCircuit hashRegion

@[keygen_norm]
theorem Configured.permutationColumns_eq (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ []) {cfg : Sinsemilla.HashPiece.Config}
    (configured : (hashCircuit G ns Q hQ hns).Configured cfg) :
    configured.permutationColumns =
      ([cfg.xA, cfg.lambda1, cfg.bits] : List AnyColumn) := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [keygen_norm, FormalCircuit.Configured.permutationColumns,
    FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
    hashCircuit, FormalRegionCircuit.toFormal,
    ElaboratedRegionCircuit.keygenRequirements, hashRegion,
    Configure.delta_pure, List.append_nil]

@[keygen_norm]
theorem hashCircuit_inputCells (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    {cfg : Sinsemilla.HashPiece.Config}
    (configured : (hashCircuit G ns Q hQ hns).Configured cfg)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp) :
    configured.inputCells input = input.pieces.toList.map (·.cell) := rfl

/-- A hash-to-point capability exported by one HashPiece configure run. -/
def hashConfigureCertificate (G : Generators) (ns : List ℕ)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (xA xP bits lambda1 lambda2 witnessPieces : Column .advice)
    (fixedYQ : Column .fixed) (genTable : Sinsemilla.GeneratorTableConfig)
    (counts : ConfigureCounts) (hfixedYQ : fixedYQ.index < counts.numFixedColumns) :
    (hashCircuit G ns Q hQ hns).ConfigurationCertificate
      ((Sinsemilla.HashPiece.configure G xA xP bits lambda1 lambda2
        witnessPieces fixedYQ genTable).output counts)
      { gates := ((Sinsemilla.HashPiece.configure G xA xP bits lambda1 lambda2
          witnessPieces fixedYQ genTable).delta counts).gates
        lookups := ((Sinsemilla.HashPiece.configure G xA xP bits lambda1 lambda2
          witnessPieces fixedYQ genTable).delta counts).lookups
        fixedColumns := fixedYQ ::
          (Sinsemilla.HashPiece.configure G xA xP bits lambda1 lambda2
            witnessPieces fixedYQ genTable).fixedColumns counts
        permutationColumns :=
          ((Sinsemilla.HashPiece.configure G xA xP bits lambda1 lambda2
            witnessPieces fixedYQ genTable).delta counts).permutationRequests } := by
  let cfg := (Sinsemilla.HashPiece.configure G xA xP bits lambda1 lambda2
    witnessPieces fixedYQ genTable).output counts
  apply ((hashRegion G ns Q hQ hns).configureCertificate cfg {}
    (Sinsemilla.HashPiece.configureOutputFixedColumnsLawful G xA xP bits
      lambda1 lambda2 witnessPieces fixedYQ genTable counts hfixedYQ)).mono
  · intro gate hgate
    simp only [hashRegion, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil] at hgate
    rcases List.mem_cons.mp hgate with hinitial | hsinsemilla
    · subst gate
      simp only
      unfold Sinsemilla.HashPiece.configure
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_left
      simp [cfg, Sinsemilla.HashPiece.configure]
    · simp only [List.mem_singleton] at hsinsemilla
      subst gate
      simp only
      unfold Sinsemilla.HashPiece.configure
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_left
      simp [cfg, Sinsemilla.HashPiece.configure]
  · intro argument hargument
    simp only [hashRegion, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil] at hargument
    simp only [List.mem_singleton] at hargument
    subst argument
    simp only
    unfold Sinsemilla.HashPiece.configure
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_left
    simp [cfg, Sinsemilla.HashPiece.configure, lookup, Configure.delta,
      ConfigureDelta.append, Sinsemilla.HashPiece.generatorLookup]
  · intro column hcolumn
    simp only [hashRegion, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.fixedColumns_pure,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hcolumn
    rcases hcolumn with rfl | rfl
    · simp
    ·
      apply List.mem_cons.mpr
      right
      simp [cfg, Sinsemilla.HashPiece.configure]
  · intro column hcolumn
    simp only [hashRegion, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hcolumn
    rcases hcolumn with rfl | rfl | rfl
    · simpa only [cfg, Sinsemilla.HashPiece.configure_output_xA] using
        Sinsemilla.HashPiece.configure_xA_mem_permutationRequests G xA xP bits
          lambda1 lambda2 witnessPieces fixedYQ genTable counts
    · simpa only [cfg, Sinsemilla.HashPiece.configure_output_lambda1] using
        Sinsemilla.HashPiece.configure_lambda1_mem_permutationRequests G xA xP bits
          lambda1 lambda2 witnessPieces fixedYQ genTable counts
    · simpa only [cfg, Sinsemilla.HashPiece.configure_output_bits] using
        Sinsemilla.HashPiece.configure_bits_mem_permutationRequests G xA xP bits
          lambda1 lambda2 witnessPieces fixedYQ genTable counts

/-- Call the hash bundle (Rust `hash_to_point` at a layouter). -/
def hashMessage (G : Generators) (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) :
    Circuit Fp (Var (Output ns.length) Fp) :=
  (hashCircuit G ns Q hQ hns).call cfg pieces

@[circuit_norm]
theorem hashMessage_regionCount
    (G : Generators) (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    ((hashMessage G ns cfg Q hQ hns pieces).operations region).regionCount = 1 := by
  simp only [hashMessage, FormalCircuit.call_regionCount, hashCircuit,
    FormalRegionCircuit.toFormal_regionCount]

@[circuit_norm]
theorem hashMessage_nextRegionIndex
    (G : Generators) (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    (hashMessage G ns cfg Q hQ hns pieces).nextRegionIndex region = region + 1 := by
  unfold hashMessage
  rw [FormalCircuit.nextRegionIndex_call]
  simp only [FormalCircuit.call_regionCount, hashCircuit,
    FormalRegionCircuit.toFormal_regionCount]

@[synthesis_summary_norm]
theorem hashMessage_synthesisSummary
    (G : Generators) (ns : List ℕ) (config : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    FloorPlanner.synthesisSummary
      ((hashMessage G ns config Q hQ hns input).operations region) =
        (hashCircuit G ns Q hQ hns).elaborated.synthesisSummary
          config input region := by
  simp only [hashMessage, FormalCircuit.call_synthesisSummary]

/-- Calling hash-to-point preserves its one deferred constant request. -/
@[synthesis_summary_norm]
theorem hashMessage_synthesisSummary_constantSiteCount
    (G : Generators) (ns : List ℕ) (config : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (region : RegionIndex) :
    (FloorPlanner.synthesisSummary
      ((hashMessage G ns config Q hQ hns input).operations
        region)).constantSiteCount = 1 := by
  simp only [hashMessage, FormalCircuit.call_synthesisSummary]
  exact hashCircuit_synthesisSummary_constantSiteCount
    G ns Q hQ hns config input region

/-- The hash bundle's output `z1s` cells (positional, rfl). -/
theorem hashCircuit_output_z1s (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (i : RegionIndex) :
    ((hashCircuit G ns Q hQ hns).output cfg pieces i).z1s
      = Vector.ofFn (fun j : Fin ns.length =>
          AssignedCell.of i (0 + Sinsemilla.Chain.prefixRows ns ↑j + 1) cfg.bits) := rfl

/-- The hash bundle's output `point.x` cell (positional, rfl). -/
theorem hashCircuit_output_point_x (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (i : RegionIndex) :
    ((hashCircuit G ns Q hQ hns).output cfg pieces i).point.x
      = AssignedCell.of i (0 + Sinsemilla.Chain.prefixRows ns ns.length) cfg.xA := rfl

/-- The hash bundle's output `point.y` cell (positional, rfl). -/
theorem hashCircuit_output_point_y (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (i : RegionIndex) :
    ((hashCircuit G ns Q hQ hns).output cfg pieces i).point.y
      = AssignedCell.of i (0 + Sinsemilla.Chain.prefixRows ns ns.length) cfg.lambda1 := rfl

/-- Both point coordinates returned by hash-to-point were assigned by its region. -/
theorem hashCircuit_call_output_point_cells_assigned
    (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) :
    let output := (hashCircuit G ns Q hQ hns).output cfg input self
    output.point.x.cell ∈ Operations.assignedCellsFrom
        (((hashCircuit G ns Q hQ hns).call cfg input).operations self) self ∧
      output.point.y.cell ∈ Operations.assignedCellsFrom
        (((hashCircuit G ns Q hQ hns).call cfg input).operations self) self := by
  dsimp only
  rw [hashCircuit_output_point_x, hashCircuit_output_point_y,
    FormalCircuit.call_operations]
  simp only [hashCircuit, FormalRegionCircuit.toFormal, hashRegion,
    operations_assignRegion, Operations.assignedCellsFrom]
  simp only [hashRegionSynthesize, RegionCircuit.operations_bind, circuit_norm,
    RegionOperations.assignedCells, RegionOperation.assignedCells,
    List.flatMap_cons, List.flatMap_append, List.mem_append, List.append_nil]
  have h := Sinsemilla.Chain.circuit_output_point_cells_assigned G ns
    (fun _ => Q.y) hns cfg 0 input self []
  dsimp only at h
  rw [Sinsemilla.Chain.output_point_x,
    Sinsemilla.Chain.output_point_y] at h
  simp only [RegionOperations.mem_assignedCellsAfter_iff, List.nil_append,
    AssignedCell.of_cell, Nat.zero_add] at h
  rw [FormalRegionCircuit.call_operations]
  exact ⟨Or.inr (Or.inr (Or.inl h.1)),
    Or.inr (Or.inr (Or.inl h.2))⟩

/-- Every running-sum cell of every piece is assigned by the corresponding
symbolic chain slot. -/
theorem hashCircuit_call_z_cell_assigned
    (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) (i : Fin ns.length)
    (r : Fin (ns.getD i.val 0 + 1)) :
    Cell.of self (Sinsemilla.Chain.prefixRows ns i.val + r.val) cfg.bits ∈
      Operations.assignedCellsFrom
        (((hashCircuit G ns Q hQ hns).call cfg input).operations self) self := by
  rw [FormalCircuit.call_operations]
  simp only [hashCircuit, FormalRegionCircuit.toFormal, hashRegion,
    operations_assignRegion, Operations.assignedCellsFrom]
  simp only [hashRegionSynthesize, RegionCircuit.operations_bind, circuit_norm,
    RegionOperations.assignedCells, RegionOperation.assignedCells,
    List.flatMap_cons, List.flatMap_append, List.mem_append, List.append_nil]
  have h := Sinsemilla.Chain.circuit_z_cell_assigned G ns
    (fun _ => Q.y) cfg 0 input self [] i r
  simp only [RegionOperations.mem_assignedCellsAfter_iff, List.nil_append,
    Nat.zero_add] at h
  rw [FormalRegionCircuit.call_operations]
  exact Or.inr (Or.inr (Or.inl h))

/-- Each `z₁` output belonging to a nontrivial piece was assigned by that piece's
symbolic chain slot. -/
theorem hashCircuit_call_output_z1_cell_assigned
    (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) (i : Fin ns.length)
    (hi : 0 < ns.getD i.val 0) :
    ((hashCircuit G ns Q hQ hns).output cfg input self).z1s[i].cell ∈
      Operations.assignedCellsFrom
        (((hashCircuit G ns Q hQ hns).call cfg input).operations self) self := by
  rw [hashCircuit_output_z1s]
  simpa only [Fin.getElem_fin, Vector.getElem_ofFn, AssignedCell.of_cell,
    Nat.zero_add] using hashCircuit_call_z_cell_assigned
      G ns Q hQ hns cfg input self i ⟨1, by omega⟩

/-- The `hashMessage` spelling of
`hashCircuit_call_output_z1_cell_assigned`. -/
theorem hashMessage_output_z1_cell_assigned
    (G : Generators) (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) (i : Fin ns.length)
    (hi : 0 < ns.getD i.val 0) :
    ((hashMessage G ns cfg Q hQ hns input).output self).z1s[i].cell ∈
      Operations.assignedCellsFrom
        ((hashMessage G ns cfg Q hQ hns input).operations self) self := by
  simpa only [hashMessage, FormalCircuit.output_call] using
    hashCircuit_call_output_z1_cell_assigned
      G ns Q hQ hns cfg input self i hi

/-- Both point coordinates returned by the layouter-level hash call were assigned
by its single region. -/
theorem hashMessage_output_point_cells_assigned
    (G : Generators) (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) :
    let output := (hashMessage G ns cfg Q hQ hns input).output self
    output.point.x.cell ∈ Operations.assignedCellsFrom
        ((hashMessage G ns cfg Q hQ hns input).operations self) self ∧
      output.point.y.cell ∈ Operations.assignedCellsFrom
        ((hashMessage G ns cfg Q hQ hns input).operations self) self := by
  simpa only [hashMessage, FormalCircuit.output_call] using
    hashCircuit_call_output_point_cells_assigned
      G ns Q hQ hns cfg input self

/-- The `hashMessage` spelling of the hash circuit's x-coordinate output cell. -/
theorem hashMessage_output_point_x (G : Generators) (ns : List ℕ)
    (cfg : Sinsemilla.HashPiece.Config) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (self : RegionIndex) :
    ((hashMessage G ns cfg Q hQ hns input).output self).point.x =
      AssignedCell.of self (0 + Sinsemilla.Chain.prefixRows ns ns.length) cfg.xA := by
  simpa only [hashMessage, FormalCircuit.output_call] using
    hashCircuit_output_point_x G ns Q hQ hns cfg input self

/-- The hash bundle's output record. -/
theorem hashCircuit_output_eq (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (i : RegionIndex) :
    (hashCircuit G ns Q hQ hns).output cfg pieces i
      = ({ point :=
             { x := AssignedCell.of i (0 + Sinsemilla.Chain.prefixRows ns ns.length) cfg.xA,
               y := AssignedCell.of i (0 + Sinsemilla.Chain.prefixRows ns ns.length) cfg.lambda1 },
           z1s :=
             Vector.ofFn (fun j : Fin ns.length => AssignedCell.of i
               (0 + Sinsemilla.Chain.prefixRows ns ↑j + 1) cfg.bits) }
        : Output ns.length (AssignedCell Fp)) := rfl

/-- The hash bundle's eval'd output (verifier view), landed on raw advice reads. -/
theorem hashCircuit_output_eval (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (eval env ((hashCircuit G ns Q hQ hns).output cfg pieces i)
        : Value (Output ns.length) Fp)
      = { point :=
            { x := env.env.advice cfg.xA
                ((env.place i + (0 + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ),
              y := env.env.advice cfg.lambda1
                ((env.place i + (0 + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ) },
          z1s :=
            Vector.ofFn (fun j : Fin ns.length => env.env.advice cfg.bits
              ((env.place i + (0 + Sinsemilla.Chain.prefixRows ns ↑j + 1) : ℕ) : ℤ)) } := by
  rw [hashCircuit_output_eq G ns Q hQ hns cfg pieces i, out_eval_lit]
  simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]
  congr 1
  ext j hj
  simp [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]

/-- The hash bundle's eval'd output (prover view), landed on raw advice reads. -/
theorem hashCircuit_output_eval_prover (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (i : RegionIndex)
    (env : Placed ProverEnvironment Fp) :
    (eval env ((hashCircuit G ns Q hQ hns).output cfg pieces i)
        : Value (Output ns.length) Fp)
      = { point :=
            { x := env.env.advice cfg.xA
                ((env.place i + (0 + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ),
              y := env.env.advice cfg.lambda1
                ((env.place i + (0 + Sinsemilla.Chain.prefixRows ns ns.length) : ℕ) : ℤ) },
          z1s :=
            Vector.ofFn (fun j : Fin ns.length => env.env.advice cfg.bits
              ((env.place i + (0 + Sinsemilla.Chain.prefixRows ns ↑j + 1) : ℕ) : ℤ)) } := by
  rw [hashCircuit_output_eq G ns Q hQ hns cfg pieces i, out_eval_lit_prover]
  simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]
  congr 1
  ext j hj
  simp [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]

derive_contract_bridges hashCircuit (G : Generators) (ns : List ℕ) (Q : Point Fp)
  (hQ : Q.OnCurve) (hns : ns ≠ []) := hashCircuit G ns Q hQ hns

end Zcash.Circuits.Sinsemilla.HashToPoint
