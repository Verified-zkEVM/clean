import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Specs.Sinsemilla
import Clean.Ironwood.Specs.SinsemillaBreak
import Clean.Ironwood.Specs.Bitrange
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece
import Clean.Ironwood.Sinsemilla.Chain
import Clean.Ironwood.Utilities.LookupRangeCheck
import Clean.Ironwood.Utilities.CondSwap
import Clean.Ironwood.Sinsemilla.HashToPoint

/-!
# Sinsemilla MerkleCRH

`MerkleCRH^Orchard(l, left, right) = SinsemillaHash(Q, l⋆ || left⋆ || right⋆)`: the 520-bit message
is witnessed as three Sinsemilla pieces
- `a = a_0 || a_1` = `l` (10 bits) `||` bits 0..240 of `left` (25 words),
- `b = b_0 || b_1 || b_2` = bits 240..250 of `left` `||` bits 250..255 of `left` `||` bits 0..5 of
  `right` (2 words),
- `c` = bits 5..255 of `right` (25 words),
with the short sub-pieces `b_1`, `b_2` range-checked to 5 bits. The `q_decompose` gate ties the
pieces to `(l, left, right)` through the hash's own `z_1` running-sum cells.

Composition: `HashLayer` = the hash (`Chain.circuit`, `z_1` read as `zs[i][1]`) + the `b_1`/`b_2`
range checks + the decomposition `Gate`. `Layer` = `CondSwap` + `HashLayer` (the swap is a stated
boundary — an abstract child). `CalculateRoot` is the 32-layer fold of `Layer`.

Reference: `halo2_gadgets/src/sinsemilla/merkle/chip.rs`.
-/

open ProvableStruct.Halo2 (eval_cells_eq_eval eval_cells_eq_eval_prover)

namespace Zcash.Circuits.Sinsemilla.Merkle

open Halo2
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Specs.Sinsemilla (Generators merkleChunks hashToPoint hashToPointB
  BreakData ValidBreak SpecOrBreak breaksOfGuarded)
open Specs (K bitrange bitrange_lt bitrange_zero bitrange_eq_div_of_lt)
open Sinsemilla (pieceWord pieceZ)

/-! ### MerkleCRH decomposition gate constants -/

def twoPow5 {R : Type} [OfNat R (2 ^ 5)] : R := OfNat.ofNat (2 ^ 5)
def twoPow10 {R : Type} [OfNat R (2 ^ 10)] : R := OfNat.ofNat (2 ^ 10)
def twoPow240 {R : Type} [OfNat R (2 ^ 240)] : R := OfNat.ofNat (2 ^ 240)

/-! ### The `q_decompose` gate

Layout relative to the gate row `g` (`q_decompose` enabled at `Rotation::cur`):

    |  a   |  b   |  c   | left | right | q_decompose |   (row g)
    | z1_a | z1_b | b_1  | b_2  |   l   |      0      |   (row g+1)

`a_whole/b_whole/c_whole/left_node/right_node` are read at `Rotation::cur`, and
`z1_a/z1_b/b_1/b_2/l` at `Rotation::next`. -/

namespace Gate

/-- The Rust `q_decompose` config: the selector and the ten advice columns the gate reads across
the two rows. -/
structure Config where
  qDecompose : Selector
  aWhole : Column .advice
  bWhole : Column .advice
  cWhole : Column .advice
  leftNode : Column .advice
  rightNode : Column .advice
  z1A : Column .advice
  z1B : Column .advice
  b1 : Column .advice
  b2 : Column .advice
  lWhole : Column .advice

/-- The four decomposition polynomials. `a_whole/…/right_node` at
`Rotation::cur`, `z1_a/z1_b/b_1/b_2/l` at `Rotation::next`.
- `l_check`   : `a_0 − l = (a_whole − z1_a·2^10) − l`
- `left_check`: `z1_a + (b_0 + b_1·2^10)·2^240 − left`, with `b_0 = b_whole − z1_b·2^10`
- `right_check`: `b_2 + c_whole·2^5 − right`
- `b1_b2_check`: `z1_b − (b_1 + b_2·2^5)` -/
def decomposeGate (cfg : Config) : Gate Fp :=
  let aWhole : Expression Fp Query := queryAdvice cfg.aWhole 0
  let bWhole : Expression Fp Query := queryAdvice cfg.bWhole 0
  let cWhole : Expression Fp Query := queryAdvice cfg.cWhole 0
  let leftNode : Expression Fp Query := queryAdvice cfg.leftNode 0
  let rightNode : Expression Fp Query := queryAdvice cfg.rightNode 0
  let z1A : Expression Fp Query := queryAdvice cfg.z1A 1
  let z1B : Expression Fp Query := queryAdvice cfg.z1B 1
  let b1 : Expression Fp Query := queryAdvice cfg.b1 1
  let b2 : Expression Fp Query := queryAdvice cfg.b2 1
  let l : Expression Fp Query := queryAdvice cfg.lWhole 1
  Gate.withSelector "Decomposition check" cfg.qDecompose
    -- `l_whole` (advices[4] @ next) is queried first in the Rust closure, ahead of the
    -- cur-row cells and the remaining next-row cells.
    [l, aWhole, bWhole, cWhole, leftNode, rightNode, z1A, z1B, b1, b2] <|
    let twoPow5 : Expression Fp Query := (2 ^ 5 : Fp)
    let twoPow10 : Expression Fp Query := (2 ^ 10 : Fp)
    let twoPow240 : Expression Fp Query := (2 ^ 240 : Fp)
    let a0 := aWhole - z1A * twoPow10
    let b0 := bWhole - z1B * twoPow10
    let lCheck := a0 - l
    let leftCheck := z1A + (b0 + b1 * twoPow10) * twoPow240 - leftNode
    let rightCheck := b2 + cWhole * twoPow5 - rightNode
    let b1b2Check := z1B - (b1 + b2 * twoPow5)
    [ ("l_check", lCheck), ("left_check", leftCheck),
      ("right_check", rightCheck), ("b1_b2_check", b1b2Check) ]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem decomposeGate_selector (cfg : Config) :
    (decomposeGate cfg).selector = cfg.qDecompose := rfl

/-- The value-level decomposition spec, over the ten cell values.
Uses the plain `(2^k : Fp)` literals (definitionally the `twoPow*` constants). -/
def Spec (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Fp) : Prop :=
  lWhole = aWhole - z1A * (2 ^ 10 : Fp) ∧
  leftNode = z1A + ((bWhole - z1B * (2 ^ 10 : Fp)) + b1 * (2 ^ 10 : Fp)) * (2 ^ 240 : Fp) ∧
  rightNode = b2 + cWhole * (2 ^ 5 : Fp) ∧
  z1B = b1 + b2 * (2 ^ 5 : Fp)

/-- Soundness half of the gate: the four polynomials vanishing gives the `Spec`. -/
theorem spec_of_polysZero {aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Fp}
    (hl : (aWhole - z1A * (2 ^ 10 : Fp)) - lWhole = 0)
    (hleft : z1A + ((bWhole - z1B * (2 ^ 10 : Fp)) + b1 * (2 ^ 10 : Fp)) * (2 ^ 240 : Fp)
      - leftNode = 0)
    (hright : b2 + cWhole * (2 ^ 5 : Fp) - rightNode = 0)
    (hb : z1B - (b1 + b2 * (2 ^ 5 : Fp)) = 0) :
    Spec aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -hl
  · linear_combination -hleft
  · linear_combination -hright
  · linear_combination hb

/-- Completeness half: the `Spec` gives each of the four polynomials vanishing (gate order). -/
theorem polysZero_of_spec {aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Fp}
    (h : Spec aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole) :
    (aWhole - z1A * (2 ^ 10 : Fp)) - lWhole = 0 ∧
    z1A + ((bWhole - z1B * (2 ^ 10 : Fp)) + b1 * (2 ^ 10 : Fp)) * (2 ^ 240 : Fp) - leftNode = 0 ∧
    b2 + cWhole * (2 ^ 5 : Fp) - rightNode = 0 ∧
    z1B - (b1 + b2 * (2 ^ 5 : Fp)) = 0 := by
  obtain ⟨hl, hleft, hright, hb⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -hl
  · linear_combination -hleft
  · linear_combination -hright
  · linear_combination hb

/-- The `q_decompose` slice of `MerkleChip::configure`: allocate the `q_decompose` selector and
register the gate — no equality enabling (the five underlying advice columns are already
equality-enabled by `SinsemillaChip::configure`). The ten config fields are instantiated
column-coincident by the chip-level `configure` (`aWhole`/`z1A` share `advices[0]`, … — the gate
reads the same five columns at rotations 0/1). -/
def configure (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Column .advice) :
    Configure Fp Config := do
  let qDecompose ← selector
  let cfg : Config :=
    Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole
  createGate (decomposeGate cfg)
  return cfg

instance (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole :
    Column .advice) :
    ElaboratedConfigure
      (configure aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole) := by
  unfold configure
  infer_instance

/-! ### The gate gadget (pure region-level assertion)

Verifier-visible inputs are the ten already-assigned cells; no output (`unit`), like
`MulOverflow.circuit`. The body copies the ten cells into the gate window and enables
`q_decompose`. -/

/-- The nine already-assigned input cells (row `g`: whole pieces + nodes; row `g+1`: `z_1` cells,
sub-pieces). `l` is not an input — it is assigned from a constant. -/
structure Inputs (F : Type) where
  -- Piece `a` (`l ‖ left[0..240]`).
  aWhole : F
  -- Piece `b` (`left[240..255] ‖ right[0..5]`).
  bWhole : F
  -- Piece `c` (`right[5..255]`).
  cWhole : F
  -- The left child node.
  leftNode : F
  -- The right child node.
  rightNode : F
  -- Running sum `z_1` of piece `a`.
  z1A : F
  -- Running sum `z_1` of piece `b`.
  z1B : F
  -- Sub-piece `b_1` (`left[240..250]`).
  b1 : F
  -- Sub-piece `b_2` (`left[250..255]`).
  b2 : F
deriving ProvableStruct

/-- The decomposition-gate body, in Rust's op order: enable `q_decompose` at `g`, assign `l` from
a constant at `(l, g+1)`, then the nine copies (row `g`: pieces + nodes; row `g+1`: `z_1` cells,
sub-pieces). Returns `unit`. -/
def body (cfg : Config) (l : Fp) (input : Inputs (AssignedCell Fp)) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  (decomposeGate cfg).enable offset
  -- `l` from a constant
  let lCell ← assignAdvice cfg.lWhole (offset + 1) (.native fun _ => #v[l])
  constrainConstant lCell l
  -- row g: the whole pieces + the two nodes
  let _a ← copyAdvice input.aWhole cfg.aWhole offset
  let _b ← copyAdvice input.bWhole cfg.bWhole offset
  let _c ← copyAdvice input.cWhole cfg.cWhole offset
  let _left ← copyAdvice input.leftNode cfg.leftNode offset
  let _right ← copyAdvice input.rightNode cfg.rightNode offset
  -- row g+1: the two z_1 cells, b_1/b_2
  let _z1A ← copyAdvice input.z1A cfg.z1A (offset + 1)
  let _z1B ← copyAdvice input.z1B cfg.z1B (offset + 1)
  let _b1 ← copyAdvice input.b1 cfg.b1 (offset + 1)
  let _b2 ← copyAdvice input.b2 cfg.b2 (offset + 1)
  return ()

/-- The value-level spec on the input cells' evaluations, at the
constant `l`. -/
def GateSpec (l : Fp) (input : Inputs Fp) : Prop :=
  Spec input.aWhole input.bWhole input.cWhole input.leftNode input.rightNode
    input.z1A input.z1B input.b1 input.b2 l

abbrev ConfigInput :=
  Column .advice × Column .advice × Column .advice × Column .advice ×
    Column .advice × Column .advice × Column .advice × Column .advice ×
    Column .advice × Column .advice

def permutationColumns (input : ConfigInput) : List AnyColumn :=
  let (a, b, c, left, right, z1A, z1B, b1, b2, lw) := input
  [a, b, c, left, right, z1A, z1B, b1, b2, lw]

/-- In the Merkle gate's symmetric use, its ten copy columns reduce to five columns. -/
theorem mem_equalityColumns_of_mem_permutationColumns
    (xA xP bits lambda1 lambda2 : Column .advice) (column : AnyColumn)
    (hcolumn : column ∈ permutationColumns
      (xA, xP, bits, lambda1, lambda2, xA, xP, bits, lambda1, lambda2)) :
    column ∈ ([xA, xP, bits, lambda1, lambda2] : List AnyColumn) := by
  simp only [permutationColumns, List.mem_cons, List.not_mem_nil, or_false] at hcolumn ⊢
  grind

/-- Reduced two-row footprint of the decomposition gate. -/
def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.qDecompose.index,
      .column .advice cfg.lWhole.index,
      .column .advice cfg.aWhole.index,
      .column .advice cfg.bWhole.index,
      .column .advice cfg.cWhole.index,
      .column .advice cfg.leftNode.index,
      .column .advice cfg.rightNode.index,
      .column .advice cfg.z1A.index,
      .column .advice cfg.z1B.index,
      .column .advice cfg.b1.index,
      .column .advice cfg.b2.index]
    (offset + 2) 1 [(cfg.qDecompose.index, offset)]

@[synthesis_summary_norm]
theorem synthesisSummary_lookupActivationCount (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).instanceRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  simp only [synthesisSummary, synthesis_summary_norm]
  intro index hcolumn
  simp at hcolumn

theorem synthesisSummary_eq (cfg : Config) (l : Fp)
    (input : Var Inputs Fp) (offset : ℕ) (self : RegionIndex) :
    synthesisSummary cfg offset =
      FloorPlanner.regionSynthesisSummary
        ((body cfg l input offset).operations self) := by
  rw [synthesisSummary]
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [body, circuit_norm, synthesis_summary_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_columns]
  · simp only [body, circuit_norm, synthesis_summary_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
    omega
  · simp only [body, circuit_norm, synthesis_summary_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]
  · simp only [body, circuit_norm, synthesis_summary_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_instanceRowExtent]
  · simp only [body, circuit_norm, synthesis_summary_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_lookupActivationCount]
  · simp only [body, circuit_norm, synthesis_summary_norm,
      decomposeGate]

@[implicit_reducible]
def elaborated (l : Fp) :
    ElaboratedRegionCircuit Fp ConfigInput Config Inputs unit
      (fun (a, b, c, left, right, z1A, z1B, b1, b2, lw) =>
        configure a b c left right z1A z1B b1 b2 lw)
      (fun cfg offset input => body cfg l input offset) :=
  { keygenRequirements :=
      { permutationColumns input _ := permutationColumns input
        inputCells _ _ input :=
          [input.aWhole.cell, input.bWhole.cell, input.cWhole.cell,
            input.leftNode.cell, input.rightNode.cell, input.z1A.cell,
            input.z1B.cell, input.b1.cell, input.b2.cell] }
    synthesisSummary cfg offset _ _ := synthesisSummary cfg offset
    synthesisSummary_eq := fun cfg offset input self =>
      synthesisSummary_eq cfg l input offset self
    registered := by keygen_registration [body, permutationColumns]
    copyCellsAssigned := by
      intro configInput counts hconfig offset input region
      simp only [body, circuit_norm,
        RegionOperations.CopyCellsAssigned,
        RegionOperations.copyCellsAssignedFrom_assignAdvice_iff,
        RegionOperations.copyCellsAssignedFrom_constrainEqual_iff,
        RegionOperations.copyCellsAssignedFrom_constrainConstant_iff,
        RegionOperations.copyCellsAssignedFrom_enableGate_iff,
        RegionOperations.copyCellsAssignedFrom_nil_iff, List.mem_cons,
        List.not_mem_nil, or_false]
    lookupActivationsWellFormed := by
      intro cfg offset input region
      simp only [body, circuit_norm,
        RegionOperations.LookupActivationsWellFormed,
        RegionOperation.LookupActivationWellFormed, List.forall_cons]
    lookupSelectorsAnchoredBy_of_registered := by
      intro configInput counts hconfig offset input region anchor hanchor
        hregistered
      apply RegionOperations.LookupSelectorsAnchoredBy.of_forall_isNotLookup
      simp only [body, circuit_norm, RegionOperation.IsNotLookup]
    lookupSelectorAssignmentsAgree_of_registered := by
      intro configInput counts hconfig offset input region
      dsimp only
      intro _hregistered
      apply RegionOperations.lookupSelectorAssignmentsAgree_of_forall_isNotLookup
      simp only [body, circuit_norm, RegionOperation.IsNotLookup]
    fixedAssignmentsAgree := by
      intro configInput counts hconfig offset input region
      apply RegionOperations.HasNoFixedAssignments.fixedAssignmentsAgree
      simp only [body, circuit_norm,
        RegionOperations.HasNoFixedAssignments,
        RegionOperation.HasNoFixedAssignment, List.forall_cons, and_self] }

/-- The decomposition-gate gadget. Pure assertion (`unit` output). Soundness: the four polys imply
`GateSpec`; completeness: `GateSpec` (the honest-caller precondition, like `MulOverflow`) implies
the polys.

STRUCTURE-COMPLETE-WITH-STATED-SORRIES: both directions reduce to `spec_of_polysZero` /
`polysZero_of_spec` after peeling the ten copies + the gate via `circuit_norm` (the
`MulOverflow.circuit` pattern); the copies chain each gate-window cell to its input component. -/
def circuit (l : Fp) :
    FormalRegionCircuit Fp ConfigInput Config Inputs unit where
  name := "Check piece decomposition"
  configure := fun (a, b, c, left, right, z1A, z1B, b1, b2, lw) =>
    configure a b c left right z1A z1B b1 b2 lw
  elaborated := elaborated l
  synthesize cfg offset input := body cfg l input offset
  Assumptions _ := True
  Spec input _ _ := GateSpec l input
  ProverAssumptions input _ _ := GateSpec l input
  soundness := by
    circuit_proof_start2 [body, decomposeGate]
    obtain ⟨hL, hLeft, hRight, hB⟩ := region_0
    simp only [region_1, region_2, region_3, region_4, region_5, region_6, region_7,
      region_8, region_9, region_10] at hL hLeft hRight hB
    exact spec_of_polysZero (by linear_combination hL) (by linear_combination hLeft)
      (by linear_combination hRight) (by linear_combination hB)
  completeness := by
    circuit_proof_start2 [body, decomposeGate]
    simp only [region_0, region_1, region_2, region_3, region_4, region_5, region_6,
      region_7, region_8, region_9]
    have h := polysZero_of_spec prover_assumptions
    dsimp only at h
    exact ⟨h, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial⟩

@[synthesis_summary_norm]
theorem circuit_synthesisSummary (l : Fp) (cfg : Config) (offset : ℕ)
    (input : Var Inputs Fp) (region : RegionIndex) :
    (circuit l).elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

@[keygen_configured]
def circuit_configured (l : Fp) (cfg : Config)
    (hsimple : cfg.qDecompose.simple = true) :
    (circuit l).Configured cfg := by
  refine ⟨(cfg.aWhole, cfg.bWhole, cfg.cWhole, cfg.leftNode, cfg.rightNode,
    cfg.z1A, cfg.z1B, cfg.b1, cfg.b2, cfg.lWhole),
    { numSelectors := cfg.qDecompose.index }, (), ?_⟩
  rcases cfg with ⟨⟨index, simple⟩, a, b, c, left, right, z1A, z1B,
    b1, b2, lWhole⟩
  simp only at hsimple
  subst simple
  rfl

/-- The decomposition gate requests one deferred constant cell for its layer
index. -/
@[synthesis_summary_norm]
theorem circuit_synthesisSummary_constantSiteCount
    (l : Fp) (config : Config) (input : Var Inputs Fp)
    (region : RegionIndex) :
    ((circuit l).elaborated.synthesisSummary
      config 0 input region).constantSiteCount = 1 := by
  rw [ElaboratedRegionCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [circuit, body, circuit_norm]

end Gate

/-! ### The chip-level configure

`CondSwapChip::configure` on the five Sinsemilla hash advices (`[x_a, x_p, bits, λ₁, λ₂]`), then
the `q_decompose` selector + the decomposition gate over the same five columns at rotations 0/1. -/

structure Config where
  -- The cond-swap child config.
  condSwap : CondSwap.Config
  -- The decomposition-gate slice.
  gate : Gate.Config
  -- The underlying Sinsemilla hash config.
  sinsemilla : HashPiece.Config

/-- Rust `MerkleChip::configure`: CondSwap first (on `advices()` order), then
`q_decompose` + the decomposition gate, whose ten reads are the five advices at
rotations 0/1 (`a_whole … right_node` at 0; `z1_a, z1_b, b_1, b_2, l` at 1). -/
def configure (scfg : HashPiece.Config) : Configure Fp Config := do
  let condSwap ← CondSwap.configure scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
  let gate ← Gate.configure scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
    scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
  return { condSwap, gate, sinsemilla := scfg }

@[configure_selector_norm, keygen_norm] theorem configure_delta_lookups
    (scfg : HashPiece.Config) (counts) :
    ((configure scfg).delta counts).lookups = [] := by
  simp [configure, CondSwap.configure, Gate.configure]

@[keygen_norm] theorem configure_delta_constants
    (scfg : HashPiece.Config) (counts) :
    ((configure scfg).delta counts).constants = [] := by
  simp [configure, CondSwap.configure, Gate.configure]

@[keygen_norm] theorem configure_fixedColumns
    (scfg : HashPiece.Config) (counts) :
    (configure scfg).fixedColumns counts = [] := by
  simp [configure, CondSwap.configure, Gate.configure]

@[reducible] private def configureInferred (scfg : HashPiece.Config) :
    ElaboratedConfigure (configure scfg) := by
  unfold configure
  infer_instance

private theorem configure_selectorRequirements
    (scfg : HashPiece.Config) (counts) :
    (configureInferred scfg).selectorRequirements counts := by
  dsimp only [configureInferred, configure]
  simp [configure_selector_norm, CondSwap.configure, Gate.configure]

instance (scfg : HashPiece.Config) :
    ElaboratedConfigure (configure scfg) :=
  ((configureInferred scfg).closeSelectorRequirements
    (configure_selectorRequirements scfg)).withNoExternalSelectors (by
      intro counts
      constructor
      · simp [configure, CondSwap.configure, Gate.configure,
          CondSwap.swapGate_selector, Gate.decomposeGate_selector]
      · simp [configure, CondSwap.configure, Gate.configure])

/-- Capabilities produced by one Merkle configure run. Hashing and range checking
remain caller-supplied because `configure` receives their already-built configs. -/
structure ConfigureCertificate (scfg : HashPiece.Config)
    (counts : ConfigureCounts) (context : KeygenContext Fp) where
  condSwap : ∀ (wb : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool),
    (CondSwap.swap wb wswap).ConfigurationCertificate
      (configure scfg |>.output counts).condSwap context
  gate : ∀ l : Fp,
    (Gate.circuit l).ConfigurationCertificate
      (configure scfg |>.output counts).gate context

namespace ConfigureCertificate

def mono {scfg : HashPiece.Config} {counts : ConfigureCounts}
    {source target : KeygenContext Fp}
    (certificate : ConfigureCertificate scfg counts source)
    (gates : ∀ gate, gate ∈ source.gates → gate ∈ target.gates)
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups)
    (fixedColumns : ∀ column,
      column ∈ source.fixedColumns → column ∈ target.fixedColumns)
    (permutationColumns : ∀ column,
      column ∈ source.permutationColumns → column ∈ target.permutationColumns) :
    ConfigureCertificate scfg counts target where
  condSwap wb wswap :=
    (certificate.condSwap wb wswap).mono gates lookups fixedColumns permutationColumns
  gate l := (certificate.gate l).mono gates lookups fixedColumns permutationColumns

end ConfigureCertificate

/-- Build the Merkle-local capabilities once, beside their producing configure. -/
def configureCertificate (scfg : HashPiece.Config) (counts : ConfigureCounts) :
    ConfigureCertificate scfg counts
      { gates := (configure scfg |>.delta counts).gates
        lookups := (configure scfg |>.delta counts).lookups
        fixedColumns := (configure scfg).fixedColumns counts
        permutationColumns :=
          Gate.permutationColumns
            (scfg.xA, scfg.xP, scfg.bits, scfg.lambda1, scfg.lambda2,
              scfg.xA, scfg.xP, scfg.bits, scfg.lambda1, scfg.lambda2) ++
            (configure scfg |>.delta counts).permutationRequests } := by
  let swapProgram := CondSwap.configure scfg.xA scfg.xP scfg.bits
    scfg.lambda1 scfg.lambda2
  let gateInput := (scfg.xA, scfg.xP, scfg.bits, scfg.lambda1, scfg.lambda2,
    scfg.xA, scfg.xP, scfg.bits, scfg.lambda1, scfg.lambda2)
  refine { condSwap := ?_, gate := ?_ }
  · intro wb wswap
    apply (CondSwap.swapConfigureCertificate scfg.xA scfg.xP scfg.bits
      scfg.lambda1 scfg.lambda2 counts wb wswap).mono
    · intro gate hgate
      simp only
      unfold configure
      apply Configure.mem_gates_delta_bind_left
      exact hgate
    · intro argument hargument
      simp only
      unfold configure
      apply Configure.mem_lookups_delta_bind_left
      exact hargument
    · intro column hcolumn
      unfold configure
      exact Configure.mem_fixedColumns_bind_left _ _ _ hcolumn
    · intro column hcolumn
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcolumn
      rcases hcolumn with (hcolumn | hcolumn) | hcolumn
      · subst column
        apply List.mem_append_left
        simp [Gate.permutationColumns]
      · subst column
        apply List.mem_append_left
        simp [Gate.permutationColumns]
      · apply List.mem_append_right
        unfold configure
        exact Configure.mem_permutationRequests_delta_bind_left _ _ _ _ hcolumn
  · intro l
    apply ((Gate.circuit l).configureCertificate gateInput
      (swapProgram.finalCounts counts) ()).mono
    · intro gate hgate
      simp only [Gate.circuit, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.mem_append] at hgate
      simp only
      unfold configure
      apply Configure.mem_gates_delta_bind_right
      rcases hgate with hgate | hgate
      · exact False.elim (List.not_mem_nil hgate)
      · simpa [gateInput, swapProgram] using hgate
    · intro argument hargument
      simp only [Gate.circuit, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.mem_append] at hargument
      simp only
      unfold configure
      apply Configure.mem_lookups_delta_bind_right
      rcases hargument with hargument | hargument
      · exact False.elim (List.not_mem_nil hargument)
      · simpa [gateInput, swapProgram] using hargument
    · intro column hcolumn
      simp only [Gate.circuit, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact False.elim (List.not_mem_nil hcolumn)
      unfold configure
      apply Configure.mem_fixedColumns_bind_right
      simpa [gateInput, swapProgram] using hcolumn
    · intro column hcolumn
      simp only [Gate.circuit, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact List.mem_append_left _ (by simpa [gateInput] using hcolumn)
      · apply List.mem_append_right
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        simpa [gateInput, swapProgram] using hcolumn

/-! ### Digit toolkit

`K`-bit little-endian digit sums: extraction, recombination, bounds. Framework-agnostic `ℕ`
arithmetic. -/

/-- Factor the lowest digit out of a digit sum. Donor `Merkle.sum_head_shift`. -/
private theorem sum_head_shift (Kb m : ℕ) (d : ℕ → ℕ) :
    ∑ j ∈ Finset.range (m + 1), d j * 2 ^ (Kb * j)
      = d 0 + 2 ^ Kb * ∑ j ∈ Finset.range m, d (j + 1) * 2 ^ (Kb * j) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have hstep : ∀ j : ℕ,
      d (j + 1) * 2 ^ (Kb * (j + 1)) = 2 ^ Kb * (d (j + 1) * 2 ^ (Kb * j)) := by
    intro j
    rw [show Kb * (j + 1) = Kb + Kb * j from by ring, pow_add]
    ring
  simp only [hstep, Nat.mul_zero, pow_zero, Nat.mul_one]
  ring

/-- A digit sum of `n` digits fits in `Kb · n` bits. Donor `Merkle.sum_digits_lt`. -/
private theorem sum_digits_lt {Kb : ℕ} {d : ℕ → ℕ} (hd : ∀ j, d j < 2 ^ Kb) (n : ℕ) :
    ∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j) < 2 ^ (Kb * n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hterm : d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) ≤ 2 ^ (Kb * (m + 1)) := by
      rw [show Kb * (m + 1) = Kb * m + Kb from by ring, pow_add]
      calc d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) = (d m + 1) * 2 ^ (Kb * m) := by ring
        _ ≤ 2 ^ Kb * 2 ^ (Kb * m) := Nat.mul_le_mul_right _ (hd m)
        _ = 2 ^ (Kb * m) * 2 ^ Kb := by ring
    omega

/-- Concatenating a `Kb·m`-bit value with high bits stays within bounds. Donor `Merkle.append_lt`. -/
private theorem append_lt {m n x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ n) :
    x + 2 ^ m * y < 2 ^ (m + n) := by
  have h1 : x + 2 ^ m * y < 2 ^ m * (1 + y) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h2 : 2 ^ m * (1 + y) ≤ 2 ^ m * 2 ^ n := Nat.mul_le_mul_left _ (by omega)
  rw [pow_add]
  omega

/-- Each digit of a bounded-digit sum is recovered by shift-and-mask. Donor `Merkle.digit_of_sum`. -/
private theorem digit_of_sum (Kb : ℕ) :
    ∀ (i n : ℕ) (d : ℕ → ℕ), (∀ j, d j < 2 ^ Kb) → i < n →
      (∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j)) / 2 ^ (Kb * i) % 2 ^ Kb = d i := by
  intro i
  induction i with
  | zero =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift, Nat.mul_zero, pow_zero, Nat.div_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0)]
  | succ i ih =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift,
      show Kb * (i + 1) = Kb + Kb * i from by ring, pow_add,
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos Kb),
      Nat.div_eq_of_lt (hd 0), Nat.zero_add]
    exact ih m (fun j => d (j + 1)) (fun j => hd (j + 1)) (by omega)

/-- A `Kb·n`-bit value is the sum of its shift-and-mask digits. Donor `Merkle.sum_words`. -/
private theorem sum_words (Kb : ℕ) :
    ∀ (n x : ℕ), x < 2 ^ (Kb * n) →
      ∑ j ∈ Finset.range n, (x / 2 ^ (Kb * j) % 2 ^ Kb) * 2 ^ (Kb * j) = x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at hx
    simp [hx]
  | succ m ih =>
    intro x hx
    rw [sum_head_shift]
    have hdig : ∀ j : ℕ, x / 2 ^ (Kb * (j + 1)) % 2 ^ Kb
        = (x / 2 ^ Kb) / 2 ^ (Kb * j) % 2 ^ Kb := by
      intro j
      rw [show Kb * (j + 1) = Kb + Kb * j from by ring, pow_add,
        Nat.div_div_eq_div_mul]
    simp only [hdig]
    rw [ih (x / 2 ^ Kb) (by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos Kb),
        ← pow_add]
      rw [show Kb * m + Kb = Kb * (m + 1) from by ring]
      exact hx)]
    rw [Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_add_div]

set_option exponentiation.threshold 600 in
/-- Split a 52-digit sum into the `a`/`b`/`c` segments of the `MerkleCRH` message. Donor
`Merkle.merkle_sum_split`. -/
private theorem merkle_sum_split (D : ℕ → ℕ) :
    ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        + 2 ^ 250 * (∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * j))
        + 2 ^ 270 * (∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * j)) := by
  have h1 : ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 27, D j * 2 ^ (K * j)
        + ∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * (27 + j)) := by
    rw [← Finset.sum_range_add]
  have h2 : ∑ j ∈ Finset.range 27, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        + ∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * (25 + j)) := by
    rw [← Finset.sum_range_add]
  have h3 : ∀ j, D (25 + j) * 2 ^ (K * (25 + j))
      = 2 ^ 250 * (D (25 + j) * 2 ^ (K * j)) := by
    intro j
    rw [show K * (25 + j) = 250 + K * j from by
        simp only [show (K : ℕ) = 10 from rfl]; ring, pow_add]
    ring
  have h4 : ∀ j, D (27 + j) * 2 ^ (K * (27 + j))
      = 2 ^ 270 * (D (27 + j) * 2 ^ (K * j)) := by
    intro j
    rw [show K * (27 + j) = 270 + K * j from by
        simp only [show (K : ℕ) = 10 from rfl]; ring, pow_add]
    ring
  rw [h1, h2]
  simp only [h3, h4, ← Finset.mul_sum]

set_option exponentiation.threshold 600 in
/-- The `MerkleCRH` chunk list is the concatenation of the three pieces' chunk lists, given that
the packed message value decomposes into the pieces' digits. Donor `Merkle.merkleChunks_eq`. -/
private theorem merkleChunks_eq {dA dB dC : ℕ → ℕ}
    (hA : ∀ j, dA j < 2 ^ K) (hB : ∀ j, dB j < 2 ^ K) (hC : ∀ j, dC j < 2 ^ K)
    {l lv rv : ℕ}
    (hm : l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = ∑ j ∈ Finset.range 25, dA j * 2 ^ (K * j)
        + 2 ^ 250 * (∑ j ∈ Finset.range 2, dB j * 2 ^ (K * j))
        + 2 ^ 270 * (∑ j ∈ Finset.range 25, dC j * 2 ^ (K * j))) :
    merkleChunks l lv rv
      = (List.range 25).map dA ++ ((List.range 2).map dB ++ (List.range 25).map dC) := by
  set D : ℕ → ℕ := fun i => if i < 25 then dA i else if i < 27 then dB (i - 25)
    else dC (i - 27) with hD
  have hDlt : ∀ j, D j < 2 ^ K := by
    intro j
    rw [hD]
    dsimp only
    split
    · exact hA j
    split
    · exact hB (j - 25)
    · exact hC (j - 27)
  have hsum : l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j) := by
    rw [merkle_sum_split, hm]
    have e1 : ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 25, dA j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        have hj' : j < 25 := Finset.mem_range.mp hj
        simp only [hD]
        rw [if_pos hj']
    have e2 : ∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 2, dB j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        have hj' : j < 2 := Finset.mem_range.mp hj
        simp only [hD]
        rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    have e3 : ∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 25, dC j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        simp only [hD]
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
    rw [e1, e2, e3]
  apply List.ext_getElem
  · simp [merkleChunks]
  intro i hi hi'
  have hi52 : i < 52 := by
    simp only [merkleChunks, List.length_map, List.length_range] at hi
    exact hi
  rw [show (merkleChunks l lv rv)[i]
      = (l + 2 ^ 10 * lv + 2 ^ 265 * rv) / 2 ^ (K * i) % 2 ^ K from by
    simp [merkleChunks]]
  rw [hsum, digit_of_sum K i 52 D hDlt hi52]
  rcases Nat.lt_or_ge i 25 with h25 | h25
  · rw [List.getElem_append_left (by simpa using h25)]
    simp only [hD]
    rw [if_pos h25]
    simp
  rw [List.getElem_append_right (by simpa using h25)]
  rcases Nat.lt_or_ge i 27 with h27 | h27
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [hD]
    rw [if_neg (by omega), if_pos h27]
    simp
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [hD]
    rw [if_neg (by omega), if_neg (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1

/-! ### Field-level helpers -/

private theorem natCast_inj_lt {a b : ℕ} (ha : a < 2 ^ 10) (hb : b < 2 ^ 10)
    (h : (a : Fp) = (b : Fp)) : a = b := by
  have hp : (2 ^ 10 : ℕ) < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

/-! ### Assembling the soundness-side encodings (lifted verbatim)

From the decomposition-gate equations, the pieces' chunk sums, and the range-checked sub-pieces,
the 255-bit encodings of `left`/`right` are recovered, and the `MerkleCRH` chunks are exactly the
pieces' chunks. Donor `Merkle.assemble`. -/

private theorem two_pow_250_lt_p : (2 : ℕ) ^ 250 < PALLAS_BASE_CARD := by
  norm_num [PALLAS_BASE_CARD]

set_option exponentiation.threshold 600 in
private theorem assemble {msA msB msC : ℕ → ℕ}
    (hmsA : ∀ j, msA j < 2 ^ K) (hmsB : ∀ j, msB j < 2 ^ K) (hmsC : ∀ j, msC j < 2 ^ K)
    {l b1n b2n : ℕ} (hl : l < 2 ^ 10) (hb1n : b1n < 2 ^ 5) (hb2n : b2n < 2 ^ 5)
    {aCell bCell cCell b1Cell b2Cell z1A z1B left right : Fp}
    (haval : aCell = ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp))
    (hbval : bCell = ((∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) : ℕ) : Fp))
    (hcval : cCell = ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Fp))
    (hb1 : b1Cell = ((b1n : ℕ) : Fp)) (hb2 : b2Cell = ((b2n : ℕ) : Fp))
    (hz1A : z1A = ((∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) : ℕ) : Fp))
    (hz1B : z1B = ((msB 1 : ℕ) : Fp))
    (hg1 : (l : Fp) = aCell - z1A * (twoPow10 : Fp))
    (hg2 : left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240)
    (hg3 : right = b2Cell + cCell * twoPow5)
    (hg4 : z1B = b1Cell + b2Cell * twoPow5) :
    ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
      lv = ZMod.val aCell / 2 ^ 10
        + 2 ^ 240 * (ZMod.val bCell % 2 ^ 10 + 2 ^ 10 * ZMod.val b1Cell) ∧
      rv = ZMod.val b2Cell + 2 ^ 5 * ZMod.val cCell ∧
      ((lv : ℕ) : Fp) = left ∧ ((rv : ℕ) : Fp) = right ∧
      merkleChunks l lv rv
        = (List.range 25).map msA
          ++ ((List.range 2).map msB ++ (List.range 25).map msC) := by
  subst haval hbval hcval hb1 hb2 hz1A hz1B
  have hK : K = 10 := rfl
  have e5 : (twoPow5 : Fp) = ((2 ^ 5 : ℕ) : Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Fp) = ((2 ^ 10 : ℕ) : Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Fp) = ((2 ^ 240 : ℕ) : Fp) := by
    norm_num [twoPow240]
  rw [e10] at hg1
  rw [e10, e240] at hg2
  rw [e5] at hg3
  rw [e5] at hg4
  set lvA := ∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) with hlvA
  set cnv := ∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) with hcnv
  have hlvA_lt : lvA < 2 ^ 240 := by
    have h := sum_digits_lt (d := fun j => msA (j + 1)) (fun j => hmsA (j + 1)) 24
    rw [hK] at h
    norm_num at h
    exact h
  have hcnv_lt : cnv < 2 ^ 250 := by
    have h := sum_digits_lt (d := msC) hmsC 25
    rw [hK] at h
    norm_num at h
    exact h
  have hSA : (∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r)) = msA 0 + 2 ^ 10 * lvA := by
    have h := sum_head_shift K 24 msA
    rw [hK] at h ⊢
    norm_num at h ⊢
    exact h
  have hSB : (∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r)) = msB 0 + 2 ^ 10 * msB 1 := by
    have h := sum_head_shift K 1 msB
    rw [hK] at h ⊢
    norm_num [Finset.sum_range_one] at h ⊢
    exact h
  have hl0 : l = msA 0 := by
    apply natCast_inj_lt hl (by rw [← hK]; exact hmsA 0)
    rw [hSA] at hg1
    push_cast at hg1
    linear_combination hg1
  have hmsB1 : msB 1 = b1n + 2 ^ 5 * b2n := by
    apply natCast_inj_lt (by rw [← hK]; exact hmsB 1)
      (by have := append_lt hb1n hb2n; norm_num at this; exact this)
    push_cast
    linear_combination hg4
  have hsumA_lt : (∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r)) < PALLAS_BASE_CARD :=
    lt_trans (by simpa [hK] using sum_digits_lt hmsA 25) two_pow_250_lt_p
  have hsumB_lt : (∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r)) < PALLAS_BASE_CARD := by
    have h := sum_digits_lt hmsB 2
    rw [hK] at h
    exact lt_trans h (by norm_num [PALLAS_BASE_CARD])
  have hvalA : ZMod.val ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp)
      = ∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) :=
    ZMod.val_natCast_of_lt hsumA_lt
  have hvalB : ZMod.val ((∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) : ℕ) : Fp)
      = ∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) :=
    ZMod.val_natCast_of_lt hsumB_lt
  have hvalC : ZMod.val ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Fp) = cnv := by
    rw [ZMod.val_natCast_of_lt (lt_trans hcnv_lt two_pow_250_lt_p), hcnv]
  have hvalB1 : ZMod.val ((b1n : ℕ) : Fp) = b1n :=
    ZMod.val_natCast_of_lt (lt_trans hb1n (by norm_num [PALLAS_BASE_CARD]))
  have hvalB2 : ZMod.val ((b2n : ℕ) : Fp) = b2n :=
    ZMod.val_natCast_of_lt (lt_trans hb2n (by norm_num [PALLAS_BASE_CARD]))
  refine ⟨lvA + 2 ^ 240 * (msB 0 + 2 ^ 10 * b1n), b2n + 2 ^ 5 * cnv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hin : msB 0 + 2 ^ 10 * b1n < 2 ^ 15 := by
      have h := append_lt (show msB 0 < 2 ^ 10 from by rw [← hK]; exact hmsB 0) hb1n
      norm_num at h
      exact h
    have h := append_lt hlvA_lt hin
    norm_num at h
    exact h
  · have h := append_lt hb2n hcnv_lt
    norm_num at h
    exact h
  · rw [hvalA, hvalB, hvalB1, hSA, hSB]
    have hA0 := hmsA 0
    have hB0 := hmsB 0
    rw [hK] at hA0 hB0
    norm_num at hA0 hB0
    omega
  · rw [hvalB2, hvalC]
  · rw [hg2, hSB]
    push_cast
    ring
  · rw [hg3]
    push_cast
    ring
  · apply merkleChunks_eq hmsA hmsB hmsC
    rw [hSA, hSB, ← hl0, hmsB1]
    ring

/-! ### The honest decomposition (lifted verbatim) -/

set_option exponentiation.threshold 600 in
/-- Decomposing the packed message value into the three honest piece values. Donor
`Merkle.merkle_honest_sum`. -/
private theorem merkle_honest_sum (l lv rv : ℕ) :
    l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = (l + 2 ^ 10 * (lv % 2 ^ 240))
        + 2 ^ 250 * (lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
            + 2 ^ 15 * (rv % 2 ^ 5))
        + 2 ^ 270 * (rv / 2 ^ 5) := by
  omega

set_option exponentiation.threshold 600 in
/-- The `MerkleCRH` chunks of the canonical encodings are the honest pieces' chunks. Donor
`Merkle.honest_chunks`. -/
private theorem honest_chunks {l lv rv : ℕ} (hl : l < 2 ^ 10) (hlv : lv < 2 ^ 255)
    (hrv : rv < 2 ^ 255) :
    merkleChunks l lv rv
      = (List.range 25).map
          (fun j => (l + 2 ^ 10 * (lv % 2 ^ 240)) / 2 ^ (K * j) % 2 ^ K)
        ++ ((List.range 2).map
            (fun j => (lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
                + 2 ^ 15 * (rv % 2 ^ 5)) / 2 ^ (K * j) % 2 ^ K)
          ++ (List.range 25).map (fun j => rv / 2 ^ 5 / 2 ^ (K * j) % 2 ^ K)) := by
  have hK : K = 10 := rfl
  have haN : l + 2 ^ 10 * (lv % 2 ^ 240) < 2 ^ (K * 25) := by
    rw [hK]
    have h := append_lt hl (Nat.mod_lt lv (y := 2 ^ 240) (by positivity))
    norm_num at h ⊢
    exact h
  have hb1n : lv / 2 ^ 250 < 2 ^ 5 := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact hlv
  have hbN : lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
      + 2 ^ 15 * (rv % 2 ^ 5) < 2 ^ (K * 2) := by
    rw [hK]
    have hin : lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5) < 2 ^ 10 := by
      have h := append_lt hb1n (Nat.mod_lt rv (y := 2 ^ 5) (by positivity))
      norm_num at h
      exact h
    have h := append_lt (Nat.mod_lt (lv / 2 ^ 240) (y := 2 ^ 10) (by positivity)) hin
    norm_num at h ⊢
    calc lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5)
        = lv / 2 ^ 240 % 2 ^ 10
          + 2 ^ 10 * (lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5)) := by ring
      _ < 1048576 := h
  have hcN : rv / 2 ^ 5 < 2 ^ (K * 25) := by
    rw [hK]
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact hrv
  apply merkleChunks_eq (fun j => Nat.mod_lt _ (by positivity))
    (fun j => Nat.mod_lt _ (by positivity))
    (fun j => Nat.mod_lt _ (by positivity))
  rw [sum_words K 25 _ haN, sum_words K 2 _ hbN, sum_words K 25 _ hcN]
  exact merkle_honest_sum l lv rv

private theorem p_lt_two_pow_255 : PALLAS_BASE_CARD < 2 ^ 255 := by
  norm_num [PALLAS_BASE_CARD]

set_option exponentiation.threshold 600 in
/-- The honest piece values are in range and their chunk words make up the `MerkleCRH` message.
Donor `Merkle.honest_pieces`. -/
private theorem honest_pieces {l lv rv : ℕ} (hl : l < 2 ^ 10)
    (hlv : lv < 2 ^ 255) (hrv : rv < 2 ^ 255)
    {aCell bCell cCell : Fp}
    (haw : aCell = ((l + 2 ^ 10 * bitrange lv 0 240 : ℕ) : Fp))
    (hbw : bCell = ((bitrange lv 240 10 + 2 ^ 10 * bitrange lv 250 5
      + 2 ^ 15 * bitrange rv 0 5 : ℕ) : Fp))
    (hcw : cCell = ((bitrange rv 5 250 : ℕ) : Fp)) :
    (ZMod.val aCell < 2 ^ (K * 25) ∧ ZMod.val bCell < 2 ^ (K * 2)
      ∧ ZMod.val cCell < 2 ^ (K * 25))
    ∧ List.map (pieceWord aCell) (List.range 25)
        ++ (List.map (pieceWord bCell) (List.range 2)
          ++ List.map (pieceWord cCell) (List.range 25))
        = merkleChunks l lv rv := by
  have hb240 : bitrange lv 240 10 = lv / 2 ^ 240 % 2 ^ 10 := rfl
  have hb250 : bitrange lv 250 5 = lv / 2 ^ 250 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hlv))
  have hc5 : bitrange rv 5 250 = rv / 2 ^ 5 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hrv))
  simp only [bitrange_zero, hb240, hb250, hc5] at haw hbw hcw
  subst haw hbw hcw
  have hK : K = 10 := rfl
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalC : ZMod.val ((rv / 2 ^ 5 : ℕ) : Fp) = rv / 2 ^ 5 :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hvalA, hK]
    omega
  · rw [hvalB, hK]
    omega
  · rw [hvalC, hK]
    omega
  · rw [honest_chunks hl hlv hrv]
    congr 1
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
          / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalA]
    congr 1
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
            + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalB]
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((rv / 2 ^ 5 : ℕ) : Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalC]

set_option exponentiation.threshold 600 in
/-- The decomposition-gate equations hold on the honest witness values. Donor `Merkle.honest_gate`. -/
private theorem honest_gate {l lv rv : ℕ} (hl : l < 2 ^ 10)
    (hlv : lv < 2 ^ 255) (hrv : rv < 2 ^ 255)
    {aCell bCell b1Cell b2Cell cCell z1A z1B left right : Fp}
    (haw : aCell = ((l + 2 ^ 10 * bitrange lv 0 240 : ℕ) : Fp))
    (hb1w : b1Cell = ((bitrange lv 250 5 : ℕ) : Fp))
    (hb2w : b2Cell = ((bitrange rv 0 5 : ℕ) : Fp))
    (hbw : bCell = ((bitrange lv 240 10 + 2 ^ 10 * bitrange lv 250 5
      + 2 ^ 15 * bitrange rv 0 5 : ℕ) : Fp))
    (hcw : cCell = ((bitrange rv 5 250 : ℕ) : Fp))
    (hz1A : z1A = pieceZ aCell 1) (hz1B : z1B = pieceZ bCell 1)
    (hleft : ((lv : ℕ) : Fp) = left) (hright : ((rv : ℕ) : Fp) = right) :
    ((l : ℕ) : Fp) = aCell - z1A * twoPow10
      ∧ left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240
      ∧ right = b2Cell + cCell * twoPow5
      ∧ z1B = b1Cell + b2Cell * twoPow5 := by
  have hb240 : bitrange lv 240 10 = lv / 2 ^ 240 % 2 ^ 10 := rfl
  have hb250 : bitrange lv 250 5 = lv / 2 ^ 250 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hlv))
  have hc5 : bitrange rv 5 250 = rv / 2 ^ 5 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hrv))
  simp only [bitrange_zero, hb240, hb250, hc5] at haw hb1w hb2w hbw hcw
  have e5 : (twoPow5 : Fp) = ((2 ^ 5 : ℕ) : Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Fp) = ((2 ^ 10 : ℕ) : Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Fp) = ((2 ^ 240 : ℕ) : Fp) := by
    norm_num [twoPow240]
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hzA : pieceZ aCell 1 = ((lv % 2 ^ 240 : ℕ) : Fp) := by
    simp only [pieceZ, haw, hvalA]
    congr 1
    rw [show K * 1 = 10 from rfl]
    omega
  have hzB : pieceZ bCell 1
      = ((lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5) : ℕ) : Fp) := by
    simp only [pieceZ, hbw, hvalB]
    congr 1
    rw [show K * 1 = 10 from rfl]
    omega
  subst hleft hright
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [haw, hz1A, hzA, e10]
    push_cast
    ring
  · rw [hz1A, hzA, hbw, hz1B, hzB, hb1w, e10, e240]
    have hnat : lv = lv % 2 ^ 240 + 2 ^ 240 * (lv / 2 ^ 240 % 2 ^ 10)
        + 2 ^ 250 * (lv / 2 ^ 250) := by omega
    have hc := congrArg (Nat.cast (R := Fp)) hnat
    push_cast at hc ⊢
    linear_combination hc
  · rw [hb2w, hcw, e5]
    have hnat : rv = rv % 2 ^ 5 + 2 ^ 5 * (rv / 2 ^ 5) := by omega
    have hc := congrArg (Nat.cast (R := Fp)) hnat
    push_cast at hc ⊢
    linear_combination hc
  · rw [hz1B, hzB, hb1w, hb2w, e5]
    push_cast
    ring

/-! ### `MerkleInstructions::hash_layer` (structure)

One Merkle layer: witness the three pieces + `b_1`/`b_2`, range-check the short sub-pieces
(`LookupRangeCheck.shortRangeCheck`, ported), hash `a || b || c` (`Chain.circuit`, ported —
`z_1` cells read off its exposed `zs` HVec as `zs[i][1]`), tie the pieces to `(l, left, right)`
via the `Gate`. Structure-complete; the value glue is the lifted `assemble`/`honest_*`. -/

namespace HashLayer

/-- The layer index `l` is a circuit parameter (a fixed column in the source). -/
structure Input (F : Type) where
  -- The left child node.
  left : F
  -- The right child node.
  right : F
deriving ProvableStruct

/-- The five decomposition cells which determine the literal 255-bit encodings
of the two children. Keeping these reads in the contract is important: the
field-valued child nodes alone do not determine their 255-bit representatives. -/
structure Encoding where
  a : Fp
  b : Fp
  c : Fp
  b1 : Fp
  b2 : Fp
deriving Inhabited

/-- Reconstruct the left input's 255-bit representative from the `a`/`b` pieces. -/
def leftEncoding (w : Encoding) : ℕ :=
  w.a.val / 2 ^ 10 + 2 ^ 240 * (w.b.val % 2 ^ 10 + 2 ^ 10 * w.b1.val)

/-- Reconstruct the right input's 255-bit representative from the `b`/`c` pieces. -/
def rightEncoding (w : Encoding) : ℕ := w.b2.val + 2 ^ 5 * w.c.val

/-- The layer spec: some 255-bit encodings of `left`/`right` whose
`MerkleCRH` message hashes (over `Q`) to a point whose `x` is the output. -/
def Spec (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : Value Input Fp) (output : Value field Fp) (w : Encoding) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    lv = leftEncoding w ∧ rv = rightEncoding w ∧
    ((lv : ℕ) : Fp) = input.left ∧ ((rv : ℕ) : Fp) = input.right ∧
    ∀ B, hashToPoint G.S Q (merkleChunks l lv rv) = some B → output = B.x

/-- The honest-prover precondition: the honest `MerkleCRH` hash over `(left, right)` is defined. -/
def ProverAssumptions (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : Value Input Fp) : Prop :=
  ∃ B, hashToPoint G.S Q
    (merkleChunks l (ZMod.val (show Fp from input.left))
      (ZMod.val (show Fp from input.right))) = some B

/-- The honest piece/sub-piece witness programs, computed off the node cells (Rust
`bitrange_subset` values, `Value`-view). `lv`/`rv` are the canonical node values. -/
def waWit (l : ℕ) (left : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((l + 2 ^ 10 * bitrange (Sinsemilla.HashPiece.readCell env left).val 0 240 : ℕ) : Fp)]

def wb1Wit (left : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (Sinsemilla.HashPiece.readCell env left).val 250 5 : ℕ) : Fp)]

def wb2Wit (right : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (Sinsemilla.HashPiece.readCell env right).val 0 5 : ℕ) : Fp)]

def wbWit (left right : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (Sinsemilla.HashPiece.readCell env left).val 240 10
        + 2 ^ 10 * bitrange (Sinsemilla.HashPiece.readCell env left).val 250 5
        + 2 ^ 15 * bitrange (Sinsemilla.HashPiece.readCell env right).val 0 5 : ℕ) : Fp)]

def wcWit (right : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (Sinsemilla.HashPiece.readCell env right).val 5 250 : ℕ) : Fp)]

/-- The MerkleCRH piece widths (25/2/25 words). -/
def merkleNs : List ℕ := [24, 1, 24]

/-- `MerkleInstructions::hash_layer`, layouter-level, in the Rust region sequence: witness `a`,
short-range-check `b_1`/`b_2` (5 bits), witness `b`/`c`, `hash_to_point` (the `hashMessage`
region), the `"Check piece decomposition"` gate region. Output: the hash point's `x` cell. -/
def synthesize (G : Generators) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ)
    (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  -- witness a; range-check b1/b2; witness b, c
  let pa ← HashToPoint.witnessMessagePiece cfg.sinsemilla (waWit l input.left)
  let b1 ← LookupRangeCheck.witnessShortCheck 10 5 lookupCfg
    (wb1Wit input.left)
  let b2 ← LookupRangeCheck.witnessShortCheck 10 5 lookupCfg
    (wb2Wit input.right)
  let pb ← HashToPoint.witnessMessagePiece cfg.sinsemilla (wbWit input.left input.right)
  let pc ← HashToPoint.witnessMessagePiece cfg.sinsemilla (wcWit input.right)
  -- the hash (the formal hash_to_point bundle)
  let out ← HashToPoint.hashMessage G merkleNs cfg.sinsemilla Q hQ (by decide)
    ⟨#v[pa, pb, pc]⟩
  -- the decomposition-gate region
  let _ ← assignRegion "Check piece decomposition"
    ((Gate.circuit (l : Fp)).call cfg.gate 0
      { aWhole := pa, bWhole := pb, cWhole := pc,
        leftNode := input.left, rightNode := input.right,
        z1A := out.z1s[0], z1B := out.z1s[1], b1 := b1, b2 := b2 })
  pure out.point.x

end HashLayer

/-- Literal-eval bridge for the gate-input record (component-wise cell evals). -/
private theorem gateInputs_eval_literal (env : Placed Environment Fp)
    (a b c ln rn zA zB s1 s2 : AssignedCell Fp) :
    (eval env ({ aWhole := a, bWhole := b, cWhole := c, leftNode := ln, rightNode := rn,
                 z1A := zA, z1B := zB, b1 := s1, b2 := s2 } : Gate.Inputs (AssignedCell Fp))
      : Value Gate.Inputs Fp)
      = { aWhole := AssignedCell.eval env.place env.env a,
          bWhole := AssignedCell.eval env.place env.env b,
          cWhole := AssignedCell.eval env.place env.env c,
          leftNode := AssignedCell.eval env.place env.env ln,
          rightNode := AssignedCell.eval env.place env.env rn,
          z1A := AssignedCell.eval env.place env.env zA,
          z1B := AssignedCell.eval env.place env.env zB,
          b1 := AssignedCell.eval env.place env.env s1,
          b2 := AssignedCell.eval env.place env.env s2 } := by
  rw [ProvableStruct.Halo2.eval_cells_eq_eval]
  provable_type_simp

/-- Literal-eval bridge for the gate-input record, prover view. -/
private theorem gateInputs_eval_literal_prover (env : Placed ProverEnvironment Fp)
    (a b c ln rn zA zB s1 s2 : AssignedCell Fp) :
    (eval env ({ aWhole := a, bWhole := b, cWhole := c, leftNode := ln, rightNode := rn,
                 z1A := zA, z1B := zB, b1 := s1, b2 := s2 } : Gate.Inputs (AssignedCell Fp))
      : Value Gate.Inputs Fp)
      = { aWhole := AssignedCell.eval env.place env.env.toEnvironment a,
          bWhole := AssignedCell.eval env.place env.env.toEnvironment b,
          cWhole := AssignedCell.eval env.place env.env.toEnvironment c,
          leftNode := AssignedCell.eval env.place env.env.toEnvironment ln,
          rightNode := AssignedCell.eval env.place env.env.toEnvironment rn,
          z1A := AssignedCell.eval env.place env.env.toEnvironment zA,
          z1B := AssignedCell.eval env.place env.env.toEnvironment zB,
          b1 := AssignedCell.eval env.place env.env.toEnvironment s1,
          b2 := AssignedCell.eval env.place env.env.toEnvironment s2 } := by
  rw [ProvableStruct.Halo2.eval_cells_eq_eval_prover]
  provable_type_simp

-- contract bridges for the children
derive_contract_bridges shortC (K : ℕ) (numBits : ℕ) :=
  LookupRangeCheck.shortRangeCheck K numBits

derive_contract_bridges gateC (lv : Fp) := Gate.circuit lv

/-- The suffix sum of bounded digits is the `pieceZ` of the recombined value (digit
canonicity: the value's `val` is the digit sum, and dividing by `2^K` drops the head). -/
private theorem sum_z1_eq_pieceZ {n : ℕ} (hn : K * (n + 1) ≤ 250) {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    {p : Fp} (hp : p = ((∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r) : ℕ) : Fp)) :
    ((∑ j ∈ Finset.range n, ms (j + 1) * 2 ^ (K * j) : ℕ) : Fp) = pieceZ p 1 := by
  have hsum_lt : (∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r)) < 2 ^ (K * (n + 1)) :=
    sum_digits_lt hms (n + 1)
  have hlt_p : (∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r)) < PALLAS_BASE_CARD :=
    lt_trans (lt_of_lt_of_le hsum_lt (Nat.pow_le_pow_right (by norm_num) hn))
      two_pow_250_lt_p
  have hval : ZMod.val p = ∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r) := by
    rw [hp, ZMod.val_natCast_of_lt hlt_p]
  have hshift := sum_head_shift K n ms
  show _ = ((ZMod.val p / 2 ^ (K * 1) : ℕ) : Fp)
  rw [hval, hshift]
  congr 1
  rw [show K * 1 = K from by ring,
    Nat.add_mul_div_left (ms 0) _ (Nat.two_pow_pos K),
    Nat.div_eq_of_lt (hms 0)]
  omega

/-- The region count of `HashLayer.synthesize`: three witness-piece regions, two short
range checks, the hash region, the decomposition region = 7. -/
private theorem hashLayer_regionCount (G : Generators) (cfg : Config)
    (lcfg : LookupRangeCheck.Config 10) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (input : Var HashLayer.Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((HashLayer.synthesize G cfg lcfg Q hQ l input).operations i) = 7 := by
  simp only [HashLayer.synthesize, HashToPoint.witnessMessagePiece,
    LookupRangeCheck.witnessShortCheck, HashToPoint.hashMessage,
    Circuit.operations_bind, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount]
  rw [show ∀ (j : RegionIndex) (pieces : Var (Sinsemilla.Chain.Inputs
        HashLayer.merkleNs.length) Fp) (h1 : HashLayer.merkleNs ≠ []),
      Operations.regionCount
        (((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ h1).call
          cfg.sinsemilla pieces).operations j) = 1 from fun j pieces h1 => by
    rw [FormalCircuit.call_regionCount]
    rfl]
  simp only [Circuit.operations_pure, Operations.regionCount]

@[keygen_output_norm]
theorem HashLayer.synthesize_output (G : Generators) (cfg : Config)
    (lcfg : LookupRangeCheck.Config 10) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (input : Var HashLayer.Input Fp) (i : RegionIndex) :
    (HashLayer.synthesize G cfg lcfg Q hQ l input).output i =
      AssignedCell.of (i + 5)
        (Sinsemilla.Chain.prefixRows HashLayer.merkleNs HashLayer.merkleNs.length)
        cfg.sinsemilla.xA := by
  simp only [HashLayer.synthesize, HashToPoint.witnessMessagePiece,
    LookupRangeCheck.witnessShortCheck, HashToPoint.hashMessage, circuit_norm,
    HashToPoint.hashCircuit_output_point_x, Nat.add_assoc, Nat.reduceAdd]

@[keygen_norm]
def HashLayer.keygenRequirements (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) :
    KeygenRequirements Fp (Config × LookupRangeCheck.Config 10)
      (Var HashLayer.Input Fp) where
  configLawful cfg :=
    (LookupRangeCheck.shortRangeCheck 10 5).Configured cfg.2 ×
      (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ (by decide)).Configured
        cfg.1.sinsemilla ×
        (Gate.circuit (l : Fp)).Configured cfg.1.gate
  gates _ configured :=
    configured.1.gates ++ configured.2.1.gates ++ configured.2.2.gates
  lookups _ configured :=
    configured.1.lookups ++ configured.2.1.lookups ++ configured.2.2.lookups
  fixedColumns _ configured :=
    configured.1.fixedColumns ++ configured.2.1.fixedColumns ++
      configured.2.2.fixedColumns
  permutationColumns cfg configured :=
    configured.1.permutationColumns ++ configured.2.1.permutationColumns ++
      configured.2.2.permutationColumns ++ [cfg.1.sinsemilla.witnessPieces.toAny]
  inputCells _ _ input :=
    [input.left.cell, input.right.cell]

private theorem HashLayer.hashMessage_keygenRegistered
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ)
    (configInput : Config × LookupRangeCheck.Config 10)
    (counts : ConfigureCounts)
    (hconfig : (HashLayer.keygenRequirements G Q hQ l).configLawful configInput)
    (input : Var HashLayer.Input Fp)
    (pieces : Var (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp)
    (i : RegionIndex)
    (hpieces : ∀ column,
      column ∈ hconfig.2.1.inputPermutationColumns pieces →
      column ∈
        (HashLayer.keygenRequirements G Q hQ l).permutationColumns
            configInput hconfig ++
          ((pure configInput : Configure Fp _).delta counts).permutationRequests ++
          (HashLayer.keygenRequirements G Q hQ l).inputPermutationColumns
            configInput hconfig input) :
    ((HashToPoint.hashMessage G HashLayer.merkleNs configInput.1.sinsemilla
      Q hQ (by decide) pieces).operations i).KeygenRegistered
      ((HashLayer.keygenRequirements G Q hQ l).gates configInput hconfig ++
        ((pure configInput : Configure Fp _).delta counts).gates)
      ((HashLayer.keygenRequirements G Q hQ l).lookups configInput hconfig ++
        ((pure configInput : Configure Fp _).delta counts).lookups)
      ((HashLayer.keygenRequirements G Q hQ l).fixedColumns configInput hconfig ++
        (pure configInput : Configure Fp _).fixedColumns counts)
      ((HashLayer.keygenRequirements G Q hQ l).permutationColumns
          configInput hconfig ++
        ((pure configInput : Configure Fp _).delta counts).permutationRequests ++
        (HashLayer.keygenRequirements G Q hQ l).inputPermutationColumns
          configInput hconfig input) := by
  unfold HashToPoint.hashMessage
  apply FormalCircuit.call_keygenRegistered _ _ hconfig.2.1
  · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_append] at *
    grind
  · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_append] at *
    grind
  · simp only [HashLayer.keygenRequirements, Configure.fixedColumns_pure,
      List.append_nil, List.mem_append] at *
    grind
  · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_append] at *
    grind
  · apply List.forall_iff_forall_mem.mpr
    intro cell hcell
    apply hpieces cell.column
    simp only [FormalCircuit.Configured.inputPermutationColumns,
      KeygenRequirements.inputPermutationColumns, List.mem_map]
    exact ⟨cell, hcell, rfl⟩

private theorem HashLayer.gate_keygenRegistered
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ)
    (configInput : Config × LookupRangeCheck.Config 10)
    (counts : ConfigureCounts)
    (hconfig : (HashLayer.keygenRequirements G Q hQ l).configLawful configInput)
    (input : Var HashLayer.Input Fp) (gateInput : Var Gate.Inputs Fp)
    (i : RegionIndex)
    (hgateInput : ∀ column,
      column ∈ hconfig.2.2.inputPermutationColumns gateInput →
      column ∈
        (HashLayer.keygenRequirements G Q hQ l).permutationColumns
            configInput hconfig ++
          ((pure configInput : Configure Fp _).delta counts).permutationRequests ++
          (HashLayer.keygenRequirements G Q hQ l).inputPermutationColumns
            configInput hconfig input) :
    ((assignRegion "Check piece decomposition"
      ((Gate.circuit (l : Fp)).call configInput.1.gate 0 gateInput)).operations i).KeygenRegistered
      ((HashLayer.keygenRequirements G Q hQ l).gates configInput hconfig ++
        ((pure configInput : Configure Fp _).delta counts).gates)
      ((HashLayer.keygenRequirements G Q hQ l).lookups configInput hconfig ++
        ((pure configInput : Configure Fp _).delta counts).lookups)
      ((HashLayer.keygenRequirements G Q hQ l).fixedColumns configInput hconfig ++
        (pure configInput : Configure Fp _).fixedColumns counts)
      ((HashLayer.keygenRequirements G Q hQ l).permutationColumns
          configInput hconfig ++
        ((pure configInput : Configure Fp _).delta counts).permutationRequests ++
        (HashLayer.keygenRequirements G Q hQ l).inputPermutationColumns
          configInput hconfig input) := by
  rw [operations_assignRegion, Operations.KeygenRegistered.region_cons]
  constructor
  · apply FormalRegionCircuit.call_keygenRegistered
      (Gate.circuit (l : Fp)) configInput.1.gate hconfig.2.2
      0 gateInput i
    · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
        List.append_nil, List.mem_append] at *
      grind
    · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
        List.append_nil, List.mem_append] at *
      grind
    · simp only [HashLayer.keygenRequirements, Configure.fixedColumns_pure,
        List.append_nil, List.mem_append] at *
      grind
    · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
        List.append_nil, List.mem_append] at *
      grind
    · apply List.forall_iff_forall_mem.mpr
      intro cell hcell
      apply hgateInput cell.column
      simp only [FormalRegionCircuit.Configured.inputPermutationColumns,
        KeygenRequirements.inputPermutationColumns, List.mem_map]
      exact ⟨cell, hcell, rfl⟩
  · exact Operations.KeygenRegistered.nil _ _ _ _

/-- Reduced layouter footprint of one Merkle hash layer. -/
def HashLayer.synthesisSummary (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) : FloorPlanner.SynthesisSummary :=
  (HashToPoint.witnessMessagePieceSynthesisSummary cfg.sinsemilla).combine
    ((LookupRangeCheck.witnessShortCheckSynthesisSummary 10 lookupCfg).combine
      ((LookupRangeCheck.witnessShortCheckSynthesisSummary 10 lookupCfg).combine
        ((HashToPoint.witnessMessagePieceSynthesisSummary cfg.sinsemilla).combine
          ((HashToPoint.witnessMessagePieceSynthesisSummary cfg.sinsemilla).combine
            ((HashToPoint.hashCircuitSynthesisSummary
                HashLayer.merkleNs cfg.sinsemilla).combine
              (FloorPlanner.SynthesisSummary.ofRegion
                (Gate.synthesisSummary cfg.gate 0)))))))

@[synthesis_summary_norm]
theorem HashLayer.synthesisSummary_lookupActivationCount
    (cfg : Config) (lookupCfg : LookupRangeCheck.Config 10) :
    (HashLayer.synthesisSummary cfg lookupCfg).lookupActivationCount = 56 := by
  simp only [HashLayer.synthesisSummary, HashLayer.merkleNs,
    synthesis_summary_norm, List.ofFn_succ, List.ofFn_zero, List.sum_cons,
    List.sum_nil]
  norm_num

@[synthesis_summary_norm]
theorem HashLayer.synthesisSummary_tableRowExtent_eq
    (cfg : Config) (lookupCfg : LookupRangeCheck.Config 10) :
    (HashLayer.synthesisSummary cfg lookupCfg).tableRowExtent = 0 := by
  simp only [HashLayer.synthesisSummary,
    HashToPoint.witnessMessagePieceSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    synthesis_summary_norm]

@[synthesis_summary_norm]
theorem HashLayer.synthesisSummary_instanceRowExtent_eq
    (cfg : Config) (lookupCfg : LookupRangeCheck.Config 10) :
    (HashLayer.synthesisSummary cfg lookupCfg).instanceRowExtent = 0 := by
  simp only [HashLayer.synthesisSummary,
    HashToPoint.witnessMessagePieceSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    synthesis_summary_norm]

/-- Fully reduced physical shape of the Merkle hash-to-point region. -/
def HashLayer.hashPhysicalShape (cfg : Sinsemilla.HashPiece.Config) :
    FloorPlanner.RegionShapeSummary :=
  HashToPoint.hashPhysicalShape HashLayer.merkleNs cfg

theorem HashLayer.hashPhysicalShape_eq
    (cfg : Sinsemilla.HashPiece.Config) :
    HashLayer.hashPhysicalShape cfg =
      (HashToPoint.hashRegionSynthesisSummary HashLayer.merkleNs cfg 0
        |>.toRegionShapeSummary).withoutSelectors := by
  rw [HashLayer.hashPhysicalShape, HashToPoint.hashPhysicalShape_eq]

@[synthesis_summary_norm]
theorem HashLayer.hashCircuitSynthesisSummary_physicalShapes_eq
    (cfg : Sinsemilla.HashPiece.Config) :
    (HashToPoint.hashCircuitSynthesisSummary HashLayer.merkleNs cfg
      |>.physicalRegionShapes) = [HashLayer.hashPhysicalShape cfg] := by
  rw [HashToPoint.hashCircuitSynthesisSummary_physicalShapes_eq]
  rfl

@[synthesis_summary_norm]
theorem HashLayer.synthesisSummary_physicalShapes_eq
    (cfg : Config) (lookupCfg : LookupRangeCheck.Config 10) :
    (HashLayer.synthesisSummary cfg lookupCfg).physicalRegionShapes =
      (HashToPoint.witnessMessagePieceSynthesisSummary cfg.sinsemilla
          |>.physicalRegionShapes) ++
      (LookupRangeCheck.witnessShortCheckSynthesisSummary 10 lookupCfg
          |>.physicalRegionShapes) ++
      (LookupRangeCheck.witnessShortCheckSynthesisSummary 10 lookupCfg
          |>.physicalRegionShapes) ++
      (HashToPoint.witnessMessagePieceSynthesisSummary cfg.sinsemilla
          |>.physicalRegionShapes) ++
      (HashToPoint.witnessMessagePieceSynthesisSummary cfg.sinsemilla
          |>.physicalRegionShapes) ++
      [HashLayer.hashPhysicalShape cfg.sinsemilla] ++
      (FloorPlanner.SynthesisSummary.ofRegion
          (Gate.synthesisSummary cfg.gate 0) |>.physicalRegionShapes) := by
  unfold HashLayer.synthesisSummary
  simp only [FloorPlanner.SynthesisSummary.combine_physicalRegionShapes,
    HashLayer.hashCircuitSynthesisSummary_physicalShapes_eq,
    List.append_assoc]

theorem HashLayer.synthesisSummary_eq (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) (input : Var HashLayer.Input Fp)
    (region : RegionIndex) :
    HashLayer.synthesisSummary cfg lookupCfg =
      FloorPlanner.synthesisSummary
        ((HashLayer.synthesize G cfg lookupCfg Q hQ l input).operations region) := by
  rw [HashLayer.synthesisSummary]
  simp only [HashLayer.synthesize, Circuit.operations_bind,
    FloorPlanner.synthesisSummary_append]
  repeat' first
    | rw [HashToPoint.witnessMessagePiece_synthesisSummary]
    | rw [LookupRangeCheck.witnessShortCheck_synthesisSummary]
  rw [HashToPoint.hashMessage_synthesisSummary]
  simp only [HashToPoint.witnessMessagePiece_nextRegionIndex,
    LookupRangeCheck.witnessShortCheck_nextRegionIndex,
    operations_assignRegion,
    FloorPlanner.synthesisSummary_region_cons,
    FloorPlanner.synthesisSummary_nil,
    Gate.circuit_synthesisSummary, circuit_norm, synthesis_summary_norm,
    Nat.add_assoc]

/-- One Merkle layer hash as a layouter-level formal circuit (`MerkleInstructions::hash_layer`),
on the proven children (`witnessShortCheck` ×2, the `hash_to_point` bundle, the decomposition
`Gate`). -/
def HashLayer.circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ)
    (hl : l < 2 ^ 10) :
    FormalCircuit Fp (Config × LookupRangeCheck.Config 10)
      (Config × LookupRangeCheck.Config 10) HashLayer.Input field where
  name := "hash layer"
  configure := pure

  synthesize := fun (cfg, lcfg) input => HashLayer.synthesize G cfg lcfg Q hQ l input

  elaborated :=
    { keygenRequirements := HashLayer.keygenRequirements G Q hQ l
      synthesisSummary cfg _ _ := HashLayer.synthesisSummary cfg.1 cfg.2
      synthesisSummary_eq := by
        intro cfg input region
        exact HashLayer.synthesisSummary_eq G Q hQ l cfg.1 cfg.2 input region
      registered := by
        intro configInput counts hconfig input i
        unfold HashLayer.synthesize
        simp only [Configure.output_pure, Circuit.operations_bind,
          Operations.KeygenRegistered.append, Circuit.operations_pure,
          Operations.KeygenRegistered.nil]
        constructor
        · exact HashToPoint.witnessMessagePiece_keygenRegistered _ _ _
        constructor
        · apply LookupRangeCheck.witnessShortCheck_keygenRegistered
          · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            left
            rw [LookupRangeCheck.shortRangeCheck_configured_gates_eq]
            simp
          · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            left
            rw [LookupRangeCheck.shortRangeCheck_configured_lookups_eq]
            simp
          · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            left
            rw [LookupRangeCheck.shortRangeCheck_configured_permutationColumns_eq]
            simp
        constructor
        · apply LookupRangeCheck.witnessShortCheck_keygenRegistered
          · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            left
            rw [LookupRangeCheck.shortRangeCheck_configured_gates_eq]
            simp
          · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            left
            rw [LookupRangeCheck.shortRangeCheck_configured_lookups_eq]
            simp
          · simp only [HashLayer.keygenRequirements, Configure.delta_pure,
              List.append_nil, List.mem_append]
            left
            rw [LookupRangeCheck.shortRangeCheck_configured_permutationColumns_eq]
            simp
        constructor
        · exact HashToPoint.witnessMessagePiece_keygenRegistered _ _ _
        constructor
        · exact HashToPoint.witnessMessagePiece_keygenRegistered _ _ _
        constructor
        · apply HashLayer.hashMessage_keygenRegistered
          intro column hcolumn
          simp only [FormalCircuit.Configured.inputPermutationColumns,
            FormalCircuit.keygenRequirements,
            ElaboratedCircuit.keygenRequirements,
            KeygenRequirements.inputPermutationColumns,
            HashToPoint.hashCircuit, FormalRegionCircuit.toFormal,
            ElaboratedRegionCircuit.keygenRequirements,
            HashToPoint.hashRegion] at hcolumn
          simp only [HashToPoint.witnessMessagePiece, Circuit.output,
            assignRegion, assignAdvice] at hcolumn
          rw [List.mem_map] at hcolumn
          obtain ⟨found, hfound, rfl⟩ := hcolumn
          have hfoundColumn : found.column =
              configInput.1.sinsemilla.witnessPieces.toAny := by
            rw [List.mem_iff_getElem] at hfound
            obtain ⟨j, hj, hvalue⟩ := hfound
            have hj' : j < 3 := by simpa using hj
            have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
            rcases hjcases with rfl | rfl | rfl <;>
              simp at hvalue <;> subst found <;> rfl
          rw [hfoundColumn]
          simp [HashLayer.keygenRequirements]
        · constructor
          · apply HashLayer.gate_keygenRegistered
            intro column hcolumn
            simp only [FormalRegionCircuit.Configured.inputPermutationColumns,
              FormalRegionCircuit.keygenRequirements,
              ElaboratedRegionCircuit.keygenRequirements,
              KeygenRequirements.inputPermutationColumns,
              Gate.circuit, Gate.elaborated,
              HashToPoint.hashMessage, FormalCircuit.output_call] at hcolumn
            rw [List.mem_map] at hcolumn
            obtain ⟨found, hfound, rfl⟩ := hcolumn
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hfound
            simp only [HashLayer.keygenRequirements, Configure.delta_pure,
              List.append_nil]
            rcases hfound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals simp [AssignedCell.of_cell, Cell.of_column,
              HashToPoint.witnessMessagePiece_output_column,
              LookupRangeCheck.witnessShortCheck_output_column,
              HashToPoint.Configured.permutationColumns_eq,
              LookupRangeCheck.shortRangeCheck_configured_permutationColumns_eq,
              KeygenRequirements.inputPermutationColumns]
          · trivial
      lookupSelectorAnchorRequirements cfg _ _ :=
        LookupRangeCheck.lookupSelectorAnchorRequirements cfg.2
      lookupSelectorsAnchoredBy_of_registered := by
        intro cfg _ hconfig input i anchor hanchor _
        simp only [HashLayer.synthesize, Circuit.operations_bind,
          Circuit.operations_pure, List.append_nil, circuit_norm]
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact HashToPoint.witnessMessagePiece_lookupSelectorsAnchoredBy
            cfg.1.sinsemilla _ i anchor
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact LookupRangeCheck.witnessShortCheck_lookupSelectorsAnchoredBy
            10 5 cfg.2 _ (i + 1) anchor hanchor
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact LookupRangeCheck.witnessShortCheck_lookupSelectorsAnchoredBy
            10 5 cfg.2 _ (i + 2) anchor hanchor
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact HashToPoint.witnessMessagePiece_lookupSelectorsAnchoredBy
            cfg.1.sinsemilla _ (i + 3) anchor
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact HashToPoint.witnessMessagePiece_lookupSelectorsAnchoredBy
            cfg.1.sinsemilla _ (i + 4) anchor
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ (by decide))
            |>.call_lookupSelectorsAnchoredBy cfg.1.sinsemilla hconfig.2.1 _
              (i + 5) anchor (by trivial)
        · apply Operations.LookupSelectorsAnchoredBy.region_cons
          · exact (Gate.circuit (l : Fp)).call_lookupSelectorsAnchoredBy
              cfg.1.gate hconfig.2.2 0 _ _ anchor (by trivial)
          · exact Operations.LookupSelectorsAnchoredBy.nil anchor
      lookupSelectorAssignmentsAgree_of_registered := by
        intro configInput counts hconfig input i program operations _hregistered
        simp only [operations, program, Configure.output_pure,
          HashLayer.synthesize, Circuit.operations_bind,
          Circuit.operations_pure, operations_assignRegion,
          keygen_norm, keygen_spine]
        exact (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
            HashLayer.synthesize._proof_1)
          |>.call_lookupSelectorAssignmentsAgree
            configInput.1.sinsemilla hconfig.2.1 _ _
      fixedWritesLawful := by
        intro cfg _ hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simp only [Configure.output_pure, HashLayer.synthesize,
            Circuit.operations_bind, Circuit.operations_pure,
            List.forall_append, circuit_norm]
          constructor
          · exact (HashToPoint.witnessMessagePiece_fixedWritesLawful
              cfg.1.sinsemilla (HashLayer.waWit l input.left) self [])
              |>.regionAssignmentsAgree
          constructor
          · exact (LookupRangeCheck.witnessShortCheck_fixedWritesLawful
              10 5 cfg.2 (HashLayer.wb1Wit input.left) (self + 1) [])
              |>.regionAssignmentsAgree
          constructor
          · exact (LookupRangeCheck.witnessShortCheck_fixedWritesLawful
              10 5 cfg.2 (HashLayer.wb2Wit input.right) (self + 2) [])
              |>.regionAssignmentsAgree
          constructor
          · exact (HashToPoint.witnessMessagePiece_fixedWritesLawful
              cfg.1.sinsemilla (HashLayer.wbWit input.left input.right)
                (self + 1 + 2) []) |>.regionAssignmentsAgree
          constructor
          · exact (HashToPoint.witnessMessagePiece_fixedWritesLawful
              cfg.1.sinsemilla (HashLayer.wcWit input.right)
                (self + 2 + 2) []) |>.regionAssignmentsAgree
          constructor
          · unfold HashToPoint.hashMessage
            exact (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
              (by decide)).call_fixedAssignmentsAgree
                cfg.1.sinsemilla hconfig.2.1 _ (self + 3 + 2)
          · exact (Gate.circuit (l : Fp)).call_fixedAssignmentsAgree
              cfg.1.gate hconfig.2.2 0 _ _
        · simp only [Configure.output_pure]
          rw [← HashLayer.synthesisSummary_eq G Q hQ l cfg.1 cfg.2 input self]
          exact HashLayer.synthesisSummary_tableRowExtent_eq cfg.1 cfg.2
      copyCellsAssigned := by
        intro configInput counts hconfig input i
        unfold HashLayer.synthesize
        simp only [Configure.output_pure, Circuit.operations_bind,
          Circuit.operations_pure, circuit_norm]
        apply Operations.CopyCellsAssignedFrom.append
        · exact HashToPoint.witnessMessagePiece_copyCellsAssignedFrom _ _ _ _
        · apply Operations.CopyCellsAssignedFrom.append
          · exact LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom _ _ _ _ _ _
          · apply Operations.CopyCellsAssignedFrom.append
            · exact LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom _ _ _ _ _ _
            · apply Operations.CopyCellsAssignedFrom.append
              · exact HashToPoint.witnessMessagePiece_copyCellsAssignedFrom _ _ _ _
              · apply Operations.CopyCellsAssignedFrom.append
                · exact HashToPoint.witnessMessagePiece_copyCellsAssignedFrom _ _ _ _
                · apply Operations.CopyCellsAssignedFrom.append
                  · apply (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
                      (by decide)).call_copyCellsAssignedFrom _ hconfig.2.1
                    intro cell hcell
                    rw [HashToPoint.hashCircuit_inputCells, List.mem_map] at hcell
                    rcases hcell with ⟨assigned, hassigned, rfl⟩
                    rw [List.mem_iff_getElem] at hassigned
                    obtain ⟨j, hj, hvalue⟩ := hassigned
                    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by
                      have : j < 3 := by simpa using hj
                      omega
                    rcases hjcases with rfl | rfl | rfl
                    · simp at hvalue
                      subst assigned
                      simp only [List.mem_append]
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inr
                      simpa using
                        HashToPoint.witnessMessagePiece_output_cell_assigned
                          configInput.1.sinsemilla (waWit l input.left) i
                    · simp at hvalue
                      subst assigned
                      simp only [List.mem_append]
                      apply Or.inl
                      apply Or.inr
                      simpa using
                        HashToPoint.witnessMessagePiece_output_cell_assigned
                          configInput.1.sinsemilla
                            (wbWit input.left input.right) (i + 1 + 2)
                    · simp at hvalue
                      subst assigned
                      simp only [List.mem_append]
                      apply Or.inr
                      simpa using
                        HashToPoint.witnessMessagePiece_output_cell_assigned
                          configInput.1.sinsemilla (wcWit input.right) (i + 2 + 2)
                  · simp only [Operations.copyCellsAssignedFrom_region_iff,
                      Operations.copyCellsAssignedFrom_nil_iff, and_true,
                      HashToPoint.witnessMessagePiece_regionCount,
                      LookupRangeCheck.witnessShortCheck_regionCount,
                      Nat.add_assoc, Nat.reduceAdd]
                    rw [HashToPoint.hashMessage_regionCount]
                    rw [HashToPoint.hashMessage_nextRegionIndex]
                    simp only [Nat.add_assoc, Nat.reduceAdd]
                    apply (Gate.circuit (l : Fp)).call_copyCellsAssignedFrom
                      configInput.1.gate hconfig.2.2 0 _ _
                    intro cell hcell
                    simp only [FormalRegionCircuit.Configured.inputCells,
                      FormalRegionCircuit.keygenRequirements,
                      ElaboratedRegionCircuit.keygenRequirements,
                      Gate.circuit, Gate.elaborated,
                      List.mem_cons, List.not_mem_nil, or_false] at hcell
                    rcases hcell with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                    all_goals simp only [List.mem_append]
                    · apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inr
                      exact HashToPoint.witnessMessagePiece_output_cell_assigned
                        configInput.1.sinsemilla (waWit l input.left) i
                    · apply Or.inl
                      apply Or.inl
                      apply Or.inr
                      exact HashToPoint.witnessMessagePiece_output_cell_assigned
                        configInput.1.sinsemilla (wbWit input.left input.right) (i + 3)
                    · apply Or.inl
                      apply Or.inr
                      exact HashToPoint.witnessMessagePiece_output_cell_assigned
                        configInput.1.sinsemilla (wcWit input.right) (i + 4)
                    · apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      simp [HashLayer.keygenRequirements]
                    · apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      simp [HashLayer.keygenRequirements]
                    · apply Or.inr
                      simpa only [Fin.getElem_fin] using
                        (HashToPoint.hashMessage_output_z1_cell_assigned
                          G merkleNs configInput.1.sinsemilla Q hQ
                            HashLayer.synthesize._proof_1
                            { pieces := #v[
                                (HashToPoint.witnessMessagePiece configInput.1.sinsemilla
                                  (waWit l input.left)).output i,
                                (HashToPoint.witnessMessagePiece configInput.1.sinsemilla
                                  (wbWit input.left input.right)).output (i + 3),
                                (HashToPoint.witnessMessagePiece configInput.1.sinsemilla
                                  (wcWit input.right)).output (i + 4)] }
                            (i + 5) ⟨0, by decide⟩ (by decide))
                    · apply Or.inr
                      simpa only [Fin.getElem_fin] using
                        (HashToPoint.hashMessage_output_z1_cell_assigned
                          G merkleNs configInput.1.sinsemilla Q hQ
                            HashLayer.synthesize._proof_1
                            { pieces := #v[
                                (HashToPoint.witnessMessagePiece configInput.1.sinsemilla
                                  (waWit l input.left)).output i,
                                (HashToPoint.witnessMessagePiece configInput.1.sinsemilla
                                  (wbWit input.left input.right)).output (i + 3),
                                (HashToPoint.witnessMessagePiece configInput.1.sinsemilla
                                  (wcWit input.right)).output (i + 4)] }
                            (i + 5) ⟨1, by decide⟩ (by decide))
                    · apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inr
                      exact LookupRangeCheck.witnessShortCheck_output_cell_assigned
                        10 5 configInput.2 (wb1Wit input.left) (i + 1)
                    · apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply Or.inr
                      exact LookupRangeCheck.witnessShortCheck_output_cell_assigned
                        10 5 configInput.2 (wb2Wit input.right) (i + 2)
      lookupActivationsWellFormed config input region := by
        unfold HashLayer.synthesize
        simp only [Circuit.operations_bind,
          Operations.LookupActivationsWellFormed,
          operations_assignRegion, Circuit.operations_pure, List.forall_append,
          List.forall_nil]
        constructor
        · keygen_registration [HashToPoint.witnessMessagePiece]
        constructor
        · keygen_registration [LookupRangeCheck.witnessShortCheck]
        constructor
        · keygen_registration [LookupRangeCheck.witnessShortCheck]
        constructor
        · keygen_registration [HashToPoint.witnessMessagePiece]
        constructor
        · keygen_registration [HashToPoint.witnessMessagePiece]
        constructor
        · simpa only [HashToPoint.hashMessage] using
            (HashToPoint.hashCircuit G merkleNs Q hQ HashLayer.synthesize._proof_1)
              |>.call_lookupActivationsWellFormed config.1.sinsemilla _ _
        · constructor
          · exact (Gate.circuit (l : Fp)).call_lookupActivationsWellFormed
              config.1.gate 0 _ _
          · trivial
      output := fun (cfg, _) _ i =>
        AssignedCell.of (i + 5)
          (Sinsemilla.Chain.prefixRows HashLayer.merkleNs HashLayer.merkleNs.length)
          cfg.sinsemilla.xA
      regionCount _ := 7
      output_eq := fun (cfg, lcfg) input i =>
        (HashLayer.synthesize_output G cfg lcfg Q hQ l input i).symm
      regionCount_eq := fun (cfg, lcfg) input i =>
        (hashLayer_regionCount G cfg lcfg Q hQ l input i).symm }

  EnvAssumptions := fun (cfg, lcfg) env =>
    Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla.generatorTable env.env ∧
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions _ := True

  Witness := fun _ => HashLayer.Encoding
  extract := fun (cfg, lcfg) _ i₀ env =>
    { a := eval env (AssignedCell.of i₀ 0 cfg.sinsemilla.witnessPieces : Var field Fp)
      b := eval env (AssignedCell.of (i₀ + 3) 0 cfg.sinsemilla.witnessPieces : Var field Fp)
      c := eval env (AssignedCell.of (i₀ + 4) 0 cfg.sinsemilla.witnessPieces : Var field Fp)
      b1 := eval env (AssignedCell.of (i₀ + 1) 0 lcfg.runningSum : Var field Fp)
      b2 := eval env (AssignedCell.of (i₀ + 2) 0 lcfg.runningSum : Var field Fp) }

  Spec input output wit := HashLayer.Spec G Q l input output wit

  ProverAssumptions input _ _ := HashLayer.ProverAssumptions G Q l input

  ProverSpec input output _ _ :=
    ∀ B, hashToPoint G.S Q
        (merkleChunks l (ZMod.val (show Fp from input.left))
          (ZMod.val (show Fp from input.right))) = some B →
      output = B.x

  soundness := by
    circuit_proof_start
    simp only [HashLayer.synthesize, HashToPoint.witnessMessagePiece,
      LookupRangeCheck.witnessShortCheck, HashToPoint.hashMessage,
      circuit_norm] at hc
    subcircuit_rw at hc
    simp only [shortC_spec_eq, shortC_assumptions_eq, shortC_envAssumptions_eq,
      gateC_spec_eq, gateC_assumptions_eq, gateC_envAssumptions_eq,
      HashToPoint.hashCircuit_spec_eq, HashToPoint.hashCircuit_assumptions_eq, HashToPoint.hashCircuit_envAssumptions_eq] at hc
    obtain ⟨hB1, hB2, hHash, hGate⟩ := hc
    obtain ⟨hEgen, hEtab, hEdist⟩ := _hE
    have hAshort : (5 : ℕ) ≤ 10 ∧ 2 ^ 10 * 2 ^ 10 < PALLAS_BASE_CARD := by
      constructor
      · norm_num
      · norm_num [PALLAS_BASE_CARD]
    -- the eval of a positional cell is the raw advice read
    have hcellEval : ∀ (j : RegionIndex) (r : ℕ) (col : Column .advice),
        (eval (⟨place, env⟩ : Placed Environment Fp)
          (AssignedCell.of j r col : Var field Fp) : Fp)
        = env.advice col ((place j + r : ℕ) : ℤ) := fun _ _ _ => by
      simp only [circuit_norm]
    -- the b_1/b_2 range bounds (the shortcheck outputs ARE the gate's b_1/b_2 cells)
    have hb1 := hB1 ⟨hEtab, hEdist⟩ hAshort
    have hb2 := hB2 ⟨hEtab, hEdist⟩ hAshort
    rw [show (LookupRangeCheck.shortRangeCheck 10 5).output cfg.2 0 () (i₀ + 1)
        = AssignedCell.of (i₀ + 1) 0 cfg.2.runningSum from rfl, hcellEval] at hb1
    rw [show (LookupRangeCheck.shortRangeCheck 10 5).output cfg.2 0 () (i₀ + 2)
        = AssignedCell.of (i₀ + 2) 0 cfg.2.runningSum from rfl, hcellEval] at hb2
    -- the hash spec: chunking + running sums + the z1 view + the hash-from-Q contract
    have hHashS := hHash hEgen trivial
    rw [ProvableStruct.Halo2.eval_cells_eq_eval, Sinsemilla.Chain.inputs_eval_literal] at hHashS
    rw [HashToPoint.hashCircuit_output_eval] at hHashS
    obtain ⟨chunks, hPC, hZs, hz1v, hContract⟩ := hHashS
    -- the gate spec on the landed cell values
    have hGateS := hGate trivial trivial
    simp only [HashToPoint.hashCircuit_output_z1s] at hGateS
    rw [gateInputs_eval_literal] at hGateS
    -- flatten every cell eval to raw advice reads
    simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
      Vector.getElem_ofFn] at hGateS hPC hb1 hb2
    -- land the running-sum extraction on the zsFam family and unpack the per-piece facts
    rw [show ((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
          HashLayer.synthesize._proof_1).extract
          cfg.1.sinsemilla
          { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
                         AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
                         AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          (i₀ + 3 + 2) { place := place, env := env }).zs
        = eval (⟨place, env⟩ : Placed Environment Fp)
            (Sinsemilla.Chain.zsCellsVal cfg.1.sinsemilla (i₀ + 3 + 2)
              HashLayer.merkleNs 0) from rfl,
      Sinsemilla.Chain.eval_zsCellsVal] at hZs
    rw [show HashLayer.merkleNs = 24 :: 1 :: 24 :: ([] : List ℕ) from rfl] at hZs
    obtain ⟨hzA, hzB, -⟩ := hZs
    simp only [Sinsemilla.Chain.zsFam_head] at hzA hzB
    have hzB' := (Sinsemilla.Chain.zsFam_tail_head
        (fun r => env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + r : ℕ) : ℤ)) 24 1 [24] 0).symm.trans hzB
    -- the piece chunking at the concrete widths (`merkleNs` unfolds reducibly)
    obtain ⟨msA, hmsA, hpAval, tailB, hchunksEq, hPCB⟩ := hPC
    obtain ⟨msB, hmsB, hpBval, tailC, htailC, hPCC⟩ := hPCB
    obtain ⟨msC, hmsC, hpCval, tailN, htailN, hnil⟩ := hPCC
    rw [show ProvableType.Halo2.eval (M := fields HashLayer.merkleNs.length) place env
        #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
           AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
           AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces]
      = #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ + 0 : ℕ) : ℤ),
           env.advice cfg.1.sinsemilla.witnessPieces
             ((place (i₀ + 1 + 2) + 0 : ℕ) : ℤ),
           env.advice cfg.1.sinsemilla.witnessPieces
             ((place (i₀ + 2 + 2) + 0 : ℕ) : ℤ)] from by
        with_unfolding_all rfl] at hpAval hpBval hpCval
    simp only [show ∀ (a b c : Fp), (#v[a, b, c] : Vector Fp 3)[0] = a from fun _ _ _ => rfl,
      show ∀ (a b c : Fp), (Vector.tail (#v[a, b, c] : Vector Fp 3))[0] = b
        from fun _ _ _ => rfl,
      show ∀ (a b c : Fp), (Vector.tail (Vector.tail (#v[a, b, c] : Vector Fp 3)))[0] = c
        from fun _ _ _ => rfl] at hpAval hpBval hpCval
    -- the z_1 values off the running-sum vectors, chunk-indexed through the append shape
    have hz1Aval := congrArg (fun v : Vector Fp 25 => v[1]'(by norm_num)) hzA
    have hz1Bval := congrArg (fun v : Vector Fp 2 => v[1]'(by norm_num)) hzB'
    simp only [Vector.getElem_ofFn] at hz1Aval hz1Bval
    -- normalize the row spellings across all facts
    simp only [show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 0 = 0 from rfl,
      show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 1 = 25 from rfl,
      Nat.add_zero, Nat.zero_add, show (24 + 1 + 1 : ℕ) = 26 from rfl]
      at hGateS hz1Aval hz1Bval hpAval hpBval hpCval hb1 hb2
    -- the chunk words through the append shape
    have hsumA : (∑ j ∈ Finset.range (24 + 1 - 1), chunks.getD (1 + j) 0 * 2 ^ (K * j))
        = ∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) := by
      refine Finset.sum_congr (by norm_num) fun j hj => ?_
      rw [hchunksEq, Sinsemilla.Chain.chunks_head_getD msA tailB (1 + j)
        (by simp at hj; omega), Nat.add_comm 1 j]
    have hdrop : chunks.drop (24 + 1) = tailB := by
      rw [hchunksEq]
      exact Sinsemilla.Chain.chunks_drop_append msA tailB
    have hsumB : (∑ j ∈ Finset.range (1 + 1 - 1),
          (chunks.drop (24 + 1)).getD (1 + j) 0 * 2 ^ (K * j))
        = msB 1 := by
      rw [show (1 + 1 - 1) = 1 from rfl, Finset.sum_range_one, hdrop, htailC,
        Sinsemilla.Chain.chunks_head_getD msB tailC 1 (by norm_num)]
      norm_num
    rw [hsumA] at hz1Aval
    rw [hsumB] at hz1Bval
    -- the gate equations
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hGateS
    dsimp only [] at hg1 hg2 hg3 hg4
    -- assemble the two node values
    have e10 : (twoPow10 : Fp) = (2 ^ 10 : Fp) := by norm_num [twoPow10]
    have e5 : (twoPow5 : Fp) = (2 ^ 5 : Fp) := by norm_num [twoPow5]
    have e240 : (twoPow240 : Fp) = (2 ^ 240 : Fp) := by norm_num [twoPow240]
    rw [show (24 + 1 : ℕ) = 25 from rfl] at hpAval
    rw [show (1 + 1 : ℕ) = 2 from rfl] at hpBval
    rw [show (24 + 1 : ℕ) = 25 from rfl] at hpCval
    rw [← e10] at hg1
    rw [← e10, ← e240] at hg2
    rw [← e5] at hg3
    rw [← e5] at hg4
    have hasm := assemble hmsA hmsB hmsC hl hb1 hb2
      hpAval hpBval hpCval
      (ZMod.natCast_zmod_val (env.advice cfg.2.runningSum
        ((place (i₀ + 1) : ℕ) : ℤ))).symm
      (ZMod.natCast_zmod_val (env.advice cfg.2.runningSum
        ((place (i₀ + 2) : ℕ) : ℤ))).symm
      hz1Aval hz1Bval hg1 hg2 hg3 hg4
    obtain ⟨lv, rv, hlv255, hrv255, hleftEnc, hrightEnc, hleftv, hrightv, hchunksM⟩ := hasm
    have hchunksIs : chunks = merkleChunks l lv rv := by
      rw [hchunksEq, htailC, htailN, hnil, hchunksM, List.append_nil]
    refine ⟨lv, rv, hlv255, hrv255, ?_, ?_, ?_, ?_, ?_⟩
    · exact hleftEnc
    · exact hrightEnc
    · show ((lv : ℕ) : Fp) = input_left
      rw [← h_input.1]
      exact hleftv
    · show ((rv : ℕ) : Fp) = input_right
      rw [← h_input.2]
      exact hrightv
    · intro B hB
      have hres := hContract B (by rw [hchunksIs]; exact hB)
      dsimp only [] at hres
      rw [← h_output]
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add] using hres.1

  completeness := by
    circuit_proof_start
    simp only [HashLayer.synthesize, HashToPoint.witnessMessagePiece,
      LookupRangeCheck.witnessShortCheck, HashToPoint.hashMessage,
      circuit_norm] at hwit ⊢
    obtain ⟨hWa, ⟨hWb1x, hWb1⟩, ⟨hWb2x, hWb2⟩, hWb, hWc, hWhash, hWgate⟩ := hwit
    -- the canonical node values, the node reads, and the honest piece values
    obtain ⟨B0, hB0⟩ := hPA
    have hlv255 : ZMod.val input_left < 2 ^ 255 :=
      lt_trans (ZMod.val_lt _) p_lt_two_pow_255
    have hrv255 : ZMod.val input_right < 2 ^ 255 :=
      lt_trans (ZMod.val_lt _) p_lt_two_pow_255
    have hreadL : Sinsemilla.HashPiece.readCell ⟨place, env⟩ input_var_left
        = input_left := by
      rw [← h_input.1]
      simp only [Sinsemilla.HashPiece.readCell, AssignedCell.eval]
    have hreadR : Sinsemilla.HashPiece.readCell ⟨place, env⟩ input_var_right
        = input_right := by
      rw [← h_input.2]
      simp only [Sinsemilla.HashPiece.readCell, AssignedCell.eval]
    have hwaV : env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ)
        = ((l + 2 ^ 10 * bitrange (ZMod.val input_left) 0 240 : ℕ) : Fp) := by
      rw [hWa]
      simp only [HashLayer.waWit, Witgen.WitgenIROver.eval_native_apply, hreadL]
      rfl
    have hwbV : env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 1 + 2) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_left) 240 10
            + 2 ^ 10 * bitrange (ZMod.val input_left) 250 5
            + 2 ^ 15 * bitrange (ZMod.val input_right) 0 5 : ℕ) : Fp) := by
      rw [hWb]
      simp only [HashLayer.wbWit, Witgen.WitgenIROver.eval_native_apply, hreadL, hreadR]
      rfl
    have hwcV : env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 2 + 2) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_right) 5 250 : ℕ) : Fp) := by
      rw [hWc]
      simp only [HashLayer.wcWit, Witgen.WitgenIROver.eval_native_apply, hreadR]
      rfl
    have hhp := honest_pieces hl hlv255 hrv255 hwaV hwbV hwcV
    obtain ⟨⟨hbA, hbB, hbC⟩, hhchunks⟩ := hhp
    -- the hash child's honest-prover precondition (used by the leaf AND the derived run)
    have hPAhash : (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
        HashLayer.synthesize._proof_1).ProverAssumptions
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ({ pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
            AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
            AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          : Var (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp))
        ((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
          HashLayer.synthesize._proof_1).extract
          cfg.1.sinsemilla
          { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          (i₀ + 3 + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)) env.hint := by
      rw [HashToPoint.hashCircuit_proverAssumptions_eq]
      rw [ProvableStruct.Halo2.eval_cells_eq_eval_prover, Sinsemilla.Chain.inputs_eval_literal,
        show ProvableType.Halo2.eval (M := fields HashLayer.merkleNs.length) place
          env.toEnvironment
          #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
             AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
             AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces]
        = #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ),
             env.advice cfg.1.sinsemilla.witnessPieces
               ((place (i₀ + 1 + 2) : ℕ) : ℤ),
             env.advice cfg.1.sinsemilla.witnessPieces
               ((place (i₀ + 2 + 2) : ℕ) : ℤ)]
        from by with_unfolding_all rfl]
      refine ⟨by decide, ⟨?_, ?_, ?_, trivial⟩, B0, ?_⟩
      · show ZMod.val (env.advice cfg.1.sinsemilla.witnessPieces
          ((place i₀ : ℕ) : ℤ)) < 2 ^ (K * 25)
        exact hbA
      · show ZMod.val (env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 1 + 2) : ℕ) : ℤ)) < 2 ^ (K * 2)
        exact hbB
      · show ZMod.val (env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 2 + 2) : ℕ) : ℤ)) < 2 ^ (K * 25)
        exact hbC
      · show Specs.Sinsemilla.hashToPoint G.S Q
          ((List.range 25).map (pieceWord (env.advice cfg.1.sinsemilla.witnessPieces
              ((place i₀ : ℕ) : ℤ)))
            ++ ((List.range 2).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 1 + 2) : ℕ) : ℤ)))
              ++ (List.range 25).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 2 + 2) : ℕ) : ℤ)))))
          = some B0
        rw [hhchunks]
        exact hB0
    -- the b_1/b_2 witnessed values, canonical
    have hb1V : env.advice cfg.2.runningSum ((place (i₀ + 1) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_left) 250 5 : ℕ) : Fp) := by
      rw [hWb1x]
      simp only [HashLayer.wb1Wit, Witgen.WitgenIROver.eval_native_apply, hreadL]
      rfl
    have hb2V : env.advice cfg.2.runningSum ((place (i₀ + 2) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_right) 0 5 : ℕ) : Fp) := by
      rw [hWb2x]
      simp only [HashLayer.wb2Wit, Witgen.WitgenIROver.eval_native_apply, hreadR]
      rfl
    -- the hash child's honest run: the verifier Spec (for the z_1 values) + the honest PS
    have hder := Halo2.SubcircuitRw.layouter_completeness_derived_placed
      (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
        HashLayer.synthesize._proof_1)
      cfg.1.sinsemilla (i₀ + 3 + 2) (⟨place, env⟩ : Placed ProverEnvironment Fp)
      { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
          AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
          AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
      hWhash _hE.1 trivial hPAhash
    obtain ⟨hSpecH, hPSH⟩ := hder
    rw [HashToPoint.hashCircuit_spec_eq] at hSpecH
    rw [HashToPoint.hashCircuit_proverSpec_eq] at hPSH
    rw [HashToPoint.hashCircuit_output_eval] at hSpecH
    obtain ⟨chunksH, hPCH, hZsH, -, -⟩ := hSpecH
    -- normalize the verifier-view spellings to the prover reads
    try simp only [Placed.toEnvironment_mk] at hPCH hZsH
    -- the running-sum families and the z_1 sums (the soundness-side extraction)
    rw [show ((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
          HashLayer.synthesize._proof_1).extract
          cfg.1.sinsemilla
          { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          (i₀ + 3 + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).zs
        = eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (Sinsemilla.Chain.zsCellsVal cfg.1.sinsemilla (i₀ + 3 + 2)
              HashLayer.merkleNs 0) from rfl,
      Sinsemilla.Chain.eval_zsCellsVal] at hZsH
    rw [show HashLayer.merkleNs = 24 :: 1 :: 24 :: ([] : List ℕ) from rfl] at hZsH
    obtain ⟨hzAH, hzBH, -⟩ := hZsH
    simp only [Sinsemilla.Chain.zsFam_head] at hzAH
    have hzBH' := (Sinsemilla.Chain.zsFam_tail_head
        (fun r => env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + r : ℕ) : ℤ)) 24 1 [24] 0).symm.trans hzBH
    obtain ⟨msA', hmsA', hpAval', tailB', hchunksEq', hPCB'⟩ := hPCH
    obtain ⟨msB', hmsB', hpBval', tailC', htailC', -⟩ := hPCB'
    have hpA2 : env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ)
        = ((∑ r ∈ Finset.range (24 + 1), msA' r * 2 ^ (K * r) : ℕ) : Fp) := by
      rw [← hpAval']
      with_unfolding_all rfl
    have hpB2 : env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 1 + 2) : ℕ) : ℤ)
        = ((∑ r ∈ Finset.range (1 + 1), msB' r * 2 ^ (K * r) : ℕ) : Fp) := by
      rw [← hpBval']
      with_unfolding_all rfl
    -- the z_1 cell values in `pieceZ` form (digit canonicity)
    have hz1AV := congrArg (fun v : Vector Fp 25 => v[1]'(by norm_num)) hzAH
    have hz1BV := congrArg (fun v : Vector Fp 2 => v[1]'(by norm_num)) hzBH'
    simp only [Vector.getElem_ofFn] at hz1AV hz1BV
    have hsumA' : (∑ j ∈ Finset.range (24 + 1 - 1), chunksH.getD (1 + j) 0 * 2 ^ (K * j))
        = ∑ j ∈ Finset.range 24, msA' (j + 1) * 2 ^ (K * j) := by
      refine Finset.sum_congr (by norm_num) fun j hj => ?_
      rw [hchunksEq', Sinsemilla.Chain.chunks_head_getD msA' tailB' (1 + j)
        (by simp at hj; omega), Nat.add_comm 1 j]
    have hsumB' : (∑ j ∈ Finset.range (1 + 1 - 1),
          (chunksH.drop (24 + 1)).getD (1 + j) 0 * 2 ^ (K * j))
        = msB' 1 := by
      rw [show (1 + 1 - 1) = 1 from rfl, Finset.sum_range_one,
        show chunksH.drop (24 + 1) = tailB' from by
          rw [hchunksEq']; exact Sinsemilla.Chain.chunks_drop_append msA' tailB',
        htailC', Sinsemilla.Chain.chunks_head_getD msB' tailC' 1 (by norm_num)]
      norm_num
    rw [hsumA'] at hz1AV
    rw [hsumB'] at hz1BV
    have hz1A_pieceZ : env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + (0 + 1) : ℕ) : ℤ)
        = pieceZ (env.advice cfg.1.sinsemilla.witnessPieces
            ((place i₀ : ℕ) : ℤ)) 1 := by
      rw [hz1AV]
      exact sum_z1_eq_pieceZ (by norm_num [show K = 10 from rfl]) hmsA' hpA2
    have hz1B_pieceZ : env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + (0 + (24 + 1) + 1) : ℕ) : ℤ)
        = pieceZ (env.advice cfg.1.sinsemilla.witnessPieces
            ((place (i₀ + 1 + 2) : ℕ) : ℤ)) 1 := by
      rw [hz1BV,
        show ((msB' 1 : ℕ) : Fp)
          = ((∑ j ∈ Finset.range 1, msB' (j + 1) * 2 ^ (K * j) : ℕ) : Fp) from by
          rw [Finset.sum_range_one]; norm_num]
      exact sum_z1_eq_pieceZ (by norm_num [show K = 10 from rfl]) hmsB' hpB2
    -- the gate spec on the honest values
    have hg := honest_gate hl hlv255 hrv255 hwaV hb1V hb2V hwbV hwcV
      hz1A_pieceZ hz1B_pieceZ (ZMod.natCast_zmod_val input_left)
      (ZMod.natCast_zmod_val input_right)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- b1 short check
      refine Halo2.SubcircuitRw.region_completeness_leaf_placed
        (LookupRangeCheck.shortRangeCheck 10 5) cfg.2 0 (i₀ + 1) (⟨place, env⟩ : Placed ProverEnvironment Fp) ()
        hWb1 ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact _hE.2.1
      · exact _hE.2.2
      · exact ⟨by norm_num, by norm_num [PALLAS_BASE_CARD]⟩
      · rw [shortC_proverAssumptions_eq]
        simp only [Placed.toEnvironment_mk]
        rw [show ((LookupRangeCheck.shortRangeCheck 10 5).extract
            cfg.2 0 () (i₀ + 1) (⟨place, env.toEnvironment⟩ : Placed Environment Fp) : Fp)
          = env.advice cfg.2.runningSum ((place (i₀ + 1) : ℕ) : ℤ) from by
            simp only [LookupRangeCheck.shortRangeCheck, circuit_norm], hWb1x]
        rw [show (Witgen.WitgenIROver.eval (HashLayer.wb1Wit input_var_left)
            { place := place, env := env })[0]
          = ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
              input_var_left).val 250 5 : ℕ) : Fp) from by
            simp only [HashLayer.wb1Wit, Witgen.WitgenIROver.eval_native_apply]
            rfl]
        show ZMod.val ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
            input_var_left).val 250 5 : ℕ) : Fp) < 2 ^ 5
        rw [ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _) (by
          norm_num [PALLAS_BASE_CARD]))]
        exact bitrange_lt _ _ _
    · -- b2 short check
      refine Halo2.SubcircuitRw.region_completeness_leaf_placed
        (LookupRangeCheck.shortRangeCheck 10 5) cfg.2 0 (i₀ + 2) (⟨place, env⟩ : Placed ProverEnvironment Fp) ()
        hWb2 ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact _hE.2.1
      · exact _hE.2.2
      · exact ⟨by norm_num, by norm_num [PALLAS_BASE_CARD]⟩
      · rw [shortC_proverAssumptions_eq]
        simp only [Placed.toEnvironment_mk]
        rw [show ((LookupRangeCheck.shortRangeCheck 10 5).extract
            cfg.2 0 () (i₀ + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp) : Fp)
          = env.advice cfg.2.runningSum ((place (i₀ + 2) : ℕ) : ℤ) from by
            simp only [LookupRangeCheck.shortRangeCheck, circuit_norm], hWb2x]
        rw [show (Witgen.WitgenIROver.eval (HashLayer.wb2Wit input_var_right)
            { place := place, env := env })[0]
          = ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
              input_var_right).val 0 5 : ℕ) : Fp) from by
            simp only [HashLayer.wb2Wit, Witgen.WitgenIROver.eval_native_apply]
            rfl]
        show ZMod.val ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
            input_var_right).val 0 5 : ℕ) : Fp) < 2 ^ 5
        rw [ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _) (by
          norm_num [PALLAS_BASE_CARD]))]
        exact bitrange_lt _ _ _
    · -- the hash
      refine Halo2.SubcircuitRw.layouter_completeness_leaf_placed
        (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ HashLayer.synthesize._proof_1)
          cfg.1.sinsemilla (i₀ + 3 + 2) (⟨place, env⟩ : Placed ProverEnvironment Fp) _ hWhash
        ⟨?_, trivial, ?_⟩
      · exact _hE.1
      · exact hPAhash
    · -- the decomposition gate
      refine Halo2.SubcircuitRw.region_completeness_leaf_placed
        (Gate.circuit (l : Fp)) cfg.1.gate 0 _ (⟨place, env⟩ : Placed ProverEnvironment Fp) _ hWgate ⟨trivial, trivial, ?_⟩
      rw [gateC_proverAssumptions_eq]
      simp only [HashToPoint.hashCircuit_output_z1s]
      rw [gateInputs_eval_literal_prover]
      simp only [AssignedCell.eval_of_advice,
        Vector.getElem_ofFn,
        show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 0 = 0 from rfl,
        show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 1 = 25 from rfl,
        Nat.add_zero, Nat.zero_add, show (25 + 1 : ℕ) = 26 from rfl]
      simp only [Nat.zero_add,
        show (24 + 1 + 1 : ℕ) = 26 from rfl,
        show (twoPow10 : Fp) = (2 ^ 10 : Fp) from by norm_num [twoPow10],
        show (twoPow5 : Fp) = (2 ^ 5 : Fp) from by norm_num [twoPow5],
        show (twoPow240 : Fp) = (2 ^ 240 : Fp) from by norm_num [twoPow240]] at hg
      rw [show Gate.GateSpec (↑l : Fp) = fun input => Gate.Spec input.aWhole input.bWhole
          input.cWhole input.leftNode input.rightNode input.z1A input.z1B input.b1
          input.b2 ↑l from rfl]
      dsimp only []
      rw [h_input.1, h_input.2]
      exact hg
    · -- the honest-prover contract
      intro B hB
      have hPSH' := hPSH B (by
        rw [show (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ({ pieces := #v[AssignedCell.of i₀ 0
                  cfg.1.sinsemilla.witnessPieces,
                AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
                AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
              : Var (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp)
              : Value (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp).pieces
          = #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 1 + 2) : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 2 + 2) : ℕ) : ℤ)] from by with_unfolding_all rfl,
          show Sinsemilla.Chain.honestChunks HashLayer.merkleNs
            #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 1 + 2) : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 2 + 2) : ℕ) : ℤ)]
          = (List.range 25).map (pieceWord (env.advice cfg.1.sinsemilla.witnessPieces
              ((place i₀ : ℕ) : ℤ)))
            ++ ((List.range 2).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 1 + 2) : ℕ) : ℤ)))
              ++ (List.range 25).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 2 + 2) : ℕ) : ℤ))))
          from by rfl, hhchunks]
        exact hB)
      rw [HashToPoint.hashCircuit_output_eval_prover] at hPSH'
      obtain ⟨hpx, -⟩ := hPSH'
      rw [← h_output]
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add] using hpx

@[synthesis_summary_norm]
theorem HashLayer.circuit_synthesisSummary_eq
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Config × LookupRangeCheck.Config 10)
    (input : Var HashLayer.Input Fp) (region : RegionIndex) :
    (HashLayer.circuit G Q hQ l hl).elaborated.synthesisSummary
      cfg input region = HashLayer.synthesisSummary cfg.1 cfg.2 := rfl

@[keygen_norm]
theorem HashLayer.circuit_lookupSelectorAnchorRequirements
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Config × LookupRangeCheck.Config 10)
    (input : Var HashLayer.Input Fp) (region : RegionIndex) :
    (HashLayer.circuit G Q hQ l hl).elaborated.lookupSelectorAnchorRequirements
      cfg input region =
        LookupRangeCheck.lookupSelectorAnchorRequirements cfg.2 := rfl

/-! ### Merkle path (`MerkleStep` / `MerkleRoot`, lifted verbatim) -/

def depth : ℕ := 32

/-- One Merkle step: the parent node from a child + its sibling (position bit unspecified). Donor
`Merkle.MerkleStep`. -/
def MerkleStep (G : Generators) (Q : Point Fp) (l : ℕ) (node node' : Fp) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : Fp) = node ∨ (rv : Fp) = node) ∧
    ∀ B, hashToPoint G.S Q (merkleChunks l lv rv) = some B → node' = B.x

/-- The Merkle root after `k` layers. Donor `Merkle.MerkleRoot`. -/
def MerkleRoot (G : Generators) (Q : Point Fp) : ℕ → Fp → ℕ → Fp → Prop
  | _, node, 0, root => root = node
  | l, node, k + 1, root =>
    ∃ mid, MerkleStep G Q l node mid ∧ MerkleRoot G Q (l + 1) mid k root

/-- One escape-free Merkle step. Unlike `MerkleStep`, this records that the
Sinsemilla hash is defined, so the parent is its actual `x`-coordinate. Together
with `MerkleBreakAt`, this is the Merkle-path breaks-as-data refinement requested
by zcash/ironwood#45. -/
def MerkleStepStrict (G : Generators) (Q : Point Fp) (l : ℕ)
    (node node' : Fp) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : Fp) = node ∨ (rv : Fp) = node) ∧
    ∃ B, hashToPoint G.S Q (merkleChunks l lv rv) = some B ∧ node' = B.x

/-- An escape-free Merkle root chain. This is the defined-hash branch of the
Merkle-path breaks-as-data refinement requested by zcash/ironwood#45. -/
def MerkleRootStrict (G : Generators) (Q : Point Fp) : ℕ → Fp → ℕ → Fp → Prop
  | _, node, 0, root => root = node
  | l, node, k + 1, root =>
    ∃ mid, MerkleStepStrict G Q l node mid ∧
      MerkleRootStrict G Q (l + 1) mid k root

/-- A valid Sinsemilla escape exhibited at layer `l + j` of a `k`-layer Merkle
window. The layer index is retained as part of the breaks-as-data witness requested
by zcash/ironwood#45. -/
def MerkleBreakAt (G : Generators) (Q : Point Fp) (l k : ℕ) : Prop :=
  ∃ j, j < k ∧ ∃ br : BreakData, ValidBreak G.S Q br ∧
    ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
      br.pre ++ br.chunk :: br.rest = merkleChunks (l + j) lv rv

private theorem merkleChunks_mem_lt {l lv rv m : ℕ}
    (h : m ∈ merkleChunks l lv rv) : m < 2 ^ K := by
  simp only [merkleChunks, List.mem_map, List.mem_range] at h
  obtain ⟨j, -, rfl⟩ := h
  exact Nat.mod_lt _ (Nat.two_pow_pos K)

theorem MerkleStepStrict.toMerkleStep (G : Generators) (Q : Point Fp)
    {l : ℕ} {node node' : Fp} (h : MerkleStepStrict G Q l node node') :
    MerkleStep G Q l node node' := by
  obtain ⟨lv, rv, hlv, hrv, hnode, B, hB, hout⟩ := h
  refine ⟨lv, rv, hlv, hrv, hnode, ?_⟩
  intro B' hB'
  rw [hB] at hB'
  cases hB'
  exact hout

/-- Refine a guarded Merkle step into its defined-hash case or an exhibited break. -/
theorem MerkleStep.strictOrBreak (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    {l : ℕ} {node node' : Fp} (h : MerkleStep G Q l node node') :
    MerkleStepStrict G Q l node node' ∨ MerkleBreakAt G Q l 1 := by
  obtain ⟨lv, rv, hlv, hrv, hnode, hcontract⟩ := h
  have hsob := breaksOfGuarded (S := G.S) (Q := Q)
    (chunks := merkleChunks l lv rv) (Or.inl hQ)
    (fun m hm => G.S_onCurve (merkleChunks_mem_lt hm)) hcontract
  cases hB : hashToPointB G.S Q (merkleChunks l lv rv) with
  | inl B =>
    simp only [SpecOrBreak, hB] at hsob
    exact Or.inl ⟨lv, rv, hlv, hrv, hnode, B,
      Specs.Sinsemilla.hashToPointB_inl hB, hsob⟩
  | inr br =>
    simp only [SpecOrBreak, hB] at hsob
    have hsplit := (Specs.Sinsemilla.hashToPointB_inr hB).1
    exact Or.inr ⟨0, by omega, br, hsob, lv, rv, hlv, hrv, by
      rw [Nat.add_zero]
      exact hsplit.symm⟩

theorem MerkleRootStrict.toMerkleRoot (G : Generators) (Q : Point Fp)
    {l : ℕ} {node : Fp} {k : ℕ} {root : Fp}
    (h : MerkleRootStrict G Q l node k root) : MerkleRoot G Q l node k root := by
  induction k generalizing l node with
  | zero => exact h
  | succ k ih =>
    obtain ⟨mid, hstep, hrest⟩ := h
    exact ⟨mid, hstep.toMerkleStep G Q, ih hrest⟩

/-- Chain two escape-free `MerkleRootStrict` segments. -/
theorem MerkleRootStrict.trans (G : Generators) (Q : Point Fp) {l a m r : _}
    {k k' : ℕ} (h1 : MerkleRootStrict G Q l a k m)
    (h2 : MerkleRootStrict G Q (l + k) m k' r) :
    MerkleRootStrict G Q l a (k + k') r := by
  induction k generalizing l a with
  | zero =>
    simp only [MerkleRootStrict] at h1
    subst h1
    simpa using h2
  | succ n ih =>
    obtain ⟨mid, hstep, hrest⟩ := h1
    rw [show n + 1 + k' = (n + k') + 1 from by omega, MerkleRootStrict]
    exact ⟨mid, hstep,
      ih hrest (by rwa [show l + 1 + n = l + (n + 1) from by omega])⟩

/-- Shift a break in a later window back into the combined window. -/
theorem MerkleBreakAt.shift (G : Generators) (Q : Point Fp) {l k k' : ℕ}
    (h : MerkleBreakAt G Q (l + k) k') : MerkleBreakAt G Q l (k + k') := by
  obtain ⟨j, hj, br, hbr, lv, rv, hlv, hrv, hmsg⟩ := h
  refine ⟨k + j, by omega, br, hbr, lv, rv, hlv, hrv, ?_⟩
  rw [show l + (k + j) = l + k + j from by omega]
  exact hmsg

/-- Enlarge the layer window containing an exhibited break. -/
theorem MerkleBreakAt.mono (G : Generators) (Q : Point Fp) {l k k' : ℕ}
    (hkk : k ≤ k') (h : MerkleBreakAt G Q l k) : MerkleBreakAt G Q l k' := by
  obtain ⟨j, hj, br, hbr, lv, rv, hlv, hrv, hmsg⟩ := h
  exact ⟨j, lt_of_lt_of_le hj hkk, br, hbr, lv, rv, hlv, hrv, hmsg⟩

/-- Chain two `MerkleRoot` segments. -/
theorem MerkleRoot.trans (G : Generators) (Q : Point Fp) {l a m r : _} {k k' : ℕ}
    (h1 : MerkleRoot G Q l a k m) (h2 : MerkleRoot G Q (l + k) m k' r) :
    MerkleRoot G Q l a (k + k') r := by
  induction k generalizing l a with
  | zero =>
    simp only [MerkleRoot] at h1
    subst h1
    simpa using h2
  | succ n ih =>
    obtain ⟨mid, hstep, hrest⟩ := h1
    rw [show n + 1 + k' = (n + k') + 1 from by omega, MerkleRoot]
    exact ⟨mid, hstep,
      ih hrest (by rwa [show l + 1 + n = l + (n + 1) from by omega])⟩

/-- Forward induction: a chain of `MerkleStep`s assembles into a `MerkleRoot`. Donor
`Merkle.merkleRoot_of_steps`. -/
theorem merkleRoot_of_steps (G : Generators) (Q : Point Fp) (f : ℕ → Fp) (l : ℕ) :
    ∀ k, (∀ i, i < k → MerkleStep G Q (l + i) (f i) (f (i + 1))) →
      MerkleRoot G Q l (f 0) k (f k) := by
  intro k
  induction k generalizing l f with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    refine ⟨f 1, ?_, ?_⟩
    · have h0 := h 0 (Nat.succ_pos k)
      simpa using h0
    · have hres := ih (l := l + 1) (f := fun i => f (i + 1)) (fun i hi => by
        have hi' := h (i + 1) (by omega)
        have : l + 1 + i = l + (i + 1) := by omega
        rw [this]; exact hi')
      simpa using hres

/-- Hash-layer extraction depends only on the assigned witness cells, not on
the input-cell spelling used by its caller. -/
theorem HashLayer.circuit_extract_input_independent (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Config) (lcfg : LookupRangeCheck.Config 10)
    (input input' : Var HashLayer.Input Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (HashLayer.circuit G Q hQ l hl).extract (cfg, lcfg) input i env =
      (HashLayer.circuit G Q hQ l hl).extract (cfg, lcfg) input' i env := by
  unfold FormalCircuit.extract HashLayer.circuit
  rfl
/-- A hash-layer output stays in the hash chip's `xA` column. -/
@[keygen_norm, keygen_output_norm]
theorem HashLayer.circuit_output_column (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Var HashLayer.Input Fp) (i : RegionIndex) :
    ((HashLayer.circuit G Q hQ l hl).output (cfg, lcfg) input i).cell.column =
      cfg.sinsemilla.xA := rfl

@[keygen_output_norm]
theorem HashLayer.circuit_output_cell_eq (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Var HashLayer.Input Fp) (i : RegionIndex) :
    ((HashLayer.circuit G Q hQ l hl).output (cfg, lcfg) input i).cell =
      (AssignedCell.of (i + 5) (Sinsemilla.Chain.prefixRows
        HashLayer.merkleNs HashLayer.merkleNs.length) cfg.sinsemilla.xA :
          AssignedCell Fp).cell := rfl

/-- The hash-layer output is the hash child's assigned x-coordinate cell. -/
theorem HashLayer.circuit_call_output_cell_assigned
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Var HashLayer.Input Fp) (self : RegionIndex) :
    ((HashLayer.circuit G Q hQ l hl).output (cfg, lcfg) input self).cell ∈
      Operations.assignedCellsFrom
        (((HashLayer.circuit G Q hQ l hl).call (cfg, lcfg) input).operations self) self := by
  rw [HashLayer.circuit_output_cell_eq]
  rw [FormalCircuit.call_operations]
  simp only [HashLayer.circuit]
  unfold HashLayer.synthesize
  simp only [Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
  apply Operations.mem_assignedCellsFrom_append_right
  apply Operations.mem_assignedCellsFrom_append_right
  apply Operations.mem_assignedCellsFrom_append_right
  apply Operations.mem_assignedCellsFrom_append_right
  apply Operations.mem_assignedCellsFrom_append_right
  apply Operations.mem_assignedCellsFrom_append_left
  have houtput := HashToPoint.hashMessage_output_point_cells_assigned
    G HashLayer.merkleNs cfg.sinsemilla Q hQ (by decide)
      { pieces := #v[
        (HashToPoint.witnessMessagePiece cfg.sinsemilla
          (HashLayer.waWit l input.left)).output self,
        (HashToPoint.witnessMessagePiece cfg.sinsemilla
          (HashLayer.wbWit input.left input.right)).output (self + 3),
        (HashToPoint.witnessMessagePiece cfg.sinsemilla
          (HashLayer.wcWit input.right)).output (self + 4)] }
      (self + 5)
  have hx := houtput.1
  rw [HashToPoint.hashMessage_output_point_x] at hx
  simpa only [AssignedCell.of_cell, Nat.zero_add, circuit_norm] using hx

/-- The column carrying a hash-layer output is included in its equality-column summary. -/
@[keygen_norm]
theorem HashLayer.Configured.outputColumn_mem_permutationColumns
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10)
    {cfg : Config × LookupRangeCheck.Config 10}
    (configured : (HashLayer.circuit G Q hQ l hl).Configured cfg) :
    cfg.1.sinsemilla.xA.toAny ∈ configured.permutationColumns := by
  rcases configured with ⟨configInput, counts, lawful, output_eq⟩
  simp only [HashLayer.circuit, Configure.output_pure] at output_eq
  subst cfg
  have hxA : configInput.1.sinsemilla.xA.toAny ∈
      lawful.2.1.permutationColumns := by
    rw [HashToPoint.Configured.permutationColumns_eq G HashLayer.merkleNs Q]
    simp
  simp only [FormalCircuit.Configured.permutationColumns, List.mem_append] at hxA
  simp only [FormalCircuit.Configured.permutationColumns,
    HashLayer.circuit, FormalCircuit.keygenRequirements,
    ElaboratedCircuit.keygenRequirements, HashLayer.keygenRequirements,
    Configure.delta_pure, List.append_nil, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hxA))

/-- A chain of guarded Merkle steps is either wholly strict or exhibits the first
window in which a valid Sinsemilla break occurs. -/
theorem merkleRootStrict_or_break_of_steps (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (f : ℕ → Fp) (l : ℕ) :
    ∀ k, (∀ i, i < k → MerkleStep G Q (l + i) (f i) (f (i + 1))) →
      MerkleRootStrict G Q l (f 0) k (f k) ∨ MerkleBreakAt G Q l k := by
  intro k
  induction k generalizing l f with
  | zero =>
    intro _
    exact Or.inl rfl
  | succ k ih =>
    intro h
    have hfirst := MerkleStep.strictOrBreak G Q hQ (h 0 (Nat.succ_pos k))
    rcases hfirst with hfirst | hbreak
    · have hrest := ih (l := l + 1) (f := fun i => f (i + 1)) (fun i hi => by
        have hi' := h (i + 1) (by omega)
        rw [show l + 1 + i = l + (i + 1) from by omega]
        exact hi')
      rcases hrest with hrest | hbreak
      · exact Or.inl ⟨f 1, by simpa using hfirst, by simpa using hrest⟩
      · exact Or.inr (by
          simpa [Nat.add_comm] using
            MerkleBreakAt.shift G Q (l := l) (k := 1) hbreak)
    · exact Or.inr (MerkleBreakAt.mono G Q (by omega) hbreak)

@[keygen_norm]
theorem HashLayer.Configured.inputCells_eq
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10)
    {cfg : Config × LookupRangeCheck.Config 10}
    (configured : (HashLayer.circuit G Q hQ l hl).Configured cfg)
    (input : Var HashLayer.Input Fp) :
    configured.inputCells input = [input.left.cell, input.right.cell] := by
  rcases configured with ⟨configInput, counts, lawful, output_eq⟩
  rfl

/-! ### `Layer` (CondSwap + HashLayer)

One Merkle path layer (`MerklePath::calculate_root`'s loop body): conditionally swap
`(node, sibling)` by the position bit — the sibling and the bit are prover witnesses
(Rust `Value`s) — then hash the swapped pair. Both children are proven
(`CondSwap.swap`, `HashLayer.circuit`). -/

/-- The swapped `(left, right)` pair a layer hashes, selected by the position bit. Donor
`Merkle.Layer.proverChunks` (value-level). -/
def proverChunks (l : ℕ) (node sibling : Fp) (posBit : Bool) : List ℕ :=
  merkleChunks l
    (ZMod.val (if posBit then sibling else node))
    (ZMod.val (if posBit then node else sibling))

namespace Layer

structure Input (F : Type) where
  -- The running node cell (the sibling and position bit are witnesses).
  node : F
deriving ProvableStruct

/-- Everything a Merkle layer must export for a path consumer.  `encoding` is
the hash-layer's decomposition witness; `side` is the Boolean interpretation of
the cond-swap flag. -/
structure Witness where
  sibling : Fp
  swap : Fp
  encoding : HashLayer.Encoding
deriving Inhabited

/-- Compatibility projection used by the existing honest-path machinery. -/
def Witness.pair (w : Witness) : Fp × Fp := (w.sibling, w.swap)

end Layer

/-- A Merkle step whose two 255-bit message representatives are fixed by the
exported decomposition cells. -/
def ExactMerkleStep (G : Generators) (Q : Point Fp) (l : ℕ)
    (node node' : Fp) (w : Layer.Witness) : Prop :=
  HashLayer.leftEncoding w.encoding < 2 ^ 255 ∧
  HashLayer.rightEncoding w.encoding < 2 ^ 255 ∧
  ((if w.swap = 1 then (HashLayer.rightEncoding w.encoding : Fp)
    else (HashLayer.leftEncoding w.encoding : Fp)) = node) ∧
  ∀ B, hashToPoint G.S Q
    (merkleChunks l (HashLayer.leftEncoding w.encoding) (HashLayer.rightEncoding w.encoding))
      = some B → node' = B.x

/-- A root chain whose children are the exact encodings exported from every
layer.  The `nodes` witness is intentionally first-order so consumers can map
it directly to a fixed-depth ledger path. -/
def ExactMerklePath (G : Generators) (Q : Point Fp) (l node : ℕ) (start root : Fp)
    (wit : ℕ → Layer.Witness) : Prop :=
  ∃ nodes : ℕ → Fp, nodes 0 = start ∧ nodes node = root ∧
    ∀ i, i < node → ExactMerkleStep G Q (l + i) (nodes i) (nodes (i + 1)) (wit i)

/-- An encoding-only exact Merkle chain.  This is the public bridge surface:
callers retain the literal 255-bit left/right representatives and the selected
side, without having to expose circuit-local decomposition witnesses. -/
def ExactMerklePathData (G : Generators) (Q : Point Fp) (l d : ℕ) (start root : Fp)
    (left right : ℕ → ℕ) (side : ℕ → Bool) : Prop :=
  ∃ nodes : ℕ → Fp, nodes 0 = start ∧ nodes d = root ∧
    ∀ i, i < d →
      left i < 2 ^ 255 ∧
      right i < 2 ^ 255 ∧
      (if side i then (right i : Fp) else (left i : Fp)) = nodes i ∧
      ∀ B, hashToPoint G.S Q (merkleChunks (l + i) (left i) (right i)) = some B →
        nodes (i + 1) = B.x

theorem ExactMerklePath.toData (G : Generators) (Q : Point Fp) (l d : ℕ)
    (start root : Fp) (wit : ℕ → Layer.Witness)
    (h : ExactMerklePath G Q l d start root wit) :
    ExactMerklePathData G Q l d start root
      (fun i => HashLayer.leftEncoding (wit i).encoding)
      (fun i => HashLayer.rightEncoding (wit i).encoding)
      (fun i => (wit i).swap = 1) := by
  rcases h with ⟨nodes, h0, hd, hs⟩
  refine ⟨nodes, h0, hd, ?_⟩
  intro i hi
  simpa only [ExactMerkleStep, decide_eq_true_eq] using hs i hi

/-- Concatenate two exact chains.  The resulting encoding functions are selected
by the public depth boundary, so this is convenient for the Action circuit's two
16-layer folds. -/
theorem ExactMerklePathData.trans (G : Generators) (Q : Point Fp)
    (l d e : ℕ) (start mid root : Fp)
    (left₁ right₁ : ℕ → ℕ) (side₁ : ℕ → Bool)
    (left₂ right₂ : ℕ → ℕ) (side₂ : ℕ → Bool)
    (h₁ : ExactMerklePathData G Q l d start mid left₁ right₁ side₁)
    (h₂ : ExactMerklePathData G Q (l + d) e mid root left₂ right₂ side₂) :
    ExactMerklePathData G Q l (d + e) start root
      (fun i => if i < d then left₁ i else left₂ (i - d))
      (fun i => if i < d then right₁ i else right₂ (i - d))
      (fun i => if i < d then side₁ i else side₂ (i - d)) := by
  rcases h₁ with ⟨nodes₁, h10, h1d, hs₁⟩
  rcases h₂ with ⟨nodes₂, h20, h2e, hs₂⟩
  refine ⟨fun i => if i < d then nodes₁ i else nodes₂ (i - d), ?_, ?_, ?_⟩
  · by_cases hd : d = 0
    · subst d
      calc
        nodes₂ (0 - 0) = nodes₂ 0 := by rfl
        _ = mid := h20
        _ = nodes₁ 0 := h1d.symm
        _ = start := h10
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      simpa [hdpos] using h10
  · simp [h2e]
  intro i hi
  by_cases hid : i < d
  · rcases hs₁ i hid with ⟨hleft, hright, hnode, hhash⟩
    refine ⟨by simpa [hid] using hleft, by simpa [hid] using hright,
      by simpa [hid] using hnode, ?_⟩
    intro B hB
    by_cases hnext : i + 1 < d
    · simpa [hid, hnext] using hhash B (by simpa [hid] using hB)
    · have hieq : i + 1 = d := by omega
      have hh := hhash B (by simpa [hid] using hB)
      rw [hieq, h1d] at hh
      simpa [hid, hnext, hieq, h20] using hh
  · have hie : i - d < e := by omega
    have hle : d ≤ i := Nat.le_of_not_gt hid
    rcases hs₂ (i - d) hie with ⟨hleft, hright, hnode, hhash⟩
    rw [show l + d + (i - d) = l + i from by omega] at hhash
    have hnext : ¬ i + 1 < d := by omega
    refine ⟨by simpa [hid] using hleft, by simpa [hid] using hright, ?_, ?_⟩
    · by_cases hieq : i = d
      · subst i
        simpa [hid, h1d, h20] using hnode
      · simpa [hid] using hnode
    · intro B hB
      have hh := hhash B (by simpa [hid] using hB)
      have hsub : i - d + 1 = i + 1 - d := by omega
      simpa [hid, hnext, hsub] using hh

/-- Replace the exported encoding functions when they agree over the path's
actual depth. -/
theorem ExactMerklePathData.congr (G : Generators) (Q : Point Fp) (l d : ℕ)
    (start root : Fp) (left right : ℕ → ℕ) (side : ℕ → Bool)
    (left' right' : ℕ → ℕ) (side' : ℕ → Bool)
    (h : ExactMerklePathData G Q l d start root left right side)
    (hleft : ∀ i, i < d → left i = left' i)
    (hright : ∀ i, i < d → right i = right' i)
    (hside : ∀ i, i < d → side i = side' i) :
    ExactMerklePathData G Q l d start root left' right' side' := by
  rcases h with ⟨nodes, h0, hd, hs⟩
  refine ⟨nodes, h0, hd, ?_⟩
  intro i hi
  rw [← hleft i hi, ← hright i hi, ← hside i hi]
  exact hs i hi

/-- Exact per-layer encodings retain the original guarded root contract and
therefore determine either an escape-free chain or an exhibited Sinsemilla break. -/
theorem ExactMerklePathData.merkleRoot_and_strictOrBreak
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l d : ℕ) (start root : Fp) (left right : ℕ → ℕ)
    (side : ℕ → Bool)
    (h : ExactMerklePathData G Q l d start root left right side) :
    MerkleRoot G Q l start d root ∧
      (MerkleRootStrict G Q l start d root ∨ MerkleBreakAt G Q l d) := by
  rcases h with ⟨nodes, hstart, hroot, hsteps⟩
  have hstep : ∀ i, i < d → MerkleStep G Q (l + i) (nodes i) (nodes (i + 1)) := by
    intro i hi
    obtain ⟨hleft, hright, hnode, hhash⟩ := hsteps i hi
    refine ⟨left i, right i, hleft, hright, ?_, hhash⟩
    by_cases hs : side i
    · exact Or.inr (by simpa [hs] using hnode)
    · exact Or.inl (by simpa [hs] using hnode)
  have hguarded := merkleRoot_of_steps G Q nodes l d hstep
  have hrefined := merkleRootStrict_or_break_of_steps G Q hQ nodes l d hstep
  simpa only [hstart, hroot] using And.intro hguarded hrefined

derive_contract_bridges HashLayer.circuit (G : Generators) (Q : Point Fp)
  (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10) := HashLayer.circuit G Q hQ l hl

/-- A Merkle hash layer requests four deferred constant cells: two short-range
inverses, the public Sinsemilla initial x-coordinate, and the layer index. -/
@[synthesis_summary_norm]
theorem HashLayer.circuit_synthesisSummary_constantSiteCount
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10)
    (config : Config × LookupRangeCheck.Config 10)
    (input : Var HashLayer.Input Fp) (region : RegionIndex) :
    ((HashLayer.circuit G Q hQ l hl).elaborated.synthesisSummary
      config input region).constantSiteCount = 4 := by
  rw [ElaboratedCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [HashLayer.circuit, HashLayer.synthesize,
    Circuit.operations_bind, Circuit.operations_pure,
    FloorPlanner.synthesisSummary_append,
    FloorPlanner.SynthesisSummary.combine_constantSiteCount,
    operations_assignRegion,
    FloorPlanner.synthesisSummary_region_cons_constantSiteCount,
    FloorPlanner.synthesisSummary_nil_constantSiteCount, Nat.add_zero]
  repeat' first
    | rw [HashToPoint.witnessMessagePiece_synthesisSummary_constantSiteCount]
    | rw [LookupRangeCheck.witnessShortCheck_synthesisSummary_constantSiteCount]
    | rw [HashToPoint.hashMessage_synthesisSummary_constantSiteCount]
  rw [FormalRegionCircuit.call_synthesisSummary,
    Gate.circuit_synthesisSummary_constantSiteCount]

/-- Assemble a hash-layer capability from its three direct child capabilities. -/
def HashLayer.configurationCertificate (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    {cfg : Config} {lcfg : LookupRangeCheck.Config 10}
    {context : KeygenContext Fp}
    (range : (LookupRangeCheck.shortRangeCheck 10 5).ConfigurationCertificate
      lcfg context)
    (hash : (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
      (by decide)).ConfigurationCertificate cfg.sinsemilla context)
    (gate : (Gate.circuit (l : Fp)).ConfigurationCertificate cfg.gate context)
    (hwitnessPieces : cfg.sinsemilla.witnessPieces.toAny ∈ context.permutationColumns) :
    (HashLayer.circuit G Q hQ l hl).ConfigurationCertificate (cfg, lcfg) context := by
  let lawful : (HashLayer.keygenRequirements G Q hQ l).configLawful (cfg, lcfg) :=
    ⟨range.configured, hash.configured, gate.configured⟩
  apply ((HashLayer.circuit G Q hQ l hl).configureCertificate
    (cfg, lcfg) {} lawful).mono
  · intro required hrequired
    simp only [HashLayer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, HashLayer.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with (hrequired | hrequired) | hrequired
    · exact range.gates_of_configured required hrequired
    · exact hash.gates_of_configured required hrequired
    · exact gate.gates_of_configured required hrequired
  · intro required hrequired
    simp only [HashLayer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, HashLayer.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with (hrequired | hrequired) | hrequired
    · exact range.lookups_of_configured required hrequired
    · exact hash.lookups_of_configured required hrequired
    · exact gate.lookups_of_configured required hrequired
  · intro required hrequired
    simp only [HashLayer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, HashLayer.keygenRequirements,
      Configure.fixedColumns_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with (hrequired | hrequired) | hrequired
    · exact range.fixedColumns_of_configured required hrequired
    · exact hash.fixedColumns_of_configured required hrequired
    · exact gate.fixedColumns_of_configured required hrequired
  · intro required hrequired
    simp only [HashLayer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, HashLayer.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hrequired
    rcases hrequired with ((hrequired | hrequired) | hrequired) | hrequired
    · exact range.permutationColumns_of_configured required hrequired
    · exact hash.permutationColumns_of_configured required hrequired
    · exact gate.permutationColumns_of_configured required hrequired
    · subst required
      exact hwitnessPieces

/-- The region count of the layer: the swap region + the hash layer's 7. -/
private theorem layer_regionCount (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (ccfg : CondSwap.Config) (cfg : Config)
    (lcfg : LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let pair ← assignRegion "swap"
          ((CondSwap.swap wsib wswap).call ccfg 0 { a := input.node })
        (HashLayer.circuit G Q hQ l hl).call (cfg, lcfg)
          { left := pair.aSwapped, right := pair.bSwapped }).operations i) = 8 := by
  simp only [Circuit.operations_bind, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount]
  rw [show ∀ (j : RegionIndex) (inp : Var HashLayer.Input Fp),
      Operations.regionCount
        (((HashLayer.circuit G Q hQ l hl).call (cfg, lcfg) inp).operations j) = 7
    from fun j inp => by
      rw [FormalCircuit.call_regionCount]
      rfl]

private theorem layer_output (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (ccfg : CondSwap.Config) (cfg : Config)
    (lcfg : LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i : RegionIndex) :
    ((do
      let pair ← assignRegion "swap"
        ((CondSwap.swap wsib wswap).call ccfg 0 { a := input.node })
      (HashLayer.circuit G Q hQ l hl).call (cfg, lcfg)
        { left := pair.aSwapped, right := pair.bSwapped }) :
      Circuit Fp (Var field Fp)).output i =
        AssignedCell.of (i + 6)
          (Sinsemilla.Chain.prefixRows HashLayer.merkleNs HashLayer.merkleNs.length)
          cfg.sinsemilla.xA := by
  simp only [Circuit.output_bind, output_assignRegion,
    nextRegionIndex_assignRegion, FormalCircuit.output_call',
    HashLayer.circuit_output, Nat.add_assoc, Nat.reduceAdd]

@[keygen_norm]
def Layer.keygenRequirements (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool) :
    KeygenRequirements Fp
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      (Var Layer.Input Fp) where
  configLawful cfg :=
    (CondSwap.swap wsib wswap).Configured cfg.1 ×
      (HashLayer.circuit G Q hQ l hl).Configured (cfg.2.1, cfg.2.2)
  gates _ configured := configured.1.gates ++ configured.2.gates
  lookups _ configured := configured.1.lookups ++ configured.2.lookups
  fixedColumns _ configured :=
    configured.1.fixedColumns ++ configured.2.fixedColumns
  permutationColumns _ configured :=
    configured.1.permutationColumns ++ configured.2.permutationColumns
  inputCells _ _ input := [input.node.cell]

/-- Reduced footprint of one conditional-swap and hash layer. -/
def Layer.synthesisSummary (ccfg : CondSwap.Config) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) : FloorPlanner.SynthesisSummary :=
  (FloorPlanner.SynthesisSummary.ofRegion
      (FloorPlanner.RegionSynthesisSummary.ofColumns
        [.selector ccfg.qSwap.index,
          .column .advice ccfg.a.index,
          .column .advice ccfg.b.index,
          .column .advice ccfg.swap.index,
          .column .advice ccfg.aSwapped.index,
          .column .advice ccfg.bSwapped.index]
        1 0 [(ccfg.qSwap.index, 0)])).combine
    (HashLayer.synthesisSummary cfg lookupCfg)

@[synthesis_summary_norm]
theorem Layer.synthesisSummary_lookupActivationCount
    (ccfg : CondSwap.Config) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) :
    (Layer.synthesisSummary ccfg cfg lookupCfg).lookupActivationCount = 56 := by
  simp only [Layer.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem Layer.synthesisSummary_tableRowExtent_eq
    (ccfg : CondSwap.Config) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) :
    (Layer.synthesisSummary ccfg cfg lookupCfg).tableRowExtent = 0 := by
  simp only [Layer.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem Layer.synthesisSummary_instanceRowExtent_eq
    (ccfg : CondSwap.Config) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) :
    (Layer.synthesisSummary ccfg cfg lookupCfg).instanceRowExtent = 0 := by
  simp only [Layer.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem Layer.synthesisSummary_physicalShapes_eq
    (ccfg : CondSwap.Config) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) :
    (Layer.synthesisSummary ccfg cfg lookupCfg).physicalRegionShapes =
      (FloorPlanner.SynthesisSummary.ofRegion
          (FloorPlanner.RegionSynthesisSummary.ofColumns
            [.selector ccfg.qSwap.index,
              .column .advice ccfg.a.index,
              .column .advice ccfg.b.index,
              .column .advice ccfg.swap.index,
              .column .advice ccfg.aSwapped.index,
              .column .advice ccfg.bSwapped.index]
            1 0) |>.physicalRegionShapes) ++
      (HashLayer.synthesisSummary cfg lookupCfg).physicalRegionShapes := by
  unfold Layer.synthesisSummary
  exact FloorPlanner.SynthesisSummary.combine_physicalRegionShapes _ _

theorem Layer.synthesisSummary_eq (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (wsib : WitgenIR Fp 1) (wswap : Placed ProverEnvironment Fp → Bool)
    (ccfg : CondSwap.Config) (cfg : Config)
    (lookupCfg : LookupRangeCheck.Config 10) (input : Var Layer.Input Fp)
    (region : RegionIndex) :
    Layer.synthesisSummary ccfg cfg lookupCfg =
      FloorPlanner.synthesisSummary
        (((do
          let pair ← assignRegion "swap"
            ((CondSwap.swap wsib wswap).call ccfg 0 { a := input.node })
          (HashLayer.circuit G Q hQ l hl).call (cfg, lookupCfg)
            { left := pair.aSwapped, right := pair.bSwapped }) :
          Circuit Fp (Var field Fp)).operations region) := by
  rw [Layer.synthesisSummary]
  simp only [Circuit.operations_bind,
    operations_assignRegion, FloorPlanner.synthesisSummary_region_cons,
    CondSwap.swap_synthesisSummary_eq,
    HashLayer.circuit_synthesisSummary_eq, circuit_norm,
    synthesis_summary_norm]

/-- One Merkle path layer (the `MerklePath::calculate_root` loop body): conditionally swap
`(node, sibling)` by the position bit — sibling and bit are prover witness programs — then
the layer hash. `Spec` is `MerkleStep`. -/
def Layer.circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ)
    (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool) :
    FormalCircuit Fp
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      Layer.Input field where
  name := "MerkleCRH layer"
  configure := pure

  synthesize := fun (ccfg, cfg, lcfg) input => do
    let pair ← assignRegion "swap"
      ((CondSwap.swap wsib wswap).call ccfg 0 { a := input.node })
    (HashLayer.circuit G Q hQ l hl).call (cfg, lcfg)
      { left := pair.aSwapped, right := pair.bSwapped }

  elaborated :=
    { keygenRequirements := Layer.keygenRequirements G Q hQ l hl wsib wswap
      synthesisSummary cfg _ _ := Layer.synthesisSummary cfg.1 cfg.2.1 cfg.2.2
      synthesisSummary_eq := by
        intro cfg input region
        exact Layer.synthesisSummary_eq G Q hQ l hl wsib wswap
          cfg.1 cfg.2.1 cfg.2.2 input region
      registered := by
        intro cfg counts hconfig input self
        simp only [Configure.output_pure, Circuit.operations_bind,
          operations_assignRegion,
          Operations.KeygenRegistered.region_cons, circuit_norm]
        constructor
        · apply (CondSwap.swap wsib wswap).call_keygenRegistered
            cfg.1 hconfig.1 0 { a := input.node } self <;>
              keygen_registration
        · apply (HashLayer.circuit G Q hQ l hl).call_keygenRegistered
            (cfg.2.1, cfg.2.2) hconfig.2 _ (self + 1) <;>
              keygen_registration
      lookupSelectorAnchorRequirements cfg _ _ :=
        LookupRangeCheck.lookupSelectorAnchorRequirements cfg.2.2
      lookupSelectorsAnchoredBy_of_registered := by
        intro cfg _ hconfig input self anchor hanchor _
        simp only [Circuit.operations_bind, operations_assignRegion, circuit_norm]
        apply Operations.LookupSelectorsAnchoredBy.region_cons
        · exact (CondSwap.swap wsib wswap).call_lookupSelectorsAnchoredBy
            cfg.1 hconfig.1 0 { a := input.node } self anchor (by trivial)
        · exact (HashLayer.circuit G Q hQ l hl)
            |>.call_lookupSelectorsAnchoredBy (cfg.2.1, cfg.2.2) hconfig.2 _
              (self + 1) anchor (by
                simpa only [HashLayer.circuit_lookupSelectorAnchorRequirements]
                  using hanchor)
      lookupSelectorAssignmentsAgree_of_registered := by
        intro cfg counts hconfig input self program operations _hregistered
        simp only [operations, program, Configure.output_pure,
          Circuit.operations_bind, operations_assignRegion,
          keygen_norm, keygen_spine]
        exact (HashLayer.circuit G Q hQ l hl)
          |>.call_lookupSelectorAssignmentsAgree
            (cfg.2.1, cfg.2.2) hconfig.2 _ (self + 1)
      fixedWritesLawful := by
        intro cfg _ hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simp only [Configure.output_pure, Circuit.operations_bind,
            operations_assignRegion, circuit_norm]
          constructor
          · exact (CondSwap.swap wsib wswap).call_fixedAssignmentsAgree
              cfg.1 hconfig.1 0 { a := input.node } self
          · exact (HashLayer.circuit G Q hQ l hl)
              |>.call_fixedAssignmentsAgree (cfg.2.1, cfg.2.2) hconfig.2 _
                (self + 1)
        · simp only [Configure.output_pure]
          rw [← Layer.synthesisSummary_eq G Q hQ l hl wsib wswap
            cfg.1 cfg.2.1 cfg.2.2 input self]
          exact Layer.synthesisSummary_tableRowExtent_eq cfg.1 cfg.2.1 cfg.2.2
      copyCellsAssigned := by
        intro cfg counts hconfig input self
        simp only [Configure.output_pure, Circuit.operations_bind,
          operations_assignRegion, circuit_norm]
        unfold Operations.CopyCellsAssigned
        rw [Operations.copyCellsAssignedFrom_region_iff]
        constructor
        · apply (CondSwap.swap wsib wswap).call_copyCellsAssignedFrom
            cfg.1 hconfig.1 0 { a := input.node } self
          intro cell hcell
          simpa only [FormalRegionCircuit.Configured.inputCells,
            CondSwap.swap, FormalRegionCircuit.keygenRequirements,
            ElaboratedRegionCircuit.keygenRequirements] using hcell
        · apply (HashLayer.circuit G Q hQ l hl).call_copyCellsAssignedFrom
            (cfg.2.1, cfg.2.2) hconfig.2 _ (self + 1)
          intro cell hcell
          rw [HashLayer.Configured.inputCells_eq] at hcell
          have hcells :
              cell = ((CondSwap.swap wsib wswap).output cfg.1 0
                  { a := input.node } self).aSwapped.cell ∨
                cell = ((CondSwap.swap wsib wswap).output cfg.1 0
                  { a := input.node } self).bSwapped.cell := by
            simpa using hcell
          rcases hcells with hleft | hright
          · rw [hleft, RegionOperations.mem_assignedCellsAfter_iff,
              List.mem_append]
            exact Or.inr (CondSwap.swap_call_output_cells_assigned
              wsib wswap cfg.1 0 { a := input.node } self).1
          · rw [hright, RegionOperations.mem_assignedCellsAfter_iff,
              List.mem_append]
            exact Or.inr (CondSwap.swap_call_output_cells_assigned
              wsib wswap cfg.1 0 { a := input.node } self).2
      lookupActivationsWellFormed := by
        intro cfg input self
        simp only [Circuit.operations_bind, operations_assignRegion,
          Operations.LookupActivationsWellFormed, circuit_norm]
        exact ⟨(CondSwap.swap wsib wswap).call_lookupActivationsWellFormed
            cfg.1 0 { a := input.node } self,
          (HashLayer.circuit G Q hQ l hl).call_lookupActivationsWellFormed
            (cfg.2.1, cfg.2.2) _ (self + 1)⟩
      output := fun (_, cfg, _) _ i =>
        AssignedCell.of (i + 6)
          (Sinsemilla.Chain.prefixRows HashLayer.merkleNs HashLayer.merkleNs.length)
          cfg.sinsemilla.xA
      regionCount _ := 8
      output_eq := fun (ccfg, cfg, lcfg) input i =>
        (layer_output G Q hQ l hl wsib wswap ccfg cfg lcfg input i).symm
      regionCount_eq := fun (ccfg, cfg, lcfg) input i =>
        (layer_regionCount G Q hQ l hl wsib wswap ccfg cfg lcfg input i).symm }

  EnvAssumptions := fun (ccfg, cfg, lcfg) env =>
    Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla.generatorTable env.env ∧
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions _ := True

  -- the swap witnesses plus the decomposition cells of the following hash layer.
  Witness := fun _ => Layer.Witness
  extract := fun (ccfg, hcfg, lcfg) _ i₀ env =>
    { sibling := eval env (AssignedCell.of i₀ 0 ccfg.b : Var field Fp)
      swap := eval env (AssignedCell.of i₀ 0 ccfg.swap : Var field Fp)
      encoding := (HashLayer.circuit G Q hQ l hl).extract (hcfg, lcfg)
        { left := AssignedCell.of i₀ 0 ccfg.a, right := AssignedCell.of i₀ 0 ccfg.b }
        (i₀ + 1) env }

  Spec input output wit :=
    MerkleStep G Q l input.node output ∧ ExactMerkleStep G Q l input.node output wit

  ProverAssumptions input wit _ :=
    ∃ B, hashToPoint G.S Q (proverChunks l input.node wit.sibling (wit.swap = 1)) = some B

  ProverSpec input output wit _ :=
    ∀ B, hashToPoint G.S Q (proverChunks l input.node wit.sibling (wit.swap = 1)) = some B →
      output = B.x

  soundness := by
    circuit_proof_start
    obtain ⟨hSwap, hHash⟩ := hc
    have hSw : CondSwap.SwapSpec input_node
        (ProvableStruct.Halo2.eval place env x_gen_out_0)
        ((CondSwap.swap wsib wswap).extract cfg.1 0 { a := input_var_node }
          i₀ ⟨place, env⟩) := hSwap trivial trivial
    obtain ⟨hbool, hASw, hBSw⟩ := hSw
    -- the swapped cells' reads are the eval'd swap-output components
    have hAread : AssignedCell.eval place env x_gen_out_0.aSwapped
        = (ProvableStruct.Halo2.eval place env x_gen_out_0).aSwapped := by
      provable_type_simp
    have hBread : AssignedCell.eval place env x_gen_out_0.bSwapped
        = (ProvableStruct.Halo2.eval place env x_gen_out_0).bSwapped := by
      provable_type_simp
    have hHashS := hHash ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial
    rw [HashLayer.circuit_spec_eq] at hHashS
    obtain ⟨lv, rv, hlv, hrv, hleftEnc, hrightEnc, hleftEq, hrightEq, hcontract⟩ := hHashS
    rw [show ({ left := AssignedCell.eval place env x_gen_out_0.aSwapped,
                right := AssignedCell.eval place env x_gen_out_0.bSwapped }
        : Value HashLayer.Input Fp).left
      = AssignedCell.eval place env x_gen_out_0.aSwapped from rfl,
      hAread, hASw] at hleftEq
    rw [show ({ left := AssignedCell.eval place env x_gen_out_0.aSwapped,
                right := AssignedCell.eval place env x_gen_out_0.bSwapped }
        : Value HashLayer.Input Fp).right
      = AssignedCell.eval place env x_gen_out_0.bSwapped from rfl,
      hBread, hBSw] at hrightEq
    subst lv
    subst rv
    have hencoding := HashLayer.circuit_extract_input_independent G Q hQ l hl
      cfg.2.1 cfg.2.2
      { left := x_gen_out_0.aSwapped, right := x_gen_out_0.bSwapped }
      { left := AssignedCell.of i₀ 0 cfg.1.a, right := AssignedCell.of i₀ 0 cfg.1.b }
      (i₀ + 1) ⟨place, env⟩
    rw [hencoding] at hlv hrv hleftEq hrightEq hcontract
    have hswap : ((CondSwap.swap wsib wswap).extract cfg.1 0
          { a := input_var_node } i₀ ⟨place, env⟩).2 =
        env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) := by
      simpa only [Nat.add_zero] using
        CondSwap.swap_extract_snd_eq wsib wswap cfg.1 0
          { a := input_var_node } i₀ ⟨place, env⟩
    rw [hswap] at hbool hleftEq hrightEq
    have houtputContract : ∀ B, hashToPoint G.S Q
        (merkleChunks l
          (HashLayer.leftEncoding ((HashLayer.circuit G Q hQ l hl).extract
            (cfg.2.1, cfg.2.2)
            { left := AssignedCell.of i₀ 0 cfg.1.a,
              right := AssignedCell.of i₀ 0 cfg.1.b }
            (i₀ + 1) ⟨place, env⟩))
          (HashLayer.rightEncoding ((HashLayer.circuit G Q hQ l hl).extract
            (cfg.2.1, cfg.2.2)
            { left := AssignedCell.of i₀ 0 cfg.1.a,
              right := AssignedCell.of i₀ 0 cfg.1.b }
            (i₀ + 1) ⟨place, env⟩))) = some B → output = B.x := by
      intro B hB
      rw [← h_output]
      simpa only [HashLayer.circuit_output, AssignedCell.eval_of_advice,
        Nat.add_assoc, Nat.reduceAdd] using hcontract B hB
    constructor
    · refine ⟨_, _, hlv, hrv, ?_, houtputContract⟩
      rcases hbool with h0 | h1
      · rw [if_neg (show ¬ _ = (1 : Fp) from by rw [h0]; decide)] at hleftEq
        exact Or.inl hleftEq
      · rw [if_pos h1] at hrightEq
        exact Or.inr hrightEq
    · refine ⟨hlv, hrv, ?_, houtputContract⟩
      rcases hbool with h0 | h1
      · simp only [h0, zero_ne_one, if_false] at hleftEq ⊢
        exact hleftEq
      · simp only [h1, if_true] at hrightEq ⊢
        exact hrightEq

  completeness := by
    circuit_proof_start
    obtain ⟨B0, hB0⟩ := hPA
    -- the swap child's honest values (its ProverSpec, over the witness-cell reads)
    have hSwPS := h_spec_0 trivial trivial trivial
    have hwit1 : ((CondSwap.swap wsib wswap).extract cfg.1 0
          { a := input_var_node } i₀ (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
        = env.advice cfg.1.b ((place i₀ : ℕ) : ℤ) := by
      simp only [CondSwap.swap, circuit_norm]
    have hwit2 : ((CondSwap.swap wsib wswap).extract cfg.1 0
          { a := input_var_node } i₀ (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2
        = env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) := by
      simp only [CondSwap.swap, circuit_norm]
    obtain ⟨-, hASw, hBSw⟩ := hSwPS
    rw [hwit1, hwit2, h_input] at hASw hBSw
    -- the swapped cells' reads are the eval'd swap-output components
    have hAread : AssignedCell.eval place env.toEnvironment x_gen_out_0.aSwapped
        = (ProvableStruct.Halo2.eval place env.toEnvironment x_gen_out_0).aSwapped := by
      provable_type_simp
    have hBread : AssignedCell.eval place env.toEnvironment x_gen_out_0.bSwapped
        = (ProvableStruct.Halo2.eval place env.toEnvironment x_gen_out_0).bSwapped := by
      provable_type_simp
    -- the hash child's honest-prover precondition
    have hPAhash : (HashLayer.circuit G Q hQ l hl).ProverAssumptions
        { left := AssignedCell.eval place env.toEnvironment x_gen_out_0.aSwapped,
          right := AssignedCell.eval place env.toEnvironment x_gen_out_0.bSwapped }
        ((HashLayer.circuit G Q hQ l hl).extract (cfg.2.1, cfg.2.2)
          { left := x_gen_out_0.aSwapped, right := x_gen_out_0.bSwapped } (i₀ + 1)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)) env.hint := by
      rw [HashLayer.circuit_proverAssumptions_eq]
      refine ⟨B0, ?_⟩
      show hashToPoint G.S Q (merkleChunks l
          (ZMod.val (AssignedCell.eval place env.toEnvironment x_gen_out_0.aSwapped))
          (ZMod.val (AssignedCell.eval place env.toEnvironment x_gen_out_0.bSwapped))) = some B0
      rw [hAread, hBread, hASw, hBSw]
      by_cases hs : env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1
      · rw [if_pos hs, if_pos hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = true from by simp [hs]] at hB0
        simpa [proverChunks] using hB0
      · rw [if_neg hs, if_neg hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = false from by simp [hs]] at hB0
        simpa [proverChunks] using hB0
    refine ⟨⟨⟨trivial, trivial, trivial⟩, ⟨_hE.1, _hE.2.1, _hE.2.2⟩, trivial, hPAhash⟩, ?_⟩
    -- the honest-prover contract
    intro B hB
    have hPShash := (h_spec_1 ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial hPAhash).2
    rw [HashLayer.circuit_proverSpec_eq] at hPShash
    have hres := hPShash B (by
      show hashToPoint G.S Q (merkleChunks l
          (ZMod.val (AssignedCell.eval place env.toEnvironment x_gen_out_0.aSwapped))
          (ZMod.val (AssignedCell.eval place env.toEnvironment x_gen_out_0.bSwapped))) = some B
      rw [hAread, hBread, hASw, hBSw]
      by_cases hs : env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1
      · rw [if_pos hs, if_pos hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = true from by simp [hs]] at hB
        simpa [proverChunks] using hB
      · rw [if_neg hs, if_neg hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = false from by simp [hs]] at hB
        simpa [proverChunks] using hB)
    rw [← h_output]
    exact hres

derive_contract_bridges Layer.circuit (G : Generators) (Q : Point Fp)
  (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
  (wsib : WitgenIR Fp 1) (wswap : Placed ProverEnvironment Fp → Bool) :=
    Layer.circuit G Q hQ l hl wsib wswap

@[keygen_norm]
theorem Layer.circuit_lookupSelectorAnchorRequirements
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    (Layer.circuit G Q hQ l hl wsib wswap).elaborated.lookupSelectorAnchorRequirements
        cfg input region =
        LookupRangeCheck.lookupSelectorAnchorRequirements cfg.2.2 := rfl

/-- A complete layer returns the x-coordinate cell assigned by its hash child. -/
theorem Layer.circuit_call_output_cell_assigned
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (self : RegionIndex) :
    ((Layer.circuit G Q hQ l hl wsib wswap).output cfg input self).cell ∈
      Operations.assignedCellsFrom
        (((Layer.circuit G Q hQ l hl wsib wswap).call cfg input).operations self) self := by
  rw [Layer.circuit_output]
  rw [FormalCircuit.call_operations]
  simp only [Layer.circuit, Circuit.operations_bind, operations_assignRegion]
  apply Operations.mem_assignedCellsFrom_append_right
  simpa only [circuit_norm] using
    HashLayer.circuit_call_output_cell_assigned
      G Q hQ l hl cfg.2.1 cfg.2.2 _ (self + 1)

/-- Conditional swapping adds no deferred constants, so a complete Merkle
layer has the same four requests as its hash layer. -/
@[synthesis_summary_norm]
theorem Layer.circuit_synthesisSummary_constantSiteCount
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (config : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    ((Layer.circuit G Q hQ l hl wsib wswap).elaborated.synthesisSummary
      config input region).constantSiteCount = 4 := by
  rw [ElaboratedCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [Layer.circuit, Circuit.operations_bind,
    FloorPlanner.synthesisSummary_append,
    FloorPlanner.SynthesisSummary.combine_constantSiteCount,
    operations_assignRegion,
    FloorPlanner.synthesisSummary_region_cons_constantSiteCount,
    FloorPlanner.synthesisSummary_nil_constantSiteCount, Nat.add_zero]
  rw [FormalRegionCircuit.call_synthesisSummary,
    CondSwap.swap_synthesisSummary_constantSiteCount,
    FormalCircuit.call_synthesisSummary,
    HashLayer.circuit_synthesisSummary_constantSiteCount]

/-- A Merkle-layer output stays in the hash chip's `xA` column. -/
@[keygen_norm, keygen_output_norm]
theorem Layer.circuit_output_column (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (wsib : WitgenIR Fp 1) (wswap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i : RegionIndex) :
    ((Layer.circuit G Q hQ l hl wsib wswap).output cfg input i).cell.column =
      cfg.2.1.sinsemilla.xA := by
  simp only [Layer.circuit_output, AssignedCell.of_cell, Cell.of_column]

/-- The column carrying a layer's output is included in its equality-column summary. -/
@[keygen_norm]
theorem Layer.Configured.outputColumn_mem_permutationColumns
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10)
    (wsib : WitgenIR Fp 1) (wswap : Placed ProverEnvironment Fp → Bool)
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    (configured : (Layer.circuit G Q hQ l hl wsib wswap).Configured cfg) :
    cfg.2.1.sinsemilla.xA.toAny ∈ configured.permutationColumns := by
  rcases configured with ⟨configInput, counts, lawful, output_eq⟩
  simp only [Layer.circuit, Configure.output_pure] at output_eq
  subst cfg
  simp only [FormalCircuit.Configured.permutationColumns,
    Layer.circuit, FormalCircuit.keygenRequirements,
    Layer.keygenRequirements, Configure.delta_pure, List.append_nil]
  apply List.mem_append_right
  exact HashLayer.Configured.outputColumn_mem_permutationColumns
    G Q hQ l hl lawful.2

/-- Assemble one Merkle-layer capability from its two direct children. -/
def Layer.configurationCertificate (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (wsib : WitgenIR Fp 1) (wswap : Placed ProverEnvironment Fp → Bool)
    {ccfg : CondSwap.Config} {cfg : Config}
    {lcfg : LookupRangeCheck.Config 10} {context : KeygenContext Fp}
    (swap : (CondSwap.swap wsib wswap).ConfigurationCertificate ccfg context)
    (hash : (HashLayer.circuit G Q hQ l hl).ConfigurationCertificate
      (cfg, lcfg) context) :
    (Layer.circuit G Q hQ l hl wsib wswap).ConfigurationCertificate
      (ccfg, cfg, lcfg) context := by
  let lawful : (Layer.keygenRequirements G Q hQ l hl wsib wswap).configLawful
      (ccfg, cfg, lcfg) := ⟨swap.configured, hash.configured⟩
  apply ((Layer.circuit G Q hQ l hl wsib wswap).configureCertificate
    (ccfg, cfg, lcfg) {} lawful).mono
  · intro required hrequired
    simp only [Layer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Layer.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with hrequired | hrequired
    · exact swap.gates_of_configured required hrequired
    · exact hash.gates_of_configured required hrequired
  · intro required hrequired
    simp only [Layer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Layer.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with hrequired | hrequired
    · exact swap.lookups_of_configured required hrequired
    · exact hash.lookups_of_configured required hrequired
  · intro required hrequired
    simp only [Layer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Layer.keygenRequirements,
      Configure.fixedColumns_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with hrequired | hrequired
    · exact swap.fixedColumns_of_configured required hrequired
    · exact hash.fixedColumns_of_configured required hrequired
  · intro required hrequired
    simp only [Layer.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, Layer.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hrequired
    rcases hrequired with hrequired | hrequired
    · exact swap.permutationColumns_of_configured required hrequired
    · exact hash.permutationColumns_of_configured required hrequired

/-! ### `CalculateRoot` (32-layer fold, structure) -/

namespace CalculateRoot

/-- The honest running node after `k` layers (`none` if any layer hash is undefined). Index-based
to mirror the circuit's fold. Donor `CalculateRoot.honestNode`. -/
def honestNode (G : Generators) (Q : Point Fp)
    (leaf : Fp) (path : Vector Fp 32) (pos : ℕ) : ℕ → Option Fp
  | 0 => some leaf
  | k + 1 =>
    if hk : k < 32 then
      (honestNode G Q leaf path pos k).bind fun node =>
        (hashToPoint G.S Q
          (proverChunks k node (path[k]'(by omega)) (decide (pos >>> k % 2 = 1)))).map (·.x)
    else none

/-- `honestNode` is downward-monotone in success. Donor `CalculateRoot.honestNode_isSome_of_succ`. -/
theorem honestNode_isSome_of_succ (G : Generators) (Q : Point Fp)
    (leaf : Fp) (path : Vector Fp 32) (pos : ℕ) (k : ℕ)
    (h : (honestNode G Q leaf path pos (k + 1)).isSome) :
    (honestNode G Q leaf path pos k).isSome := by
  rw [honestNode] at h
  split at h
  · rcases hb : honestNode G Q leaf path pos k with _ | v
    · rw [hb] at h; simp at h
    · simp
  · simp at h

theorem honestNode_isSome_le (G : Generators) (Q : Point Fp)
    (leaf : Fp) (path : Vector Fp 32) (pos : ℕ) {i j : ℕ} (hij : i ≤ j)
    (h : (honestNode G Q leaf path pos j).isSome) :
    (honestNode G Q leaf path pos i).isSome := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact ih (by omega) (honestNode_isSome_of_succ G Q leaf path pos m h)
    · have : i = m + 1 := by omega
      rwa [this]

/-! #### The 32-layer fold (`MerklePath::calculate_root`), on `FormalCircuit.foldCall` -/

/-- The layer family: layer `i` is `Layer.circuit` at `l = i` (`% 2 ^ 10` totalizer —
identity on the 32 layers used). -/
def layerAt (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l₀ : ℕ)
    (wsib : ℕ → WitgenIR Fp 1) (wswap : ℕ → Placed ProverEnvironment Fp → Bool) (i : ℕ) :
    FormalCircuit Fp
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      Layer.Input field :=
  Layer.circuit G Q hQ ((l₀ + i) % 2 ^ 10) (Nat.mod_lt _ (by norm_num)) (wsib i) (wswap i)

@[keygen_norm]
private theorem layerAt_output_column
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l₀ : ℕ)
    (wsib : ℕ → WitgenIR Fp 1)
    (wswap : ℕ → Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) (i : ℕ) :
    ((layerAt G Q hQ l₀ wsib wswap i).output cfg input region).cell.column =
      cfg.2.1.sinsemilla.xA :=
  Layer.circuit_output_column G Q hQ _ _ _ _ cfg input region

/-- Feed a layer's root cell back as the next layer's node. -/
def toInput : Var field Fp → Var Layer.Input Fp := fun out => { node := out }

/-- The running node over the *extracted* per-layer `(sibling, swap)` readings (`none` once a
layer hash is undefined) — the fold's own honest-node chain. The honest-input instantiation
(path/pos witness programs) recovers `honestNode`. -/
def pathNode (G : Generators) (Q : Point Fp) (l₀ : ℕ) (wit : ℕ → Fp × Fp) (node : Fp) :
    ℕ → Option Fp
  | 0 => some node
  | k + 1 => (pathNode G Q l₀ wit node k).bind fun n =>
      (hashToPoint G.S Q (proverChunks (l₀ + k) n (wit k).1 ((wit k).2 = 1))).map (·.x)

/-- `pathNode` only reads the witness below the depth. -/
theorem pathNode_congr (G : Generators) (Q : Point Fp) (l₀ : ℕ)
    {w w' : ℕ → Fp × Fp} (node : Fp) (k : ℕ) (h : ∀ j, j < k → w j = w' j) :
    pathNode G Q l₀ w node k = pathNode G Q l₀ w' node k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [pathNode, pathNode, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem pathNode_congr₂ (G : Generators) (Q : Point Fp) (l₀ : ℕ)
    {w w' : ℕ → Fp × Fp} {node node' : Fp} (k : ℕ)
    (hw : ∀ j, j < k → w j = w' j) (hn : node = node') :
    pathNode G Q l₀ w node k = pathNode G Q l₀ w' node' k := by
  rw [hn, pathNode_congr G Q l₀ node' k hw]

theorem pathNode_isSome_of_succ (G : Generators) (Q : Point Fp) (l₀ : ℕ) (wit : ℕ → Fp × Fp)
    (node : Fp) (k : ℕ) (h : (pathNode G Q l₀ wit node (k + 1)).isSome) :
    (pathNode G Q l₀ wit node k).isSome := by
  rw [pathNode] at h
  rcases hb : pathNode G Q l₀ wit node k with _ | v
  · rw [hb] at h; simp at h
  · simp

theorem pathNode_isSome_le (G : Generators) (Q : Point Fp) (l₀ : ℕ) (wit : ℕ → Fp × Fp)
    (node : Fp) {i j : ℕ} (hij : i ≤ j) (h : (pathNode G Q l₀ wit node j).isSome) :
    (pathNode G Q l₀ wit node i).isSome := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact ih (by omega) (pathNode_isSome_of_succ G Q l₀ wit node m h)
    · have : i = m + 1 := by omega
      rwa [this]

variable (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l₀ d : ℕ)
  (hld : l₀ + d ≤ 2 ^ 10)
  (wsib : ℕ → WitgenIR Fp 1) (wswap : ℕ → Placed ProverEnvironment Fp → Bool)

/-- The fold's region index entering layer `m`: 8 regions per layer. -/
private theorem foldState_snd
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i₀ : RegionIndex) : ∀ m : ℕ,
    (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg input i₀ m).2
      = i₀ + 8 * m
  | 0 => rfl
  | m + 1 => by
    show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg input i₀ m).2 + 8
      = i₀ + 8 * (m + 1)
    rw [foldState_snd cfg input i₀ m, Nat.mul_succ, Nat.add_assoc]

/-- The fold's region count: `8 * d`. -/
private theorem fold_regionCount
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i : RegionIndex) :
    Operations.regionCount
      (((FormalCircuit.foldCall (layerAt G Q hQ l₀ wsib wswap) toInput cfg input d >>=
        fun acc => pure acc.node) : Circuit Fp (Var field Fp)).operations i)
      = 8 * d := by
  have h := FormalCircuit.foldOps_regionCount (layerAt G Q hQ l₀ wsib wswap) toInput cfg input
    i d
  rw [foldState_snd G Q hQ l₀ wsib wswap cfg input i d] at h
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    FormalCircuit.foldCall_operations, Operations.regionCount_append, Operations.regionCount]
  rw [Nat.add_zero]
  exact Nat.add_left_cancel h

/-- Projection landing: `.node` of an eval'd `Layer.Input` var is the eval of its cell. -/
private theorem input_eval_node (env : Placed Environment Fp) (v : Var Layer.Input Fp) :
    (eval env v : Value Layer.Input Fp).node = (eval env v.node : Fp) := by
  rw [ProvableStruct.Halo2.eval_cells_eq_eval]
  provable_type_simp

private theorem input_eval_node_prover (env : Placed ProverEnvironment Fp)
    (v : Var Layer.Input Fp) :
    (eval env v : Value Layer.Input Fp).node = (eval env v.node : Fp) := by
  rw [ProvableStruct.Halo2.eval_cells_eq_eval_prover]
  provable_type_simp

private def retargetSwapConfigured
    {cfg : CondSwap.Config}
    {wb wb' : WitgenIR Fp 1}
    {swapWitness swapWitness' : Placed ProverEnvironment Fp → Bool}
    (configured : (CondSwap.swap wb swapWitness).Configured cfg) :
    (CondSwap.swap wb' swapWitness').Configured cfg := by
  rcases configured with ⟨configInput, counts, configLawful, output_eq⟩
  exact ⟨configInput, counts, configLawful, output_eq⟩

private def retargetGateConfigured
    {cfg : Gate.Config} {l l' : Fp}
    (configured : (Gate.circuit l).Configured cfg) :
    (Gate.circuit l').Configured cfg := by
  rcases configured with ⟨configInput, counts, configLawful, output_eq⟩
  exact ⟨configInput, counts, configLawful, output_eq⟩

private def retargetHashLayerConfigured
    {cfg : Config × LookupRangeCheck.Config 10} {l l' : ℕ}
    {hl : l < 2 ^ 10} {hl' : l' < 2 ^ 10}
    (configured : (HashLayer.circuit G Q hQ l hl).Configured cfg) :
    (HashLayer.circuit G Q hQ l' hl').Configured cfg := by
  rcases configured with ⟨configInput, counts, configLawful, output_eq⟩
  exact ⟨configInput, counts,
    ⟨configLawful.1, configLawful.2.1,
      retargetGateConfigured configLawful.2.2⟩,
    output_eq⟩

private def retargetLayerConfigured
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    {l l' : ℕ} {hl : l < 2 ^ 10} {hl' : l' < 2 ^ 10}
    {wb wb' : WitgenIR Fp 1}
    {swapWitness swapWitness' : Placed ProverEnvironment Fp → Bool}
    (configured : (Layer.circuit G Q hQ l hl wb swapWitness).Configured cfg) :
    (Layer.circuit G Q hQ l' hl' wb' swapWitness').Configured cfg := by
  rcases configured with ⟨configInput, counts, configLawful, output_eq⟩
  exact ⟨configInput, counts,
    ⟨retargetSwapConfigured configLawful.1,
      retargetHashLayerConfigured G Q hQ configLawful.2⟩,
    output_eq⟩

@[keygen_norm]
private theorem retargetLayerConfigured_gates
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    {l l' : ℕ} {hl : l < 2 ^ 10} {hl' : l' < 2 ^ 10}
    {wb wb' : WitgenIR Fp 1}
    {swapWitness swapWitness' : Placed ProverEnvironment Fp → Bool}
    (configured : (Layer.circuit G Q hQ l hl wb swapWitness).Configured cfg) :
    (retargetLayerConfigured G Q hQ
      (l' := l') (hl' := hl') (wb' := wb')
      (swapWitness' := swapWitness') configured).gates = configured.gates := by
  rcases configured with ⟨configInput, counts,
    ⟨swapConfigured, hashConfigured⟩, output_eq⟩
  rcases swapConfigured with ⟨swapInput, swapCounts, swapLawful, swapOutput⟩
  rcases hashConfigured with ⟨hashInput, hashCounts,
    ⟨rangeConfigured, hashToPointConfigured, gateConfigured⟩, hashOutput⟩
  rcases gateConfigured with ⟨gateInput, gateCounts, gateLawful, gateOutput⟩
  rfl

@[keygen_norm]
private theorem retargetLayerConfigured_lookups
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    {l l' : ℕ} {hl : l < 2 ^ 10} {hl' : l' < 2 ^ 10}
    {wb wb' : WitgenIR Fp 1}
    {swapWitness swapWitness' : Placed ProverEnvironment Fp → Bool}
    (configured : (Layer.circuit G Q hQ l hl wb swapWitness).Configured cfg) :
    (retargetLayerConfigured G Q hQ
      (l' := l') (hl' := hl') (wb' := wb')
      (swapWitness' := swapWitness') configured).lookups = configured.lookups := by
  rcases configured with ⟨configInput, counts,
    ⟨swapConfigured, hashConfigured⟩, output_eq⟩
  rcases swapConfigured with ⟨swapInput, swapCounts, swapLawful, swapOutput⟩
  rcases hashConfigured with ⟨hashInput, hashCounts,
    ⟨rangeConfigured, hashToPointConfigured, gateConfigured⟩, hashOutput⟩
  rcases gateConfigured with ⟨gateInput, gateCounts, gateLawful, gateOutput⟩
  rfl

@[keygen_norm]
private theorem retargetLayerConfigured_fixedColumns
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    {l l' : ℕ} {hl : l < 2 ^ 10} {hl' : l' < 2 ^ 10}
    {wb wb' : WitgenIR Fp 1}
    {swapWitness swapWitness' : Placed ProverEnvironment Fp → Bool}
    (configured : (Layer.circuit G Q hQ l hl wb swapWitness).Configured cfg) :
    (retargetLayerConfigured G Q hQ
      (l' := l') (hl' := hl') (wb' := wb')
      (swapWitness' := swapWitness') configured).fixedColumns =
        configured.fixedColumns := by
  rcases configured with ⟨configInput, counts,
    ⟨swapConfigured, hashConfigured⟩, output_eq⟩
  rcases swapConfigured with ⟨swapInput, swapCounts, swapLawful, swapOutput⟩
  rcases hashConfigured with ⟨hashInput, hashCounts,
    ⟨rangeConfigured, hashToPointConfigured, gateConfigured⟩, hashOutput⟩
  rcases gateConfigured with ⟨gateInput, gateCounts, gateLawful, gateOutput⟩
  rfl

@[keygen_norm]
private theorem retargetLayerConfigured_permutationColumns
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    {l l' : ℕ} {hl : l < 2 ^ 10} {hl' : l' < 2 ^ 10}
    {wb wb' : WitgenIR Fp 1}
    {swapWitness swapWitness' : Placed ProverEnvironment Fp → Bool}
    (configured : (Layer.circuit G Q hQ l hl wb swapWitness).Configured cfg) :
    (retargetLayerConfigured G Q hQ
      (l' := l') (hl' := hl') (wb' := wb')
      (swapWitness' := swapWitness') configured).permutationColumns =
        configured.permutationColumns := by
  rcases configured with ⟨configInput, counts,
    ⟨swapConfigured, hashConfigured⟩, output_eq⟩
  rcases swapConfigured with ⟨swapInput, swapCounts, swapLawful, swapOutput⟩
  rcases hashConfigured with ⟨hashInput, hashCounts,
    ⟨rangeConfigured, hashToPointConfigured, gateConfigured⟩, hashOutput⟩
  rcases gateConfigured with ⟨gateInput, gateCounts, gateLawful, gateOutput⟩
  rfl

@[keygen_norm]
def keygenRequirements :
    KeygenRequirements Fp
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      (Var Layer.Input Fp) where
  configLawful cfg :=
    (layerAt G Q hQ l₀ wsib wswap 0).Configured cfg
  gates _ configured := configured.gates
  lookups _ configured := configured.lookups
  fixedColumns _ configured := configured.fixedColumns
  permutationColumns _ configured := configured.permutationColumns
  inputCells _ _ input := [input.node.cell]

@[keygen_configured]
private def layerAtConfigured
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    (configured : (layerAt G Q hQ l₀ wsib wswap 0).Configured cfg) (i : ℕ) :
    (layerAt G Q hQ l₀ wsib wswap i).Configured cfg :=
  retargetLayerConfigured G Q hQ configured

@[keygen_norm]
private theorem layerAtConfigured_gates
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    (configured : (layerAt G Q hQ l₀ wsib wswap 0).Configured cfg) (i : ℕ) :
    (layerAtConfigured G Q hQ l₀ wsib wswap configured i).gates =
      configured.gates :=
  retargetLayerConfigured_gates G Q hQ configured

@[keygen_norm]
private theorem layerAtConfigured_lookups
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    (configured : (layerAt G Q hQ l₀ wsib wswap 0).Configured cfg) (i : ℕ) :
    (layerAtConfigured G Q hQ l₀ wsib wswap configured i).lookups =
      configured.lookups :=
  retargetLayerConfigured_lookups G Q hQ configured

@[keygen_norm]
private theorem layerAtConfigured_fixedColumns
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    (configured : (layerAt G Q hQ l₀ wsib wswap 0).Configured cfg) (i : ℕ) :
    (layerAtConfigured G Q hQ l₀ wsib wswap configured i).fixedColumns =
      configured.fixedColumns :=
  retargetLayerConfigured_fixedColumns G Q hQ configured

@[keygen_norm]
private theorem layerAtConfigured_permutationColumns
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    (configured : (layerAt G Q hQ l₀ wsib wswap 0).Configured cfg) (i : ℕ) :
    (layerAtConfigured G Q hQ l₀ wsib wswap configured i).permutationColumns =
      configured.permutationColumns :=
  retargetLayerConfigured_permutationColumns G Q hQ configured

private theorem foldState_node_column_mem
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    (configured : (layerAt G Q hQ l₀ wsib wswap 0).Configured cfg)
    (input : Var Layer.Input Fp) (region : RegionIndex) : ∀ m : ℕ,
    (FormalCircuit.foldState
        (layerAt G Q hQ l₀ wsib wswap) toInput cfg input region m).1.node.cell.column ∈
      configured.permutationColumns ++ [input.node.cell.column]
  | 0 => by
      simp [FormalCircuit.foldState]
  | m + 1 => by
      simp only [FormalCircuit.foldState, toInput]
      rw [layerAt_output_column]
      apply List.mem_append_left
      have hcolumn := Layer.Configured.outputColumn_mem_permutationColumns
        G Q hQ _ _ _ _ (layerAtConfigured G Q hQ l₀ wsib wswap configured m)
      simpa only [layerAtConfigured_permutationColumns] using hcolumn

/-- The node carried by a nonempty fold is the output cell assigned by its last
layer. -/
private theorem foldState_succ_node_cell_mem_assigned
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) (m : ℕ) :
    (FormalCircuit.foldState
        (layerAt G Q hQ l₀ wsib wswap) toInput cfg input region (m + 1)).1.node.cell ∈
      (FormalCircuit.foldOps (layerAt G Q hQ l₀ wsib wswap)
        toInput cfg input region (m + 1)).assignedCellsFrom region := by
  simp only [FormalCircuit.foldState, toInput]
  rw [FormalCircuit.foldOps]
  apply Operations.mem_assignedCellsFrom_append_right
  rw [show region + Operations.regionCount
          (FormalCircuit.foldOps (layerAt G Q hQ l₀ wsib wswap)
            toInput cfg input region m) =
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
          toInput cfg input region m).2 from
      FormalCircuit.foldOps_regionCount
        (layerAt G Q hQ l₀ wsib wswap) toInput cfg input region m]
  exact Layer.circuit_call_output_cell_assigned
    G Q hQ ((l₀ + m) % 2 ^ 10) (Nat.mod_lt _ (by norm_num))
    (wsib m) (wswap m) _
    (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
      toInput cfg input region m).1
    (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
      toInput cfg input region m).2

/-- Every node carried by the fold is either its original input or the output cell
assigned by an earlier layer. -/
private theorem foldState_node_cell_mem
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) : ∀ m : ℕ,
    (FormalCircuit.foldState
        (layerAt G Q hQ l₀ wsib wswap) toInput cfg input region m).1.node.cell ∈
      [input.node.cell] ++
        (FormalCircuit.foldOps (layerAt G Q hQ l₀ wsib wswap)
          toInput cfg input region m).assignedCellsFrom region
  | 0 => by simp [FormalCircuit.foldState, FormalCircuit.foldOps]
  | m + 1 => List.mem_append_right _
      (foldState_succ_node_cell_mem_assigned G Q hQ l₀ wsib wswap
        cfg input region m)

/-- A nonempty Merkle fold carries the last layer's `xA` output column; the empty
fold returns its input cell unchanged. -/
@[keygen_norm]
private theorem foldState_node_column
    (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l₀ : ℕ)
    (wsib : ℕ → WitgenIR Fp 1)
    (wswap : ℕ → Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) (m : ℕ) :
    (FormalCircuit.foldState
        (layerAt G Q hQ l₀ wsib wswap) toInput cfg input region m).1.node.cell.column =
      if m = 0 then input.node.cell.column else cfg.2.1.sinsemilla.xA := by
  cases m with
  | zero => simp [FormalCircuit.foldState]
  | succ m =>
      simp only [FormalCircuit.foldState, toInput]
      rw [layerAt_output_column]
      simp

private def synthesize
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) : Circuit Fp (Var field Fp) := do
  let acc ← FormalCircuit.foldCall
    (layerAt G Q hQ l₀ wsib wswap) toInput cfg input d
  pure acc.node

private theorem synthesize_keygenRegistered :
    ∀ (configInput : CondSwap.Config × Config × LookupRangeCheck.Config 10)
      (counts : ConfigureCounts)
      (hconfig : (keygenRequirements G Q hQ l₀ wsib wswap).configLawful configInput)
      (input : Var Layer.Input Fp) (region : RegionIndex),
    let program := (pure configInput : Configure Fp _)
    ((synthesize G Q hQ l₀ d wsib wswap (program.output counts) input).operations
      region).KeygenRegistered
      ((keygenRequirements G Q hQ l₀ wsib wswap).gates configInput hconfig ++
        (program.delta counts).gates)
      ((keygenRequirements G Q hQ l₀ wsib wswap).lookups configInput hconfig ++
        (program.delta counts).lookups)
      ((keygenRequirements G Q hQ l₀ wsib wswap).fixedColumns configInput hconfig ++
        program.fixedColumns counts)
      ((keygenRequirements G Q hQ l₀ wsib wswap).permutationColumns configInput hconfig ++
        (program.delta counts).permutationRequests ++
        (keygenRequirements G Q hQ l₀ wsib wswap).inputPermutationColumns
          configInput hconfig input) := by
  intro configInput counts hconfig input region
  simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
    Operations.KeygenRegistered.append, Operations.KeygenRegistered.nil,
    and_true]
  apply FormalCircuit.foldCall_keygenRegistered
    (c := layerAt G Q hQ l₀ wsib wswap)
    (toInput := toInput) (config := configInput)
    (init := input) (i₀ := region) d
    (fun i => layerAtConfigured G Q hQ l₀ wsib wswap hconfig i)
  · intro i gate hgate
    rw [layerAtConfigured_gates] at hgate
    simpa only [keygenRequirements, Configure.delta_pure,
      List.append_nil] using hgate
  · intro i argument hargument
    rw [layerAtConfigured_lookups] at hargument
    simpa only [keygenRequirements, Configure.delta_pure,
      List.append_nil] using hargument
  · intro i column hcolumn
    rw [layerAtConfigured_fixedColumns] at hcolumn
    simpa only [keygenRequirements, Configure.fixedColumns_pure,
      List.append_nil] using hcolumn
  · intro i column hcolumn
    rw [layerAtConfigured_permutationColumns] at hcolumn
    simp only [keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_append]
    exact Or.inl hcolumn
  · intro i
    simp only [layerAt, Layer.circuit, Layer.keygenRequirements]
    exact foldState_node_column_mem G Q hQ l₀ wsib wswap
      hconfig input region i

/-- Reduced summary of all Merkle layers, composed from each layer's declared
summary at its fold state. -/
def synthesisSummary
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    : FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.replicate d
    (Layer.synthesisSummary cfg.1 cfg.2.1 cfg.2.2)

@[synthesis_summary_norm]
theorem synthesisSummary_lookupActivationCount
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10) :
    (synthesisSummary d cfg).lookupActivationCount = d * 56 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_tableRowExtent_eq
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10) :
    (synthesisSummary d cfg).tableRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10) :
    (synthesisSummary d cfg).instanceRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem synthesisSummary_physicalShapes_eq
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10) :
    (synthesisSummary d cfg).physicalRegionShapes =
      (List.replicate d
        (Layer.synthesisSummary cfg.1 cfg.2.1 cfg.2.2).physicalRegionShapes).flatten := by
  unfold synthesisSummary
  exact FloorPlanner.SynthesisSummary.replicate_physicalRegionShapes _ _

theorem synthesisSummary_eq
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    synthesisSummary d cfg =
      FloorPlanner.synthesisSummary
        ((synthesize G Q hQ l₀ d wsib wswap cfg input).operations region) := by
  rw [synthesize, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil,
    FormalCircuit.foldCall_operations]
  rw [← FormalCircuit.foldSynthesisSummary_eq]
  symm
  apply FormalCircuit.foldSynthesisSummary_eq_replicate
  · intro i
    rfl
  · rw [Layer.synthesisSummary_eq G Q hQ ((l₀ + 0) % 2 ^ 10)
        (Nat.mod_lt _ (by norm_num)) (wsib 0) (wswap 0)
        cfg.1 cfg.2.1 cfg.2.2 input region]
    exact FloorPlanner.synthesisSummary_columns_nodup _

/-- Extract the swap data and literal hash input encodings exported by every
layer of a calculated Merkle path. -/
def extractWitness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l₀ : ℕ) (ccfg : CondSwap.Config) (hcfg : Config)
    (lcfg : LookupRangeCheck.Config 10) (i₀ : RegionIndex)
    (env : Placed Environment Fp) : ℕ → Layer.Witness := fun j =>
  { sibling := eval env (AssignedCell.of (i₀ + 8 * j) 0 ccfg.b : Var field Fp)
    swap := eval env (AssignedCell.of (i₀ + 8 * j) 0 ccfg.swap : Var field Fp)
    encoding := (HashLayer.circuit G Q hQ ((l₀ + j) % 2 ^ 10)
        (Nat.mod_lt _ (by norm_num))).extract (hcfg, lcfg)
      { left := AssignedCell.of (i₀ + 8 * j) 0 ccfg.a,
        right := AssignedCell.of (i₀ + 8 * j) 0 ccfg.b }
      (i₀ + 8 * j + 1) env }

/-- Rust `MerklePath::calculate_root` (`merkle.rs`): the 32-layer serial fold of
`Layer.circuit` (layer `i` at `l = i`), fed by the per-layer sibling/position-bit witness
programs. Its spec is the extraction-friendly `ExactMerklePathData` chain (zcash/ironwood#97):
the literal 255-bit child encodings and swap bits of every layer, with each layer's hash
in the guarded ⊥-model. Escapes are not turned into break statements here — the security
layer recomputes them from the exported encodings. -/
def circuit :
    FormalCircuit Fp
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      (CondSwap.Config × Config × LookupRangeCheck.Config 10)
      Layer.Input field where
  name := "MerkleCRH calculate_root"
  configure := pure

  synthesize := synthesize G Q hQ l₀ d wsib wswap

  elaborated :=
    { keygenRequirements := keygenRequirements G Q hQ l₀ wsib wswap
      synthesisSummary cfg _ _ := synthesisSummary d cfg
      synthesisSummary_eq := synthesisSummary_eq G Q hQ l₀ d wsib wswap
      registered := synthesize_keygenRegistered G Q hQ l₀ d wsib wswap
      lookupSelectorAssignmentsAgree_of_registered := by
        intro cfg counts hconfig input region program operations _hregistered
        simp only [operations, program, Configure.output_pure, synthesize,
          Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
        exact FormalCircuit.foldCall_lookupSelectorAssignmentsAgree
          (c := layerAt G Q hQ l₀ wsib wswap) (toInput := toInput)
          (config := cfg) (init := input) (i₀ := region) d
          (fun i => layerAtConfigured G Q hQ l₀ wsib wswap hconfig i)
      lookupSelectorAnchorRequirements cfg _ _ :=
        LookupRangeCheck.lookupSelectorAnchorRequirements cfg.2.2
      lookupSelectorsAnchoredBy_of_registered := by
        intro cfg _ hconfig input region anchor hanchor _
        simp only [synthesize, Circuit.operations_bind,
          Circuit.operations_pure, List.append_nil]
        apply FormalCircuit.foldCall_lookupSelectorsAnchoredBy
          (c := layerAt G Q hQ l₀ wsib wswap) (toInput := toInput)
          (config := cfg) (init := input) (i₀ := region) d
          (fun i => layerAtConfigured G Q hQ l₀ wsib wswap hconfig i)
          anchor
        intro i
        simpa only [layerAt,
          Layer.circuit_lookupSelectorAnchorRequirements] using hanchor
      fixedWritesLawful := by
        intro cfg _ hconfig input region
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simp only [Configure.output_pure, synthesize,
            Circuit.operations_bind, Circuit.operations_pure,
            List.forall_append, List.forall_nil, and_true]
          exact FormalCircuit.foldCall_fixedAssignmentsAgree
            (c := layerAt G Q hQ l₀ wsib wswap) (toInput := toInput)
            (config := cfg) (init := input) (i₀ := region) d
            (fun i => layerAtConfigured G Q hQ l₀ wsib wswap hconfig i)
        · simp only [Configure.output_pure]
          rw [← synthesisSummary_eq G Q hQ l₀ d wsib wswap cfg input region]
          exact synthesisSummary_tableRowExtent_eq d cfg
      copyCellsAssigned := by
        intro cfg counts hconfig input region
        simp only [synthesize, Configure.output_pure,
          Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
        apply FormalCircuit.foldCall_copyCellsAssignedFrom
          (c := layerAt G Q hQ l₀ wsib wswap)
          (toInput := toInput) (config := cfg) (init := input)
          (i₀ := region) d
          (fun i => layerAtConfigured G Q hQ l₀ wsib wswap hconfig i)
        intro i cell hcell
        simp only [FormalCircuit.Configured.inputCells,
          layerAt, Layer.circuit, FormalCircuit.keygenRequirements,
          ElaboratedCircuit.keygenRequirements, Layer.keygenRequirements,
          List.mem_singleton] at hcell
        subst cell
        exact foldState_node_cell_mem (G := G) (Q := Q) (hQ := hQ)
          (l₀ := l₀) (wsib := wsib) (wswap := wswap) cfg input region i
      lookupActivationsWellFormed := by
        intro cfg input region
        simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
          Operations.LookupActivationsWellFormed, List.forall_append,
          List.forall_nil, and_true]
        rw [FormalCircuit.foldCall_forall]
        intro i
        exact (layerAt G Q hQ l₀ wsib wswap i)
          |>.call_lookupActivationsWellFormed cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
              toInput cfg input region i).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
              toInput cfg input region i).2
      output := fun cfg input i =>
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg input i d).1.node
      regionCount _ := 8 * d
      output_eq := by
        intro cfg input i
        symm
        show (FormalCircuit.foldCall (layerAt G Q hQ l₀ wsib wswap) toInput cfg input d >>=
          fun acc => pure acc.node).output i = _
        rw [Circuit.output_bind, FormalCircuit.foldCall_output]
        rfl
      regionCount_eq := fun cfg input i =>
        (fold_regionCount G Q hQ l₀ d wsib wswap cfg input i).symm }

  EnvAssumptions := fun (_, cfg, lcfg) env =>
    Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla.generatorTable env.env ∧
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions _ := True

  -- The complete per-layer extraction: cond-swap readings plus the literal
  -- decomposition encoding used by the following seven-region hash layer.
  Witness := fun _ => ℕ → Layer.Witness
  extract := fun (ccfg, hcfg, lcfg) _ i₀ env =>
    extractWitness G Q hQ l₀ ccfg hcfg lcfg i₀ env

  Spec input output wit :=
    ExactMerklePathData G Q l₀ d input.node output
        (fun j => HashLayer.leftEncoding (wit j).encoding)
        (fun j => HashLayer.rightEncoding (wit j).encoding)
        (fun j => decide ((wit j).swap = 1)) ∧
      MerkleRoot G Q l₀ input.node d output ∧
        (MerkleRootStrict G Q l₀ input.node d output ∨ MerkleBreakAt G Q l₀ d)

  ProverAssumptions input wit _ :=
    (pathNode G Q l₀ (fun j => (wit j).pair) input.node d).isSome

  -- the honest output is the running `pathNode` value (exported so a parent can chain
  -- a second fold from this fold's output cell)
  ProverSpec input output wit _ :=
    ∀ n, pathNode G Q l₀ (fun j => (wit j).pair) (input.node : Fp) d = some n →
      (output : Fp) = n

  soundness := by
    circuit_proof_start
    rw [FormalCircuit.foldCall_operations, FormalCircuit.foldOps_constraints] at hc
    subcircuit_rw at hc
    -- the per-layer contract, `l = i`
    have hExactStep : ∀ i : Fin d, ExactMerkleStep G Q (l₀ + ↑i)
        ((eval (⟨place, env⟩ : Placed Environment Fp)
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ ↑i).1 : Value Layer.Input Fp).node)
        (eval (⟨place, env⟩ : Placed Environment Fp)
          ((layerAt G Q hQ l₀ wsib wswap ↑i).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ ↑i).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ ↑i).2))
        ((layerAt G Q hQ l₀ wsib wswap ↑i).extract cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ ↑i).1
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ ↑i).2 ⟨place, env⟩) := by
      intro i
      have h := (hc i ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial).2
      rwa [Nat.mod_eq_of_lt (show l₀ + (↑i : ℕ) < 2 ^ 10 from by
        have := i.isLt; omega)] at h
    -- land the endpoints
    have hf0 : (eval (⟨place, env⟩ : Placed Environment Fp)
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ 0).1 : Value Layer.Input Fp).node = input_node := by
      rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ 0).1
        = ({ node := input_var_node } : Var Layer.Input Fp) from rfl]
      rw [input_eval_node]
      rw [show (eval (⟨place, env⟩ : Placed Environment Fp)
          (({ node := input_var_node } : Var Layer.Input Fp).node) : Fp)
        = AssignedCell.eval place env input_var_node from by simp only [circuit_norm]]
      exact h_input
    have hfd : (eval (⟨place, env⟩ : Placed Environment Fp)
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ d).1 : Value Layer.Input Fp).node = output := by
      rw [input_eval_node]
      rw [show (eval (⟨place, env⟩ : Placed Environment Fp)
          ((FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ d).1.node) : Fp)
        = AssignedCell.eval place env (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
            toInput cfg { node := input_var_node } i₀ d).1.node
          from by simp only [circuit_norm]]
      exact h_output
    suffices hexact : ExactMerklePathData G Q l₀ d input_node output
        (fun j => HashLayer.leftEncoding
          ((extractWitness G Q hQ l₀ cfg.1 cfg.2.1 cfg.2.2
            i₀ ⟨place, env⟩ j).encoding))
        (fun j => HashLayer.rightEncoding
          ((extractWitness G Q hQ l₀ cfg.1 cfg.2.1 cfg.2.2
            i₀ ⟨place, env⟩ j).encoding))
        (fun j => decide
          ((extractWitness G Q hQ l₀ cfg.1 cfg.2.1 cfg.2.2
            i₀ ⟨place, env⟩ j).swap = 1)) by
      exact ⟨hexact,
        hexact.merkleRoot_and_strictOrBreak G Q hQ l₀ d input_node output _ _ _⟩
    rw [← hf0, ← hfd]
    refine ⟨fun k => (eval (⟨place, env⟩ : Placed Environment Fp)
      (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
        { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node, rfl, rfl, ?_⟩
    intro i hi
    have h := hExactStep ⟨i, hi⟩
    have hnext :
        (eval (⟨place, env⟩ : Placed Environment Fp)
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ (i + 1)).1 : Value Layer.Input Fp).node
          = eval (⟨place, env⟩ : Placed Environment Fp)
            ((layerAt G Q hQ l₀ wsib wswap i).output cfg
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ i).1
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ i).2) := by
      rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ (i + 1)).1
        = toInput ((layerAt G Q hQ l₀ wsib wswap i).output cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ i).1
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ i).2) from rfl]
      rw [input_eval_node]
      rfl
    rw [← hnext] at h
    rw [foldState_snd G Q hQ l₀ wsib wswap cfg { node := input_var_node } i₀ i] at h
    have hextract :
        (layerAt G Q hQ l₀ wsib wswap i).extract cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ i).1
          (i₀ + 8 * i) ⟨place, env⟩ =
          ({ sibling := eval (⟨place, env⟩ : Placed Environment Fp)
                (AssignedCell.of (i₀ + 8 * i) 0 cfg.1.b : Var field Fp)
             swap := eval (⟨place, env⟩ : Placed Environment Fp)
                (AssignedCell.of (i₀ + 8 * i) 0 cfg.1.swap : Var field Fp)
             encoding := (HashLayer.circuit G Q hQ ((l₀ + i) % 2 ^ 10)
                (Nat.mod_lt _ (by norm_num))).extract (cfg.2.1, cfg.2.2)
                { left := AssignedCell.of (i₀ + 8 * i) 0 cfg.1.a,
                  right := AssignedCell.of (i₀ + 8 * i) 0 cfg.1.b }
                (i₀ + 8 * i + 1) ⟨place, env⟩ } : Layer.Witness) := by
      rfl
    rw [hextract] at h
    have hswap : eval (⟨place, env⟩ : Placed Environment Fp)
        (AssignedCell.of (i₀ + 8 * i) 0 cfg.1.swap : Var field Fp)
        = env.advice cfg.1.swap ((place (i₀ + 8 * i) : ℕ) : ℤ) := by
      simp only [circuit_norm]
    rw [hswap] at h
    simpa only [ExactMerkleStep, extractWitness, circuit_norm,
      decide_eq_true_eq] using h

  completeness := by
    circuit_proof_start
    rw [FormalCircuit.foldCall_operations, FormalCircuit.foldOps_extendsWitnesses] at hwit
    set w : ℕ → Layer.Witness :=
      extractWitness G Q hQ l₀ cfg.1 cfg.2.1 cfg.2.2 i₀
        (⟨place, env.toEnvironment⟩ : Placed Environment Fp) with hw_def
    -- the per-layer extract readings ARE `w`
    have hext : ∀ k : ℕ, (layerAt G Q hQ l₀ wsib wswap k).extract cfg
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env⟩ : Placed Environment Fp)
        = w k := by
      intro k
      rw [foldState_snd G Q hQ l₀ wsib wswap cfg { node := input_var_node } i₀ k]
      with_unfolding_all rfl
    -- accumulator step landing (prover view)
    have hnodeS : ∀ k : ℕ,
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ (k + 1)).1 : Value Layer.Input Fp).node
        = (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ((layerAt G Q hQ l₀ wsib wswap k).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) : Fp) := by
      intro k
      rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ (k + 1)).1
        = toInput ((layerAt G Q hQ l₀ wsib wswap k).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) from rfl]
      rw [input_eval_node_prover]
      rfl
    -- the honest running node lands on the accumulator, layer by layer
    have hmain : ∀ k : ℕ, k ≤ d →
        ∀ n, pathNode G Q l₀ (fun j => (w j).pair) input_node k = some n →
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node = n := by
      intro k
      induction k with
      | zero =>
        intro _ n hn
        simp only [pathNode, Option.some.injEq] at hn
        rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ 0).1
          = ({ node := input_var_node } : Var Layer.Input Fp) from rfl]
        rw [input_eval_node_prover]
        rw [show (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (({ node := input_var_node } : Var Layer.Input Fp).node) : Fp)
          = AssignedCell.eval place env.toEnvironment input_var_node from by simp only [circuit_norm]]
        rw [← hn]
        exact h_input
      | succ k ih =>
        intro hk n hn
        rw [pathNode] at hn
        rcases hpk : pathNode G Q l₀ (fun j => (w j).pair) input_node k with _ | nk
        · rw [hpk] at hn; simp at hn
        rw [hpk] at hn
        simp only [Option.bind_some] at hn
        rcases hB : hashToPoint G.S Q
          (proverChunks (l₀ + k) nk (w k).pair.1 ((w k).pair.2 = 1)) with _ | B
        · rw [hB] at hn; simp at hn
        rw [hB] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        -- layer k's honest-prover precondition
        have hPAk : (layerAt G Q hQ l₀ wsib wswap k).ProverAssumptions
            (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1)
            ((layerAt G Q hQ l₀ wsib wswap k).extract cfg
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
            env.hint := by
          show ∃ B', hashToPoint G.S Q (proverChunks ((l₀ + k) % 2 ^ 10)
              ((eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node)
              ((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
              (((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 = 1)) = some B'
          rw [hext k, ih (by omega) nk hpk,
            Nat.mod_eq_of_lt (show l₀ + k < 2 ^ 10 from by omega)]
          exact ⟨B, hB⟩
        -- layer k's honest contract: the output cell is the layer hash
        have hd := SubcircuitRw.layouter_completeness_derived_placed (layerAt G Q hQ l₀ wsib wswap k) cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
          (hwit ⟨k, Nat.lt_of_succ_le hk⟩) ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial hPAk
        have hps : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ((layerAt G Q hQ l₀ wsib wswap k).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) : Fp) = B.x := by
          refine (show ∀ B' : Point Fp, hashToPoint G.S Q (proverChunks ((l₀ + k) % 2 ^ 10)
              ((eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node)
              ((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
              (((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 = 1)) = some B' →
              (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ((layerAt G Q hQ l₀ wsib wswap k).output cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) : Fp) = B'.x from hd.2) B ?_
          rw [hext k, ih (by omega) nk hpk,
            Nat.mod_eq_of_lt (show l₀ + k < 2 ^ 10 from by omega)]
          exact hB
        rw [hnodeS k, hps, hn]
    -- the honest-output landing (the strengthened `ProverSpec`), then the constraints
    refine ⟨?_, fun n hn => h_output.symm.trans
      (by with_unfolding_all exact hmain d (Nat.le_refl d) n hn)⟩
    rw [FormalCircuit.foldCall_operations, FormalCircuit.foldOps_constraints]
    -- discharge each layer's chunk
    intro i
    have hs := pathNode_isSome_le G Q l₀ (fun j => (w j).pair) input_node
      (show (↑i + 1 : ℕ) ≤ d from i.isLt) hPA
    rw [pathNode] at hs
    rcases hpk : pathNode G Q l₀ (fun j => (w j).pair) input_node ↑i with _ | nk
    · rw [hpk] at hs; simp at hs
    rw [hpk] at hs
    simp only [Option.bind_some] at hs
    rcases hB : hashToPoint G.S Q
      (proverChunks (l₀ + ↑i) nk (w ↑i).pair.1 ((w ↑i).pair.2 = 1)) with _ | B
    · rw [hB] at hs; simp at hs
    refine SubcircuitRw.layouter_completeness_leaf_placed (layerAt G Q hQ l₀ wsib wswap ↑i) cfg
      (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).2 (⟨place, env⟩ : Placed ProverEnvironment Fp)
      (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1
      (hwit i) ⟨⟨_hE.1, _hE.2.1, _hE.2.2⟩, trivial, ?_⟩
    show ∃ B', hashToPoint G.S Q (proverChunks ((l₀ + ↑i) % 2 ^ 10)
        ((eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1 : Value Layer.Input Fp).node)
        ((layerAt G Q hQ l₀ wsib wswap ↑i).extract cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
        (((layerAt G Q hQ l₀ wsib wswap ↑i).extract cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 = 1)) = some B'
    rw [hext ↑i, hmain ↑i (Nat.le_of_lt i.isLt) nk hpk,
      Nat.mod_eq_of_lt (show l₀ + (↑i : ℕ) < 2 ^ 10 from by
        have := i.isLt; omega)]
    exact ⟨B, hB⟩

/-- A calculate-root call publishes the fold's reduced synthesis summary. -/
@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq
    (config : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    (circuit G Q hQ l₀ d hld wsib wswap).elaborated.synthesisSummary
        config input region =
      synthesisSummary d config := rfl

/-- The calculate-root output column is determined by the fold shape alone. -/
@[keygen_norm, keygen_output_norm]
theorem circuit_output_column
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    ((circuit G Q hQ l₀ d hld wsib wswap).output cfg input region).cell.column =
      if d = 0 then input.node.cell.column else cfg.2.1.sinsemilla.xA := by
  unfold FormalCircuit.output ElaboratedCircuit.output circuit
  exact foldState_node_column G Q hQ l₀ wsib wswap cfg input region d

/-- The calculate-root output is the final node carried by its circuit fold. -/
@[keygen_output_norm]
theorem circuit_output_eq
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    (circuit G Q hQ l₀ d hld wsib wswap).output cfg input region =
      (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
        toInput cfg input region d).1.node := rfl

/-- Opening one calculate-root call yields the operation fold over its layers. -/
theorem circuit_call_operations_eq
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    ((circuit G Q hQ l₀ d hld wsib wswap).call cfg input).operations region =
      FormalCircuit.foldOps (layerAt G Q hQ l₀ wsib wswap)
        toInput cfg input region d := by
  rw [FormalCircuit.call_operations]
  simp only [circuit, synthesize, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil,
    FormalCircuit.foldCall_operations]

/-- A calculate-root call only copies from its input node; every later node is
assigned by an earlier layer. -/
theorem circuit_call_copyCellsAssignedFrom
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (configured : (circuit G Q hQ l₀ d hld wsib wswap).Configured cfg)
    (input : Var Layer.Input Fp) (region : RegionIndex)
    {available : List Cell} (hnode : input.node.cell ∈ available) :
    ((circuit G Q hQ l₀ d hld wsib wswap).call cfg input).operations region
      |>.CopyCellsAssignedFrom region available := by
  apply (circuit G Q hQ l₀ d hld wsib wswap).call_copyCellsAssignedFrom
    cfg configured input region
  intro cell hcell
  simp only [FormalCircuit.Configured.inputCells, circuit,
    FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
    keygenRequirements, List.mem_singleton] at hcell
  simpa only [hcell] using hnode

/-- The final node of a calculate-root fold is either its original node or was
assigned by one of the fold's layers. -/
theorem circuit_call_output_cell_mem_input_or_assigned
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    ((circuit G Q hQ l₀ d hld wsib wswap).output cfg input region).cell ∈
      [input.node.cell] ++
        ((((circuit G Q hQ l₀ d hld wsib wswap).call cfg input).operations region)
          |>.assignedCellsFrom region) := by
  rw [circuit_output_eq, circuit_call_operations_eq]
  exact
    foldState_node_cell_mem (G := G) (Q := Q) (hQ := hQ) (l₀ := l₀)
      (wsib := wsib) (wswap := wswap) cfg input region d

/-- A nonempty calculate-root fold returns a cell assigned by one of its layers. -/
theorem circuit_call_output_cell_assigned
    (cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) (hd : 0 < d) :
    ((circuit G Q hQ l₀ d hld wsib wswap).output cfg input region).cell ∈
      (((circuit G Q hQ l₀ d hld wsib wswap).call cfg input).operations region
        |>.assignedCellsFrom region) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [circuit_output_eq, circuit_call_operations_eq]
  exact foldState_succ_node_cell_mem_assigned G Q hQ l₀ wsib wswap
    cfg input region m

/-- A calculate-root fold requests exactly four deferred constants per Merkle
layer. -/
@[synthesis_summary_norm]
theorem circuit_synthesisSummary_constantSiteCount
    (config : CondSwap.Config × Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (region : RegionIndex) :
    ((circuit G Q hQ l₀ d hld wsib wswap).elaborated.synthesisSummary
      config input region).constantSiteCount = 4 * d := by
  rw [ElaboratedCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [circuit, synthesize, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil]
  rw [FormalCircuit.foldCall_synthesisSummary_constantSiteCount]
  have hround (i : Fin d) :
      ((layerAt G Q hQ l₀ wsib wswap i).elaborated.synthesisSummary
        config
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
          toInput config input region i).1
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap)
          toInput config input region i).2).constantSiteCount = 4 := by
    simp only [layerAt]
    apply Layer.circuit_synthesisSummary_constantSiteCount
  simp_rw [hround]
  simp
  omega

/-- Package the fold from the single layer-family capability it exposes. -/
def configurationCertificate
    {cfg : CondSwap.Config × Config × LookupRangeCheck.Config 10}
    {context : KeygenContext Fp}
    (layer : (layerAt G Q hQ l₀ wsib wswap 0).ConfigurationCertificate
      cfg context) :
    (circuit G Q hQ l₀ d hld wsib wswap).ConfigurationCertificate cfg context := by
  apply ((circuit G Q hQ l₀ d hld wsib wswap).configureCertificate
    cfg {} layer.configured).mono
  · intro required hrequired
    simp only [circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.delta_pure, List.append_nil] at hrequired
    exact layer.gates_of_configured required hrequired
  · intro required hrequired
    simp only [circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.delta_pure, List.append_nil] at hrequired
    exact layer.lookups_of_configured required hrequired
  · intro required hrequired
    simp only [circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.fixedColumns_pure, List.append_nil] at hrequired
    exact layer.fixedColumns_of_configured required hrequired
  · intro required hrequired
    simp only [circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, keygenRequirements,
      Configure.delta_pure, List.append_nil] at hrequired
    exact layer.permutationColumns_of_configured required hrequired

derive_contract_bridges circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
  (l₀ d : ℕ) (hld : l₀ + d ≤ 2 ^ 10) (wsib : ℕ → WitgenIR Fp 1)
  (wswap : ℕ → Placed ProverEnvironment Fp → Bool) :=
  circuit G Q hQ l₀ d hld wsib wswap

attribute [keygen_metadata_projection]
  circuit layerAt Layer.circuit HashLayer.circuit

end CalculateRoot

end Zcash.Circuits.Sinsemilla.Merkle
