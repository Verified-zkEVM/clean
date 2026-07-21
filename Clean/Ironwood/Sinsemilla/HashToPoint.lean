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

namespace Halo2.Ironwood.Sinsemilla.HashToPoint

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Specs.Sinsemilla (Generators)

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

/-! ## The layouter-level `hash_message`

The formal wrapper is `(hashRegion …).toFormal` (below); `hashMessage` is its `.call`. -/

/-! ## The formal `hash_message` bundle

The region-level Q-pin wrapper over `Chain.circuit`: the `public_q_initialization` ops pin
the entering accumulator to the public `Q` (the constant copy fixes `x_a(0) = Q.x`; the
`Initial y_Q` gate fixes `Y_A(0) = 2·Q.y`), so the chain's `∀ A`-quantified contract
collapses to the hash from `Q`. `toFormal "hash_to_point"` lifts it to the layouter level
(one region — the Rust `hash_to_point` `assign_region`). -/

open Halo2.Ironwood.Sinsemilla.Chain in
/-- The per-piece `z_1` values off the chain's running-sum extraction data (`HVec` is
stored flat; piece `i`'s `z_1` sits at flat index `prefixRows ns i + 1`). -/
def z1View (ns : List ℕ) (zs : Halo2.Ironwood.Sinsemilla.HVec (zLengths ns) Fp) :
    Vector Fp ns.length :=
  Vector.ofFn fun i : Fin ns.length => zs.elems[prefixRows ns ↑i + 1]!

open Halo2.Ironwood.Sinsemilla.Chain in
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

open Halo2.Ironwood.Sinsemilla.Chain in
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
    ∀ B, Halo2.Ironwood.Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output.point.x = B.x ∧ output.point.y = B.y

/-- The honest-prover precondition: nonempty message, pieces in range, honest hash defined. -/
def ProverAssumptions (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp) : Prop :=
  ns ≠ [] ∧ Sinsemilla.Chain.PieceBounds ns input.pieces ∧
  ∃ B, Halo2.Ironwood.Specs.Sinsemilla.hashToPoint G.S Q
    (Sinsemilla.Chain.honestChunks ns input.pieces) = some B

/-- The honest-prover contract: the output point is the honest hash. -/
def ProverSpec (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
    (output : Value (Output ns.length) Fp) : Prop :=
  ∀ B, Halo2.Ironwood.Specs.Sinsemilla.hashToPoint G.S Q
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
  rw [ProvableStruct.eval_cells_eq_eval]
  rw [show ProvableStruct.eval env.place env.env
      ({ point := p, z1s := v } : Output k (AssignedCell Fp))
    = ({ point := ProvableType.eval env.place env.env p,
         z1s := ProvableType.eval (M := fields k) env.place env.env v }
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
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  rw [show ProvableStruct.eval env.place env.env.toEnvironment
      ({ point := p, z1s := v } : Output k (AssignedCell Fp))
    = ({ point := ProvableType.eval env.place env.env.toEnvironment p,
         z1s := ProvableType.eval (M := fields k) env.place env.env.toEnvironment v }
        : Value (Output k) Fp) from by rfl]
  rw [show p = ({ x := p.x, y := p.y } : Point (AssignedCell Fp)) from rfl,
    Sinsemilla.Chain.point_eval_literal, Sinsemilla.Chain.eval_fields_eq_map]

/-- The elaborated instance of the `hash_message` region body (explicit — `soundness` must
not elaborate with metavariables). -/
instance hashRegionElaborated (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (cfg : Sinsemilla.HashPiece.Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp (Sinsemilla.Chain.Inputs ns.length) (Output ns.length)
      (fun pieces => do
        (Sinsemilla.HashPiece.initialYQGate cfg).enable offset
        let _yq ← assignFixed cfg.fixedYQ offset Q.y
        let xa ← assignAdvice cfg.xA offset (constWit Q.x)
        constrainConstant xa Q.x
        let out ← (Sinsemilla.Chain.circuit G ns (fun _ => Q.y)).call cfg offset pieces
        let z1s ← (fun self =>
          (Vector.ofFn (fun i : Fin ns.length =>
            AssignedCell.of self (offset + Sinsemilla.Chain.prefixRows ns ↑i + 1) cfg.bits),
           ([] : RegionOperations Fp)))
        pure ({ point := out.point, z1s := z1s } : Output ns.length (AssignedCell Fp))) := {}

/-- The `hash_message` region bundle (public `Q`): `public_q_initialization` + the chain.
`hns`: a Sinsemilla message is nonempty (for `ns = []` the trailing dummy row's `λ₁` is
unconstrained, so the exit `y` would be unpinned). -/
def hashRegion (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) :
    FormalRegionCircuit Fp Sinsemilla.HashPiece.Config Sinsemilla.HashPiece.Config
      (Sinsemilla.Chain.Inputs ns.length) (Output ns.length) where
  name := "hash_to_point"
  configure := pure

  synthesize cfg offset (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) := do
    -- public_q_initialization
    (Sinsemilla.HashPiece.initialYQGate cfg).enable offset
    let _yq ← assignFixed cfg.fixedYQ offset Q.y
    let xa ← assignAdvice cfg.xA offset (constWit Q.x)
    constrainConstant xa Q.x
    -- hash_all_pieces
    let out ← (Sinsemilla.Chain.circuit G ns (fun _ => Q.y)).call cfg offset pieces
    -- name the z_1 cells (no ops)
    let z1s ← (fun self =>
      (Vector.ofFn (fun i : Fin ns.length =>
        AssignedCell.of self (offset + Sinsemilla.Chain.prefixRows ns ↑i + 1) cfg.bits),
       ([] : RegionOperations Fp)))
    pure ({ point := out.point, z1s := z1s } : Output ns.length (AssignedCell Fp))

  elaborated cfg offset := hashRegionElaborated G ns Q cfg offset

  Witness := Sinsemilla.Chain.ChainWit ns
  extract cfg offset input self env :=
    (Sinsemilla.Chain.circuit G ns (fun _ => Q.y)).extract cfg offset input self env

  EnvAssumptions cfg env :=
    Halo2.Ironwood.Sinsemilla.GeneratorTableLoaded G cfg.generatorTable env.env

  Spec input output wit := Spec G ns Q input output wit
  ProverAssumptions input _ _ := ProverAssumptions G ns Q input
  ProverSpec input output _ _ := ProverSpec G ns Q input output

  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE hA hc
    simp only [RegionCircuit.operations_bind, RegionOperations.constraints_append,
      operations_enable, operations_assignFixed, operations_assignAdvice,
      operations_constrainConstant] at hc
    subcircuit_rw at hc
    simp only [chainC_spec_eq, chainC_assumptions_eq, chainC_envAssumptions_eq,
      Sinsemilla.HashPiece.initialYQGate, Sinsemilla.HashPiece.yAExpr,
      Sinsemilla.HashPiece.xRExpr, Constraints.withSelector, circuit_norm] at hc
    obtain ⟨hGate, hYQ, hXa, hChain, -⟩ := hc
    have hSpec := hChain _hE
    rw [← ProvableStruct.eval_cells_eq_eval env
        ((Sinsemilla.Chain.circuit G ns fun _ => Q.y).output cfg offset input_var self),
      Sinsemilla.Chain.circuit_output_eval] at hSpec
    obtain ⟨chunks, hPC, hZs, hContract⟩ := hSpec
    have hin : ProvableStruct.eval env.place env.env input_var = input := by
      rw [← h_input, ProvableStruct.eval_cells_eq_eval]
    rw [hin] at hPC
    -- land our output on its literal
    rw [ElaboratedRegionCircuit.output_eq] at h_output
    simp only [RegionCircuit.output_bind, RegionCircuit.output_pure] at h_output
    rw [out_eval_lit,
      FormalRegionCircuit.output_call (Sinsemilla.Chain.circuit G ns fun _ => Q.y) cfg offset
        input_var self,
      Sinsemilla.Chain.output_point_x, Sinsemilla.Chain.output_point_y] at h_output
    simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice] at h_output
    refine ⟨chunks, hPC, hZs, ?_, ?_⟩
    · -- the z_1 view of the running sums
      intro hpos
      rw [← h_output]
      show (Vector.ofFn fun i : Fin ns.length =>
          AssignedCell.of self (offset + Sinsemilla.Chain.prefixRows ns ↑i + 1) cfg.bits).map
            (AssignedCell.eval env.place env.env)
        = z1View ns ((Sinsemilla.Chain.circuit G ns fun _ => Q.y).extract cfg offset
            input_var self env).zs
      rw [show ((Sinsemilla.Chain.circuit G ns fun _ => Q.y).extract cfg offset
            input_var self env).zs
          = eval env (Sinsemilla.Chain.zsCellsVal cfg self ns offset) from rfl,
        Sinsemilla.Chain.eval_zsCellsVal, z1View_zsFam _ _ _ hpos]
      ext j hj
      simp only [Vector.getElem_map, Vector.getElem_ofFn, AssignedCell.eval,
        AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
        Environment.get_advice]
      congr 2
    · -- the hash from `Q`
      intro B hB
      have hres := hContract Q hQ hXa.symm (by
        rw [show ns.isEmpty = false from by
          cases ns with
          | nil => exact absurd rfl hns
          | cons a l => rfl]
        show 2 * Q.y = Halo2.Ironwood.Ecc.DoubleAndAdd.yA _
        simp only [Halo2.Ironwood.Ecc.DoubleAndAdd.yA, Halo2.Ironwood.Ecc.DoubleAndAdd.xR]
        linear_combination hGate - 2 * hYQ) B hB
      rw [← h_output]
      exact hres

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [RegionCircuit.operations_bind, RegionOperations.extendsWitnesses_append,
      operations_enable, operations_assignFixed, operations_assignAdvice,
      operations_constrainConstant, circuit_norm] at hwit
    obtain ⟨hWyq, hWxa, hWchain, -⟩ := hwit
    obtain ⟨-, hbounds, B0, hchain0⟩ := hPA
    have hxa_eval : (eval env.toEnvironment
        (AssignedCell.of self offset cfg.xA : Var field Fp) : Fp)
        = env.env.advice cfg.xA ((env.place self + offset : ℕ) : ℤ) := by
      simp only [circuit_norm]
    have hPAchain : (Sinsemilla.Chain.circuit G ns fun _ => Q.y).ProverAssumptions
        (eval env input_var)
        ((Sinsemilla.Chain.circuit G ns fun _ => Q.y).extract cfg offset input_var self
          env.toEnvironment) env.env.hint := by
      rw [chainC_proverAssumptions_eq]
      show Sinsemilla.Chain.ProverAssumptions G ns (eval env input_var) _
      rw [h_input]
      refine ⟨hns, hbounds, Q, B0, hQ, ?_, rfl, hchain0⟩
      show Q.x = (eval env.toEnvironment
        (AssignedCell.of self offset cfg.xA : Var field Fp) : Fp)
      rw [hxa_eval, hWxa]
    have hder := Halo2.SubcircuitRw.region_completeness_derived_placed
      (Sinsemilla.Chain.circuit G ns fun _ => Q.y) cfg offset self env input_var hWchain
      (by rw [chainC_envAssumptions_eq]; exact _hE) trivial hPAchain
    rw [chainC_proverSpec_eq] at hder
    have hPSchain : Sinsemilla.Chain.ProverSpec G ns input
        (eval env ((Sinsemilla.Chain.circuit G ns fun _ => Q.y).output cfg offset
          input_var self))
        ((Sinsemilla.Chain.circuit G ns fun _ => Q.y).extract cfg offset input_var self
          env.toEnvironment) := by
      rw [← h_input]
      exact hder.2
    have hfacts := hPSchain Q B0 (by
        show Q.x = (eval env.toEnvironment
          (AssignedCell.of self offset cfg.xA : Var field Fp) : Fp)
        rw [hxa_eval, hWxa]) rfl hchain0
    rw [Sinsemilla.Chain.circuit_output_eval_prover] at hfacts
    obtain ⟨hpx, hpy, henter⟩ := hfacts
    -- land our own output
    rw [ElaboratedRegionCircuit.output_eq] at h_output
    simp only [RegionCircuit.output_bind, RegionCircuit.output_pure] at h_output
    rw [out_eval_lit_prover,
      FormalRegionCircuit.output_call (Sinsemilla.Chain.circuit G ns fun _ => Q.y) cfg offset
        input_var self,
      Sinsemilla.Chain.output_point_x, Sinsemilla.Chain.output_point_y] at h_output
    simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice] at h_output
    refine ⟨?_, ?_⟩
    · -- the constraints
      simp only [RegionCircuit.operations_bind, RegionOperations.constraints_append,
        operations_enable, operations_assignFixed, operations_assignAdvice,
        operations_constrainConstant]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- the Initial y_Q gate at the entering row
        simp only [Sinsemilla.HashPiece.initialYQGate, Sinsemilla.HashPiece.yAExpr,
          Sinsemilla.HashPiece.xRExpr, Constraints.withSelector, circuit_norm]
        rw [show ns.isEmpty = false from by
            cases ns with
            | nil => exact absurd rfl hns
            | cons a l => rfl] at henter
        simp only [Sinsemilla.Chain.enterYA, Bool.false_eq_true, if_false,
          Halo2.Ironwood.Ecc.DoubleAndAdd.yA, Halo2.Ironwood.Ecc.DoubleAndAdd.xR] at henter
        linear_combination 2 * hWyq - henter
      · -- the fixed y_Q load
        simp only [circuit_norm]
        exact hWyq
      · -- assignAdvice emits no constraint
        simp only [circuit_norm]
      · -- the x_a constant
        simp only [circuit_norm]
        exact hWxa
      · -- the chain child, via the engine leaf
        exact Halo2.SubcircuitRw.region_completeness_leaf_placed
          (Sinsemilla.Chain.circuit G ns fun _ => Q.y) cfg offset self env input_var
          hWchain ⟨by rw [chainC_envAssumptions_eq]; exact _hE, trivial, hPAchain⟩
      · -- no ops
        trivial
      · -- pure emits no constraints
        trivial
    · -- the honest-prover contract
      intro B hB
      have hBB : B0 = B := Option.some.inj (hchain0.symm.trans hB)
      rw [← h_output, ← hBB]
      exact ⟨hpx, hpy⟩

/-- The layouter-level `hash_message` bundle: the `"hash_to_point"` region (Rust
`SinsemillaChip::hash_to_point`). -/
def hashCircuit (G : Generators) (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) :
    FormalCircuit Fp Sinsemilla.HashPiece.Config Sinsemilla.HashPiece.Config
      (Sinsemilla.Chain.Inputs ns.length) (Output ns.length) :=
  (hashRegion G ns Q hQ hns).toFormal

/-- Call the hash bundle (Rust `hash_to_point` at a layouter). -/
def hashMessage (G : Generators) (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) :
    Circuit Fp (Var (Output ns.length) Fp) :=
  (hashCircuit G ns Q hQ hns).call cfg pieces

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
      = AssignedCell.of i (0 + Sinsemilla.Chain.prefixRows ns ns.length) cfg.xA := by
  show (((Sinsemilla.Chain.circuit G ns fun _ => Q.y).call cfg 0 pieces).output i).point.x = _
  rw [FormalRegionCircuit.output_call, Sinsemilla.Chain.output_point_x]

/-- The hash bundle's output `point.y` cell (positional, rfl). -/
theorem hashCircuit_output_point_y (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Sinsemilla.HashPiece.Config)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) (i : RegionIndex) :
    ((hashCircuit G ns Q hQ hns).output cfg pieces i).point.y
      = AssignedCell.of i (0 + Sinsemilla.Chain.prefixRows ns ns.length) cfg.lambda1 := by
  show (((Sinsemilla.Chain.circuit G ns fun _ => Q.y).call cfg 0 pieces).output i).point.y = _
  rw [FormalRegionCircuit.output_call, Sinsemilla.Chain.output_point_y]

/-- The hash bundle's output record, reassembled from its cell projections (was a `rfl`; under
full-`call` opacity the child point cells no longer reduce through the output walk, so we rebuild
from `hashCircuit_output_point_x`/`_y`/`_z1s`). -/
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
        : Output ns.length (AssignedCell Fp)) := by
  rw [← hashCircuit_output_point_x G ns Q hQ hns cfg pieces i,
    ← hashCircuit_output_point_y G ns Q hQ hns cfg pieces i,
    ← hashCircuit_output_z1s G ns Q hQ hns cfg pieces i]
  rfl

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

end Halo2.Ironwood.Sinsemilla.HashToPoint
