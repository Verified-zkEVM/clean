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

  elaborated := {}

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
    simp only [RegionCircuit.operations, RegionCircuit.output, circuit_norm]
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
      -- the chain's entering row, concretized (position-determined cells)
      have hfirst : (ProvableStruct.Halo2.eval place env out_first)
          = ({ xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
               xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
               lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
               lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) }
             : Ecc.DoubleAndAddRow Fp) := by
        rw [show out_first = ((Sinsemilla.Chain.circuit G ns fun x => Q_y).output cfg
            offset input_var self).first from by rw [out_eq]]
        with_unfolding_all rfl
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
      exact hres

  completeness := by
    circuit_proof_start2 [Sinsemilla.HashPiece.initialYQGate,
      Sinsemilla.HashPiece.yAExpr, Sinsemilla.HashPiece.xRExpr]
    obtain ⟨-, hbounds, B0, hchain0⟩ := prover_assumptions
    -- the raw z1s-naming step: no ops, output = the named cell vector
    simp only [RegionCircuit.operations, RegionCircuit.output, circuit_norm]
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
      -- the chain's entering row, concretized (position-determined cells)
      have hfirst : (ProvableStruct.Halo2.eval place env.toEnvironment out_first)
          = ({ xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
               xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
               lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
               lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) }
             : Ecc.DoubleAndAddRow Fp) := by
        rw [show out_first = ((Sinsemilla.Chain.circuit G ns fun x => Q_y).output cfg
            offset input_var self).first from by rw [out_eq]]
        with_unfolding_all rfl
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

end Zcash.Circuits.Sinsemilla.HashToPoint
