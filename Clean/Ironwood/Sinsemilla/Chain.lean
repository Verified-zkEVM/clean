import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.ContractBridges
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Ecc.DoubleAndAdd
import Clean.Orchard.Sinsemilla.HVec
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece

/-!
`hash_all_pieces` (`hash_to_point.rs`:218-290) as a native variable-stride loop over the
piece list (the loop-composition restructure — `sinsemilla-loop-design.md`): one
`HashPiece.circuit` call per piece at the running offset, the piece-linking
`sinsemillaGate` at each piece's last row (rotation +1 crosses the boundary), and the
trailing dummy row (the final `y_a` materialized into `λ₁`, dummy `λ₂`/`x_p`).

Rust-faithfulness: the accumulator threads POSITIONALLY (piece `i+1`'s entering `x_a` is
piece `i`'s exit cell — same position; the entering `y_a` is a pure value thread,
`boundaryYA`, derived from the previous piece's cells — the scratch cells the old port
materialized are gone).
-/

namespace Halo2.Ironwood.Sinsemilla.Chain

open Orchard (Point)
open Orchard.Ecc (DoubleAndAddRow)
open Orchard.Ecc.DoubleAndAdd (xR yA)
open Orchard.Specs.Sinsemilla (Generators step hashToPoint)
open Orchard.Specs (K)
open Orchard.Sinsemilla (HVec)
open Halo2.Ironwood.Sinsemilla
  (GeneratorTableConfig GeneratorTableLoaded pieceWord pieceZ rowValue accAfter nextYA
   pieceWord_lt pieceZ_zero pieceZ_succ pieceZ_last chain_eq_sum piece_recombine
   chain_eq_suffix_sum step_coordinates_of_constraints step_honest accAfter_eq_chain)
open Halo2.Ironwood.Sinsemilla.HashPiece
  (Config sinsemillaGate qS3Expr yAExpr xRExpr qS2Boundary qS2Boundary_run
   State reads readState cellAt cellVec)

/-! ## Value-level chain algebra (donor-lifted, unchanged) -/

/-- Per-piece running-sum lengths: piece `i` of width `nᵢ` produces `nᵢ + 1` running-sum cells
(`z₀..z_{nᵢ}`). Donor `Chain.zLengths`. -/
def zLengths (ns : List ℕ) : List ℕ := ns.map (· + 1)

/-- The entering accumulator `2·y` of a level, as derived by the preceding gate from the level's
first row: the `Y_A` expression for in-message rows, twice the witnessed `y_a` cell (held in `λ₁`)
for the final dummy row. Donor `Chain.enterYA`. -/
def enterYA {F : Type} [Add F] [Sub F] [Mul F] [OfNat F 2]
    (isFinal : Bool) (row : DoubleAndAddRow F) : F :=
  if isFinal then 2 * row.lambda1 else yA row

/-- The pieces decompose into the given flat chunk list (`K`-bit words, little-endian within each
piece, `ns[i] + 1` words for piece `i`). Donor `Chain.PieceChunks`. -/
def PieceChunks : (ns : List ℕ) → Vector Fp ns.length → List ℕ → Prop
  | [], _, chunks => chunks = []
  | n :: rest, pieces, chunks => ∃ ms : ℕ → ℕ,
      (∀ r, ms r < 2 ^ K) ∧
      pieces[0] = ((∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
      ∃ tailChunks, chunks = (List.range (n + 1)).map ms ++ tailChunks ∧
        PieceChunks rest pieces.tail tailChunks

/-- The honest chunk values of the pieces. Donor `Chain.honestChunks`. -/
def honestChunks : (ns : List ℕ) → Vector Fp ns.length → List ℕ
  | [], _ => []
  | n :: rest, pieces =>
    (List.range (n + 1)).map (pieceWord pieces[0]) ++ honestChunks rest pieces.tail

/-- Each piece value fits in `K·(ns[i] + 1)` bits. Donor `Chain.PieceBounds`. -/
def PieceBounds : (ns : List ℕ) → Vector Fp ns.length → Prop
  | [], _ => True
  | n :: rest, pieces =>
    ZMod.val pieces[0] < 2 ^ (K * (n + 1)) ∧
      PieceBounds rest pieces.tail

/-- The honest chunk values realize `PieceChunks` when the pieces are in range (each piece is the
recombination of its `K`-bit words). Donor `Chain.pieceChunks_honestChunks`. -/
theorem pieceChunks_honestChunks : (ns : List ℕ) → (pieces : Vector Fp ns.length) →
    PieceBounds ns pieces → PieceChunks ns pieces (honestChunks ns pieces)
  | [], _, _ => rfl
  | n :: rest, pieces, hbounds => by
    obtain ⟨hb0, hbrest⟩ := hbounds
    refine ⟨pieceWord pieces[0], fun r => pieceWord_lt _ _, ?_,
      honestChunks rest pieces.tail, rfl, pieceChunks_honestChunks rest pieces.tail hbrest⟩
    exact piece_recombine pieces[0] (n + 1) hb0

/-- Every chunk is a valid generator index. Donor `Chain.pieceChunks_bound`. -/
theorem pieceChunks_bound {ns : List ℕ} {pieces : Vector Fp ns.length}
    {chunks : List ℕ} (h : PieceChunks ns pieces chunks) :
    ∀ m ∈ chunks, m < 2 ^ K := by
  induction ns generalizing chunks with
  | nil =>
      intro m hm
      simp only [PieceChunks] at h
      subst h
      simp at hm
  | cons n rest ih =>
      simp only [PieceChunks] at h
      obtain ⟨ms, hms, _, tailChunks, hchunks, htail⟩ := h
      intro m hm
      rw [hchunks] at hm
      simp only [List.mem_append, List.mem_map, List.mem_range] at hm
      rcases hm with ⟨r, hr, rfl⟩ | hm
      · exact hms r
      · exact ih htail m hm

/-- Each exposed running-sum vector is the per-row suffix recombination of its piece's chunks
(anchored to the same flat chunk list as `PieceChunks`). Donor `Chain.ZsFacts`. -/
def ZsFacts : (ns : List ℕ) → List ℕ → HVec (zLengths ns) Fp → Prop
  | [], _, _ => True
  | n :: rest, chunks, zs =>
    HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) =>
      ((∑ j ∈ Finset.range (n + 1 - r.val),
        chunks.getD (r.val + j) 0 * 2 ^ (K * j) : ℕ) : Fp)) ∧
      ZsFacts rest (chunks.drop (n + 1)) (HVec.tail zs)

/-- The honest running-sum vectors: each piece's vector holds `z₀..z_{nᵢ}`. Donor `Chain.ZsHonest`. -/
def ZsHonest : (ns : List ℕ) → Vector Fp ns.length → HVec (zLengths ns) Fp → Prop
  | [], _, _ => True
  | n :: rest, pieces, zs =>
    HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) => pieceZ pieces[0] r.val) ∧
      ZsHonest rest pieces.tail (HVec.tail zs)

/-- `ZsFacts` introduction at a `cons` (stated abstractly — unfolding `ZsFacts` on a large
concrete running-sum term whnf-explodes; this lemma unfolds it once, on abstract arguments). -/
theorem zsFacts_cons {n : ℕ} {rest : List ℕ} (chunks : List ℕ)
    (hd : Vector Fp (n + 1)) (tl : HVec (zLengths rest) Fp)
    (h1 : hd = Vector.ofFn (fun r : Fin (n + 1) =>
      ((∑ j ∈ Finset.range (n + 1 - r.val), chunks.getD (r.val + j) 0 * 2 ^ (K * j) : ℕ) : Fp)))
    (h2 : ZsFacts rest (chunks.drop (n + 1)) tl) :
    ZsFacts (n :: rest) chunks (HVec.cons hd tl : HVec (zLengths (n :: rest)) Fp) := by
  simp only [ZsFacts, HVec.head_cons]
  exact ⟨h1, (HVec.tail_cons hd tl).symm ▸ h2⟩

/-- A head-piece chunk index resolves to its word value. Donor `Chain.chunks_head_getD`. -/
theorem chunks_head_getD {n : ℕ} (ms : ℕ → ℕ) (tailChunks : List ℕ) (k : ℕ) (hk : k < n + 1) :
    ((List.range (n + 1)).map ms ++ tailChunks).getD k 0 = ms k := by
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-- The chunk tail after a head piece. Donor `Chain.chunks_drop_append`. -/
theorem chunks_drop_append {n : ℕ} (ms : ℕ → ℕ) (tailChunks : List ℕ) :
    ((List.range (n + 1)).map ms ++ tailChunks).drop (n + 1) = tailChunks :=
  List.drop_left' (by simp)

/-! ## Inputs / Output (region-level, whole message)

The message pieces are the only verifier-visible inputs: the entering accumulator is
positional (`x_a` at the chain's first row) and the entering `y` a derivation program —
matching Rust, where `hash_all_pieces` receives the init's `X`/`Y` and never copies. -/

/-- Verifier-visible inputs of the whole chain: the piece values. -/
structure Inputs (len : ℕ) (F : Type) where
  pieces : Vector F len
deriving ProvableStruct

/-- Outputs: the hash point, the message's first double-and-add row (the init gate /
`Spec` anchor), and the full per-piece running sums `zs`. -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  first : DoubleAndAddRow F
  zs : HVec (zLengths ns) F
deriving ProvableStruct

/-- The honest accumulator after hashing the whole suffix `ns` starting from `(x, y)`. Each piece
of width `n` advances the accumulator by `accAfter G · piece (n+1)`. -/
def chainAcc (G : Generators) : (ns : List ℕ) → Vector Fp ns.length → Fp × Fp → Fp × Fp
  | [], _, acc => acc
  | n :: rest, pieces, acc =>
    chainAcc G rest pieces.tail (accAfter G acc pieces[0] (n + 1))

/-! ## The loop body plumbing -/

/-- Rows occupied by the first `i` pieces: `Σ_{j<i} (ns_j + 1)`. -/
def prefixRows (ns : List ℕ) (i : ℕ) : ℕ := ((ns.take i).map (· + 1)).sum

@[simp] theorem prefixRows_zero (ns : List ℕ) : prefixRows ns 0 = 0 := rfl

theorem prefixRows_succ (n : ℕ) (rest : List ℕ) (i : ℕ) :
    prefixRows (n :: rest) (i + 1) = (n + 1) + prefixRows rest i := by
  simp [prefixRows, List.take_succ_cons]

/-- The boundary entering-`y` value: the previous piece's exit `y`, derived from its last
row and the next row's `x_a` (`y_exit = nextYA / 2`) — Rust's `Y<Value>` thread, positional. -/
def boundaryYA (last : DoubleAndAddRow (AssignedCell Fp)) (xNext : AssignedCell Fp) :
    Placed Environment Fp → Fp := fun env =>
  nextYA { xA := last.xA.eval env.place env.env, xP := last.xP.eval env.place env.env,
           lambda1 := last.lambda1.eval env.place env.env,
           lambda2 := last.lambda2.eval env.place env.env }
    (xNext.eval env.place env.env) * (2 : Fp)⁻¹

/-- The trailing dummy row's `λ₁` witness: the final `y_a` (Rust `hash_all_pieces`
post-loop). -/
def finalYAWit (last : DoubleAndAddRow (AssignedCell Fp)) (xNext : AssignedCell Fp) :
    WitgenIR Fp 1 :=
  .native fun env => #v[boundaryYA last xNext env.toEnvironment]

@[circuit_norm]
theorem finalYAWit_eval (last : DoubleAndAddRow (AssignedCell Fp)) (xNext : AssignedCell Fp)
    (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((finalYAWit last xNext).eval env)[j] = boundaryYA last xNext env.toEnvironment := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [finalYAWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Constant-zero witness (the dummy `λ₂`/`x_p` cells of the trailing row). -/
def zeroWit : WitgenIR Fp 1 := .native fun _ => #v[(0 : Fp)]

@[circuit_norm]
theorem zeroWit_eval (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    (zeroWit.eval env)[j] = 0 := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [zeroWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The positional running-sum cells of the whole message: piece `i`'s `nsᵢ + 1` cells in
the `bits` column, starting at its base row. -/
def zsCellsVal (cfg : Config) (self : RegionIndex) :
    (ns : List ℕ) → (off : ℕ) → HVec (zLengths ns) (AssignedCell Fp)
  | [], _ => HVec.nil
  | n :: rest, off =>
    (HVec.cons (Vector.ofFn fun r : Fin (n + 1) => .of self (off + r.val) cfg.bits)
      (zsCellsVal cfg self rest (off + (n + 1))) : HVec (zLengths (n :: rest)) _)

/-- Name the running-sum cells (no ops emitted). -/
def zsCells (cfg : Config) (ns : List ℕ) (off : ℕ) :
    RegionCircuit Fp (HVec (zLengths ns) (AssignedCell Fp)) :=
  fun self => (zsCellsVal cfg self ns off, [])

@[circuit_norm]
theorem operations_zsCells (cfg : Config) (ns : List ℕ) (off : ℕ) (self : RegionIndex) :
    (zsCells cfg ns off).operations self = [] := rfl

@[circuit_norm]
theorem output_zsCells (cfg : Config) (ns : List ℕ) (off : ℕ) (self : RegionIndex) :
    (zsCells cfg ns off).output self = zsCellsVal cfg self ns off := rfl

-- contract bridges for the piece child (opened by the chain's proofs)
derive_contract_bridges pieceC (G : Generators) (n : ℕ) (b : Bool)
  (ya : Placed Environment Fp → Fp) := HashPiece.circuit G n b ya

/-- One piece's slot of the chain loop, at piece index `i` and base row `base` (top-level
def — the outer peel keeps it folded; the per-slot reduction unfolds it selectively).
`prev`/`xEnter` name the boundary cells for the entering-`y` derivation (junk reads at
`i = 0`, where `yaIn` is used instead). -/
def pieceSlot (G : Generators) (ns : List ℕ) (yaIn : Placed Environment Fp → Fp)
    (cfg : Config) (pieces : Vector (AssignedCell Fp) ns.length) (i base : ℕ) :
    RegionCircuit Fp Unit := do
  let prev ← readState cfg (base - 1)
  let xEnter ← cellAt cfg.xA base
  let _ ← (HashPiece.circuit G (ns.getD i 0) (decide (i = ns.length - 1))
      (if i = 0 then yaIn else boundaryYA prev.row xEnter)).call cfg base (pieces[i]!)
  let _q ← assignFixed cfg.qS2 (base + ns.getD i 0)
    (qS2Boundary (decide (i = ns.length - 1)))
  (sinsemillaGate cfg).enable (base + ns.getD i 0)

/-! ## The chain contract -/

/-- The chain `Spec` (donor `Chain.Spec`), verifier view, anchored on the first row
(positional — no input accumulator cells). -/
def Spec (G : Generators) (ns : List ℕ) (input : Value (Inputs ns.length) Fp)
    (output : Value (Output ns) Fp) : Prop :=
  ∃ chunks : List ℕ, PieceChunks ns input.pieces chunks ∧
    ZsFacts ns chunks output.zs ∧
    ∀ A : Point Fp, A.OnCurve → A.x = output.first.xA →
      2 * A.y = enterYA ns.isEmpty output.first →
      ∀ B, hashToPoint G.S A chunks = some B →
        output.point.x = B.x ∧ output.point.y = B.y

/-- The honest-prover precondition: pieces in range and the honest chain from the
entering accumulator (the `Witness` pair — positional `x_a`, `yaIn` value) defined. -/
def ProverAssumptions (G : Generators) (ns : List ℕ)
    (input : Value (Inputs ns.length) Fp) (wit : Fp × Fp) : Prop :=
  PieceBounds ns input.pieces ∧
  ∃ A B : Point Fp, A.OnCurve ∧ A.x = wit.1 ∧ A.y = wit.2 ∧
    hashToPoint G.S A (honestChunks ns input.pieces) = some B

/-- The honest-prover contract: the hash point is the honest chain point, and the first
row's `enterYA` derivation is `2·y_enter` (what a composing init gate consumes). -/
def ProverSpec (G : Generators) (ns : List ℕ) (input : Value (Inputs ns.length) Fp)
    (output : Value (Output ns) Fp) (wit : Fp × Fp) : Prop :=
  ∀ A B : Point Fp, A.x = wit.1 → A.y = wit.2 →
    hashToPoint G.S A (honestChunks ns input.pieces) = some B →
    output.point.x = B.x ∧ output.point.y = B.y ∧
    enterYA ns.isEmpty output.first = 2 * A.y

theorem soundness_aux (G : Generators) (n : ℕ) (isFinal : Bool)
    (ms : ℕ → ℕ) (hms : ∀ r, ms r < 2 ^ K)
    {first last tailFirst : DoubleAndAddRow Fp} {xAin : Fp}
    (hlast_xP : last.xP = (G.S (ms n)).x)
    (hlast_yp : yA last * (2 : Fp)⁻¹ - last.lambda1 * (last.xA - last.xP) = (G.S (ms n)).y)
    (hchain_piece : ∀ A : Point Fp, A.OnCurve → A.x = xAin →
      2 * A.y = yA first →
      ∀ B, hashToPoint G.S A ((List.range n).map ms) = some B →
        last.xA = B.x ∧ 2 * B.y = yA last)
    -- the linking gate's secant + y-check equations (from `sinsemillaGate` at the link row)
    (hsec : last.lambda2 * last.lambda2 = tailFirst.xA + xR last + last.xA)
    (hyck : 4 * last.lambda2 * (last.xA - tailFirst.xA)
      = 2 * yA last + 2 * enterYA isFinal tailFirst)
    {xATail : Fp} (htfxA : tailFirst.xA = xATail)
    (tailChunks : List ℕ) {pointX pointY : Fp}
    (htail_chain : ∀ A : Point Fp, A.OnCurve → A.x = xATail →
      2 * A.y = enterYA isFinal tailFirst →
      ∀ B, hashToPoint G.S A tailChunks = some B →
        pointX = B.x ∧ pointY = B.y) :
    ∀ A : Point Fp, A.OnCurve → A.x = xAin →
      2 * A.y = yA first →
      ∀ B, hashToPoint G.S A ((List.range (n + 1)).map ms ++ tailChunks) = some B →
        pointX = B.x ∧ pointY = B.y := by
  intro A hAon hAx hAyA B hB
  have hAvalid : A.Valid := Or.inl hAon
  have hA0 : A ≠ 0 := Orchard.Point.ne_zero_of_onCurve hAon
  rw [Orchard.Specs.Sinsemilla.hashToPoint_append] at hB
  cases hpre : hashToPoint G.S A ((List.range (n + 1)).map ms) with
  | none => rw [hpre] at hB; simp at hB
  | some B₁ =>
    rw [hpre] at hB
    replace hB : hashToPoint G.S B₁ tailChunks = some B := hB
    rw [List.range_succ] at hpre
    simp only [List.map_append, List.map_cons, List.map_nil] at hpre
    rw [Orchard.Specs.Sinsemilla.hashToPoint_concat] at hpre
    cases hpre0 : hashToPoint G.S A ((List.range n).map ms) with
    | none => rw [hpre0] at hpre; simp at hpre
    | some B₀ =>
      rw [hpre0] at hpre
      replace hpre : step G.S (ms n) B₀ = some B₁ := hpre
      obtain ⟨hlast_xA, hlast_yA⟩ := hchain_piece A hAon hAx hAyA B₀ hpre0
      have hlast_yA' := hlast_yA
      simp only [yA, xR] at hlast_yA'
      have hsec' := hsec
      simp only [xR] at hsec'
      -- clear the halving in the `y_p` derivation
      have hlast_yp2 : yA last - 2 * (last.lambda1 * (last.xA - last.xP)) = 2 * (G.S (ms n)).y := by
        have h2 := congrArg (fun t => 2 * t) hlast_yp
        simp only [mul_sub] at h2
        rw [show (2 : Fp) * (yA last * (2 : Fp)⁻¹) = yA last from by
          rw [mul_comm (yA last), ← mul_assoc, mul_inv_cancel₀ (by decide : (2 : Fp) ≠ 0),
            one_mul]] at h2
        linear_combination h2
      have hpin := step_coordinates_of_constraints G.S hpre
        (xp := last.xP) (lambda1 := last.lambda1) (lambda2 := last.lambda2)
        (xa' := tailFirst.xA) (YA' := enterYA isFinal tailFirst)
        (by linear_combination hlast_yp2 + hlast_yA + 2 * last.lambda1 * hlast_xA)
        hlast_xP
        (by linear_combination hlast_yA' + 2 * (last.lambda1 + last.lambda2) * hlast_xA)
        (by linear_combination hsec')
        (by linear_combination hyck - 4 * last.lambda2 * hlast_xA - 2 * hlast_yA)
      have hB₀valid : B₀.Valid :=
        Orchard.Specs.Sinsemilla.hashToPoint_valid hAvalid
          (fun m hm => by
            rcases List.mem_map.mp hm with ⟨r, hr, rfl⟩
            exact hms r)
          hpre0
      have hB₁valid : B₁.Valid :=
        Orchard.Specs.Sinsemilla.step_valid hB₀valid (hms n) hpre
      have hB₁0 : B₁ ≠ 0 :=
        Orchard.Specs.Sinsemilla.step_ne_zero hB₀valid (hms n) hpre
      have hB₁on : B₁.OnCurve := by
        rcases hB₁valid with h | h
        · exact h
        · exact False.elim (hB₁0 h)
      exact htail_chain B₁ hB₁on (hpin.1.symm.trans htfxA) hpin.2.symm B hB

/-- The gate's y-check RHS at the boundary `q_s2` value reduces to `2·enterYA` of the next row
(donor `Cons.gate_yRhs_enterYA`): `q_s3 = 0` between pieces selects the next row's `Y_A`,
`q_s3 = 2` on the final piece selects twice the witnessed `y_a` in `λ₁`. -/
private theorem qS3_yRhs (b : Bool) (row : DoubleAndAddRow Fp) :
    (2 - qS2Boundary b * (qS2Boundary b - 1)) * yA row
      + qS2Boundary b * (qS2Boundary b - 1) * 2 * row.lambda1
    = 2 * enterYA b row := by
  cases b
  · simp only [enterYA, HashPiece.qS2Boundary, Bool.false_eq_true, if_false]
    ring
  · simp only [enterYA, HashPiece.qS2Boundary, if_true]
    norm_num
    ring

/-! ## The bundle -/

def circuit (G : Generators) (ns : List ℕ) (yaIn : Placed Environment Fp → Fp) :
    FormalRegionCircuit Fp Config Config (Inputs ns.length) (Output ns) where
  name := "sinsemilla hash_all_pieces"
  configure := pure

  synthesize cfg offset (input : Var (Inputs ns.length) Fp) := do
    RegionCircuit.forRangeVar' (fun i => offset + prefixRows ns i) ns.length
      (pieceSlot G ns yaIn cfg input.pieces)
    -- the trailing dummy row: the final `y_a` into `λ₁`, dummy `λ₂`/`x_p`
    let ex ← readState cfg (offset + prefixRows ns ns.length - 1)
    let xExit ← cellAt cfg.xA (offset + prefixRows ns ns.length)
    let yFin ← assignAdvice cfg.lambda1 (offset + prefixRows ns ns.length)
      (finalYAWit ex.row xExit)
    let _l2d ← assignAdvice cfg.lambda2 (offset + prefixRows ns ns.length) zeroWit
    let _xpd ← assignAdvice cfg.xP (offset + prefixRows ns ns.length) zeroWit
    let first ← readState cfg offset
    let zs ← zsCells cfg ns offset
    return { point := { x := xExit, y := yFin }, first := first.row, zs }

  Witness := fieldPair
  extract cfg offset _ self env :=
    (eval env (AssignedCell.of self offset cfg.xA : Var field Fp), yaIn env)

  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env

  Spec input output _ := Spec G ns input output
  ProverAssumptions input wit _ := ProverAssumptions G ns input wit
  ProverSpec input output wit _ := ProverSpec G ns input output wit

  soundness := by
    -- ENGINE WALL (recorded in sinsemilla-loop-design.md): the heterogeneous piece call
    -- (child output type `HashPiece.Output (ns.getD i 0 + 1)` depends on the loop index)
    -- times out `circuit_proof_start`/the peel at whnf. Plan: wrap each slot as a
    -- Unit-output FormalRegionCircuit family (`slot i` — positional contract over its
    -- Witness readings, the `round i` pattern at piece scale) so the loop is homogeneous.
    sorry

  completeness := by
    sorry

end Halo2.Ironwood.Sinsemilla.Chain
