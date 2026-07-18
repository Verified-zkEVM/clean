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

/-- Outputs: the hash point and the message's first double-and-add row (the init gate /
`Spec` anchor). The per-piece running sums are NOT output data: they are extraction
data — `ChainWit.zs` in the `Witness` slot (which never routes through the eval-of-var
machinery, so its list-indexed `HVec` shape is harmless) — and consumers read the `z`
CELLS positionally (the `zs[i][1]` reads of Merkle/NoteCommit). -/
structure Output (F : Type) where
  point : Point F
  first : DoubleAndAddRow F
deriving ProvableStruct

/-- The chain's extraction data: the entering accumulator (positional `x_a`, the `yaIn`
value) and the running sums of every piece. -/
structure ChainWit (ns : List ℕ) (F : Type) where
  xIn : F
  yIn : F
  zs : HVec (zLengths ns) F

instance {ns : List ℕ} : Inhabited (ChainWit ns Fp) :=
  ⟨{ xIn := 0, yIn := 0, zs := default }⟩

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

/-- Step the prefix-row count at an in-range index. -/
theorem prefixRows_step (ns : List ℕ) (m : ℕ) (hm : m < ns.length) :
    prefixRows ns (m + 1) = prefixRows ns m + (ns.getD m 0 + 1) := by
  induction ns generalizing m with
  | nil => simp at hm
  | cons n rest ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp [prefixRows_succ, prefixRows_zero]
    · have hm' : m - 1 < rest.length := by
        simp at hm
        omega
      rw [show m = (m - 1) + 1 from by omega]
      rw [prefixRows_succ, prefixRows_succ, ih (m - 1) hm']
      rw [show (n :: rest).getD ((m - 1) + 1) 0 = rest.getD (m - 1) 0 from rfl]
      omega

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

/-- The slot's positional neighborhood: the previous row (the preceding piece's last row
— the boundary-`y` derivation's cells; junk for slot 0), the piece's first row, its
`n + 1` running-sum cells, and the next row (the following piece's first row / the
trailing dummy row — the linking gate's rotation-+1 reads). -/
structure SlotReads (m : ℕ) (F : Type) where
  prev : DoubleAndAddRow F
  first : DoubleAndAddRow F
  last : DoubleAndAddRow F
  zs : Vector F m
  next : DoubleAndAddRow F
  /-- The entering-`y` VALUE (the `yaIn`/boundary derivation — `extract` computes it;
  the cell-record `slotReads` fills a junk cell, never read). -/
  yIn : F
deriving ProvableStruct

/-- The slot's neighborhood cells at base row `base` (piece width `n`). -/
def slotReads (cfg : Config) (n base : ℕ) (self : RegionIndex) :
    SlotReads (n + 1) (AssignedCell Fp) where
  prev := { xA := .of self (base - 1) cfg.xA, xP := .of self (base - 1) cfg.xP,
            lambda1 := .of self (base - 1) cfg.lambda1,
            lambda2 := .of self (base - 1) cfg.lambda2 }
  first := { xA := .of self base cfg.xA, xP := .of self base cfg.xP,
             lambda1 := .of self base cfg.lambda1, lambda2 := .of self base cfg.lambda2 }
  last := { xA := .of self (base + n) cfg.xA, xP := .of self (base + n) cfg.xP,
            lambda1 := .of self (base + n) cfg.lambda1,
            lambda2 := .of self (base + n) cfg.lambda2 }
  zs := Vector.ofFn fun r : Fin (n + 1) => .of self (base + r.val) cfg.bits
  next := { xA := .of self (base + n + 1) cfg.xA, xP := .of self (base + n + 1) cfg.xP,
            lambda1 := .of self (base + n + 1) cfg.lambda1,
            lambda2 := .of self (base + n + 1) cfg.lambda2 }
  yIn := .of self base cfg.xA

/-- The slot's entering-`y` value over its neighborhood: the chain's `yaIn` program for
slot 0, the positional boundary derivation otherwise. -/
def slotEnterY {m : ℕ} (yaIn : Placed Environment Fp → Fp) (i : ℕ) (w : SlotReads m Fp)
    (env : Placed Environment Fp) : Fp :=
  if i = 0 then yaIn env else nextYA w.prev w.first.xA * (2 : Fp)⁻¹

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

/-- The linking gate completes the piece's last word: from the piece's prefix contract
(its last row anchors the `n`-word chain) and the boundary gate's secant/y-check, the
*next* row anchors the `(n+1)`-word chain (the `soundness_aux` core, tail-free). -/
private theorem link_step (G : Generators) (n : ℕ) (isFinal : Bool) (ms : ℕ → ℕ)
    {first last next : DoubleAndAddRow Fp}
    (hlast_xP : last.xP = (G.S (ms n)).x)
    (hlast_yp : yA last * (2 : Fp)⁻¹ - last.lambda1 * (last.xA - last.xP) = (G.S (ms n)).y)
    (hchain_piece : ∀ A : Point Fp, A.OnCurve → A.x = first.xA → 2 * A.y = yA first →
      ∀ B, hashToPoint G.S A ((List.range n).map ms) = some B →
        last.xA = B.x ∧ 2 * B.y = yA last)
    (hsec : last.lambda2 * last.lambda2 = next.xA + xR last + last.xA)
    (hyck : 4 * last.lambda2 * (last.xA - next.xA)
      = 2 * yA last + 2 * enterYA isFinal next) :
    ∀ A : Point Fp, A.OnCurve → A.x = first.xA → 2 * A.y = yA first →
      ∀ B, hashToPoint G.S A ((List.range (n + 1)).map ms) = some B →
        next.xA = B.x ∧ 2 * B.y = enterYA isFinal next := by
  intro A hAon hAx hAyA B hB
  obtain ⟨B0, hB0⟩ := Halo2.Ironwood.Sinsemilla.HashPiece.range_prefix_some G.S A ms hB
    (show n ≤ n + 1 by omega)
  have hstep : step G.S (ms n) B0 = some B :=
    Halo2.Ironwood.Sinsemilla.HashPiece.prefix_step_some G.S A ms hB0 hB
  obtain ⟨hlast_xA, hlast_yA⟩ := hchain_piece A hAon hAx hAyA B0 hB0
  have hlast_yA' := hlast_yA
  simp only [yA, xR] at hlast_yA'
  have hsec' := hsec
  simp only [xR] at hsec'
  have hlast_yp2 : yA last - 2 * (last.lambda1 * (last.xA - last.xP))
      = 2 * (G.S (ms n)).y := by
    have h2 := congrArg (fun t => 2 * t) hlast_yp
    simp only [mul_sub] at h2
    rw [show (2 : Fp) * (yA last * (2 : Fp)⁻¹) = yA last from by
      rw [mul_comm (yA last), ← mul_assoc, mul_inv_cancel₀ (by decide : (2 : Fp) ≠ 0),
        one_mul]] at h2
    linear_combination h2
  have hpin := step_coordinates_of_constraints G.S hstep
    (xp := last.xP) (lambda1 := last.lambda1) (lambda2 := last.lambda2)
    (xa' := next.xA) (YA' := enterYA isFinal next)
    (by linear_combination hlast_yp2 + hlast_yA + 2 * last.lambda1 * hlast_xA)
    hlast_xP
    (by linear_combination hlast_yA' + 2 * (last.lambda1 + last.lambda2) * hlast_xA)
    (by linear_combination hsec')
    (by linear_combination hyck - 4 * last.lambda2 * hlast_xA - 2 * hlast_yA)
  exact ⟨hpin.1, hpin.2.symm⟩

/-- The slot's piece contract, positional (the donor `HashPiece.Spec` over the slot's
neighborhood; the linking gate is chain-owned, so the chain completes the last word via
`link_step`). -/
def SlotSpec (G : Generators) (n : ℕ) (piece : Fp) (w : SlotReads (n + 1) Fp) : Prop :=
  ∃ ms : ℕ → ℕ,
    (∀ r, ms r < 2 ^ K) ∧
    piece = ((∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
    w.zs = Vector.ofFn (fun r : Fin (n + 1) =>
      ((∑ j ∈ Finset.range (n + 1 - r.val), ms (r.val + j) * 2 ^ (K * j) : ℕ) : Fp)) ∧
    w.last.xP = (G.S (ms n)).x ∧
    yA w.last * (2 : Fp)⁻¹ - w.last.lambda1 * (w.last.xA - w.last.xP) = (G.S (ms n)).y ∧
    ∀ A : Point Fp, A.OnCurve → A.x = w.first.xA → 2 * A.y = yA w.first →
      ∀ B, hashToPoint G.S A ((List.range n).map ms) = some B →
        w.last.xA = B.x ∧ 2 * B.y = yA w.last

/-- The slot's honest-prover precondition. -/
def SlotPA (G : Generators) (n : ℕ) (piece : Fp) (w : SlotReads (n + 1) Fp) : Prop :=
  piece.val < 2 ^ (K * (n + 1)) ∧
  ∃ A B : Point Fp, A.OnCurve ∧ A.x = w.first.xA ∧ A.y = w.yIn ∧
    hashToPoint G.S A ((List.range (n + 1)).map (pieceWord piece)) = some B

/-- The slot's honest-prover contract (the piece's, positionally). -/
def SlotPS (G : Generators) (n : ℕ) (piece : Fp) (w : SlotReads (n + 1) Fp) : Prop :=
  ∀ A B : Point Fp, A.x = w.first.xA → A.y = w.yIn →
    hashToPoint G.S A ((List.range (n + 1)).map (pieceWord piece)) = some B →
    yA w.first = 2 * A.y ∧ w.next.xA = B.x ∧
    w.last.lambda2 * w.last.lambda2 = w.next.xA + xR w.last + w.last.xA ∧
    2 * w.last.lambda2 * (w.last.xA - w.next.xA) - yA w.last = 2 * B.y

/-- One piece slot as a `Unit`-output formal circuit (the loop stays homogeneous — the
piece call's width-dependent output lives inside this bundle). Slot `i` of the width list
`ns`: the `HashPiece` call at its own base row, the boundary `q_s2` re-pin, and the
piece-linking `sinsemillaGate` at its last row. -/
def slot (G : Generators) (ns : List ℕ) (yaIn : Placed Environment Fp → Fp) (i : ℕ) :
    FormalRegionCircuit Fp Config Config field unit where
  configure := pure

  synthesize cfg base (piece : AssignedCell Fp) := do
    let prev ← readState cfg (base - 1)
    let xEnter ← cellAt cfg.xA base
    let _ ← (HashPiece.circuit G (ns.getD i 0) (decide (i = ns.length - 1))
        (if i = 0 then yaIn else boundaryYA prev.row xEnter)).call cfg base piece
    pure ()

  Witness := SlotReads (ns.getD i 0 + 1)
  extract cfg base _ self env :=
    { eval env (slotReads cfg (ns.getD i 0) base self) with
      yIn := if i = 0 then yaIn env
        else boundaryYA (slotReads cfg (ns.getD i 0) base self).prev
          (AssignedCell.of self base cfg.xA) env }

  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env

  Spec piece _ w := SlotSpec G (ns.getD i 0) piece w
  ProverAssumptions piece w _ := SlotPA G (ns.getD i 0) piece w
  ProverSpec piece _ w _ := SlotPS G (ns.getD i 0) piece w

  soundness := by
    circuit_proof_start [slotReads, SlotSpec]
    rw [pieceC_envAssumptions_eq, pieceC_assumptions_eq, pieceC_spec_eq] at hc
    simp only [HashPiece.Spec, circuit_norm] at hc
    obtain ⟨ms, hms, hrecomb, hzs, hlxP, hlyP, hchainP⟩ := hc _hE
    refine ⟨ms, hms, ?_, hzs, hlxP, hlyP, hchainP⟩
    have hgi : (eval (⟨place, env⟩ : Placed Environment Fp) input_var : Fp)
        = env.get input_var.cell.column
          ((place input_var.cell.regionIndex + input_var.cell.rowOffset : ℕ) : ℤ) := by
      with_unfolding_all rfl
    rw [← h_input, hgi]
    exact hrecomb

  completeness := by
    circuit_proof_start [slotReads, SlotPA, SlotPS]
    obtain ⟨hbound, A, B, hAon, hAx, hAy, hchain⟩ := hPA
    rw [pieceC_envAssumptions_eq, pieceC_assumptions_eq, pieceC_proverAssumptions_eq,
      pieceC_extract_eq] at h_spec_0
    have hCPA : HashPiece.ProverAssumptions G (ns.getD i 0)
        (env.get input_var.cell.column
          ((place input_var.cell.regionIndex + input_var.cell.rowOffset : ℕ) : ℤ))
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of self offset cfg.xA : Var field Fp),
          (if i = 0 then yaIn
            else boundaryYA (reads cfg (offset - 1) self).row
              (AssignedCell.of self offset cfg.xA)) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)) := by
      rw [h_input]
      refine ⟨hbound, A, B, hAon, ?_, ?_, hchain⟩
      · rw [hAx]
        with_unfolding_all rfl
      · rw [hAy]
        by_cases hi : i = 0 <;> simp [hi, reads]
    have hsp := h_spec_0 _hE trivial hCPA
    rw [pieceC_proverSpec_eq] at hsp
    simp only [HashPiece.ProverSpec, circuit_norm] at hsp
    obtain ⟨-, hPS⟩ := hsp
    refine ⟨⟨_hE, trivial, ?_⟩, ?_⟩
    · rw [pieceC_proverAssumptions_eq, pieceC_extract_eq]
      rw [h_input] at hCPA
      exact hCPA
    · -- the slot's ProverSpec, off the child's
      intro A' B' hA'x hA'y hchain'
      have hres := hPS A' B'
        (by rw [hA'x]; try with_unfolding_all rfl)
        (by rw [hA'y]; by_cases hi : i = 0 <;> simp [hi, reads])
        (by rw [h_input]; exact hchain')
      exact hres

/-! Contract bridges for the slot child (hand-written rfl — `derive_contract_bridges`
chokes on the function-typed `yaIn` binder). -/

private theorem slotC_spec_eq (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (i : ℕ) :
    (slot G ns yaIn i).Spec = fun piece _ w => SlotSpec G (ns.getD i 0) piece w := rfl

private theorem slotC_assumptions_eq (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (i : ℕ) :
    (slot G ns yaIn i).Assumptions = fun _ => True := rfl

private theorem slotC_envAssumptions_eq (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (i : ℕ) (cfg : Config)
    (env : Placed Environment Fp) :
    (slot G ns yaIn i).EnvAssumptions cfg env
      = GeneratorTableLoaded G cfg.generatorTable env.env := rfl

private theorem slotC_proverAssumptions_eq (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (i : ℕ) :
    (slot G ns yaIn i).ProverAssumptions
      = fun piece w _ => SlotPA G (ns.getD i 0) piece w := rfl

private theorem slotC_proverSpec_eq (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (i : ℕ) :
    (slot G ns yaIn i).ProverSpec
      = fun piece _ w _ => SlotPS G (ns.getD i 0) piece w := rfl

private theorem slotC_extract_eq (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (i : ℕ) (cfg : Config) (base : ℕ)
    (iv : AssignedCell Fp) (self : RegionIndex) (env : Placed Environment Fp) :
    (slot G ns yaIn i).extract cfg base iv self env
      = { eval env (slotReads cfg (ns.getD i 0) base self) with
          yIn := if i = 0 then yaIn env
            else boundaryYA (slotReads cfg (ns.getD i 0) base self).prev
              (AssignedCell.of self base cfg.xA) env } := rfl

/-! ## Value-level families for the chain induction -/

/-- The flat chunk list of the per-piece word families, pieces indexed from `i0`. -/
def chunksOf (msF : ℕ → ℕ → ℕ) : (ns : List ℕ) → (i0 : ℕ) → List ℕ
  | [], _ => []
  | n :: rest, i0 => (List.range (n + 1)).map (msF i0) ++ chunksOf msF rest (i0 + 1)

/-- The running-sum family as a per-piece `HVec` (piece `i`'s `nᵢ + 1` values from its
base row). -/
def zsFam (zV : ℕ → Fp) : (ns : List ℕ) → (base : ℕ) → HVec (zLengths ns) Fp
  | [], _ => HVec.nil
  | n :: rest, base =>
    (HVec.cons (Vector.ofFn fun r : Fin (n + 1) => zV (base + r.val))
      (zsFam zV rest (base + (n + 1))) : HVec (zLengths (n :: rest)) _)

/-- `zsFam`'s head vector (the first piece's running sums). -/
theorem zsFam_head (zV : ℕ → Fp) (n : ℕ) (rest : List ℕ) (base : ℕ) :
    Orchard.Sinsemilla.HVec.head (zsFam zV (n :: rest) base)
      = Vector.ofFn (fun r : Fin (n + 1) => zV (base + r.val)) :=
  Orchard.Sinsemilla.HVec.head_cons _ _

/-- `zsFam`'s tail (the remaining pieces' running sums). -/
theorem zsFam_tail (zV : ℕ → Fp) (n : ℕ) (rest : List ℕ) (base : ℕ) :
    Orchard.Sinsemilla.HVec.tail (zsFam zV (n :: rest) base)
      = zsFam zV rest (base + (n + 1)) :=
  Orchard.Sinsemilla.HVec.tail_cons _ _

/-- `zsFam`'s second piece's running sums (the composed tail-head view). -/
theorem zsFam_tail_head (zV : ℕ → Fp) (n m : ℕ) (rest : List ℕ) (base : ℕ) :
    Orchard.Sinsemilla.HVec.head
        (Orchard.Sinsemilla.HVec.tail (zsFam zV (n :: m :: rest) base))
      = Vector.ofFn (fun r : Fin (m + 1) => zV (base + (n + 1) + r.val)) :=
  (congrArg Orchard.Sinsemilla.HVec.head (zsFam_tail zV n (m :: rest) base)).trans
    (zsFam_head zV m rest (base + (n + 1)))

/-- Flat eval of a `fields`-vector of cells is the pointwise cell eval. -/
theorem eval_fields_eq_map (place : RegionIndex → ℕ) (env : Environment Fp) {k : ℕ}
    (v : Vector (AssignedCell Fp) k) :
    ProvableType.eval (M := fields k) place env v = v.map (AssignedCell.eval place env) := by
  simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements]

/-- Flat eval distributes over `HVec.cons`. -/
private theorem hvec_eval_cons (place : RegionIndex → ℕ) (env : Environment Fp)
    {n : ℕ} {ls : List ℕ}
    (a : Vector (AssignedCell Fp) n) (b : HVec ls (AssignedCell Fp)) :
    ProvableType.eval (M := HVec (n :: ls)) place env (HVec.cons a b)
      = HVec.cons (ProvableType.eval (M := fields n) place env a)
          (ProvableType.eval (M := HVec ls) place env b) := by
  simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements,
    HVec.cons]
  exact congrArg HVec.mk (Vector.map_append ..)

/-- `hvec_eval_cons` at the `zLengths (n :: rest)` spelling (keyed matching does not
unfold `zLengths`). -/
theorem hvec_eval_cons_zl (place : RegionIndex → ℕ) (env : Environment Fp)
    {n : ℕ} {rest : List ℕ}
    (a : Vector (AssignedCell Fp) (n + 1)) (b : HVec (zLengths rest) (AssignedCell Fp)) :
    ProvableType.eval (M := HVec (zLengths (n :: rest))) place env (HVec.cons a b)
      = HVec.cons (ProvableType.eval (M := fields (n + 1)) place env a)
          (ProvableType.eval (M := HVec (zLengths rest)) place env b) :=
  hvec_eval_cons place env a b

/-- The flat eval of the positional running-sum cells is the `zsFam` family. -/
private theorem eval_zsCellsVal_flat (cfg : Config) (self : RegionIndex)
    (env : Placed Environment Fp) :
    ∀ (ns : List ℕ) (off : ℕ),
      ProvableType.eval (M := HVec (zLengths ns)) env.place env.env
          (zsCellsVal cfg self ns off)
        = zsFam (fun r => env.env.advice cfg.bits ((env.place self + r : ℕ) : ℤ)) ns off := by
  intro ns
  induction ns with
  | nil =>
    intro off
    with_unfolding_all rfl
  | cons n rest ih =>
    intro off
    rw [show zsCellsVal cfg self (n :: rest) off
        = (HVec.cons (Vector.ofFn fun r : Fin (n + 1) => .of self (off + r.val) cfg.bits)
            (zsCellsVal cfg self rest (off + (n + 1)))
          : HVec (zLengths (n :: rest)) _) from rfl]
    rw [hvec_eval_cons_zl]
    rw [show zsFam (fun r => env.env.advice cfg.bits ((env.place self + r : ℕ) : ℤ))
          (n :: rest) off
        = (HVec.cons (Vector.ofFn fun r : Fin (n + 1) =>
              env.env.advice cfg.bits ((env.place self + (off + r.val) : ℕ) : ℤ))
            (zsFam (fun r => env.env.advice cfg.bits ((env.place self + r : ℕ) : ℤ)) rest
              (off + (n + 1))) : HVec (zLengths (n :: rest)) Fp) from rfl]
    congr 1
    · rw [eval_fields_eq_map]
      apply Vector.ext
      intro r hr
      simp [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice]
    · exact ih (off + (n + 1))

/-- The `Eval`-head version of `eval_zsCellsVal_flat`. -/
theorem eval_zsCellsVal (cfg : Config) (self : RegionIndex)
    (env : Placed Environment Fp) (ns : List ℕ) (off : ℕ) :
    (eval env (zsCellsVal cfg self ns off) : HVec (zLengths ns) Fp)
      = zsFam (fun r => env.env.advice cfg.bits ((env.place self + r : ℕ) : ℤ)) ns off := by
  rw [ProvableType.eval_cells (M := HVec (zLengths ns))]
  exact eval_zsCellsVal_flat cfg self env ns off

/-! ## The chain contract -/

/-- The chain `Spec` (donor `Chain.Spec`), verifier view, anchored on the first row
(positional — no input accumulator cells); the running-sum facts are stated on the
extraction data. -/
def Spec (G : Generators) (ns : List ℕ) (input : Value (Inputs ns.length) Fp)
    (output : Value Output Fp) (wit : ChainWit ns Fp) : Prop :=
  ∃ chunks : List ℕ, PieceChunks ns input.pieces chunks ∧
    ZsFacts ns chunks wit.zs ∧
    ∀ A : Point Fp, A.OnCurve → A.x = output.first.xA →
      2 * A.y = enterYA ns.isEmpty output.first →
      ∀ B, hashToPoint G.S A chunks = some B →
        output.point.x = B.x ∧ output.point.y = B.y

/-- The honest-prover precondition: pieces in range and the honest chain from the
entering accumulator (the `Witness` pair — positional `x_a`, `yaIn` value) defined. -/
def ProverAssumptions (G : Generators) (ns : List ℕ)
    (input : Value (Inputs ns.length) Fp) (wit : ChainWit ns Fp) : Prop :=
  ns ≠ [] ∧ PieceBounds ns input.pieces ∧
  ∃ A B : Point Fp, A.OnCurve ∧ A.x = wit.xIn ∧ A.y = wit.yIn ∧
    hashToPoint G.S A (honestChunks ns input.pieces) = some B

/-- The honest-prover contract: the hash point is the honest chain point, and the first
row's `enterYA` derivation is `2·y_enter` (what a composing init gate consumes). -/
def ProverSpec (G : Generators) (ns : List ℕ) (input : Value (Inputs ns.length) Fp)
    (output : Value Output Fp) (wit : ChainWit ns Fp) : Prop :=
  ∀ A B : Point Fp, A.x = wit.xIn → A.y = wit.yIn →
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

/-- Literal-eval bridges for the output record, at the `ProvableStruct`/`ProvableType`
eval heads (the old-Chain-proven shape; the `Eval`-head spelling is bridged by a manual
`ProvableStruct.eval_cells_eq_eval` rw at the reduced literal). -/
private theorem output_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    (p : Point (AssignedCell Fp)) (f : DoubleAndAddRow (AssignedCell Fp)) :
    ProvableStruct.eval place env ({ point := p, first := f } : Output (AssignedCell Fp))
      = { point := ProvableType.eval place env p, first := ProvableType.eval place env f } := by
  with_unfolding_all rfl

theorem point_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    (a b : AssignedCell Fp) :
    ProvableType.eval place env ({ x := a, y := b } : Point (AssignedCell Fp))
      = { x := AssignedCell.eval place env a, y := AssignedCell.eval place env b } := by
  with_unfolding_all rfl

private theorem row_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    (a b c d : AssignedCell Fp) :
    ProvableType.eval place env ({ xA := a, xP := b, lambda1 := c, lambda2 := d }
        : DoubleAndAddRow (AssignedCell Fp))
      = { xA := AssignedCell.eval place env a, xP := AssignedCell.eval place env b,
          lambda1 := AssignedCell.eval place env c,
          lambda2 := AssignedCell.eval place env d } := by
  rw [ProvableStruct.eval_eq_eval]
  with_unfolding_all rfl

theorem inputs_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    {k : ℕ} (p : Vector (AssignedCell Fp) k) :
    ProvableStruct.eval place env ({ pieces := p } : Inputs k (AssignedCell Fp))
      = { pieces := ProvableType.eval (M := fields k) place env p } := by
  with_unfolding_all rfl

private theorem slotReads_eval_literal (env : Placed Environment Fp) {m : ℕ}
    (p f l : DoubleAndAddRow (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) m)
    (nx : DoubleAndAddRow (AssignedCell Fp)) (y : AssignedCell Fp) :
    (eval env ({ prev := p, first := f, last := l, zs := zs, next := nx, yIn := y }
        : SlotReads m (AssignedCell Fp)) : SlotReads m Fp)
      = { prev := ProvableType.eval env.place env.env p,
          first := ProvableType.eval env.place env.env f,
          last := ProvableType.eval env.place env.env l,
          zs := ProvableType.eval (M := fields m) env.place env.env zs,
          next := ProvableType.eval env.place env.env nx,
          yIn := AssignedCell.eval env.place env.env y } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

/-- The flattened eval of the slot neighborhood (all cells named, rows explicit). -/
private theorem slotReads_eval (env : Placed Environment Fp) (cfg : Config) (n base : ℕ)
    (self : RegionIndex) :
    (eval env (slotReads cfg n base self) : SlotReads (n + 1) Fp)
      = { prev :=
            { xA := AssignedCell.eval env.place env.env (.of self (base - 1) cfg.xA),
              xP := AssignedCell.eval env.place env.env (.of self (base - 1) cfg.xP),
              lambda1 := AssignedCell.eval env.place env.env (.of self (base - 1) cfg.lambda1),
              lambda2 := AssignedCell.eval env.place env.env (.of self (base - 1) cfg.lambda2) },
          first :=
            { xA := AssignedCell.eval env.place env.env (.of self base cfg.xA),
              xP := AssignedCell.eval env.place env.env (.of self base cfg.xP),
              lambda1 := AssignedCell.eval env.place env.env (.of self base cfg.lambda1),
              lambda2 := AssignedCell.eval env.place env.env (.of self base cfg.lambda2) },
          last :=
            { xA := AssignedCell.eval env.place env.env (.of self (base + n) cfg.xA),
              xP := AssignedCell.eval env.place env.env (.of self (base + n) cfg.xP),
              lambda1 := AssignedCell.eval env.place env.env (.of self (base + n) cfg.lambda1),
              lambda2 := AssignedCell.eval env.place env.env (.of self (base + n) cfg.lambda2) },
          zs := (Vector.ofFn (fun r : Fin (n + 1) => .of self (base + r.val) cfg.bits)).map
            (AssignedCell.eval env.place env.env),
          next :=
            { xA := AssignedCell.eval env.place env.env (.of self (base + n + 1) cfg.xA),
              xP := AssignedCell.eval env.place env.env (.of self (base + n + 1) cfg.xP),
              lambda1 := AssignedCell.eval env.place env.env
                (.of self (base + n + 1) cfg.lambda1),
              lambda2 := AssignedCell.eval env.place env.env
                (.of self (base + n + 1) cfg.lambda2) },
          yIn := AssignedCell.eval env.place env.env (.of self base cfg.xA) } := by
  rw [show slotReads cfg n base self
      = ({ prev :=
              { xA := .of self (base - 1) cfg.xA, xP := .of self (base - 1) cfg.xP,
                lambda1 := .of self (base - 1) cfg.lambda1,
                lambda2 := .of self (base - 1) cfg.lambda2 },
           first :=
              { xA := .of self base cfg.xA, xP := .of self base cfg.xP,
                lambda1 := .of self base cfg.lambda1, lambda2 := .of self base cfg.lambda2 },
           last :=
              { xA := .of self (base + n) cfg.xA, xP := .of self (base + n) cfg.xP,
                lambda1 := .of self (base + n) cfg.lambda1,
                lambda2 := .of self (base + n) cfg.lambda2 },
           zs := Vector.ofFn (fun r : Fin (n + 1) => .of self (base + r.val) cfg.bits),
           next :=
              { xA := .of self (base + n + 1) cfg.xA, xP := .of self (base + n + 1) cfg.xP,
                lambda1 := .of self (base + n + 1) cfg.lambda1,
                lambda2 := .of self (base + n + 1) cfg.lambda2 },
           yIn := .of self base cfg.xA } : SlotReads (n + 1) (AssignedCell Fp)) from rfl,
    slotReads_eval_literal]
  rw [row_eval_literal, row_eval_literal, row_eval_literal, row_eval_literal,
    eval_fields_eq_map]

/-- Prover-side field-cell eval, in the `AssignedCell.eval` spelling. -/
private theorem eval_field_cell (env : Placed ProverEnvironment Fp) (c : AssignedCell Fp) :
    (eval env (c : Var field Fp) : Fp)
      = AssignedCell.eval env.place env.env.toEnvironment c := by
  with_unfolding_all rfl

/-- The chain induction over abstract row/sum families: per-piece slot contracts and the
per-boundary linking gates fold into the whole-message chain contract. Pieces indexed
from `i0` (of `N` total — the final boundary flag), rows from `base`. The exit anchor is
the trailing row: its `x_a` cell and (via the final gate's `enterYA true`) its `λ₁`. -/
private theorem chain_fold (G : Generators) (N : ℕ)
    (dR : ℕ → DoubleAndAddRow Fp) (zV : ℕ → Fp) (msF : ℕ → ℕ → ℕ)
    (hms : ∀ j r, msF j r < 2 ^ K) :
    ∀ (ns : List ℕ) (i0 base : ℕ) (pieces : Vector Fp ns.length),
    i0 + ns.length = N →
    (∀ j : Fin ns.length,
      pieces[j] = ((∑ r ∈ Finset.range (ns.getD j.val 0 + 1),
          msF (i0 + j.val) r * 2 ^ (K * r) : ℕ) : Fp) ∧
      (∀ r : Fin (ns.getD j.val 0 + 1),
        zV (base + prefixRows ns j.val + r.val)
          = ((∑ t ∈ Finset.range (ns.getD j.val 0 + 1 - r.val),
              msF (i0 + j.val) (r.val + t) * 2 ^ (K * t) : ℕ) : Fp)) ∧
      (dR (base + prefixRows ns j.val + ns.getD j.val 0)).xP
        = (G.S (msF (i0 + j.val) (ns.getD j.val 0))).x ∧
      yA (dR (base + prefixRows ns j.val + ns.getD j.val 0)) * (2 : Fp)⁻¹
        - (dR (base + prefixRows ns j.val + ns.getD j.val 0)).lambda1
          * ((dR (base + prefixRows ns j.val + ns.getD j.val 0)).xA
            - (dR (base + prefixRows ns j.val + ns.getD j.val 0)).xP)
        = (G.S (msF (i0 + j.val) (ns.getD j.val 0))).y ∧
      (∀ A : Point Fp, A.OnCurve → A.x = (dR (base + prefixRows ns j.val)).xA →
        2 * A.y = yA (dR (base + prefixRows ns j.val)) →
        ∀ B, hashToPoint G.S A
            ((List.range (ns.getD j.val 0)).map (msF (i0 + j.val))) = some B →
          (dR (base + prefixRows ns j.val + ns.getD j.val 0)).xA = B.x ∧
          2 * B.y = yA (dR (base + prefixRows ns j.val + ns.getD j.val 0)))) →
    (∀ j : Fin ns.length,
      (dR (base + prefixRows ns j.val + ns.getD j.val 0)).lambda2
          * (dR (base + prefixRows ns j.val + ns.getD j.val 0)).lambda2
        = (dR (base + prefixRows ns j.val + ns.getD j.val 0 + 1)).xA
          + xR (dR (base + prefixRows ns j.val + ns.getD j.val 0))
          + (dR (base + prefixRows ns j.val + ns.getD j.val 0)).xA ∧
      4 * (dR (base + prefixRows ns j.val + ns.getD j.val 0)).lambda2
          * ((dR (base + prefixRows ns j.val + ns.getD j.val 0)).xA
            - (dR (base + prefixRows ns j.val + ns.getD j.val 0 + 1)).xA)
        = 2 * yA (dR (base + prefixRows ns j.val + ns.getD j.val 0))
          + 2 * enterYA (decide (i0 + j.val = N - 1))
              (dR (base + prefixRows ns j.val + ns.getD j.val 0 + 1))) →
    PieceChunks ns pieces (chunksOf msF ns i0) ∧
    ZsFacts ns (chunksOf msF ns i0) (zsFam zV ns base) ∧
    (∀ A : Point Fp, A.OnCurve → A.x = (dR base).xA →
      2 * A.y = enterYA ns.isEmpty (dR base) →
      ∀ B, hashToPoint G.S A (chunksOf msF ns i0) = some B →
        (dR (base + prefixRows ns ns.length)).xA = B.x ∧
        (dR (base + prefixRows ns ns.length)).lambda1 = B.y) := by
  intro ns
  induction ns with
  | nil =>
    intro i0 base pieces hN hSlots hGates
    refine ⟨rfl, trivial, ?_⟩
    intro A hAon hAx hAyA B hB
    rw [show chunksOf msF [] i0 = [] from rfl,
      Orchard.Specs.Sinsemilla.hashToPoint_nil] at hB
    obtain rfl : A = B := Option.some.inj hB
    simp only [List.isEmpty_nil, enterYA, if_true] at hAyA
    refine ⟨?_, ?_⟩
    · simpa using hAx.symm
    · have h2 : (2 : Fp) ≠ 0 := by decide
      have := mul_left_cancel₀ h2 hAyA
      simpa using this.symm
  | cons n rest ih =>
    intro i0 base pieces hN hSlots hGates
    have hlen : rest.length + 1 = (n :: rest).length := rfl
    -- head facts (piece index 0 → rows base..base+n)
    have h0 := hSlots ⟨0, by simp⟩
    simp only [prefixRows_zero, Nat.add_zero, List.getD_cons_zero, Fin.getElem_fin] at h0
    obtain ⟨hrec0, hzs0, hxP0, hyP0, hchain0⟩ := h0
    have hg0 := hGates ⟨0, by simp⟩
    simp only [prefixRows_zero, Nat.add_zero, List.getD_cons_zero] at hg0
    obtain ⟨hsec0, hyck0⟩ := hg0
    -- the head boundary flag agrees with the tail's emptiness
    have hflag : decide (i0 + 0 = N - 1) = rest.isEmpty := by
      have : rest.isEmpty = decide (rest.length = 0) := by
        cases rest <;> simp
      rw [this]
      simp only [Nat.add_zero]
      apply Bool.decide_congr
      omega
    -- the head piece + linking gate: the (n+1)-word chain to the next row's anchor
    have hLinked := link_step G n rest.isEmpty (msF i0)
      (first := dR base) (last := dR (base + n)) (next := dR (base + n + 1))
      hxP0 hyP0 hchain0 hsec0
      (by rw [← hflag]; simpa using hyck0)
    -- tail via the induction hypothesis
    have hTail := ih (i0 + 1) (base + (n + 1)) (Vector.cast (by simp) pieces.tail)
      (by
        simp only [List.length_cons] at hN
        omega)
      (by
        intro j
        have hj := hSlots ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
        simp only [prefixRows_succ, List.getD_cons_succ, Fin.getElem_fin] at hj ⊢
        rw [show i0 + (j.val + 1) = i0 + 1 + j.val from by omega] at hj
        rw [show base + ((n + 1) + prefixRows rest j.val)
            = base + (n + 1) + prefixRows rest j.val from by omega] at hj
        refine ⟨?_, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2⟩
        have hcst : (Vector.cast (by simp : (n :: rest).length - 1 = rest.length) pieces.tail
            : Vector Fp rest.length)[j.val] = pieces[j.val + 1] := by
          simp [Nat.add_comm]
        rw [hcst]
        exact hj.1)
      (by
        intro j
        have hj := hGates ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
        simp only [prefixRows_succ, List.getD_cons_succ] at hj ⊢
        rw [show i0 + (j.val + 1) = i0 + 1 + j.val from by omega,
          show base + ((n + 1) + prefixRows rest j.val)
            = base + (n + 1) + prefixRows rest j.val from by omega] at hj
        exact hj)
    obtain ⟨hPCt, hZst, hCt⟩ := hTail
    refine ⟨?_, ?_, ?_⟩
    · -- the pieces decompose
      refine ⟨msF i0, hms i0, ?_, chunksOf msF rest (i0 + 1), rfl, ?_⟩
      · simpa using hrec0
      · exact hPCt
    · -- the running sums
      refine zsFacts_cons _ _ _ ?_ ?_
      · apply Vector.ext
        intro r hr
        simp only [Vector.getElem_ofFn]
        have hz := hzs0 ⟨r, hr⟩
        rw [hz]
        refine congrArg _ (Finset.sum_congr rfl fun t ht => ?_)
        rw [show chunksOf msF (n :: rest) i0
            = (List.range (n + 1)).map (msF i0) ++ chunksOf msF rest (i0 + 1) from rfl,
          chunks_head_getD (msF i0) (chunksOf msF rest (i0 + 1)) (r + t)
            (by simp only [Finset.mem_range] at ht; omega)]
      · rw [show chunksOf msF (n :: rest) i0
            = (List.range (n + 1)).map (msF i0) ++ chunksOf msF rest (i0 + 1) from rfl,
          chunks_drop_append]
        exact hZst
    · -- the chain contract
      intro A hAon hAx hAyA B hB
      have hAyA' : 2 * A.y = yA (dR base) := by
        simpa only [List.isEmpty_cons, enterYA, Bool.false_eq_true, if_false] using hAyA
      rw [show chunksOf msF (n :: rest) i0
          = (List.range (n + 1)).map (msF i0) ++ chunksOf msF rest (i0 + 1) from rfl,
        Orchard.Specs.Sinsemilla.hashToPoint_append] at hB
      cases hpre : hashToPoint G.S A ((List.range (n + 1)).map (msF i0)) with
      | none =>
        rw [hpre] at hB
        simp at hB
      | some B1 =>
        rw [hpre] at hB
        replace hB : hashToPoint G.S B1 (chunksOf msF rest (i0 + 1)) = some B := hB
        have hAvalid : A.Valid := Or.inl hAon
        have hA0 : A ≠ 0 := Orchard.Point.ne_zero_of_onCurve hAon
        have hpre_lt : ∀ m ∈ (List.range (n + 1)).map (msF i0), m < 2 ^ K := by
          intro m hm
          rcases List.mem_map.mp hm with ⟨t, ht, rfl⟩
          exact hms i0 t
        have hB1valid : B1.Valid :=
          Orchard.Specs.Sinsemilla.hashToPoint_valid hAvalid hpre_lt hpre
        have hB10 : B1 ≠ 0 :=
          Orchard.Specs.Sinsemilla.hashToPoint_ne_zero hAvalid hA0 hpre_lt hpre
        have hB1on : B1.OnCurve := by
          rcases hB1valid with h | h
          · exact h
          · exact False.elim (hB10 h)
        obtain ⟨hB1x, hB1y⟩ := hLinked A hAon hAx hAyA' B1 hpre
        have hres := hCt B1 hB1on hB1x.symm hB1y B hB
        rw [show base + prefixRows (n :: rest) (n :: rest).length
            = base + (n + 1) + prefixRows rest rest.length from by
          rw [show (n :: rest).length = rest.length + 1 from rfl, prefixRows_succ]
          omega]
        exact hres

/-- Per-index piece bound out of `PieceBounds`. -/
private theorem pieceBounds_getElem :
    ∀ (nsSuf : List ℕ) (pieces : Vector Fp nsSuf.length),
    PieceBounds nsSuf pieces →
    ∀ j : Fin nsSuf.length, (pieces[j] : Fp).val < 2 ^ (K * (nsSuf.getD j.val 0 + 1)) := by
  intro nsSuf
  induction nsSuf with
  | nil =>
    intro pieces _ j
    exact absurd j.isLt (by simp)
  | cons n rest ih =>
    intro pieces hb j
    obtain ⟨hb0, hbrest⟩ := hb
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · have : j = ⟨0, by simp⟩ := Fin.ext h0
      subst this
      simpa using hb0
    · have hlt : j.val - 1 < rest.length := by
        have := j.isLt
        simp at this
        omega
      have hres := ih pieces.tail hbrest ⟨j.val - 1, hlt⟩
      simp only [Fin.getElem_fin] at hres ⊢
      rw [show (n :: rest).getD j.val 0 = rest.getD (j.val - 1) 0 from by
        rw [show j.val = (j.val - 1) + 1 from by omega]
        rfl]
      convert hres using 2
      simp
      congr 1
      omega

/-- Suffix chunk list over a piece-value family (pieces indexed from `k`). -/
private def sufChunks (pv : ℕ → Fp) : (rem : List ℕ) → (k : ℕ) → List ℕ
  | [], _ => []
  | n :: rest, k => (List.range (n + 1)).map (pieceWord (pv k)) ++ sufChunks pv rest (k + 1)

/-- `honestChunks` over a matching value family is the 0-indexed suffix chunk list. -/
private theorem honestChunks_eq_suf (pv : ℕ → Fp) :
    ∀ (nsSuf : List ℕ) (pieces : Vector Fp nsSuf.length) (k : ℕ),
    (∀ j : Fin nsSuf.length, pieces[j] = pv (k + j.val)) →
    honestChunks nsSuf pieces = sufChunks pv nsSuf k := by
  intro nsSuf
  induction nsSuf with
  | nil =>
    intro pieces k _
    rfl
  | cons n rest ih =>
    intro pieces k hpv
    show (List.range (n + 1)).map (pieceWord pieces[0]) ++ honestChunks rest pieces.tail
      = (List.range (n + 1)).map (pieceWord (pv k)) ++ sufChunks pv rest (k + 1)
    rw [show pieces[0] = pv k from by simpa using hpv ⟨0, by simp⟩]
    congr 1
    have hcast : honestChunks rest pieces.tail
        = honestChunks rest (Vector.cast (by simp) pieces.tail) := by
      simp
    rw [hcast]
    exact ih (Vector.cast (by simp) pieces.tail) (k + 1) (by
      intro j
      have h := hpv ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      simp only [Fin.getElem_fin] at h ⊢
      rw [show (Vector.cast (by simp) pieces.tail
          : Vector Fp rest.length)[j.val] = pieces[j.val + 1] from by simp [Nat.add_comm]]
      rw [h]
      congr 1
      omega)

/-- Step a suffix chunk list at an in-range index. -/
private theorem sufChunks_drop_succ (pv : ℕ → Fp) (ns : List ℕ) (k : ℕ) (hk : k < ns.length) :
    sufChunks pv (ns.drop k) k
      = (List.range (ns.getD k 0 + 1)).map (pieceWord (pv k))
        ++ sufChunks pv (ns.drop (k + 1)) (k + 1) := by
  rw [List.drop_eq_getElem_cons hk]
  rw [show sufChunks pv (ns[k] :: ns.drop (k + 1)) k
      = (List.range (ns[k] + 1)).map (pieceWord (pv k))
        ++ sufChunks pv (ns.drop (k + 1)) (k + 1) from rfl]
  congr 3
  rw [List.getD_eq_getElem ns 0 hk]

/-- Prover-view literal-eval bridges for the output record. -/
private theorem output_eval_literal_prover (env : Placed ProverEnvironment Fp)
    (p : Point (AssignedCell Fp)) (f : DoubleAndAddRow (AssignedCell Fp)) :
    (eval env ({ point := p, first := f } : Output (AssignedCell Fp)) : Output Fp)
      = { point := ProvableType.eval env.place env.env.toEnvironment p,
          first := ProvableType.eval env.place env.env.toEnvironment f } := by
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  with_unfolding_all rfl

/-- The slot-`k` entering-`y` VALUE (the `yaIn` program for slot 0, the positional
boundary derivation otherwise) — choice-free spelling shared by the completeness facts. -/
private def slotEnterVal (yaIn : Placed Environment Fp → Fp) (cfg : Config)
    (ns : List ℕ) (offset : ℕ) (self : RegionIndex) (env : Placed Environment Fp)
    (k : ℕ) : Fp :=
  if k = 0 then yaIn env
  else boundaryYA (slotReads cfg (ns.getD k 0) (offset + prefixRows ns k) self).prev
    (AssignedCell.of self (offset + prefixRows ns k) cfg.xA) env

/-- Prover-env double-and-add row read at region-local row `r` (top-level def — compact
spelling for the completeness facts; unfolds to the raw advice reads). -/
private def dRowP (cfg : Config) (pl : RegionIndex → ℕ) (e : ProverEnvironment Fp)
    (self : RegionIndex) (r : ℕ) : DoubleAndAddRow Fp where
  xA := e.advice cfg.xA ((pl self + r : ℕ) : ℤ)
  xP := e.advice cfg.xP ((pl self + r : ℕ) : ℤ)
  lambda1 := e.advice cfg.lambda1 ((pl self + r : ℕ) : ℤ)
  lambda2 := e.advice cfg.lambda2 ((pl self + r : ℕ) : ℤ)

/-! ## The bundle -/

instance circuitElaborated (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (cfg : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp (Inputs ns.length) Output
      (fun input : Var (Inputs ns.length) Fp => do
        RegionCircuit.forRangeVar' (fun i => offset + prefixRows ns i) ns.length
          (fun i base => do
            let _ ← (slot G ns yaIn i).call cfg base (input.pieces[i]!)
            let _q ← assignFixed cfg.qS2 (base + ns.getD i 0)
              (qS2Boundary (decide (i = ns.length - 1)))
            (sinsemillaGate cfg).enable (base + ns.getD i 0))
        let ex ← readState cfg (offset + prefixRows ns ns.length - 1)
        let xExit ← cellAt cfg.xA (offset + prefixRows ns ns.length)
        let yFin ← assignAdvice cfg.lambda1 (offset + prefixRows ns ns.length)
          (finalYAWit ex.row xExit)
        let _l2d ← assignAdvice cfg.lambda2 (offset + prefixRows ns ns.length) zeroWit
        let _xpd ← assignAdvice cfg.xP (offset + prefixRows ns ns.length) zeroWit
        let first ← readState cfg offset
        return ({ point := { x := xExit, y := yFin }, first := first.row }
          : Output (AssignedCell Fp))) := {}

def circuit (G : Generators) (ns : List ℕ) (yaIn : Placed Environment Fp → Fp) :
    FormalRegionCircuit Fp Config Config (Inputs ns.length) Output where
  name := "sinsemilla hash_all_pieces"
  configure := pure

  synthesize cfg offset (input : Var (Inputs ns.length) Fp) := do
    RegionCircuit.forRangeVar' (fun i => offset + prefixRows ns i) ns.length
      (fun i base => do
        let _ ← (slot G ns yaIn i).call cfg base (input.pieces[i]!)
        -- the boundary `q_s2` re-pin (idempotent) and the piece-linking gate at this
        -- piece's last row — chain-owned: the gate reads the NEXT slot's first row
        let _q ← assignFixed cfg.qS2 (base + ns.getD i 0)
          (qS2Boundary (decide (i = ns.length - 1)))
        (sinsemillaGate cfg).enable (base + ns.getD i 0))
    -- the trailing dummy row: the final `y_a` into `λ₁`, dummy `λ₂`/`x_p`
    let ex ← readState cfg (offset + prefixRows ns ns.length - 1)
    let xExit ← cellAt cfg.xA (offset + prefixRows ns ns.length)
    let yFin ← assignAdvice cfg.lambda1 (offset + prefixRows ns ns.length)
      (finalYAWit ex.row xExit)
    let _l2d ← assignAdvice cfg.lambda2 (offset + prefixRows ns ns.length) zeroWit
    let _xpd ← assignAdvice cfg.xP (offset + prefixRows ns ns.length) zeroWit
    let first ← readState cfg offset
    return { point := { x := xExit, y := yFin }, first := first.row }

  elaborated cfg offset := circuitElaborated G ns yaIn cfg offset

  Witness := ChainWit ns
  extract cfg offset _ self env :=
    { xIn := eval env (AssignedCell.of self offset cfg.xA : Var field Fp),
      yIn := yaIn env,
      zs := eval env (zsCellsVal cfg self ns offset) }

  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env

  Spec input output wit := Spec G ns input output wit
  ProverAssumptions input wit _ := ProverAssumptions G ns input wit
  ProverSpec input output wit _ := ProverSpec G ns input output wit

  soundness := by
    -- ENGINE WALL (recorded in sinsemilla-loop-design.md): the heterogeneous piece call
    -- (child output type `HashPiece.Output (ns.getD i 0 + 1)` depends on the loop index)
    -- times out `circuit_proof_start`/the peel at whnf. Plan: wrap each slot as a
    -- Unit-output FormalRegionCircuit family (`slot i` — positional contract over its
    -- Witness readings, the `round i` pattern at piece scale) so the loop is homogeneous.
    -- TACTIC GAP (recorded in sinsemilla-loop-design.md): `circuit_proof_start`'s
    -- step (b) `simp only [circuit_norm] at h_output` dies at whnf on this bundle's
    -- composed output (a single six-figure `Eq.rec`/`List.rec` reduction, surviving the
    -- simproc heartbeat caps added in StructEvalSimprocs.speculative). Manual house
    -- prefix + targeted peel (the Mul.lean idiom) until that burn is excised.
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE hA hc
    simp only [RegionCircuit.operations_bind, RegionOperations.constraints_append,
      RegionCircuit.forRangeVar'_constraints, HashPiece.operations_readState] at hc
    subcircuit_rw at hc
    simp only [slotC_spec_eq, slotC_assumptions_eq, slotC_envAssumptions_eq,
      slotC_extract_eq, sinsemillaGate, HashPiece.qS3Expr, HashPiece.yAExpr,
      HashPiece.xRExpr, Constraints.withSelector, SlotSpec, slotReads,
      circuit_norm] at hc
    -- per-slot facts and the totalized word family
    have hSp := fun i : Fin ns.length => (hc i).1 _hE
    choose msF hbF hrecF hzsF hxPF hyPF hchF using hSp
    have hQg := fun i : Fin ns.length => (hc i).2.1
    have hGg := fun i : Fin ns.length => (hc i).2.2
    clear hc
    have hfold := chain_fold G ns.length
      (fun r => { xA := env.env.advice cfg.xA ((env.place self + r : ℕ) : ℤ),
                  xP := env.env.advice cfg.xP ((env.place self + r : ℕ) : ℤ),
                  lambda1 := env.env.advice cfg.lambda1 ((env.place self + r : ℕ) : ℤ),
                  lambda2 := env.env.advice cfg.lambda2 ((env.place self + r : ℕ) : ℤ) }
        : ℕ → DoubleAndAddRow Fp)
      (fun r => env.env.advice cfg.bits ((env.place self + r : ℕ) : ℤ))
      (fun j r => if h : j < ns.length then msF ⟨j, h⟩ r else 0)
      (by
        intro j r
        beta_reduce
        by_cases h : j < ns.length
        · rw [dif_pos h]
          exact hbF ⟨j, h⟩ r
        · rw [dif_neg h]
          norm_num [K])
      ns 0 offset input.pieces (by omega)
      (by
        intro j
        beta_reduce
        simp only [Nat.zero_add, dif_pos j.isLt]
        have hzsv := hzsF j
        rw [ProvableType.eval_cells (M := fields (ns.getD j.val 0 + 1)),
          eval_fields_eq_map] at hzsv
        refine ⟨?_, ?_, hxPF j, hyPF j, hchF j⟩
        · -- the piece value
          have hpieces_eq : input.pieces
              = input_var.pieces.map (fun c => AssignedCell.eval env.place env.env c) := by
            rw [← h_input, ProvableStruct.eval_cells_eq_eval]
            cases input_var with
            | mk pv =>
              rw [inputs_eval_literal]
              exact eval_fields_eq_map env.place env.env pv
          rw [Fin.getElem_fin, hpieces_eq, Vector.getElem_map]
          have hrec := hrecF j
          rw [getElem!_pos input_var.pieces j.val j.isLt] at hrec
          simpa [AssignedCell.eval, Environment.get_advice] using hrec
        · -- the running sums, pointwise off the vector equation
          intro r
          have hv := congrArg
            (fun v : Vector Fp (ns.getD j.val 0 + 1) => v[r.val]'r.isLt) hzsv
          simp only [Vector.getElem_map, Vector.getElem_ofFn] at hv
          simpa [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
            Cell.of_rowOffset, Cell.of_column, Environment.get_advice] using hv)
      (by
        intro j
        beta_reduce
        simp only [Nat.zero_add]
        obtain ⟨hsec, hyck⟩ := hGg j
        rw [(hQg j)] at hyck
        constructor
        · simp only [xR]
          linear_combination hsec
        · have hq := qS3_yRhs (decide (j.val = ns.length - 1))
            { xA := env.env.advice cfg.xA
                ((env.place self + (offset + prefixRows ns j.val + ns.getD j.val 0 + 1)
                  : ℕ) : ℤ),
              xP := env.env.advice cfg.xP
                ((env.place self + (offset + prefixRows ns j.val + ns.getD j.val 0 + 1)
                  : ℕ) : ℤ),
              lambda1 := env.env.advice cfg.lambda1
                ((env.place self + (offset + prefixRows ns j.val + ns.getD j.val 0 + 1)
                  : ℕ) : ℤ),
              lambda2 := env.env.advice cfg.lambda2
                ((env.place self + (offset + prefixRows ns j.val + ns.getD j.val 0 + 1)
                  : ℕ) : ℤ) }
          simp only [yA, xR] at hq ⊢
          linear_combination hyck + hq)
    obtain ⟨hPC, hZs, hContract⟩ := hfold
    -- land the output on its record components
    rw [ElaboratedRegionCircuit.output_eq] at h_output
    simp only [RegionCircuit.output_bind, RegionCircuit.output_pure,
      HashPiece.output_readState,
      output_assignAdvice] at h_output
    rw [ProvableStruct.eval_cells_eq_eval, output_eval_literal, point_eval_literal,
      row_eval_literal] at h_output
    simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice] at h_output
    refine ⟨chunksOf (fun j r => if h : j < ns.length then msF ⟨j, h⟩ r else 0) ns 0,
      hPC, ?_, ?_⟩
    · -- the running sums (the extraction data)
      rw [eval_zsCellsVal]
      exact hZs
    · -- the chain contract
      intro A hAon hAx hAyA B hB
      rw [← h_output] at hAx hAyA
      have hres := hContract A hAon (by simpa using hAx) (by simpa using hAyA) B hB
      rw [← h_output]
      simp only []
      exact ⟨hres.1.symm ▸ rfl, hres.2.symm ▸ rfl⟩

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [RegionCircuit.operations_bind, RegionOperations.extendsWitnesses_append,
      RegionCircuit.forRangeVar'_extendsWitnesses, HashPiece.operations_readState,
      circuit_norm] at hwit
    obtain ⟨hWs, hWyFin, -, -⟩ := hwit
    obtain ⟨hns, hbounds, A, B, hAon, hAx, hAy, hchain⟩ := hPA
    -- the piece-value family and the chunk-list rewrite
    have hpieces_eq : input.pieces
        = input_var.pieces.map
            (fun c => AssignedCell.eval env.place env.env.toEnvironment c) := by
      rw [← h_input, ProvableStruct.eval_cells_eq_eval_prover]
      cases input_var with
      | mk pv =>
        rw [inputs_eval_literal]
        exact eval_fields_eq_map env.place env.env.toEnvironment pv
    have hpv : ∀ j : Fin ns.length,
        input.pieces[j] = AssignedCell.eval env.place env.env.toEnvironment
          (input_var.pieces[j.val]!) := by
      intro j
      rw [Fin.getElem_fin, hpieces_eq, Vector.getElem_map,
        getElem!_pos input_var.pieces j.val j.isLt]
    have hchainS : hashToPoint G.S A
        (sufChunks (fun t => AssignedCell.eval env.place env.env.toEnvironment
          (input_var.pieces[t]!)) ns 0) = some B := by
      rw [← honestChunks_eq_suf _ ns input.pieces 0 (by
        intro j
        simpa using hpv j)]
      exact hchain
    -- the honest thread: per-suffix entering point with its positional facts
    have hthread : ∀ k : ℕ, k ≤ ns.length → ∃ Ck : Point Fp, Ck.OnCurve ∧
        Ck.x = env.env.advice cfg.xA
          ((env.place self + (offset + prefixRows ns k) : ℕ) : ℤ) ∧
        Ck.y = slotEnterVal yaIn cfg ns offset self env.toEnvironment k ∧
        hashToPoint G.S Ck (sufChunks (fun t =>
          AssignedCell.eval env.place env.env.toEnvironment (input_var.pieces[t]!))
          (ns.drop k) k) = some B := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨A, hAon, ?_, ?_, by simpa using hchainS⟩
        · rw [hAx]
          show (eval env.toEnvironment (AssignedCell.of self offset cfg.xA : Var field Fp)
            : Fp) = _
          simp only [Nat.add_zero, prefixRows_zero]
          with_unfolding_all rfl
        · rw [slotEnterVal, if_pos rfl, hAy]
      | succ m ih =>
        intro hm1
        obtain ⟨Cm, hCon, hCx, hCy, hCchain⟩ := ih (by omega)
        rw [sufChunks_drop_succ _ ns m (by omega),
          Orchard.Specs.Sinsemilla.hashToPoint_append] at hCchain
        cases hsplit : hashToPoint G.S Cm ((List.range (ns.getD m 0 + 1)).map
            (pieceWord (AssignedCell.eval env.place env.env.toEnvironment
              (input_var.pieces[m]!)))) with
        | none =>
          rw [hsplit] at hCchain
          simp at hCchain
        | some Dm =>
          rw [hsplit] at hCchain
          -- slot m's honest-prover precondition and derived contract
          have hPAm : SlotPA G (ns.getD m 0)
              (eval env (input_var.pieces[m]! : Var field Fp))
              ((slot G ns yaIn m).extract cfg (offset + prefixRows ns m)
                (input_var.pieces[m]!) self env.toEnvironment) := by
            rw [slotC_extract_eq, slotReads_eval]
            simp only [AssignedCell.eval, eval_field_cell]
            refine ⟨?_, Cm, Dm, hCon, ?_, ?_, ?_⟩
            · have hb := pieceBounds_getElem ns input.pieces hbounds ⟨m, by omega⟩
              rw [hpv ⟨m, by omega⟩] at hb
              simpa using hb
            · exact hCx
            · rw [hCy, slotEnterVal]
            · simp only [AssignedCell.eval] at hsplit
              exact hsplit
          -- the slot's derived contract on the honest run
          have hder := Halo2.SubcircuitRw.region_completeness_derived_placed
            (slot G ns yaIn m) cfg (offset + prefixRows ns m) self env
            (input_var.pieces[m]!) ((hWs ⟨m, by omega⟩).1)
            (by rw [slotC_envAssumptions_eq]; exact _hE) trivial
            (by rw [slotC_proverAssumptions_eq]; exact hPAm)
          rw [slotC_proverSpec_eq] at hder
          obtain ⟨-, hPS⟩ := hder
          rw [SlotPS, slotC_extract_eq, slotReads_eval] at hPS
          simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
            Cell.of_rowOffset, Cell.of_column, Environment.get_advice] at hPS
          have hfacts := hPS Cm Dm hCx hCy (by
            rw [eval_field_cell]
            simp only [AssignedCell.eval]
            exact hsplit)
          obtain ⟨hfy, hnx, hlsec, hlnyA⟩ := hfacts
          -- Dm is on-curve
          have hCmValid : Cm.Valid := Or.inl hCon
          have hCm0 : Cm ≠ 0 := Orchard.Point.ne_zero_of_onCurve hCon
          have hwords_lt : ∀ w ∈ (List.range (ns.getD m 0 + 1)).map
              (pieceWord (AssignedCell.eval env.place env.env.toEnvironment
                (input_var.pieces[m]!))), w < 2 ^ K := by
            intro w hw
            rcases List.mem_map.mp hw with ⟨t, ht, rfl⟩
            exact pieceWord_lt _ t
          have hDmValid : Dm.Valid :=
            Orchard.Specs.Sinsemilla.hashToPoint_valid hCmValid hwords_lt hsplit
          have hDm0 : Dm ≠ 0 :=
            Orchard.Specs.Sinsemilla.hashToPoint_ne_zero hCmValid hCm0 hwords_lt hsplit
          have hDmOn : Dm.OnCurve := by
            rcases hDmValid with h | h
            · exact h
            · exact False.elim (hDm0 h)
          have hrowstep : offset + prefixRows ns (m + 1)
              = offset + prefixRows ns m + ns.getD m 0 + 1 := by
            rw [prefixRows_step ns m (by omega)]
            omega
          refine ⟨Dm, hDmOn, ?_, ?_, ?_⟩
          · rw [hrowstep]
            exact hnx.symm
          · rw [slotEnterVal, if_neg (by omega : ¬ m + 1 = 0)]
            have h2 : (2 : Fp) ≠ 0 := by decide
            simp only [boundaryYA, nextYA, slotReads, AssignedCell.eval,
              AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
              Cell.of_column, Environment.get_advice]
            rw [hrowstep,
              show offset + prefixRows ns m + ns.getD m 0 + 1 - 1
                = offset + prefixRows ns m + ns.getD m 0 from by omega]
            linear_combination (norm := (field_simp; ring)) (-(2 : Fp)⁻¹) * hlnyA
          · exact hCchain
    -- per-slot data: the PA (for the engine leaf), the first-row Y_A value fact, and
    -- the last-row secant/y-law facts (for the chain-owned gates) — all choice-free
    have hSlotData : ∀ i : Fin ns.length,
        ((slot G ns yaIn ↑i).ProverAssumptions
          (eval env (input_var.pieces[↑i]! : Var field Fp))
          ((slot G ns yaIn ↑i).extract cfg (offset + prefixRows ns ↑i)
            (input_var.pieces[↑i]!) self env.toEnvironment) env.env.hint) ∧
        yA (dRowP cfg env.place env.env self (offset + prefixRows ns ↑i))
          = 2 * slotEnterVal yaIn cfg ns offset self env.toEnvironment ↑i ∧
        (dRowP cfg env.place env.env self
            (offset + prefixRows ns ↑i + ns.getD ↑i 0)).lambda2
          * (dRowP cfg env.place env.env self
              (offset + prefixRows ns ↑i + ns.getD ↑i 0)).lambda2
          = (dRowP cfg env.place env.env self
              (offset + prefixRows ns ↑i + ns.getD ↑i 0 + 1)).xA
            + xR (dRowP cfg env.place env.env self
                (offset + prefixRows ns ↑i + ns.getD ↑i 0))
            + (dRowP cfg env.place env.env self
                (offset + prefixRows ns ↑i + ns.getD ↑i 0)).xA ∧
        2 * (dRowP cfg env.place env.env self
              (offset + prefixRows ns ↑i + ns.getD ↑i 0)).lambda2
          * ((dRowP cfg env.place env.env self
              (offset + prefixRows ns ↑i + ns.getD ↑i 0)).xA
            - (dRowP cfg env.place env.env self
                (offset + prefixRows ns ↑i + ns.getD ↑i 0 + 1)).xA)
          - yA (dRowP cfg env.place env.env self
              (offset + prefixRows ns ↑i + ns.getD ↑i 0))
          = 2 * slotEnterVal yaIn cfg ns offset self env.toEnvironment (↑i + 1) := by
      intro i
      obtain ⟨m, hm⟩ := i
      simp only [Fin.val_mk]
      obtain ⟨Ci, hCon, hCx, hCy, hCchain⟩ := hthread m (le_of_lt hm)
      rw [sufChunks_drop_succ _ ns m hm,
        Orchard.Specs.Sinsemilla.hashToPoint_append] at hCchain
      cases hsplit : hashToPoint G.S Ci
          ((List.range (ns.getD m 0 + 1)).map (pieceWord
            (AssignedCell.eval env.place env.env.toEnvironment
              (input_var.pieces[m]!)))) with
      | none =>
        rw [hsplit] at hCchain
        simp at hCchain
      | some Di =>
        rw [hsplit] at hCchain
        have hPAi : SlotPA G (ns.getD m 0)
            (eval env (input_var.pieces[m]! : Var field Fp))
            ((slot G ns yaIn m).extract cfg (offset + prefixRows ns m)
              (input_var.pieces[m]!) self env.toEnvironment) := by
          rw [slotC_extract_eq, slotReads_eval]
          simp only [AssignedCell.eval, eval_field_cell]
          refine ⟨?_, Ci, Di, hCon, ?_, ?_, ?_⟩
          · have hb := pieceBounds_getElem ns input.pieces hbounds ⟨m, hm⟩
            rw [hpv ⟨m, hm⟩] at hb
            simpa using hb
          · exact hCx
          · rw [hCy, slotEnterVal]
          · simp only [AssignedCell.eval] at hsplit
            exact hsplit
        have hder := Halo2.SubcircuitRw.region_completeness_derived_placed
          (slot G ns yaIn m) cfg (offset + prefixRows ns m) self env
          (input_var.pieces[m]!) ((hWs ⟨m, hm⟩).1)
          (by rw [slotC_envAssumptions_eq]; exact _hE) trivial
          (by rw [slotC_proverAssumptions_eq]; exact hPAi)
        rw [slotC_proverSpec_eq] at hder
        obtain ⟨-, hPS⟩ := hder
        rw [SlotPS, slotC_extract_eq, slotReads_eval] at hPS
        simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
          Cell.of_rowOffset, Cell.of_column, Environment.get_advice] at hPS
        have hfacts := hPS Ci Di hCx hCy (by
          rw [eval_field_cell]
          simp only [AssignedCell.eval]
          exact hsplit)
        obtain ⟨hfy, hnx, hlsec, hlnyA⟩ := hfacts
        refine ⟨by rw [slotC_proverAssumptions_eq]; exact hPAi, ?_, ?_, ?_⟩
        · simp only [dRowP]
          rw [← hCy]
          exact hfy
        · simp only [dRowP]
          exact hlsec
        · -- the exit `2·y` is the (i+1)-boundary entering value — pure boundary algebra
          rw [slotEnterVal, if_neg (by omega : ¬ m + 1 = 0)]
          have hrowstep : offset + prefixRows ns (m + 1)
              = offset + prefixRows ns m + ns.getD m 0 + 1 := by
            rw [prefixRows_step ns m hm]
            omega
          simp only [boundaryYA, nextYA, slotReads, dRowP, yA, AssignedCell.eval,
            AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
            Cell.of_column, Environment.get_advice, Placed.toEnvironment_place,
            Placed.toEnvironment_env]
          rw [hrowstep,
            show offset + prefixRows ns m + ns.getD m 0 + 1 - 1
              = offset + prefixRows ns m + ns.getD m 0 from by omega]
          have h2 : (2 : Fp) ≠ 0 := by decide
          field_simp
    refine ⟨?_, ?_⟩
    · -- the constraints
      simp only [RegionCircuit.operations_bind, RegionOperations.constraints_append,
        RegionCircuit.forRangeVar'_constraints, HashPiece.operations_readState]
      refine ⟨fun i => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := i
        obtain ⟨hPAm, h2yA, hsec, hlny⟩ := hSlotData ⟨m, hm⟩
        refine ⟨?_, ?_, ?_⟩
        · -- the slot subcircuit, via the engine leaf
          exact Halo2.SubcircuitRw.region_completeness_leaf_placed
            (slot G ns yaIn m) cfg (offset + prefixRows ns m) self env
            (input_var.pieces[m]!) ((hWs ⟨m, hm⟩).1)
            ⟨by rw [slotC_envAssumptions_eq]; exact _hE, trivial, hPAm⟩
        · -- the boundary `q_s2` value
          simp only [circuit_norm]
          exact (hWs ⟨m, hm⟩).2
        · -- the piece-linking gate
          simp only [sinsemillaGate, HashPiece.qS3Expr, HashPiece.yAExpr,
            HashPiece.xRExpr, Constraints.withSelector, circuit_norm]
          rw [(hWs ⟨m, hm⟩).2]
          simp only [dRowP, yA, xR] at hsec hlny
          have hq := qS3_yRhs (decide (m = ns.length - 1))
            { xA := env.env.advice cfg.xA
                ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ),
              xP := env.env.advice cfg.xP
                ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ),
              lambda1 := env.env.advice cfg.lambda1
                ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ),
              lambda2 := env.env.advice cfg.lambda2
                ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ) }
          have henter : enterYA (decide (m = ns.length - 1))
              { xA := env.env.advice cfg.xA
                  ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ),
                xP := env.env.advice cfg.xP
                  ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ),
                lambda1 := env.env.advice cfg.lambda1
                  ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ),
                lambda2 := env.env.advice cfg.lambda2
                  ((env.place self + (offset + prefixRows ns m + ns.getD m 0 + 1) : ℕ) : ℤ) }
              = 2 * slotEnterVal yaIn cfg ns offset self env.toEnvironment (m + 1) := by
            by_cases hb : m = ns.length - 1
            · -- the final boundary: the trailing row's witnessed `y_a`
              rw [show (decide (m = ns.length - 1)) = true from by simp [hb]]
              simp only [enterYA, if_true]
              rw [show m + 1 = ns.length from by omega]
              rw [slotEnterVal, if_neg (by omega : ¬ ns.length = 0)]
              rw [show offset + prefixRows ns m + ns.getD m 0 + 1
                  = offset + prefixRows ns ns.length from by
                rw [show ns.length = m + 1 from by omega, prefixRows_step ns m hm]
                omega]
              rw [hWyFin]
              simp only [boundaryYA, nextYA, slotReads, HashPiece.reads,
                AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
                Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
                Placed.toEnvironment_place, Placed.toEnvironment_env]
            · -- an interior boundary: the next slot's first-row `Y_A`
              rw [show (decide (m = ns.length - 1)) = false from by simp [hb]]
              simp only [enterYA, Bool.false_eq_true, if_false]
              have h := (hSlotData ⟨m + 1, by omega⟩).2.1
              rw [show offset + prefixRows ns (m + 1)
                  = offset + prefixRows ns m + ns.getD m 0 + 1 from by
                rw [prefixRows_step ns m hm]
                omega] at h
              simp only [dRowP] at h
              exact h
          simp only [yA, xR] at hq
          refine ⟨?_, ?_⟩
          · linear_combination hsec
          · linear_combination 2 * hlny - hq - 2 * henter
      · -- the trailing dummy row emits no constraints
        simp only [circuit_norm]
    · -- the honest-prover contract
      rw [ElaboratedRegionCircuit.output_eq] at h_output
      simp only [RegionCircuit.output_bind, RegionCircuit.output_pure,
        HashPiece.output_readState,
        output_assignAdvice] at h_output
      rw [output_eval_literal_prover, point_eval_literal, row_eval_literal] at h_output
      simp only [HashPiece.reads, AssignedCell.eval, AssignedCell.of_cell,
        Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
        Environment.get_advice] at h_output
      intro A' B' hA'x hA'y hchain'
      have hA'A : A' = A := by
        cases A'
        cases A
        rw [Point.mk.injEq]
        exact ⟨hA'x.trans hAx.symm, hA'y.trans hAy.symm⟩
      rw [hA'A] at hchain'
      have hBB : B' = B := Option.some.inj (hchain'.symm.trans hchain)
      obtain ⟨C, hCon, hCx, hCy, hCch⟩ := hthread ns.length le_rfl
      rw [List.drop_length] at hCch
      have hCB : C = B := Option.some.inj hCch
      have hlen0 : ¬ ns.length = 0 := by
        simp only [List.length_eq_zero_iff]
        exact hns
      rw [← h_output, hA'A, hBB, ← hCB]
      simp only []
      refine ⟨?_, ?_, ?_⟩
      · exact hCx.symm
      · rw [hCy, slotEnterVal, if_neg hlen0, hWyFin]
        simp only [boundaryYA, nextYA, slotReads, HashPiece.reads,
          AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
          Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
          Placed.toEnvironment_place, Placed.toEnvironment_env]
      · rw [show ns.isEmpty = false from by simp [hns]]
        simp only [enterYA, Bool.false_eq_true, if_false]
        have h := (hSlotData ⟨0, by omega⟩).2.1
        rw [slotEnterVal, if_pos rfl] at h
        simp only [prefixRows_zero, Nat.add_zero, dRowP] at h
        rw [h, hAy]

/-- The chain's eval'd output, landed on raw advice reads (the public composition lemma —
what `hash_message`-level consumers rewrite `(circuit …).output` with). -/
theorem circuit_output_eval (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (cfg : Config) (offset : ℕ)
    (iv : Var (Inputs ns.length) Fp) (self : RegionIndex) (env : Placed Environment Fp) :
    (eval env ((circuit G ns yaIn).output cfg offset iv self) : Value Output Fp)
      = { point :=
            { x := env.env.advice cfg.xA
                ((env.place self + (offset + prefixRows ns ns.length) : ℕ) : ℤ),
              y := env.env.advice cfg.lambda1
                ((env.place self + (offset + prefixRows ns ns.length) : ℕ) : ℤ) },
          first :=
            { xA := env.env.advice cfg.xA ((env.place self + offset : ℕ) : ℤ),
              xP := env.env.advice cfg.xP ((env.place self + offset : ℕ) : ℤ),
              lambda1 := env.env.advice cfg.lambda1 ((env.place self + offset : ℕ) : ℤ),
              lambda2 := env.env.advice cfg.lambda2 ((env.place self + offset : ℕ) : ℤ) } } := by
  rw [FormalRegionCircuit.output, ((circuit G ns yaIn).elaborated cfg offset).output_eq]
  show (eval env ((do
        RegionCircuit.forRangeVar' (fun i => offset + prefixRows ns i) ns.length
          (fun i base => do
            let _ ← (slot G ns yaIn i).call cfg base (iv.pieces[i]!)
            let _q ← assignFixed cfg.qS2 (base + ns.getD i 0)
              (qS2Boundary (decide (i = ns.length - 1)))
            (sinsemillaGate cfg).enable (base + ns.getD i 0))
        let ex ← readState cfg (offset + prefixRows ns ns.length - 1)
        let xExit ← cellAt cfg.xA (offset + prefixRows ns ns.length)
        let yFin ← assignAdvice cfg.lambda1 (offset + prefixRows ns ns.length)
          (finalYAWit ex.row xExit)
        let _l2d ← assignAdvice cfg.lambda2 (offset + prefixRows ns ns.length) zeroWit
        let _xpd ← assignAdvice cfg.xP (offset + prefixRows ns ns.length) zeroWit
        let first ← readState cfg offset
        return ({ point := { x := xExit, y := yFin }, first := first.row }
          : Output (AssignedCell Fp))).output self) : Value Output Fp) = _
  simp only [RegionCircuit.output_bind, RegionCircuit.output_pure,
    HashPiece.output_readState, Halo2.output_cellAt, output_assignAdvice]
  rw [ProvableStruct.eval_cells_eq_eval, output_eval_literal, point_eval_literal,
    row_eval_literal]
  simp only [HashPiece.reads, AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]

/-- The chain's eval'd output, prover view (the completeness-side composition lemma). -/
theorem circuit_output_eval_prover (G : Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (cfg : Config) (offset : ℕ)
    (iv : Var (Inputs ns.length) Fp) (self : RegionIndex)
    (env : Placed ProverEnvironment Fp) :
    (eval env ((circuit G ns yaIn).output cfg offset iv self) : Value Output Fp)
      = { point :=
            { x := env.env.advice cfg.xA
                ((env.place self + (offset + prefixRows ns ns.length) : ℕ) : ℤ),
              y := env.env.advice cfg.lambda1
                ((env.place self + (offset + prefixRows ns ns.length) : ℕ) : ℤ) },
          first :=
            { xA := env.env.advice cfg.xA ((env.place self + offset : ℕ) : ℤ),
              xP := env.env.advice cfg.xP ((env.place self + offset : ℕ) : ℤ),
              lambda1 := env.env.advice cfg.lambda1 ((env.place self + offset : ℕ) : ℤ),
              lambda2 := env.env.advice cfg.lambda2 ((env.place self + offset : ℕ) : ℤ) } } := by
  rw [FormalRegionCircuit.output, ((circuit G ns yaIn).elaborated cfg offset).output_eq]
  show (eval env ((do
        RegionCircuit.forRangeVar' (fun i => offset + prefixRows ns i) ns.length
          (fun i base => do
            let _ ← (slot G ns yaIn i).call cfg base (iv.pieces[i]!)
            let _q ← assignFixed cfg.qS2 (base + ns.getD i 0)
              (qS2Boundary (decide (i = ns.length - 1)))
            (sinsemillaGate cfg).enable (base + ns.getD i 0))
        let ex ← readState cfg (offset + prefixRows ns ns.length - 1)
        let xExit ← cellAt cfg.xA (offset + prefixRows ns ns.length)
        let yFin ← assignAdvice cfg.lambda1 (offset + prefixRows ns ns.length)
          (finalYAWit ex.row xExit)
        let _l2d ← assignAdvice cfg.lambda2 (offset + prefixRows ns ns.length) zeroWit
        let _xpd ← assignAdvice cfg.xP (offset + prefixRows ns ns.length) zeroWit
        let first ← readState cfg offset
        return ({ point := { x := xExit, y := yFin }, first := first.row }
          : Output (AssignedCell Fp))).output self) : Value Output Fp) = _
  simp only [RegionCircuit.output_bind, RegionCircuit.output_pure,
    HashPiece.output_readState, Halo2.output_cellAt, output_assignAdvice]
  rw [output_eval_literal_prover, point_eval_literal, row_eval_literal]
  simp only [HashPiece.reads, AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]

/-- The chain output's `point.x` cell (positional — the exit `x_a`). -/
theorem output_point_x (G : Generators) (ns : List ℕ) (yaIn : Placed Environment Fp → Fp)
    (cfg : Config) (offset : ℕ) (iv : Var (Inputs ns.length) Fp) (self : RegionIndex) :
    ((circuit G ns yaIn).output cfg offset iv self).point.x
      = AssignedCell.of self (offset + prefixRows ns ns.length) cfg.xA := rfl

/-- The chain output's `point.y` cell (positional — the trailing `y_a` in `λ₁`). -/
theorem output_point_y (G : Generators) (ns : List ℕ) (yaIn : Placed Environment Fp → Fp)
    (cfg : Config) (offset : ℕ) (iv : Var (Inputs ns.length) Fp) (self : RegionIndex) :
    ((circuit G ns yaIn).output cfg offset iv self).point.y
      = AssignedCell.of self (offset + prefixRows ns ns.length) cfg.lambda1 := rfl

end Halo2.Ironwood.Sinsemilla.Chain
