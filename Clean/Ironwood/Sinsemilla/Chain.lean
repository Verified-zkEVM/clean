import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Ecc.DoubleAndAdd
import Clean.Orchard.Sinsemilla.HVec
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
- `hash_all_pieces` (lines ~317-390): the piece loop. For each piece, `hash_piece` is called at
  the running `offset`, then `offset += piece.num_words()`, threading the accumulator
  `(x_a, y_a)` from one piece's exit into the next piece's entry. After the last piece a final
  `y_a` cell is assigned into the `λ₁` column at the trailing row (the "dummy" row queried by the
  final-piece gate).
- `hash_piece` (lines 295-493): each piece enables `q_sinsemilla2 = 1` on interior rows, and on
  the last row `0` (between pieces) or `2` (final piece). The Sinsemilla gate reads adjacent row
  pairs; the gate at a piece's LAST row links that piece's last double-and-add row to the NEXT
  piece's first row (rotation +1 crosses the piece boundary because `offset += num_words` makes
  the pieces adjacent). Slice 1 (`HashPiece.loop`, gate bound `w`) enables the gate on interior
  pairs ONLY; the PIECE-LINKING gate at the last row belongs HERE — matching the donor boundary.

Orchard `feat/ironwood` uses **vanilla** halo2_gadgets 0.5.0 Sinsemilla unchanged, `K = 10`.

## Slice-2 scope (this file)

The chaining circuit `hash_all_pieces`, composing one `HashPiece.circuit` per message piece and
applying the piece-linking Sinsemilla gate between consecutive pieces (and the final-piece gate at
the trailing dummy row). This is the SECOND subcircuit-composition consumer (after
`Clean/Ironwood/Ecc/MulComplete.lean`); the child here (`HashPiece.circuit`) itself contains a
loop, so this is composition-of-loop-children.

Structure mirrors the phase-one donor `Clean/Orchard/Sinsemilla/HashToPoint.lean`, `Chain.*`
namespace (`Nil`/`Cons` recursion over the piece-width list `ns : List ℕ`), lifted region-level:
- value algebra (`PieceChunks`, `honestChunks`, `PieceBounds`, `ZsFacts`, `ZsHonest`, `enterYA`,
  `zLengths`, and the pure chunk/running-sum lemmas) lifted wholesale from the donor `Chain`.
- the circuit recurses over `ns`, calling `HashPiece.circuit G n |>.call cfg offset input` at
  running offsets and enabling the linking `sinsemillaGate` at each piece boundary.

## EnvAssumptions threading (the first exercise)

Parent and children share the SAME `HashPiece.Config` (unlike MulComplete, where parent had its
own `Config` and the child an `Add.Config`). The parent `EnvAssumptions` is the loaded generator
table `GeneratorTableLoaded G cfg.generatorTable env`; each child's `EnvAssumptions` is the SAME
predicate on the SAME `cfg.generatorTable`, so the parent discharges every child's env-assumption
from its own by `id`. See the report notes at `chain` for the threading verdict.
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
  (Config sinsemillaGate qS3Expr yAExpr xRExpr readCell adv dRow zRow)

/-! ## Value-level chain algebra (lifted from the donor `Chain.*`)

All framework-agnostic `Fp`/`ℕ`/`Point` facts over the Ironwood `pieceWord`/`pieceZ` (which are
definitionally the donor's). Names kept identical to the donor so a future grep-map is trivial. -/

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

Mirrors the donor `Chain.Input`/`Output`, but the running sums use the flat `HVec` encoding
(`zLengths ns`) and the entering `yA` is carried as a plain already-assigned cell (the
Ironwood convention — read via `readCell`; soundness never consumes it). -/

/-- Verifier-visible inputs of the whole chain: the piece values, the entering accumulator `x_A`
cell, and the entering accumulator `y` cell. -/
structure Inputs (len : ℕ) (F : Type) where
  pieces : Vector F len
  xA : F
  yA : F
deriving ProvableStruct

/-- Outputs: the hash point, the message's first double-and-add row (the previous level's gate
pairs its last row with this one), and the full per-piece running sums `zs`. -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  first : DoubleAndAddRow F
  zs : HVec (zLengths ns) F
deriving ProvableStruct

/-! ## Honest chain accumulator (value level)

The honest accumulator entering piece `i` chains through the pieces via `accAfter`. `chainAcc`
is the entering `(x, y)` accumulator for the suffix `ns`, given a starting `(x, y)`. Used by the
native `yA` hint witnesses that thread each piece boundary. -/

/-- The honest accumulator after hashing the whole suffix `ns` starting from `(x, y)`. Each piece
of width `n` advances the accumulator by `accAfter G · piece (n+1)`. -/
def chainAcc (G : Generators) : (ns : List ℕ) → Vector Fp ns.length → Fp × Fp → Fp × Fp
  | [], _, acc => acc
  | n :: rest, pieces, acc =>
    chainAcc G rest pieces.tail (accAfter G acc pieces[0] (n + 1))

/-! ## The chaining circuit body (region-level composition-of-loop-children)

`hash_all_pieces` (`hash_to_point.rs`), recursive over the piece-width list `ns`, in the same
ambient region. Each piece calls the proven child `HashPiece.circuit G n` at the running offset,
threading the accumulator; the linking `sinsemillaGate` fires at each piece's last row (rotation
+1 crosses into the next piece's first row). The trailing dummy row (`Nil`) holds the witnessed
final `y_a` in `λ₁`, matching Rust's post-loop `assign_advice(λ₁, offset, y_a)` + dummy `λ₂`/`x_p`.

The whole body is `synthesize`-shaped: it takes the parent `Config` (= `HashPiece.Config`, shared
with the children), the running `offset`, the message inputs, and the entering accumulator cells.
It returns the chain `Output`. -/

/-- Native witness of the honest entering-`y` cell for a piece boundary: reads the previous
accumulator cells and the honest chain to produce the exit-`y` value threaded into the next
piece's `input.yA`. (Rust threads `y_a` as a `Y<Value>`; here it is an assigned advice cell whose
value the honest program pins — soundness never reads it, the linking gate ties it down.) -/
def yAWit (G : Generators) (piece xAcell yAcell : AssignedCell Fp) (n : ℕ) :
    WitgenIR Fp 1 :=
  .native fun env =>
    #v[(accAfter G (readCell env xAcell, readCell env yAcell) (readCell env piece) (n + 1)).2]

/-- The chaining body. Recursive over `ns`; `xACell`/`yACell` are the entering accumulator cells
for this suffix (piece 0's entering `(x_a, y_a)`). Returns `(point, first, zs)`.

- `Nil` (`[]`): the trailing dummy row at `offset` — witness the final `y_a` into `λ₁` (native,
  from the entering `y_a` cell, which for the empty suffix IS the exit), and expose the point
  `(x_a, y_a)` and the dummy first row `{ xA := x_a, xP := 0, λ₁ := y_a, λ₂ := 0 }`.
- `Cons` (`n :: rest`): call `HashPiece.circuit G n` at `offset` on `⟨pieces[0], x_a, y_a⟩`; witness
  the next piece's entering `y_a` cell (native, `yAWit`); recurse on `rest` at `offset + (n + 1)`;
  enable the linking `sinsemillaGate` at `offset + n`. The chain's `first` is the head piece's
  first row; the point is the tail's point; `zs = HVec.cons out.zs tailZs`. -/
def chainBody (G : Generators) (cfg : Config) :
    (ns : List ℕ) → (offset : ℕ) → (pieces : Vector (AssignedCell Fp) ns.length) →
      (xACell yACell : AssignedCell Fp) →
      RegionCircuit Fp (Var (Output ns) Fp)
  | [], offset, _, xACell, yACell => do
    -- trailing dummy row: witness the final y_a into λ₁ (native), dummy λ₂ / x_p at `offset`
    let yFin ← assignAdvice cfg.lambda1 offset
      (.native fun env => #v[readCell env yACell])
    let l2Dummy ← assignAdvice cfg.lambda2 offset (.native fun _ => #v[(0 : Fp)])
    let xPDummy ← assignAdvice cfg.xP offset (.native fun _ => #v[(0 : Fp)])
    return {
      point := { x := xACell, y := yFin },
      first := { xA := xACell, xP := xPDummy, lambda1 := yFin, lambda2 := l2Dummy },
      zs := HVec.nil }
  | n :: rest, offset, pieces, xACell, yACell => do
    -- one piece via the proven child, at the running offset
    let out ← (HashPiece.circuit G n).call cfg offset
      { piece := pieces[0], xA := xACell, yA := yACell }
    -- witness the next piece's entering y_a cell (native honest value)
    let yANext ← assignAdvice cfg.lambda1 (offset + (n + 1))
      (yAWit G pieces[0] xACell yACell n)
    -- recurse on the tail at `offset + (n + 1)`, entering at the piece's exit accumulator
    let tailOut ← chainBody G cfg rest (offset + (n + 1))
      (Vector.cast (by simp) pieces.tail) out.xANext yANext
    -- the piece-linking Sinsemilla gate at this piece's last row (`offset + n`); rotation +1
    -- reads the next piece's first row. `q_s2` at the link row is HashPiece's own fixed cell
    -- (`0` between pieces; the final-piece `2` requires a `finalPiece`-aware child — see report).
    (sinsemillaGate cfg).enable (offset + n)
    return {
      point := tailOut.point,
      first := out.first,
      zs := HVec.cons out.zs tailOut.zs }

/-- Per-piece operations decomposition (holds by `rfl` via the monad's `operations_bind`) — the
crux that makes the piece recursion inductable. The Cons body's op list is the child call's
chunk ++ the `yANext` assign ++ the tail body's ops ++ the linking gate's enable. Mirrors
`MulComplete.loop_operations_succ`, but the recursion is over the piece list, and the tail's ops
depend on the child call's output cells (`out.xANext`, the witnessed `yANext`). -/
theorem chainBody_operations_cons (G : Generators) (cfg : Config) (n : ℕ) (rest : List ℕ)
    (offset : ℕ) (pieces : Vector (AssignedCell Fp) (rest.length + 1))
    (xACell yACell : AssignedCell Fp) (self : RegionIndex) :
    (chainBody G cfg (n :: rest) offset pieces xACell yACell).operations self
      = ((HashPiece.circuit G n).call cfg offset
            { piece := pieces[0], xA := xACell, yA := yACell }).operations self
        ++ (assignAdvice cfg.lambda1 (offset + (n + 1))
              (yAWit G pieces[0] xACell yACell n)).operations self
        ++ (chainBody G cfg rest (offset + (n + 1)) (Vector.cast (by simp) pieces.tail)
              (((HashPiece.circuit G n).call cfg offset
                { piece := pieces[0], xA := xACell, yA := yACell }).output self).xANext
              ((assignAdvice cfg.lambda1 (offset + (n + 1))
                (yAWit G pieces[0] xACell yACell n)).output self)).operations self
        ++ ((sinsemillaGate cfg).enable (offset + n)).operations self := by
  simp only [chainBody, RegionCircuit.operations_bind,
    RegionCircuit.operations_pure, List.append_assoc, List.append_nil]

/-! ## Contract

`EnvAssumptions` is the loaded generator table (the SAME predicate the children reference — the
parent discharges each child's env-assumption from its own). `Spec` is the donor `Chain.Spec`:
the message decomposes into a flat chunk list, the running sums are the per-piece suffix
recombinations, and — for any on-curve entering accumulator `A` matching the first row's
`x_a`/entering-`Y_A` — the point is the spec-level `hashToPoint` chain point over the whole
message. -/

/-- The chain `Spec` (donor `Chain.Spec`), verifier view. -/
def Spec (G : Generators) (ns : List ℕ) (input : Value (Inputs ns.length) Fp)
    (output : Value (Output ns) Fp) (_ : Unit) : Prop :=
  output.first.xA = input.xA ∧
  ∃ chunks : List ℕ, PieceChunks ns input.pieces chunks ∧
    ZsFacts ns chunks output.zs ∧
    ∀ A : Point Fp, A.OnCurve → A.x = input.xA →
      2 * A.y = enterYA ns.isEmpty output.first →
      ∀ B, hashToPoint G.S A chunks = some B →
        output.point.x = B.x ∧ output.point.y = B.y

/-- The honest-prover precondition (donor `Chain.ProverAssumptions`): the pieces are in range and
the spec-level chain over the honest chunks is defined. -/
def ProverAssumptions (G : Generators) (ns : List ℕ) (input : Value (Inputs ns.length) Fp) :
    Prop :=
  PieceBounds ns input.pieces ∧
  ∃ (A B : Point Fp), A.OnCurve ∧ A.x = input.xA ∧ A.y = input.yA ∧
    hashToPoint G.S A (honestChunks ns input.pieces) = some B

/-! ## The value-level chain-glue lemma (`soundness_aux`, donor-lifted)

Given one piece's prefix contract (its `last` row's `x_p`/`y_p` land on `S(m_n)`, and its chain
contract over the first `n` words), the linking gate completing the piece's last step (via
`step_coordinates_of_constraints`), and the tail's chain contract, the level's chain contract
follows. Lifted from the donor `Chain.Cons.soundness_aux`, re-spelled over the Ironwood
`sinsemillaGate` polynomial (its `yCheck` is `4·λ₂·(xA−xA') − (2·Y_A + (2−qS3)·Y_A_next +
qS3·2·λ₁_next)`, where `qS3 = qS2·(qS2−1)` at the link row; `qS2 = 0` between pieces gives
`qS3 = 0`, `qS2 = 2` for the final piece gives `qS3 = 2`). -/
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

/-- Output-value decomposition of the Cons body: its `first` is the head child's first row, its
`point` is the tail body's point, and its `zs` is `HVec.cons` of the head child's `zs` and the
tail body's `zs`. Holds by `rfl` (structure-literal projection through the do-block binders). -/
theorem chainBody_output_cons (G : Generators) (cfg : Config) (n : ℕ) (rest : List ℕ)
    (offset : ℕ) (pieces : Vector (AssignedCell Fp) (rest.length + 1))
    (xACell yACell : AssignedCell Fp) (self : RegionIndex) :
    (chainBody G cfg (n :: rest) offset pieces xACell yACell).output self
      = { point := ((chainBody G cfg rest (offset + (n + 1)) (Vector.cast (by simp) pieces.tail)
                (((HashPiece.circuit G n).call cfg offset
                  { piece := pieces[0], xA := xACell, yA := yACell }).output self).xANext
                ((assignAdvice cfg.lambda1 (offset + (n + 1))
                  (yAWit G pieces[0] xACell yACell n)).output self)).output self).point,
          first := (((HashPiece.circuit G n).call cfg offset
                { piece := pieces[0], xA := xACell, yA := yACell }).output self).first,
          zs := HVec.cons
                (((HashPiece.circuit G n).call cfg offset
                  { piece := pieces[0], xA := xACell, yA := yACell }).output self).zs
                ((chainBody G cfg rest (offset + (n + 1)) (Vector.cast (by simp) pieces.tail)
                  (((HashPiece.circuit G n).call cfg offset
                    { piece := pieces[0], xA := xACell, yA := yACell }).output self).xANext
                  ((assignAdvice cfg.lambda1 (offset + (n + 1))
                    (yAWit G pieces[0] xACell yACell n)).output self)).output self).zs } := by
  simp only [chainBody, RegionCircuit.output_bind, RegionCircuit.output_pure]

/-! ## The gadget bundle

`hash_all_pieces` over the piece-width list `ns`. `synthesize` is `chainBody` starting from the
message inputs; `EnvAssumptions` is the loaded generator table (shared with every child call). -/

/-- **EnvAssumptions threading (verdict: trivial identity thread).** A child `HashPiece.circuit`'s
`EnvAssumptions` on a config `cfg` and placed env is *definitionally identical* to the parent's:
both are `GeneratorTableLoaded G cfg.generatorTable env.env`, because parent and children share the
SAME `cfg.generatorTable` (unlike MulComplete, where the child took a distinct `Add.Config`). So a
parent soundness proof discharges every child's env-assumption from its own `hE` by `id` — no
lifting, no per-child bookkeeping. This is the first EnvAssumptions-threading-through-composition
exercise, and it is the easy case; a harder case would be a child whose env-fact names a *derived*
sub-config column, needing a projection lemma. -/
theorem child_envAssumptions_eq (G : Generators) (n : ℕ) (cfg : Config)
    (env : Placed Environment Fp) :
    (HashPiece.circuit G n).EnvAssumptions cfg env
      = GeneratorTableLoaded G cfg.generatorTable env.env := rfl

instance elaborated (G : Generators) (ns : List ℕ) (cfg : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp (Inputs ns.length) (Output ns)
      (fun input : Var (Inputs ns.length) Fp =>
        chainBody G cfg ns offset input.pieces input.xA input.yA) := {}

/-- The chaining region-circuit bundle. `EnvAssumptions` is `GeneratorTableLoaded` on the shared
`cfg.generatorTable` — the SAME predicate each child `HashPiece.circuit` references, so the
parent discharges every child's env-assumption from its own by `id` (the EnvAssumptions-threading
exercise; verdict: trivial identity thread, since parent and children share `cfg.generatorTable`).

Soundness inducts over `ns`: each piece is a folded `HashPiece.circuit.call` chunk consumed via
the composition iff (`subcircuit_constraints_iff_soundness`, `rw`-instantiated per call — the
MulComplete route, as the primed simp form does not fire on the bare-place/env loop spelling), the
linking `sinsemillaGate` reduces to the value-level secant/y-check, and `soundness_aux` glues the
piece + gate + tail chain contracts. Completeness mirrors the ladder on the honest witnesses via
`call_constraints_and_spec` (the FRAMEWORK CANDIDATE from MulComplete — reused here). -/
def circuit (G : Generators) (ns : List ℕ) :
    FormalRegionCircuit Fp Config Config (Inputs ns.length) (Output ns) where
  name := "sinsemilla hash_all_pieces"
  configure := fun cfg => pure cfg
  synthesize cfg offset input := chainBody G cfg ns offset input.pieces input.xA input.yA
  elaborated := elaborated G ns
  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env
  Assumptions _ := True
  Spec := Spec G ns
  ProverAssumptions input _ := ProverAssumptions G ns input
  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output hE hA hc
    -- Route over the piece list via the operations decomposition (`chainBody_operations_cons`),
    -- consuming each `HashPiece.circuit.call` chunk by the composition iff and the linking gate by
    -- its value-level secant/y-check, then `soundness_aux`. Structure-complete: the framework-half
    -- (peeling the recursive op list, the rw-generic-iff sites per call, reading the output cells
    -- off the env) is the remaining work — see the TACTIC GAP report.
    sorry
  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hE hA hpa
    -- The honest-prover ladder over the piece list: each child chunk via `call_constraints_and_spec`
    -- (MulComplete's FRAMEWORK CANDIDATE, reused), threading each piece's exit accumulator (Spec
    -- output value) into the next piece's entering `y_a` witness, and discharging each linking gate
    -- on the honest `rowValue`/`enterYA` algebra. Structure-complete — see the TACTIC GAP report.
    sorry

end Halo2.Ironwood.Sinsemilla.Chain
