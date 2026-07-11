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
  (Config sinsemillaGate qS3Expr yAExpr xRExpr readCell adv dRow zRow qS2Boundary
   qS2Boundary_run)

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

/-- The number of region rows the chain occupies: `nᵢ + 1` word rows per piece, plus the
trailing dummy row. The bundle places the boundary-`y` scratch cells past this extent. -/
def pieceRows : List ℕ → ℕ
  | [] => 1
  | n :: rest => (n + 1) + pieceRows rest

/-- The chaining body. Recursive over `ns`; `xACell`/`yACell` are the entering accumulator cells
for this suffix (piece 0's entering `(x_a, y_a)`); `scratch` is a row index past the whole
message's rows where the boundary-`y` witness cells live (one per piece boundary — Rust threads
`y_a` as a pure `Y<Value>` and never materializes it; the Ironwood child reads its entering `y`
off a cell, so the chain pins one witness-only scratch cell per boundary, constrained by nothing
and tied down by the linking gate). Returns `(point, first, zs)`.

- `Nil` (`[]`): the trailing dummy row at `offset` — witness the final `y_a` into `λ₁` (native,
  from the entering `y_a` cell, which for the empty suffix IS the exit), and dummy `λ₂`/`x_p`
  (Rust `hash_all_pieces` post-loop).
- `Cons` (`n :: rest`): call `HashPiece.circuit G n rest.isEmpty` at `offset` on
  `⟨pieces[0], x_a, y_a⟩`; re-pin the link-row `q_s2` (the same value the child assigns — fixed
  equations are idempotent — giving the PARENT a handle on the value for the gate reduction);
  witness the next piece's entering `y_a` (native, `yAWit`, at `scratch`); recurse on `rest` at
  `offset + (n + 1)`; enable the linking `sinsemillaGate` at `offset + n` (rotation +1 reads the
  next piece's first row / the dummy row). -/
def chainBody (G : Generators) (cfg : Config) :
    (ns : List ℕ) → (offset scratch : ℕ) → (pieces : Vector (AssignedCell Fp) ns.length) →
      (xACell yACell : AssignedCell Fp) →
      RegionCircuit Fp (Var (Output ns) Fp)
  | [], offset, _, _, xACell, yACell => do
    -- trailing dummy row: witness the final y_a into λ₁ (native), dummy λ₂ / x_p at `offset`
    let yFin ← assignAdvice cfg.lambda1 offset
      (.native fun env => #v[readCell env yACell])
    let l2Dummy ← assignAdvice cfg.lambda2 offset (.native fun _ => #v[(0 : Fp)])
    let xPDummy ← assignAdvice cfg.xP offset (.native fun _ => #v[(0 : Fp)])
    return {
      point := { x := xACell, y := yFin },
      first := { xA := xACell, xP := xPDummy, lambda1 := yFin, lambda2 := l2Dummy },
      zs := HVec.nil }
  | n :: rest, offset, scratch, pieces, xACell, yACell => do
    -- one piece via the proven child, at the running offset; the message's LAST piece runs
    -- with `final_piece = true` (its last-row `q_s2 = 2`), per Rust `hash_all_pieces`
    let out ← (HashPiece.circuit G n rest.isEmpty).call cfg offset
      { piece := pieces[0], xA := xACell, yA := yACell }
    -- the parent's own handle on the link-row `q_s2` (same value the child's round assigns;
    -- `assignFixed` constraints are equations, so the duplicate is idempotent)
    let _q ← assignFixed cfg.qS2 (offset + n) (qS2Boundary rest.isEmpty)
    -- witness the next piece's entering y_a cell (native honest value) at the scratch row
    let yANext ← assignAdvice cfg.lambda1 scratch (yAWit G pieces[0] xACell yACell n)
    -- recurse on the tail at `offset + (n + 1)`, entering at the piece's exit accumulator
    let tailOut ← chainBody G cfg rest (offset + (n + 1)) (scratch + 1)
      (Vector.cast (by simp) pieces.tail) out.xANext yANext
    -- the piece-linking Sinsemilla gate at this piece's last row (`offset + n`); rotation +1
    -- reads the next piece's first row (or the trailing dummy row for the final piece)
    (sinsemillaGate cfg).enable (offset + n)
    return {
      point := tailOut.point,
      first := out.first,
      zs := HVec.cons out.zs tailOut.zs }

/-- Per-piece operations decomposition (holds via the monad's `operations_bind`) — the crux that
makes the piece recursion inductable. The Cons body's op list is the child call's chunk ++ the
link-row `q_s2` re-pin ++ the boundary-`y` assign ++ the tail body's ops ++ the linking gate's
enable. Mirrors `MulComplete.loop_operations_succ`, but the recursion is over the piece list, and
the tail's ops depend on the child call's output cells (`out.xANext`, the witnessed `yANext`). -/
theorem chainBody_operations_cons (G : Generators) (cfg : Config) (n : ℕ) (rest : List ℕ)
    (offset scratch : ℕ) (pieces : Vector (AssignedCell Fp) (rest.length + 1))
    (xACell yACell : AssignedCell Fp) (self : RegionIndex) :
    (chainBody G cfg (n :: rest) offset scratch pieces xACell yACell).operations self
      = ((HashPiece.circuit G n rest.isEmpty).call cfg offset
            { piece := pieces[0], xA := xACell, yA := yACell }).operations self
        ++ (assignFixed cfg.qS2 (offset + n) (qS2Boundary rest.isEmpty)).operations self
        ++ (assignAdvice cfg.lambda1 scratch
              (yAWit G pieces[0] xACell yACell n)).operations self
        ++ (chainBody G cfg rest (offset + (n + 1)) (scratch + 1)
              (Vector.cast (by simp) pieces.tail)
              (((HashPiece.circuit G n rest.isEmpty).call cfg offset
                { piece := pieces[0], xA := xACell, yA := yACell }).output self).xANext
              ((assignAdvice cfg.lambda1 scratch
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
    (offset scratch : ℕ) (pieces : Vector (AssignedCell Fp) (rest.length + 1))
    (xACell yACell : AssignedCell Fp) (self : RegionIndex) :
    (chainBody G cfg (n :: rest) offset scratch pieces xACell yACell).output self
      = { point := ((chainBody G cfg rest (offset + (n + 1)) (scratch + 1)
                (Vector.cast (by simp) pieces.tail)
                (((HashPiece.circuit G n rest.isEmpty).call cfg offset
                  { piece := pieces[0], xA := xACell, yA := yACell }).output self).xANext
                ((assignAdvice cfg.lambda1 scratch
                  (yAWit G pieces[0] xACell yACell n)).output self)).output self).point,
          first := (((HashPiece.circuit G n rest.isEmpty).call cfg offset
                { piece := pieces[0], xA := xACell, yA := yACell }).output self).first,
          zs := HVec.cons
                (((HashPiece.circuit G n rest.isEmpty).call cfg offset
                  { piece := pieces[0], xA := xACell, yA := yACell }).output self).zs
                ((chainBody G cfg rest (offset + (n + 1)) (scratch + 1)
                  (Vector.cast (by simp) pieces.tail)
                  (((HashPiece.circuit G n rest.isEmpty).call cfg offset
                    { piece := pieces[0], xA := xACell, yA := yACell }).output self).xANext
                  ((assignAdvice cfg.lambda1 scratch
                    (yAWit G pieces[0] xACell yACell n)).output self)).output self).zs } := by
  simp only [chainBody, RegionCircuit.output_bind, RegionCircuit.output_pure]

/-! ## Contract-projection and output bridges (the child stays folded)

`rfl`-bridges exposing exactly the child's contract fields and output record without unfolding
the bundle literal — the MulComplete pattern. FRAMEWORK CANDIDATE: a deriving-style mechanism
(or simproc) exposing a `FormalRegionCircuit` literal's contract projections and output record
without unfolding. -/

private theorem hashPiece_spec_eq (G : Generators) (n : ℕ) (b : Bool) :
    (HashPiece.circuit G n b).Spec = HashPiece.Spec G n := rfl

private theorem hashPiece_proverAssumptions_eq (G : Generators) (n : ℕ) (b : Bool) :
    (HashPiece.circuit G n b).ProverAssumptions
      = fun input _ => HashPiece.ProverAssumptions G n input := rfl

private theorem hashPiece_proverSpec_eq (G : Generators) (n : ℕ) (b : Bool) :
    (HashPiece.circuit G n b).ProverSpec
      = fun input output _ => HashPiece.ProverSpec G n input output () := rfl

/-- The child call's output record: the four first/last row cells, the exit `x_a` cell, and the
`w + 1` running-sum cells, at their fixed region-local rows (`HashPiece.synthesize`'s
`cellAt`/`cellVec` reads). -/
private theorem hashPiece_call_output (G : Generators) (n : ℕ) (b : Bool) (cfg : Config)
    (offset : ℕ) (inp : Var HashPiece.Inputs Fp) (self : RegionIndex) :
    ((HashPiece.circuit G n b).call cfg offset inp).output self
      = { first := { xA := .of self offset cfg.xA, xP := .of self offset cfg.xP,
                     lambda1 := .of self offset cfg.lambda1,
                     lambda2 := .of self offset cfg.lambda2 },
          last := { xA := .of self (offset + n) cfg.xA, xP := .of self (offset + n) cfg.xP,
                    lambda1 := .of self (offset + n) cfg.lambda1,
                    lambda2 := .of self (offset + n) cfg.lambda2 },
          xANext := .of self (offset + (n + 1)) cfg.xA,
          zs := Vector.ofFn (fun i => .of self (offset + i.val) cfg.bits) } := rfl

/-- Flat eval of a `fields`-vector of cells is the pointwise cell eval. -/
private theorem eval_fields_eq_map (place : RegionIndex → ℕ) (env : Environment Fp) {k : ℕ}
    (v : Vector (AssignedCell Fp) k) :
    ProvableType.eval (M := fields k) place env v = v.map (AssignedCell.eval place env) := by
  simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements]

/-- Flat eval distributes over `HVec.cons` (the region-level analogue of
`Orchard.Sinsemilla.HVec.eval_cons`). -/
private theorem hvec_eval_cons (place : RegionIndex → ℕ) (env : Environment Fp)
    {n : ℕ} {ns : List ℕ}
    (a : Vector (AssignedCell Fp) n) (b : HVec ns (AssignedCell Fp)) :
    ProvableType.eval (M := HVec (n :: ns)) place env (HVec.cons a b)
      = HVec.cons (ProvableType.eval (M := fields n) place env a)
          (ProvableType.eval (M := HVec ns) place env b) := by
  simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements,
    HVec.cons]
  exact congrArg HVec.mk (Vector.map_append ..)

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

/-- The child's output var in the `FormalRegionCircuit.output` spelling (the composition iff's
form) — same record as `hashPiece_call_output`. -/
private theorem hashPiece_output (G : Generators) (n : ℕ) (b : Bool) (cfg : Config)
    (offset : ℕ) (inp : Var HashPiece.Inputs Fp) (self : RegionIndex) :
    (HashPiece.circuit G n b).output cfg offset inp self
      = { first := { xA := .of self offset cfg.xA, xP := .of self offset cfg.xP,
                     lambda1 := .of self offset cfg.lambda1,
                     lambda2 := .of self offset cfg.lambda2 },
          last := { xA := .of self (offset + n) cfg.xA, xP := .of self (offset + n) cfg.xP,
                    lambda1 := .of self (offset + n) cfg.lambda1,
                    lambda2 := .of self (offset + n) cfg.lambda2 },
          xANext := .of self (offset + (n + 1)) cfg.xA,
          zs := Vector.ofFn (fun i => .of self (offset + i.val) cfg.bits) } := rfl

/-- Mapped-eval plumbing: mapping over the cast tail is the tail of the map. -/
private theorem map_cast_tail {k : ℕ} (pieces : Vector (AssignedCell Fp) (k + 1))
    (f : AssignedCell Fp → Fp) :
    (Vector.cast (by simp) pieces.tail : Vector (AssignedCell Fp) k).map f
      = (pieces.map f).tail := by
  ext i hi
  simp

/-- Halo2-eval (typeclass form) distributes over `HVec.cons`, RHS in the flat
`ProvableType.eval` form (bridged back by `ProvableType.eval_cells` at use sites). -/
private theorem hvec_eval_cons' (env : Placed Environment Fp) {n : ℕ} {ns : List ℕ}
    (a : Vector (AssignedCell Fp) n) (b : HVec ns (AssignedCell Fp)) :
    (eval env (HVec.cons a b : Var (HVec (n :: ns)) Fp) : Value (HVec (n :: ns)) Fp)
      = HVec.cons (ProvableType.eval (M := fields n) env.place env.env a)
          (ProvableType.eval (M := HVec ns) env.place env.env b) := by
  rw [ProvableType.eval_cells (M := HVec (n :: ns))]
  exact hvec_eval_cons env.place env.env a b

/-! ### Literal-eval bridges for the `Output` record

The generic struct-eval simproc does not fire on an `Output ns` literal (its `zs` component's
type `HVec (zLengths ns)` needs `zLengths` unfolding), so the decomposition is provided as
explicit `rfl`-bridges. -/

private theorem output_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    {ns : List ℕ} (p : Point (AssignedCell Fp)) (f : DoubleAndAddRow (AssignedCell Fp))
    (z : HVec (zLengths ns) (AssignedCell Fp)) :
    ProvableStruct.eval place env
        ({ point := p, first := f, zs := z } : (Output ns) (AssignedCell Fp))
      = { point := ProvableType.eval place env p,
          first := ProvableType.eval place env f,
          zs := ProvableType.eval place env z } := by with_unfolding_all rfl

private theorem row_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    (a b c d : AssignedCell Fp) :
    ProvableType.eval place env
        ({ xA := a, xP := b, lambda1 := c, lambda2 := d } : DoubleAndAddRow (AssignedCell Fp))
      = { xA := AssignedCell.eval place env a, xP := AssignedCell.eval place env b,
          lambda1 := AssignedCell.eval place env c, lambda2 := AssignedCell.eval place env d } := by
  rw [ProvableStruct.eval_eq_eval]
  with_unfolding_all rfl

private theorem point_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    (a b : AssignedCell Fp) :
    ProvableType.eval place env ({ x := a, y := b } : Point (AssignedCell Fp))
      = { x := AssignedCell.eval place env a, y := AssignedCell.eval place env b } := by
  with_unfolding_all rfl

private theorem hvec_nil_eval (place : RegionIndex → ℕ) (env : Environment Fp) :
    ProvableType.eval place env (HVec.nil : HVec (zLengths []) (AssignedCell Fp))
      = (HVec.nil : HVec (zLengths []) Fp) := by with_unfolding_all rfl

/-- `hvec_eval_cons` at the `zLengths (n :: rest)` spelling (the form `chainBody`'s output
carries — `rw`'s reducible-transparency keyed matching does not unfold `zLengths`). -/
private theorem hvec_eval_cons_zl (place : RegionIndex → ℕ) (env : Environment Fp)
    (n : ℕ) (rest : List ℕ)
    (a : Vector (AssignedCell Fp) (n + 1)) (b : HVec (zLengths rest) (AssignedCell Fp)) :
    ProvableType.eval (M := HVec (zLengths (n :: rest))) place env (HVec.cons a b)
      = HVec.cons (ProvableType.eval (M := fields (n + 1)) place env a)
          (ProvableType.eval (M := HVec (zLengths rest)) place env b) :=
  hvec_eval_cons place env a b

/-- Projection/eval commute for an OPAQUE `Output` value (destructure + the literal bridge):
the component eval is the projection of the struct eval. -/
private theorem eval_output_point (place : RegionIndex → ℕ) (env : Environment Fp)
    {ns : List ℕ} (x : (Output ns) (AssignedCell Fp)) :
    ProvableType.eval place env x.point = (ProvableStruct.eval place env x).point := by
  cases x with
  | mk p f z => simp only [output_eval_literal]

private theorem eval_output_first (place : RegionIndex → ℕ) (env : Environment Fp)
    {ns : List ℕ} (x : (Output ns) (AssignedCell Fp)) :
    ProvableType.eval place env x.first = (ProvableStruct.eval place env x).first := by
  cases x with
  | mk p f z => simp only [output_eval_literal]

private theorem eval_output_zs (place : RegionIndex → ℕ) (env : Environment Fp)
    {ns : List ℕ} (x : (Output ns) (AssignedCell Fp)) :
    ProvableType.eval place env x.zs = (ProvableStruct.eval place env x).zs := by
  cases x with
  | mk p f z => simp only [output_eval_literal]

/-- Literal-eval bridge for the `Inputs` record. -/
private theorem inputs_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    {k : ℕ} (p : Vector (AssignedCell Fp) k) (a b : AssignedCell Fp) :
    ProvableStruct.eval place env
        ({ pieces := p, xA := a, yA := b } : (Inputs k) (AssignedCell Fp))
      = { pieces := ProvableType.eval (M := fields k) place env p,
          xA := AssignedCell.eval place env a, yA := AssignedCell.eval place env b } := by
  with_unfolding_all rfl

private theorem eval_inputs_pieces (place : RegionIndex → ℕ) (env : Environment Fp)
    {k : ℕ} (x : (Inputs k) (AssignedCell Fp)) :
    (ProvableStruct.eval place env x).pieces
      = ProvableType.eval (M := fields k) place env x.pieces := by
  cases x with
  | mk p a b => simp only [inputs_eval_literal]

private theorem eval_inputs_xA (place : RegionIndex → ℕ) (env : Environment Fp)
    {k : ℕ} (x : (Inputs k) (AssignedCell Fp)) :
    (ProvableStruct.eval place env x).xA = AssignedCell.eval place env x.xA := by
  cases x with
  | mk p a b => simp only [inputs_eval_literal]

private theorem eval_inputs_yA (place : RegionIndex → ℕ) (env : Environment Fp)
    {k : ℕ} (x : (Inputs k) (AssignedCell Fp)) :
    (ProvableStruct.eval place env x).yA = AssignedCell.eval place env x.yA := by
  cases x with
  | mk p a b => simp only [inputs_eval_literal]

/-! ## The soundness induction

The composition-of-loop-children core: induction over the piece list, consuming each folded
`HashPiece.circuit.call` chunk via the composition iff (`rw`-instantiated, MulComplete's
delimited-site convention), the parent-pinned link-row `q_s2` and the linking gate, and the
tail via the induction hypothesis, glued by `soundness_aux`. -/

theorem chainBody_sound (G : Generators) (cfg : Config)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (hTable : GeneratorTableLoaded G cfg.generatorTable env) :
    ∀ (ns : List ℕ) (offset scratch : ℕ) (pieces : Vector (AssignedCell Fp) ns.length)
      (xACell yACell : AssignedCell Fp),
    RegionOperations.Constraints place self env
      ((chainBody G cfg ns offset scratch pieces xACell yACell).operations self) →
    (eval (⟨place, env⟩ : Placed Environment Fp)
        ((chainBody G cfg ns offset scratch pieces xACell yACell).output self)).first
      = { xA := eval (⟨place, env⟩ : Placed Environment Fp) xACell,
          xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
          lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
          lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) }
    ∧ ∃ chunks : List ℕ,
      PieceChunks ns
        (pieces.map (fun c => eval (⟨place, env⟩ : Placed Environment Fp) c)) chunks ∧
      ZsFacts ns chunks (eval (⟨place, env⟩ : Placed Environment Fp)
        ((chainBody G cfg ns offset scratch pieces xACell yACell).output self)).zs ∧
      ∀ A : Point Fp, A.OnCurve →
        A.x = eval (⟨place, env⟩ : Placed Environment Fp) xACell →
        2 * A.y = enterYA ns.isEmpty ((eval (⟨place, env⟩ : Placed Environment Fp)
          ((chainBody G cfg ns offset scratch pieces xACell yACell).output self)).first) →
        ∀ B, hashToPoint G.S A chunks = some B →
          ((eval (⟨place, env⟩ : Placed Environment Fp)
            ((chainBody G cfg ns offset scratch pieces xACell yACell).output self)).point).x
            = B.x
          ∧ ((eval (⟨place, env⟩ : Placed Environment Fp)
            ((chainBody G cfg ns offset scratch pieces xACell yACell).output self)).point).y
            = B.y := by
  intro ns
  induction ns with
  | nil =>
    intro offset scratch pieces xACell yACell _hc
    -- compute the output record (three witnessed dummy cells) and normalize its eval
    simp only [chainBody, circuit_norm, RegionCircuit.output_bind, RegionCircuit.output_pure,
      output_eval_literal, row_eval_literal, point_eval_literal]
    -- (the simp discharges the first-row record equality; the ∃ remains)
    refine ⟨([] : List ℕ), ?_, ?_, ?_⟩
    · simp only [PieceChunks]
    · simp only [ZsFacts]
    -- the trailing dummy row's chain contract: the empty chain returns the entering point
    intro A hAon hAx hAyA B hB
    rw [Orchard.Specs.Sinsemilla.hashToPoint_nil] at hB
    obtain rfl : A = B := Option.some.inj hB
    simp only [List.isEmpty_nil, enterYA, if_true] at hAyA
    refine ⟨hAx.symm, ?_⟩
    have h2 : (2 : Fp) ≠ 0 := by decide
    exact (mul_left_cancel₀ h2 hAyA).symm
  | cons n rest ih =>
    intro offset scratch pieces xACell yACell hc
    rw [chainBody_operations_cons] at hc
    simp only [RegionOperations.constraints_append] at hc
    obtain ⟨⟨⟨⟨hChild, hQdup⟩, hYAw⟩, hTail⟩, hGate⟩ := hc
    -- ▸▸ composition-iff rw site (the piece child; delimited per MulComplete) ◂◂
    rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness
          (HashPiece.circuit G n rest.isEmpty) cfg offset self ⟨place, env⟩
          ⟨pieces[0], xACell, yACell⟩] at hChild
    obtain ⟨-, hSpecFn⟩ := hChild
    have hSpec := hSpecFn hTable trivial
    -- expose the child's contract over env reads (the child stays folded)
    rw [hashPiece_spec_eq] at hSpec
    rw [hashPiece_output] at hSpec
    simp only [HashPiece.Spec, circuit_norm] at hSpec
    obtain ⟨ms, hms, hrecomb, hzs, hfxA, hlxP, hlyP, hchainPc⟩ := hSpec
    -- the tail, via the induction hypothesis (entering cells reduced to their named reads)
    rw [hashPiece_call_output, output_assignAdvice] at hTail
    dsimp only at hTail
    have ihT := ih (offset + (n + 1)) (scratch + 1) (Vector.cast (by simp) pieces.tail)
      (AssignedCell.of self (offset + (n + 1)) cfg.xA)
      (AssignedCell.of self scratch cfg.lambda1)
      hTail
    obtain ⟨hTailFirst, chunksT, hPCt, hZsT, hChainT⟩ := ihT
    -- the parent-pinned link-row q_s2 and the linking gate, over env reads
    have hz1 : ((place self + (offset + n) : ℕ) : ℤ) + 1
        = ((place self + (offset + (n + 1)) : ℕ) : ℤ) := by push_cast; ring
    simp only [circuit_norm] at hQdup
    simp only [sinsemillaGate, Constraints.withSelector, circuit_norm, yAExpr, xRExpr,
      qS3Expr, hz1] at hGate
    rw [hQdup] at hGate
    obtain ⟨hsec, hyck⟩ := hGate
    -- ── assemble: normalize the Cons output components and the tail facts ──
    simp only [circuit_norm] at hTailFirst hZsT hChainT hPCt
    rw [ProvableType.eval_cells (M := fields (n + 1))] at hzs
    -- ▸▸ rw sites (simp misses the Vector-length defeq in the decomposition lemma) ◂◂
    rw [chainBody_output_cons]
    rw [hashPiece_call_output, output_assignAdvice]
    dsimp only
    rw [ProvableStruct.eval_cells_eq_eval]
    dsimp only
    rw [output_eval_literal]
    dsimp only
    rw [row_eval_literal, eval_output_point, hvec_eval_cons_zl place env, eval_output_zs]
    -- reads normalization (targeted — the full `circuit_norm` pass whnf-explodes here)
    simp only [ProvableType.eval_field, AssignedCell.eval, AssignedCell.of_cell,
      Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
      List.isEmpty_cons]
    -- the gate rows, as explicit read-records (projections reduce definitionally)
    refine ⟨?_, (List.range (n + 1)).map ms ++ chunksT, ?_, ?_, ?_⟩
    · -- the first row: the child's first-row cells, its `x_a` pinned to the entering cell
      simp only [DoubleAndAddRow.mk.injEq]
      exact ⟨hfxA, trivial, trivial, trivial⟩
    · -- the pieces decompose into the chunks
      simp only [PieceChunks]
      refine ⟨ms, hms, ?_, chunksT, rfl, ?_⟩
      · rw [Vector.getElem_map]
        exact hrecomb
      · rw [map_cast_tail] at hPCt
        exact hPCt
    · -- the running-sum vectors
      refine zsFacts_cons _ _ _ ?_ ?_
      · rw [hzs]
        apply Vector.ext
        intro r hr
        simp only [Vector.getElem_ofFn]
        refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
        rw [chunks_head_getD ms chunksT (r + j)
          (by simp only [Finset.mem_range] at hj; omega)]
      · rw [chunks_drop_append]
        exact hZsT
    · -- the chain contract: head-piece prefix + linking gate + tail, glued by `soundness_aux`
      intro A hAon hAx hAyA B hB
      have hAyA' : 2 * A.y = yA
          { xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
            xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
            lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
            lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) } := by
        simpa only [List.isEmpty_cons, enterYA, Bool.false_eq_true, if_false] using hAyA
      have hsec' :
          (env.advice cfg.lambda2 ((place self + (offset + n) : ℕ) : ℤ))
            * (env.advice cfg.lambda2 ((place self + (offset + n) : ℕ) : ℤ))
          = (env.advice cfg.xA ((place self + (offset + (n + 1)) : ℕ) : ℤ))
            + xR { xA := env.advice cfg.xA ((place self + (offset + n) : ℕ) : ℤ),
                   xP := env.advice cfg.xP ((place self + (offset + n) : ℕ) : ℤ),
                   lambda1 := env.advice cfg.lambda1 ((place self + (offset + n) : ℕ) : ℤ),
                   lambda2 := env.advice cfg.lambda2 ((place self + (offset + n) : ℕ) : ℤ) }
            + env.advice cfg.xA ((place self + (offset + n) : ℕ) : ℤ) := by
        simp only [xR]
        linear_combination hsec
      have hyck' :
          4 * (env.advice cfg.lambda2 ((place self + (offset + n) : ℕ) : ℤ))
            * ((env.advice cfg.xA ((place self + (offset + n) : ℕ) : ℤ))
              - (env.advice cfg.xA ((place self + (offset + (n + 1)) : ℕ) : ℤ)))
          = 2 * yA { xA := env.advice cfg.xA ((place self + (offset + n) : ℕ) : ℤ),
                     xP := env.advice cfg.xP ((place self + (offset + n) : ℕ) : ℤ),
                     lambda1 := env.advice cfg.lambda1 ((place self + (offset + n) : ℕ) : ℤ),
                     lambda2 := env.advice cfg.lambda2 ((place self + (offset + n) : ℕ) : ℤ) }
            + 2 * enterYA rest.isEmpty
                { xA := env.advice cfg.xA ((place self + (offset + (n + 1)) : ℕ) : ℤ),
                  xP := env.advice cfg.xP ((place self + (offset + (n + 1)) : ℕ) : ℤ),
                  lambda1 := env.advice cfg.lambda1 ((place self + (offset + (n + 1)) : ℕ) : ℤ),
                  lambda2 := env.advice cfg.lambda2 ((place self + (offset + (n + 1)) : ℕ) : ℤ) } := by
        have h := qS3_yRhs rest.isEmpty
          { xA := env.advice cfg.xA ((place self + (offset + (n + 1)) : ℕ) : ℤ),
            xP := env.advice cfg.xP ((place self + (offset + (n + 1)) : ℕ) : ℤ),
            lambda1 := env.advice cfg.lambda1 ((place self + (offset + (n + 1)) : ℕ) : ℤ),
            lambda2 := env.advice cfg.lambda2 ((place self + (offset + (n + 1)) : ℕ) : ℤ) }
        simp only [yA, xR] at h ⊢
        linear_combination hyck + h
      -- the tail's contract, with its first row landed on the read-record
      rw [hTailFirst] at hChainT
      exact soundness_aux G n rest.isEmpty ms hms
        (first := { xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
                    xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
                    lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
                    lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) })
        (last := { xA := env.advice cfg.xA ((place self + (offset + n) : ℕ) : ℤ),
                   xP := env.advice cfg.xP ((place self + (offset + n) : ℕ) : ℤ),
                   lambda1 := env.advice cfg.lambda1 ((place self + (offset + n) : ℕ) : ℤ),
                   lambda2 := env.advice cfg.lambda2 ((place self + (offset + n) : ℕ) : ℤ) })
        (tailFirst := { xA := env.advice cfg.xA ((place self + (offset + (n + 1)) : ℕ) : ℤ),
                        xP := env.advice cfg.xP ((place self + (offset + (n + 1)) : ℕ) : ℤ),
                        lambda1 := env.advice cfg.lambda1 ((place self + (offset + (n + 1)) : ℕ) : ℤ),
                        lambda2 := env.advice cfg.lambda2 ((place self + (offset + (n + 1)) : ℕ) : ℤ) })
        (xAin := env.get xACell.cell.column
          ((place xACell.cell.regionIndex + xACell.cell.rowOffset : ℕ) : ℤ))
        hlxP hlyP hchainPc hsec' hyck' rfl chunksT hChainT A hAon hAx hAyA' B hB

/-! ## The completeness ladder

Honest-prover side. Each child chunk is consumed by `call_constraints_and_specs` (MulComplete's
`call_constraints_and_spec`, extended with the child's `ProverSpec` — the honest-cell facts the
parent needs to discharge the linking gate; copied per the no-cross-gadget-import convention).
FRAMEWORK CANDIDATE (see `MulComplete`): the absorption completeness iff neither exposes the
child's Spec at the honest env nor its ProverSpec; this lemma fills both gaps generically. -/

/-- Completeness-side consumption of a child call: from the chunk's `ExtendsWitnesses` and the
child's preconditions, the chunk's `Constraints`, the child's verifier `Spec` at the prover env's
verifier view, AND the child's honest-prover `ProverSpec`. -/
theorem call_constraints_and_specs {CI Cfg : Type} {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output]
    (child : FormalRegionCircuit Fp CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp) (input : Var Input Fp)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((child.call config offset input).operations self))
    (hE : child.EnvAssumptions config env.toEnvironment)
    (hA : child.Assumptions (eval env.toEnvironment input))
    (hpa : child.ProverAssumptions (eval env input) env.env.hint) :
    RegionOperations.Constraints env.place self env.env
      ((child.call config offset input).operations self)
    ∧ child.Spec (eval env.toEnvironment input)
        (eval env.toEnvironment (child.output config offset input self))
        (child.extract config offset input self env.toEnvironment)
    ∧ child.ProverSpec (eval env input)
        (eval env (child.output config offset input self)) env.env.hint := by
  have hw' : RegionOperations.ExtendsWitnesses env.place self env.env
      ((child.synthesize config offset input).operations self) := hw.1
  obtain ⟨hcons, hps⟩ := child.completeness config offset self env input hw' hE hA hpa
  exact ⟨⟨hcons, trivial⟩,
    child.soundness config offset self env.toEnvironment input hE hA hcons, hps⟩

/-- Literal-eval bridge for the child's `Output` record. -/
private theorem hp_output_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    {w : ℕ} (f l : DoubleAndAddRow (AssignedCell Fp)) (x : AssignedCell Fp)
    (zs : Vector (AssignedCell Fp) w) :
    ProvableStruct.eval place env
        ({ first := f, last := l, xANext := x, zs := zs }
          : HashPiece.Output w (AssignedCell Fp))
      = { first := ProvableType.eval place env f, last := ProvableType.eval place env l,
          xANext := AssignedCell.eval place env x,
          zs := ProvableType.eval (M := fields w) place env zs } := by
  with_unfolding_all rfl

/-- Literal-eval bridge for the child's `Inputs` record. -/
private theorem hp_inputs_eval_literal (place : RegionIndex → ℕ) (env : Environment Fp)
    (p a b : AssignedCell Fp) :
    ProvableStruct.eval place env
        ({ piece := p, xA := a, yA := b } : HashPiece.Inputs (AssignedCell Fp))
      = { piece := AssignedCell.eval place env p, xA := AssignedCell.eval place env a,
          yA := AssignedCell.eval place env b } := by
  with_unfolding_all rfl

/-- **Chain-body completeness induction.** From the body's honest witnesses, the loaded
generator table, and the honest-prover chain preconditions (entering point `A` on the entering
cells, in-range pieces, defined chain to `B`): the body's constraints hold, and the level's
first-row `enterYA` derivation lands on `2·A.y` (the fact the PREVIOUS level's linking gate
consumes — the exit-accumulator → entering-`y` threading). -/
theorem chainBody_complete (G : Generators) (cfg : Config)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (hTable : GeneratorTableLoaded G cfg.generatorTable env.env.toEnvironment) :
    ∀ (ns : List ℕ) (offset scratch : ℕ) (pieces : Vector (AssignedCell Fp) ns.length)
      (xACell yACell : AssignedCell Fp) (A B : Point Fp),
    A.OnCurve →
    A.x = eval env.toEnvironment xACell →
    A.y = eval env.toEnvironment yACell →
    PieceBounds ns (pieces.map (fun c => eval env.toEnvironment c)) →
    hashToPoint G.S A
      (honestChunks ns (pieces.map (fun c => eval env.toEnvironment c))) = some B →
    RegionOperations.ExtendsWitnesses env.place self env.env
      ((chainBody G cfg ns offset scratch pieces xACell yACell).operations self) →
    RegionOperations.Constraints env.place self env.env
      ((chainBody G cfg ns offset scratch pieces xACell yACell).operations self)
    ∧ enterYA ns.isEmpty (ProvableStruct.eval env.place env.env.toEnvironment
        ((chainBody G cfg ns offset scratch pieces xACell yACell).output self)).first
      = 2 * A.y := by
  intro ns
  induction ns with
  | nil =>
    intro offset scratch pieces xACell yACell A B hAon hAx hAy hbounds hchain hwit
    simp only [chainBody, circuit_norm, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure, RegionCircuit.output_bind, RegionCircuit.output_pure,
      output_eval_literal, row_eval_literal, point_eval_literal,
      List.isEmpty_nil, enterYA, if_true] at hwit ⊢
    obtain ⟨hWy, -, -⟩ := hwit
    simp only [Witgen.WitgenIROver.eval] at hWy
    rw [hWy, hAy]
    simp [readCell, ProvableType.eval_field, AssignedCell.eval,
      Placed.toEnvironment_place, Placed.toEnvironment_env]
  | cons n rest ih =>
    intro offset scratch pieces xACell yACell A B hAon hAx hAy hbounds hchain hwit
    -- normalize the entering values to the raw cell-read spelling
    simp only [ProvableType.eval_field, Placed.toEnvironment_place, Placed.toEnvironment_env,
      AssignedCell.eval] at hAx hAy hbounds hchain
    have hAvalid : A.Valid := Or.inl hAon
    have hA0 : A ≠ 0 := Orchard.Point.ne_zero_of_onCurve hAon
    -- split the honest witnesses at the piece boundary
    rw [chainBody_operations_cons] at hwit
    simp only [RegionOperations.extendsWitnesses_append] at hwit
    obtain ⟨⟨⟨⟨hWchild, hWq⟩, hWyA⟩, hWtail⟩, -⟩ := hwit
    -- split the honest chain at the piece boundary
    simp only [honestChunks, Vector.getElem_map] at hchain
    obtain ⟨B₁, hpre, hsuffix⟩ := Orchard.Specs.Sinsemilla.hashToPoint_append_some hchain
    simp only [PieceBounds, Vector.getElem_map] at hbounds
    obtain ⟨hb0, hbrest⟩ := hbounds
    -- ── the head piece, via `call_constraints_and_specs` ──
    have hinp : (eval env (⟨pieces[0], xACell, yACell⟩ : Var HashPiece.Inputs Fp)
        : HashPiece.Inputs Fp)
        = { piece := AssignedCell.eval env.place env.env.toEnvironment pieces[0],
            xA := AssignedCell.eval env.place env.env.toEnvironment xACell,
            yA := AssignedCell.eval env.place env.env.toEnvironment yACell } := by
      rw [ProvableStruct.eval_cells_eq_eval_prover, hp_inputs_eval_literal]
    obtain ⟨hCchild, hSpecChild, hPSchild⟩ := call_constraints_and_specs
      (HashPiece.circuit G n rest.isEmpty) cfg offset self env
      ⟨pieces[0], xACell, yACell⟩ hWchild hTable trivial
      (by rw [hashPiece_proverAssumptions_eq, hinp]
          simp only [AssignedCell.eval]
          exact ⟨hb0, A, B₁, hAon, hAx, hAy, hpre⟩)
    -- the child's honest-cell facts (ProverSpec) at the honest entering point
    rw [hashPiece_proverSpec_eq, hashPiece_output] at hPSchild
    simp only [ProvableStruct.eval_cells_eq_eval_prover, hp_inputs_eval_literal,
      hp_output_eval_literal, HashPiece.ProverSpec, row_eval_literal,
      AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice] at hPSchild
    obtain ⟨hYAfirst, hxANext, hsecH, hyRel⟩ := hPSchild A B₁ hAx hAy hpre
    -- B₁ is on-curve (chain points of a defined hash)
    have hprefix_lt : ∀ m ∈ (List.range (n + 1)).map
        (pieceWord (env.env.get pieces[0].cell.column
          ((env.place pieces[0].cell.regionIndex + pieces[0].cell.rowOffset : ℕ) : ℤ))),
        m < 2 ^ K := by
      intro m hm
      rcases List.mem_map.mp hm with ⟨r, hr, rfl⟩
      exact pieceWord_lt _ r
    have hB₁valid : B₁.Valid :=
      Orchard.Specs.Sinsemilla.hashToPoint_valid hAvalid hprefix_lt hpre
    have hB₁0 : B₁ ≠ 0 :=
      Orchard.Specs.Sinsemilla.hashToPoint_ne_zero hAvalid hA0 hprefix_lt hpre
    have hB₁on : B₁.OnCurve := by
      rcases hB₁valid with h | h
      · exact h
      · exact False.elim (hB₁0 h)
    -- the scratch boundary-y pin lands on B₁.y (the honest chain through `accAfter`)
    simp only [circuit_norm, yAWit, Witgen.WitgenIROver.eval, readCell] at hWyA
    rw [← hAx, ← hAy] at hWyA
    have hacc := accAfter_eq_chain G
      (env.env.get pieces[0].cell.column
        ((env.place pieces[0].cell.regionIndex + pieces[0].cell.rowOffset : ℕ) : ℤ)) hpre
    rw [hacc] at hWyA
    -- the tail, via the induction hypothesis (entering at (B₁.x, B₁.y) on the named cells)
    rw [hashPiece_call_output, output_assignAdvice] at hWtail
    dsimp only at hWtail
    obtain ⟨hCtail, hEnterTail⟩ := ih (offset + (n + 1)) (scratch + 1)
      (Vector.cast (by simp) pieces.tail)
      (AssignedCell.of self (offset + (n + 1)) cfg.xA)
      (AssignedCell.of self scratch cfg.lambda1) B₁ B hB₁on
      (by simp only [ProvableType.eval_field, Placed.toEnvironment_place,
            Placed.toEnvironment_env, AssignedCell.eval, AssignedCell.of_cell,
            Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice]
          exact hxANext.symm)
      (by simp only [ProvableType.eval_field, Placed.toEnvironment_place,
            Placed.toEnvironment_env, AssignedCell.eval, AssignedCell.of_cell,
            Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice]
          exact hWyA.symm)
      (by simp only [ProvableType.eval_field, Placed.toEnvironment_place,
            Placed.toEnvironment_env]
          rw [map_cast_tail]
          exact hbrest)
      (by simp only [ProvableType.eval_field, Placed.toEnvironment_place,
            Placed.toEnvironment_env]
          rw [map_cast_tail]
          exact hsuffix)
      hWtail
    -- the tail's first row reads (soundness of the tail's own constraints)
    obtain ⟨hTailFirst, -⟩ := chainBody_sound G cfg env.place self env.env.toEnvironment hTable
      rest (offset + (n + 1)) (scratch + 1) (Vector.cast (by simp) pieces.tail)
      (AssignedCell.of self (offset + (n + 1)) cfg.xA)
      (AssignedCell.of self scratch cfg.lambda1) hCtail
    rw [ProvableStruct.eval_cells_eq_eval] at hTailFirst
    dsimp only at hTailFirst
    rw [hTailFirst] at hEnterTail
    simp only [ProvableType.eval_field, AssignedCell.eval, AssignedCell.of_cell,
      Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
      Environment.get_advice] at hEnterTail
    -- ── assemble ──
    refine ⟨?_, ?_⟩
    · -- the constraints: child ++ q_s2 re-pin ++ boundary-y ++ tail ++ linking gate
      rw [chainBody_operations_cons]
      simp only [RegionOperations.constraints_append]
      simp only [circuit_norm] at hWq
      refine ⟨⟨⟨⟨hCchild, ?_⟩, ?_⟩, hCtail⟩, ?_⟩
      · -- the re-pinned fixed cell: constraint = its own witness pin
        simp only [circuit_norm]
        exact hWq
      · -- the boundary-y cell is witness-only
        simp only [circuit_norm]
      · -- the linking gate on the honest values
        have hz1 : ((env.place self + (offset + n) : ℕ) : ℤ) + 1
            = ((env.place self + (offset + (n + 1)) : ℕ) : ℤ) := by push_cast; ring
        simp only [sinsemillaGate, Constraints.withSelector, circuit_norm, yAExpr, xRExpr,
          qS3Expr, hz1]
        rw [hWq]
        constructor
        · -- secant: the child's honest last-step completion
          simp only [xR] at hsecH
          linear_combination hsecH
        · -- y check: `nextYA` lands on `2·B₁.y`, the tail's entering `Y_A` derivation too
          have hq := qS3_yRhs rest.isEmpty
            { xA := env.env.toEnvironment.advice cfg.xA
                ((env.place self + (offset + (n + 1)) : ℕ) : ℤ),
              xP := env.env.toEnvironment.advice cfg.xP
                ((env.place self + (offset + (n + 1)) : ℕ) : ℤ),
              lambda1 := env.env.toEnvironment.advice cfg.lambda1
                ((env.place self + (offset + (n + 1)) : ℕ) : ℤ),
              lambda2 := env.env.toEnvironment.advice cfg.lambda2
                ((env.place self + (offset + (n + 1)) : ℕ) : ℤ) }
          simp only [yA, xR, enterYA] at hq hEnterTail hyRel hYAfirst ⊢
          linear_combination 2 * hyRel - hq - 2 * hEnterTail
    · -- the level's entering-`Y_A` fact for the PREVIOUS gate: the child's first row
      rw [chainBody_output_cons, hashPiece_call_output, output_assignAdvice]
      dsimp only
      rw [output_eval_literal]
      dsimp only
      rw [row_eval_literal]
      simp only [List.isEmpty_cons, enterYA, Bool.false_eq_true, if_false]
      simpa only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
        Cell.of_rowOffset, Cell.of_column, Environment.get_advice] using hYAfirst

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
theorem child_envAssumptions_eq (G : Generators) (n : ℕ) (b : Bool) (cfg : Config)
    (env : Placed Environment Fp) :
    (HashPiece.circuit G n b).EnvAssumptions cfg env
      = GeneratorTableLoaded G cfg.generatorTable env.env := rfl

instance elaborated (G : Generators) (ns : List ℕ) (cfg : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp (Inputs ns.length) (Output ns)
      (fun input : Var (Inputs ns.length) Fp =>
        chainBody G cfg ns offset (offset + pieceRows ns) input.pieces input.xA input.yA) := {}

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
  synthesize cfg offset input :=
    chainBody G cfg ns offset (offset + pieceRows ns) input.pieces input.xA input.yA
  elaborated := elaborated G ns
  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env
  Assumptions _ := True
  Spec := Spec G ns
  ProverAssumptions input _ := ProverAssumptions G ns input
  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output hE hA hc
    -- the piece-list induction does all the work
    obtain ⟨hFirst, chunks, hPC, hZs, hContract⟩ :=
      chainBody_sound G cfg env.place self env.env hE ns offset (offset + pieceRows ns)
        input_var.pieces input_var.xA input_var.yA hc
    -- land the abstract input/output values on the body's eval forms
    rw [ElaboratedRegionCircuit.output_eq] at h_output
    rw [ProvableStruct.eval_cells_eq_eval] at h_input h_output
    rw [ProvableStruct.eval_cells_eq_eval] at hFirst hZs
    simp only [ProvableStruct.eval_cells_eq_eval] at hContract
    dsimp only at hFirst hZs hContract
    refine ⟨?_, chunks, ?_, ?_, ?_⟩
    · -- output.first.xA = input.xA
      rw [← h_output, ← h_input, eval_inputs_xA, hFirst]
      simp only [ProvableType.eval_field, AssignedCell.eval]
    · -- the pieces decompose
      have h : input.pieces = Vector.map
          (fun c => eval (⟨env.place, env.env⟩ : Placed Environment Fp) c)
          input_var.pieces := by
        rw [← h_input, eval_inputs_pieces, eval_fields_eq_map]
        apply Vector.ext
        intro i hi
        simp [Vector.getElem_map, AssignedCell.eval, ProvableType.eval_field]
      rw [h]
      exact hPC
    · -- the running sums
      rw [← h_output]
      exact hZs
    · -- the chain contract
      intro A hAon hAx hAyA B hB
      rw [← h_output]
      refine hContract A hAon ?_ ?_ B hB
      · rw [hAx, ← h_input, eval_inputs_xA]
        simp only [ProvableType.eval_field, AssignedCell.eval]
      · rw [← h_output] at hAyA
        exact hAyA
  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hE hA hpa
    obtain ⟨hbounds, A, B, hAon, hAx, hAy, hchain⟩ := hpa
    simp only [Placed.toEnvironment_env] at hE
    -- land the abstract input value on the entering cells
    rw [ProvableStruct.eval_cells_eq_eval_prover] at h_input
    have hpieces : input.pieces = Vector.map
        (fun c => eval env.toEnvironment c) input_var.pieces := by
      rw [← h_input, eval_inputs_pieces, eval_fields_eq_map]
      apply Vector.ext
      intro i hi
      simp [Vector.getElem_map, AssignedCell.eval, ProvableType.eval_field,
        Placed.toEnvironment_place, Placed.toEnvironment_env]
    rw [hpieces] at hbounds hchain
    refine ⟨(chainBody_complete G cfg self env hE ns offset (offset + pieceRows ns)
      input_var.pieces input_var.xA input_var.yA A B hAon ?_ ?_ hbounds hchain hwit).1, trivial⟩
    · rw [hAx, ← h_input, eval_inputs_xA]
      simp only [ProvableType.eval_field, AssignedCell.eval, Placed.toEnvironment_place,
        Placed.toEnvironment_env]
    · rw [hAy, ← h_input, eval_inputs_yA]
      simp only [ProvableType.eval_field, AssignedCell.eval, Placed.toEnvironment_place,
        Placed.toEnvironment_env]

end Halo2.Ironwood.Sinsemilla.Chain
