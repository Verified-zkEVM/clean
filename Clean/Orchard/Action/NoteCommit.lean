import Clean.Orchard.Action.Canonicity
import Clean.Orchard.Action.Decompose
import Clean.Orchard.Sinsemilla.Domain
import Clean.Orchard.Specs.Bitrange
import Clean.Orchard.Utilities

/-!
# `gadgets::note_commit` synthesis-level entry

Port of `orchard@0.14.0/src/circuit/note_commit.rs` `gadgets::note_commit` and its
synthesis helpers (`canon_bitshift_130`, `pkd_x_canonicity`, `rho_canonicity`,
`psi_canonicity`, `y_canonicity`, the `Decompose*::decompose` message-piece builders).

The custom-gate `FormalAssertion`s live in `Clean.Orchard.Action.NoteCommitGate` under
`Orchard.Action.NoteCommit`; that module is kept separate (low in the import graph) while
this entry circuit depends on `Sinsemilla.Domain` (the `CommitDomain.WithZs` hash that
exposes the running sums), which sits above `ScalarMul`.
-/

namespace Orchard.Action.NoteCommit

open Utilities.LookupRangeCheck (K)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Ecc (Point)
open Orchard.Ecc.ScalarMul
open Orchard.Sinsemilla
open Orchard.Specs (bitrange bitrange_lt)
open Orchard.Specs.Sinsemilla (chunksOf chunksOf_mod noteCommitMessage noteCommitChunks
  noteCommitChunks_tiling hashToPoint sum_head_shift sum_digits_lt digit_of_sum
  chunksOf_eq_map_of_sum chunksOf_eq_map_of_cast_sum chunksOf_one_eq_singleton)

section
set_option exponentiation.threshold 900

private theorem noteCommitChunks_segment_a (gdX gdY pkdX pkdY v rho psi : ℕ) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi) 25 =
      chunksOf gdX 25 := by
  unfold noteCommitMessage
  rw [show
      gdX + 2 ^ 255 * gdY + 2 ^ 256 * pkdX + 2 ^ 511 * pkdY +
          2 ^ 512 * v + 2 ^ 576 * rho + 2 ^ 831 * psi =
        gdX + 2 ^ (K * 25) *
          (2 ^ 5 * gdY + 2 ^ 6 * pkdX + 2 ^ 261 * pkdY +
            2 ^ 262 * v + 2 ^ 326 * rho + 2 ^ 581 * psi) by
    norm_num [K]
    ring_nf]
  rw [← chunksOf_mod
    (gdX + 2 ^ (K * 25) *
      (2 ^ 5 * gdY + 2 ^ 6 * pkdX + 2 ^ 261 * pkdY +
        2 ^ 262 * v + 2 ^ 326 * rho + 2 ^ 581 * psi)) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [Nat.add_mul_mod_self_left]
  exact chunksOf_mod gdX 25

private theorem noteCommitChunks_segment_b_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 250) %
        2 ^ K =
      gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 + (pkdX % 16) * 64 := by
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_b (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 250) 1 =
      [gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 + (pkdX % 16) * 64] := by
  unfold chunksOf bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_b_word gdX gdY pkdX pkdY v rho psi hgdX hgdY]

private theorem noteCommitChunks_segment_c_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 260) %
        2 ^ (K * 25) =
      (pkdX / 16) % 2 ^ (K * 25) := by
  rw [show 2 ^ (K * 25) = 2 ^ 250 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_c (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 260) 25 =
      chunksOf (pkdX / 16) 25 := by
  rw [← chunksOf_mod
      (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 260) 25,
    ← chunksOf_mod (pkdX / 16) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_c_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY]

private theorem noteCommitChunks_segment_d_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) (hpkdX : pkdX < 2 ^ 255) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) %
        2 ^ (K * 6) =
      (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) % 2 ^ (K * 6) := by
  rw [show 2 ^ (K * 6) = 2 ^ 60 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_d (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) (hpkdX : pkdX < 2 ^ 255) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) 6 =
      chunksOf
        (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) 6 := by
  rw [← chunksOf_mod
      (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) 6,
    ← chunksOf_mod
      (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) 6]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 6) = 2 ^ (K * 6) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_d_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX]

private theorem noteCommitChunks_segment_e_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 570) %
        2 ^ K =
      v / 2 ^ 58 % 64 + (rho % 16) * 64 := by
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_e (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 570) 1 =
      [v / 2 ^ 58 % 64 + (rho % 16) * 64] := by
  unfold chunksOf bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_e_word gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv]

private theorem noteCommitChunks_segment_f_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 580) %
        2 ^ (K * 25) =
      (rho / 16) % 2 ^ (K * 25) := by
  rw [show 2 ^ (K * 25) = 2 ^ 250 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_f (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 580) 25 =
      chunksOf (rho / 16) 25 := by
  rw [← chunksOf_mod
      (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 580) 25,
    ← chunksOf_mod (rho / 16) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_f_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv]

private theorem noteCommitChunks_segment_g_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) %
        2 ^ (K * 25) =
      (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) % 2 ^ (K * 25) := by
  rw [show 2 ^ (K * 25) = 2 ^ 250 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_g (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) 25 =
      chunksOf
        (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) 25 := by
  rw [← chunksOf_mod
      (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) 25,
    ← chunksOf_mod
      (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_g_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho]

private theorem noteCommitChunks_segment_h_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 1080) %
        2 ^ K =
      psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 := by
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_h (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 1080) 1 =
      [psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32] := by
  unfold chunksOf bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_h_word gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho hpsi]

private theorem noteCommitChunks_tiling_segments (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    noteCommitChunks gdX gdY pkdX pkdY v rho psi =
      chunksOf gdX 25 ++
      [gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 + (pkdX % 16) * 64] ++
      chunksOf (pkdX / 16) 25 ++
      chunksOf
        (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) 6 ++
      [v / 2 ^ 58 % 64 + (rho % 16) * 64] ++
      chunksOf (rho / 16) 25 ++
      chunksOf (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) 25 ++
      [psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32] := by
  rw [noteCommitChunks_tiling]
  rw [noteCommitChunks_segment_a]
  rw [noteCommitChunks_segment_b _ _ _ _ _ _ _ hgdX hgdY]
  rw [noteCommitChunks_segment_c _ _ _ _ _ _ _ hgdX hgdY]
  rw [noteCommitChunks_segment_d _ _ _ _ _ _ _ hgdX hgdY hpkdX]
  rw [noteCommitChunks_segment_e _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv]
  rw [noteCommitChunks_segment_f _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv]
  rw [noteCommitChunks_segment_g _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv hrho]
  rw [noteCommitChunks_segment_h _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv hrho hpsi]

end

/-! ### Subpiece witnessing helpers -/

/-- `bitrangeSubset value start numBits = (value.val >> start) mod 2^numBits`. -/
abbrev bitrangeSubset : Fp → ℕ → ℕ → Fp :=
  Utilities.LookupRangeCheck.WitnessShort.bitrangeSubset

/-! ### `y_canonicity` (note_commit.rs:1962)

Decomposes `y = lsb || k_0 || k_1 || k_2 || k_3`, range-decomposes `j = lsb + 2·k_0 +
2^10·k_1` (strict, 25 words), reuses `canon_bitshift_130` on `j`, and wires the
`YCanonicity` gate. The gadget inlines this assignment at each call site so the proof
boundary is the already-bundled `CopyCheck` and `YCanonicity` circuits, not a local plain
`Circuit` wrapper. -/

/-! ### `gadgets::note_commit` (note_commit.rs:1594) -/

/-- Inputs of `gadgets::note_commit`: the note's `g_d`, `pk_d` points, the value/`rho`/`psi`
field cells, and the prover-side commitment randomness `rcm`. -/
structure Input (F : Type) where
  gd : Point F
  pkd : Point F
  value : F
  rho : F
  psi : F
  rcm : Unconstrained Fq F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ gd := default, pkd := default, value := default, rho := default, psi := default,
     rcm := fun _ => default }⟩

structure MessageCells (F : Type) where
  a : F
  b : F
  c : F
  d : F
  e : F
  f : F
  g : F
  h : F
  b0 : F
  b1 : F
  b2 : F
  b3 : F
  d0 : F
  d1 : F
  d2 : F
  e0 : F
  e1 : F
  g0 : F
  g1 : F
  h0 : F
  h1 : F
deriving ProvableStruct

instance : Inhabited (Var MessageCells Fp) :=
  ⟨{
    a := default, b := default, c := default, d := default,
    e := default, f := default, g := default, h := default,
    b0 := default, b1 := default, b2 := default, b3 := default,
    d0 := default, d1 := default, d2 := default,
    e0 := default, e1 := default,
    g0 := default, g1 := default,
    h0 := default, h1 := default
  }⟩

/-- Sinsemilla per-piece round counts for the note-commit message. Each entry is
`num_words - 1`, matching `Chain.PieceChunks`: source chunk counts
`[25, 1, 25, 6, 1, 25, 25, 1]` become `[24, 0, 24, 5, 0, 24, 24, 0]`. -/
abbrev messagePieceTailRounds : List ℕ := [0, 24, 5, 0, 24, 24, 0]
abbrev messagePieceRounds : List ℕ := 24 :: messagePieceTailRounds

/-- The seven natural-number scalars encoded by the Orchard note-commit message. -/
structure NoteCommitScalars where
  gdX : ℕ
  gdYbit : ℕ
  pkdX : ℕ
  pkdYbit : ℕ
  v : ℕ
  rho : ℕ
  psi : ℕ

namespace NoteCommitScalars

def chunks (s : NoteCommitScalars) : List ℕ :=
  noteCommitChunks s.gdX s.gdYbit s.pkdX s.pkdYbit s.v s.rho s.psi

end NoteCommitScalars

/-- Semantic statement that the eight Sinsemilla pieces are exactly the note-commit
message pieces for `s`, with the canonical range facts needed to recover the unique
natural chunk list from field-valued piece constraints. -/
def NoteCommitPieceValues (s : NoteCommitScalars)
    (pieces : Vector Fp messagePieceRounds.length) : Prop :=
  pieces[0] = ((s.gdX % 2 ^ (K * 25) : ℕ) : Fp) ∧
  pieces[1] =
    ((s.gdX / 2 ^ 250 % 16 + (s.gdX / 2 ^ 254 % 2) * 16 + s.gdYbit * 32 +
      (s.pkdX % 16) * 64 : ℕ) : Fp) ∧
  pieces[2] = (((s.pkdX / 16) % 2 ^ (K * 25) : ℕ) : Fp) ∧
  pieces[3] =
    ((s.pkdX / 2 ^ 254 % 2 + s.pkdYbit * 2 + (s.v % 2 ^ 58) * 4 : ℕ) : Fp) ∧
  pieces[4] = ((s.v / 2 ^ 58 % 64 + (s.rho % 16) * 64 : ℕ) : Fp) ∧
  pieces[5] = (((s.rho / 16) % 2 ^ (K * 25) : ℕ) : Fp) ∧
  pieces[6] =
    ((s.rho / 2 ^ 254 % 2 + (s.psi % 2 ^ 249) * 2 : ℕ) : Fp) ∧
  pieces[7] = ((s.psi / 2 ^ 249 % 32 + (s.psi / 2 ^ 254 % 2) * 32 : ℕ) : Fp) ∧
  s.gdX < 2 ^ 255 ∧ s.gdYbit < 2 ∧
  s.pkdX < 2 ^ 255 ∧ s.pkdYbit < 2 ∧
  s.v < 2 ^ 64 ∧ s.rho < 2 ^ 255 ∧ s.psi < 2 ^ 255

private theorem noteCommitChunks_eq_of_piece_digit_sums
    {msA msB msC msD msE msF msG msH : ℕ → ℕ}
    {gdX gdY pkdX pkdY v rho psi : ℕ}
    (hmsA : ∀ r, msA r < 2 ^ K) (hmsB : ∀ r, msB r < 2 ^ K)
    (hmsC : ∀ r, msC r < 2 ^ K) (hmsD : ∀ r, msD r < 2 ^ K)
    (hmsE : ∀ r, msE r < 2 ^ K) (hmsF : ∀ r, msF r < 2 ^ K)
    (hmsG : ∀ r, msG r < 2 ^ K) (hmsH : ∀ r, msH r < 2 ^ K)
    (hA : ((gdX % 2 ^ (K * 25) : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp))
    (hB : ((gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 +
        (pkdX % 16) * 64 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 1, msB r * 2 ^ (K * r) : ℕ) : Fp))
    (hC : (((pkdX / 16) % 2 ^ (K * 25) : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Fp))
    (hD : ((pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 6, msD r * 2 ^ (K * r) : ℕ) : Fp))
    (hE : ((v / 2 ^ 58 % 64 + (rho % 16) * 64 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 1, msE r * 2 ^ (K * r) : ℕ) : Fp))
    (hF : (((rho / 16) % 2 ^ (K * 25) : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msF r * 2 ^ (K * r) : ℕ) : Fp))
    (hG : ((rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msG r * 2 ^ (K * r) : ℕ) : Fp))
    (hH : ((psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 1, msH r * 2 ^ (K * r) : ℕ) : Fp))
    (hgdX255 : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX255 : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    (List.range 25).map msA ++
      (List.range 1).map msB ++
      (List.range 25).map msC ++
      (List.range 6).map msD ++
      (List.range 1).map msE ++
      (List.range 25).map msF ++
      (List.range 25).map msG ++
      (List.range 1).map msH =
      noteCommitChunks gdX gdY pkdX pkdY v rho psi := by
  have hBValueLt : gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 +
      (pkdX % 16) * 64 < 2 ^ K := by
    have hb0 : gdX / 2 ^ 250 % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have hb1 : gdX / 2 ^ 254 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hb3 : pkdX % 16 < 16 := Nat.mod_lt _ (by norm_num)
    norm_num [K]
    omega
  have hDValueLt : pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4 < 2 ^ (K * 6) := by
    have hd0 : pkdX / 2 ^ 254 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hv0 : v % 2 ^ 58 < 2 ^ 58 := Nat.mod_lt _ (by norm_num)
    norm_num [K]
    omega
  have hEValueLt : v / 2 ^ 58 % 64 + (rho % 16) * 64 < 2 ^ K := by
    have he0 : v / 2 ^ 58 % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have he1 : rho % 16 < 16 := Nat.mod_lt _ (by norm_num)
    norm_num [K]
    omega
  have hGValueLt : rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2 < 2 ^ (K * 25) := by
    have hg0 : rho / 2 ^ 254 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hg2 : psi % 2 ^ 249 < 2 ^ 249 := Nat.mod_lt _ (by norm_num)
    norm_num [K]
    omega
  have hHValueLt : psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 < 2 ^ K := by
    have hh0 : psi / 2 ^ 249 % 32 < 32 := Nat.mod_lt _ (by norm_num)
    have hh1 : psi / 2 ^ 254 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    norm_num [K]
    omega
  have hChunksA_low := chunksOf_eq_map_of_cast_sum hmsA hA
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsA 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksA : chunksOf gdX 25 = (List.range 25).map msA := by
    rw [← chunksOf_mod gdX 25]
    exact hChunksA_low
  have hChunksB := chunksOf_eq_map_of_cast_sum hmsB hB
    (lt_trans hBValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsB 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC_low := chunksOf_eq_map_of_cast_sum hmsC hC
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsC 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC : chunksOf (pkdX / 16) 25 =
      (List.range 25).map msC := by
    rw [← chunksOf_mod (pkdX / 16) 25]
    exact hChunksC_low
  have hChunksD := chunksOf_eq_map_of_cast_sum hmsD hD
    (lt_trans hDValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsD 6) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksE := chunksOf_eq_map_of_cast_sum hmsE hE
    (lt_trans hEValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsE 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksF_low := chunksOf_eq_map_of_cast_sum hmsF hF
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsF 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksF : chunksOf (rho / 16) 25 =
      (List.range 25).map msF := by
    rw [← chunksOf_mod (rho / 16) 25]
    exact hChunksF_low
  have hChunksG := chunksOf_eq_map_of_cast_sum hmsG hG
    (lt_trans hGValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsG 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksH := chunksOf_eq_map_of_cast_sum hmsH hH
    (lt_trans hHValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsH 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  rw [← hChunksA, ← hChunksB, ← hChunksC, ← hChunksD,
    ← hChunksE, ← hChunksF, ← hChunksG, ← hChunksH]
  rw [chunksOf_one_eq_singleton hBValueLt, chunksOf_one_eq_singleton hEValueLt,
    chunksOf_one_eq_singleton hHValueLt]
  exact (noteCommitChunks_tiling_segments gdX gdY pkdX pkdY v rho psi
    hgdX255 hgdY hpkdX255 hpkdY hv hrho hpsi).symm

theorem pieceChunks_messagePieceRounds_chunks
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    (h : Chain.PieceChunks messagePieceRounds pieces chunks) :
    ∃ msA msB msC msD msE msF msG msH : ℕ → ℕ,
      (∀ r, msA r < 2 ^ K) ∧ (∀ r, msB r < 2 ^ K) ∧
      (∀ r, msC r < 2 ^ K) ∧ (∀ r, msD r < 2 ^ K) ∧
      (∀ r, msE r < 2 ^ K) ∧ (∀ r, msF r < 2 ^ K) ∧
      (∀ r, msG r < 2 ^ K) ∧ (∀ r, msH r < 2 ^ K) ∧
      chunks =
        (List.range 25).map msA ++
        (List.range 1).map msB ++
        (List.range 25).map msC ++
        (List.range 6).map msD ++
        (List.range 1).map msE ++
        (List.range 25).map msF ++
        (List.range 25).map msG ++
        (List.range 1).map msH := by
  simp only [messagePieceTailRounds, Chain.PieceChunks] at h
  obtain ⟨msA, hA, _hpA, tailA, rfl, h⟩ := h
  obtain ⟨msB, hB, _hpB, tailB, rfl, h⟩ := h
  obtain ⟨msC, hC, _hpC, tailC, rfl, h⟩ := h
  obtain ⟨msD, hD, _hpD, tailD, rfl, h⟩ := h
  obtain ⟨msE, hE, _hpE, tailE, rfl, h⟩ := h
  obtain ⟨msF, hF, _hpF, tailF, rfl, h⟩ := h
  obtain ⟨msG, hG, _hpG, tailG, rfl, h⟩ := h
  obtain ⟨msH, hH, _hpH, tailH, rfl, h⟩ := h
  subst tailH
  exact ⟨msA, msB, msC, msD, msE, msF, msG, msH,
    hA, hB, hC, hD, hE, hF, hG, hH, by simp only [List.append_nil, List.append_assoc]⟩

private theorem pieceChunks_eq_noteCommitChunks_of_indexed_piece_values
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {gdX gdY pkdX pkdY v rho psi : ℕ}
    (hPC : Chain.PieceChunks messagePieceRounds pieces chunks)
    (hA : pieces[0] = ((gdX % 2 ^ (K * 25) : ℕ) : Fp))
    (hB : pieces[1] =
      ((gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 +
        (pkdX % 16) * 64 : ℕ) : Fp))
    (hC : pieces[2] = (((pkdX / 16) % 2 ^ (K * 25) : ℕ) : Fp))
    (hD : pieces[3] =
      ((pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4 : ℕ) : Fp))
    (hE : pieces[4] =
      ((v / 2 ^ 58 % 64 + (rho % 16) * 64 : ℕ) : Fp))
    (hF : pieces[5] = (((rho / 16) % 2 ^ (K * 25) : ℕ) : Fp))
    (hG : pieces[6] =
      ((rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2 : ℕ) : Fp))
    (hH : pieces[7] =
      ((psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 : ℕ) : Fp))
    (hgdX255 : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX255 : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    chunks = noteCommitChunks gdX gdY pkdX pkdY v rho psi := by
  simp only [messagePieceTailRounds, Chain.PieceChunks] at hPC
  obtain ⟨msA, hmsA, hpA, tailA, rfl, hPC⟩ := hPC
  obtain ⟨msB, hmsB, hpB, tailB, rfl, hPC⟩ := hPC
  obtain ⟨msC, hmsC, hpC, tailC, rfl, hPC⟩ := hPC
  obtain ⟨msD, hmsD, hpD, tailD, rfl, hPC⟩ := hPC
  obtain ⟨msE, hmsE, hpE, tailE, rfl, hPC⟩ := hPC
  obtain ⟨msF, hmsF, hpF, tailF, rfl, hPC⟩ := hPC
  obtain ⟨msG, hmsG, hpG, tailG, rfl, hPC⟩ := hPC
  obtain ⟨msH, hmsH, hpH, tailH, rfl, hPC⟩ := hPC
  subst tailH
  have ht1 : pieces.tail[0] = pieces[1] :=
    Vector.getElem_tail (v := pieces) (i := 0) (hi := by decide)
  have ht2 : pieces.tail.tail[0] = pieces[2] := by
    exact (Vector.getElem_tail (v := pieces.tail) (i := 0) (hi := by decide)).trans
      (Vector.getElem_tail (v := pieces) (i := 1) (hi := by decide))
  have ht3 : pieces.tail.tail.tail[0] = pieces[3] := by
    exact (Vector.getElem_tail (v := pieces.tail.tail) (i := 0) (hi := by decide)).trans
      ((Vector.getElem_tail (v := pieces.tail) (i := 1) (hi := by decide)).trans
        (Vector.getElem_tail (v := pieces) (i := 2) (hi := by decide)))
  have ht4 : pieces.tail.tail.tail.tail[0] = pieces[4] := by
    exact (Vector.getElem_tail (v := pieces.tail.tail.tail) (i := 0) (hi := by decide)).trans
      ((Vector.getElem_tail (v := pieces.tail.tail) (i := 1) (hi := by decide)).trans
        ((Vector.getElem_tail (v := pieces.tail) (i := 2) (hi := by decide)).trans
          (Vector.getElem_tail (v := pieces) (i := 3) (hi := by decide))))
  have ht5 : pieces.tail.tail.tail.tail.tail[0] = pieces[5] := by
    exact (Vector.getElem_tail (v := pieces.tail.tail.tail.tail) (i := 0) (hi := by decide)).trans
      ((Vector.getElem_tail (v := pieces.tail.tail.tail) (i := 1) (hi := by decide)).trans
        ((Vector.getElem_tail (v := pieces.tail.tail) (i := 2) (hi := by decide)).trans
          ((Vector.getElem_tail (v := pieces.tail) (i := 3) (hi := by decide)).trans
            (Vector.getElem_tail (v := pieces) (i := 4) (hi := by decide)))))
  have ht6 : pieces.tail.tail.tail.tail.tail.tail[0] = pieces[6] := by
    exact (Vector.getElem_tail (v := pieces.tail.tail.tail.tail.tail) (i := 0) (hi := by decide)).trans
      ((Vector.getElem_tail (v := pieces.tail.tail.tail.tail) (i := 1) (hi := by decide)).trans
        ((Vector.getElem_tail (v := pieces.tail.tail.tail) (i := 2) (hi := by decide)).trans
          ((Vector.getElem_tail (v := pieces.tail.tail) (i := 3) (hi := by decide)).trans
            ((Vector.getElem_tail (v := pieces.tail) (i := 4) (hi := by decide)).trans
              (Vector.getElem_tail (v := pieces) (i := 5) (hi := by decide))))))
  have ht7 : pieces.tail.tail.tail.tail.tail.tail.tail[0] = pieces[7] := by
    exact (Vector.getElem_tail (v := pieces.tail.tail.tail.tail.tail.tail) (i := 0) (hi := by decide)).trans
      ((Vector.getElem_tail (v := pieces.tail.tail.tail.tail.tail) (i := 1) (hi := by decide)).trans
        ((Vector.getElem_tail (v := pieces.tail.tail.tail.tail) (i := 2) (hi := by decide)).trans
          ((Vector.getElem_tail (v := pieces.tail.tail.tail) (i := 3) (hi := by decide)).trans
            ((Vector.getElem_tail (v := pieces.tail.tail) (i := 4) (hi := by decide)).trans
              ((Vector.getElem_tail (v := pieces.tail) (i := 5) (hi := by decide)).trans
                (Vector.getElem_tail (v := pieces) (i := 6) (hi := by decide)))))))
  exact noteCommitChunks_eq_of_piece_digit_sums hmsA hmsB hmsC hmsD hmsE hmsF hmsG hmsH
    (hA.symm.trans hpA)
    ((ht1.trans hB).symm.trans hpB)
    ((ht2.trans hC).symm.trans hpC)
    ((ht3.trans hD).symm.trans hpD)
    ((ht4.trans hE).symm.trans hpE)
    ((ht5.trans hF).symm.trans hpF)
    ((ht6.trans hG).symm.trans hpG)
    ((ht7.trans hH).symm.trans hpH)
    hgdX255 hgdY hpkdX255 hpkdY hv hrho hpsi

namespace YCanonicity

structure Input (F : Type) where
  y : F
  lsb : F
deriving ProvableStruct

instance : Inhabited (Var Input Fp) :=
  ⟨{ y := default, lsb := default }⟩

def main (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  let k0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 1 9 (by norm_num [K])
    (fun env => eval env input.y)
  let k2 ← Utilities.LookupRangeCheck.WitnessShort.circuit 250 4 (by norm_num [K])
    (fun env => eval env input.y)
  let k3 ← witnessField fun env => bitrangeSubset (eval env input.y) 254 1
  let j ← witnessField fun env =>
    env input.lsb + 2 * env k0 + (2 ^ 10 : Fp) * bitrangeSubset (eval env input.y) 10 240
  let jZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 25 j
  assertZero jZs[25]
  let j' ← witnessField fun env => env jZs[0] + (2 ^ 130 : Fp) - Ecc.tP
  let j'Zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 j'
  Gate.circuit
    { y := input.y, lsb := input.lsb, k0 := k0, k2 := k2, k3 := k3, j := jZs[0],
      z1J := jZs[1], z13J := jZs[13], j' := j'Zs[0], z13J' := j'Zs[13] }
  return input.lsb

instance elaborated : ElaboratedCircuit Fp Input field main := by
  elaborate_circuit

def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  IsBool (show Fp from input.lsb) ∧
    IsLowBit (show Fp from input.y) (show Fp from input.lsb)

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  IsLowBit (show Fp from input.y) (show Fp from input.lsb)

def Spec (input : Value Input Fp) (output : Fp) (_ : ProverData Fp) : Prop :=
  output = input.lsb ∧ IsLowBit (show Fp from input.y) (show Fp from input.lsb)

def ProverSpec (input : ProverValue Input Fp) (output : Fp)
    (_ : ProverHint Fp) : Prop :=
  output = input.lsb ∧ IsLowBit (show Fp from input.y) (show Fp from input.lsb)

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [bitrangeSubset, Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.CopyCheck.circuit, Gate.circuit, Ecc.tP]
  exact h_assumptions.2

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [bitrangeSubset, Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.WitnessShort.ProverSpec,
    Utilities.LookupRangeCheck.CopyCheck.circuit,
    Utilities.LookupRangeCheck.CopyCheck.ProverSpec, Gate.circuit, Gate.Assumptions, Gate.Spec]
  obtain ⟨⟨-, hk0⟩, ⟨-, hk2⟩, hk3, hjdef, ⟨-, hjZs⟩, hj'def, ⟨-, hj'Zs⟩⟩ := h_env
  -- `input_y : ProverValue field Fp` doesn't expose `.val`; it is defeq to a field element.
  change Fp at input_y
  -- The honest prover assigns every cell its bit slice of `y`; the gate's `Assumptions`
  -- then hold by construction, and its canonicity guards are discharged inside the gate.
  have hlsb : input_lsb = ((bitrange input_y.val 0 1 : ℕ) : Fp) := by
    rw [isLowBit_iff_mod_two.mp h_assumptions,
      show input_y.val % 2 = bitrange input_y.val 0 1 from by simp [bitrange]]
  -- `j` is the low 250 bits of `y`
  have hJ : env.get (i₀ + 2 + 2 + 1) = ((bitrange input_y.val 0 250 : ℕ) : Fp) := by
    rw [hjdef, hk0, hlsb]
    show ((bitrange input_y.val 0 1 : ℕ) : Fp)
          + 2 * ((bitrange input_y.val 1 9 : ℕ) : Fp)
          + 2 ^ 10 * ((bitrange input_y.val 10 240 : ℕ) : Fp)
        = ((bitrange input_y.val 0 250 : ℕ) : Fp)
    rw [low_250_decomp input_y.val]; push_cast; ring
  have hbound : bitrange input_y.val 0 250 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD :=
    lt_trans (bitrange_lt _ 0 250)
      (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hJval : (env.get (i₀ + 2 + 2 + 1)).val = bitrange input_y.val 0 250 := by
    rw [hJ]; exact ZMod.val_natCast_of_lt hbound
  -- the `jZs` running-sum reads at positions 0, 1, 13, 25
  have hz0 := hjZs ⟨0, by norm_num⟩
  simp only [mul_zero, pow_zero, Nat.div_one] at hz0
  rw [hJval] at hz0
  have hz1 := hjZs ⟨1, by norm_num⟩
  rw [show K * 1 = 10 from by norm_num [K], hJval,
    show bitrange input_y.val 0 250 / 2 ^ 10 = bitrange input_y.val 10 240 from
      bitrange_low_div input_y.val 10 240] at hz1
  have hz13 := hjZs ⟨13, by norm_num⟩
  rw [show K * 13 = 130 from by norm_num [K], hJval,
    show bitrange input_y.val 0 250 / 2 ^ 130 = bitrange input_y.val 130 120 from
      bitrange_low_div input_y.val 130 120] at hz13
  have hz25 := hjZs ⟨25, by norm_num⟩
  rw [show K * 25 = 250 from by norm_num [K], hJval,
    Nat.div_eq_of_lt (bitrange_lt input_y.val 0 250), Nat.cast_zero] at hz25
  -- `j'` is the canonicity-shifted low part
  have htp : tPNat ≤ bitrange input_y.val 0 250 + 2 ^ 130 := by
    have h1 : tPNat < 2 ^ 130 := by norm_num [tPNat]
    omega
  have hJP : env.get (i₀ + 2 + 2 + 1 + 1 + 26)
      = ((bitrange input_y.val 0 250 + 2 ^ 130 - tPNat : ℕ) : Fp) := by
    rw [hj'def, hz0, Nat.cast_sub htp, tP_eq]; push_cast; ring
  have hJPbound : bitrange input_y.val 0 250 + 2 ^ 130 - tPNat
      < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    have := bitrange_lt input_y.val 0 250
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at this ⊢
    omega
  have hJPval : (env.get (i₀ + 2 + 2 + 1 + 1 + 26)).val
      = bitrange input_y.val 0 250 + 2 ^ 130 - tPNat := by
    rw [hJP]; exact ZMod.val_natCast_of_lt hJPbound
  -- the `j'Zs` reads at positions 0 and 13
  have hj'0 := hj'Zs ⟨0, by norm_num⟩
  simp only [mul_zero, pow_zero, Nat.div_one] at hj'0
  have hj'13 := hj'Zs ⟨13, by norm_num⟩
  rw [show K * 13 = 130 from by norm_num [K]] at hj'13
  refine ⟨⟨hz25, ⟨hk0, hk2, hk3, hz0, hz1, hz13, ?_, ?_⟩, h_assumptions⟩, h_assumptions⟩
  · -- `j'.val` equals the shifted low part
    rw [hj'0, ZMod.val_natCast_of_lt (ZMod.val_lt _)]; exact hJPval
  · -- `z13J'` is the top read of `j'`'s decomposition.  Closed term-mode: rewriting the
    -- indexed running-sum cell `j'Zs[13]` in the goal makes the `rw` motive blow up.
    have hval0 : ZMod.val _ = (env.get (i₀ + 2 + 2 + 1 + 1 + 26)).val :=
      (congrArg ZMod.val hj'0).trans
        (ZMod.val_natCast_of_lt (ZMod.val_lt (env.get (i₀ + 2 + 2 + 1 + 1 + 26))))
    exact hj'13.trans (congrArg (fun n : ℕ => ((n / 2 ^ 130 : ℕ) : Fp)) hval0.symm)

def circuit : GeneralFormalCircuit.WithHint Fp Input field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec
  soundness := soundness
  completeness := completeness

end YCanonicity

/-- The note's seven field-element scalars, as `ℕ`, extracted from a circuit value.
`g_d`/`pk_d` contribute their `x` and the `ỹ` sign bit (`y mod 2`). -/
def noteScalars (gd pkd : Point Fp) (value rho psi : Fp) : NoteCommitScalars where
  gdX := gd.x.val
  gdYbit := gd.y.val % 2
  pkdX := pkd.x.val
  pkdYbit := pkd.y.val % 2
  v := value.val
  rho := rho.val
  psi := psi.val

def noteScalarsOf (gd pkd : Point Fp) (value rho psi : Fp) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let s := noteScalars gd pkd value rho psi
  (s.gdX, s.gdYbit, s.pkdX, s.pkdYbit, s.v, s.rho, s.psi)

def messagePieces (cells : MessageCells Fp) : Vector Fp messagePieceRounds.length :=
  #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h]

/-- Semantic facts about the note-commit message cells assigned before the Sinsemilla
commitment. These are the local bit-slice facts produced by `AssignMessagePieces`; the
Sinsemilla piece/chunk relation is stated separately as `MessagePiecesEncode`. -/
def MessageCellFacts (gd pkd : Point Fp) (value rho psi : Fp) (cells : MessageCells Fp) :
    Prop :=
  cells.a = ((bitrange gd.x.val 0 250 : ℕ) : Fp) ∧
  cells.b0 = ((bitrange gd.x.val 250 4 : ℕ) : Fp) ∧
  cells.b1 = ((bitrange gd.x.val 254 1 : ℕ) : Fp) ∧
  IsLowBit gd.y cells.b2 ∧
  cells.b3 = ((bitrange pkd.x.val 0 4 : ℕ) : Fp) ∧
  cells.c = ((bitrange pkd.x.val 4 250 : ℕ) : Fp) ∧
  cells.d0 = ((bitrange pkd.x.val 254 1 : ℕ) : Fp) ∧
  IsLowBit pkd.y cells.d1 ∧
  cells.d2 = ((bitrange value.val 0 8 : ℕ) : Fp) ∧
  cells.e0 = ((bitrange value.val 58 6 : ℕ) : Fp) ∧
  cells.e1 = ((bitrange rho.val 0 4 : ℕ) : Fp) ∧
  cells.f = ((bitrange rho.val 4 250 : ℕ) : Fp) ∧
  cells.g0 = ((bitrange rho.val 254 1 : ℕ) : Fp) ∧
  cells.g1 = ((bitrange psi.val 0 9 : ℕ) : Fp) ∧
  cells.h0 = ((bitrange psi.val 249 5 : ℕ) : Fp) ∧
  cells.h1 = ((bitrange psi.val 254 1 : ℕ) : Fp) ∧
  cells.b =
    cells.b0 + cells.b1 * 16 + cells.b2 * 32 + cells.b3 * 64 ∧
  cells.d =
    cells.d0 + cells.d1 * 2 + cells.d2 * 4 +
      ((bitrange value.val 8 50 : ℕ) : Fp) * 1024 ∧
  cells.e = cells.e0 + cells.e1 * 64 ∧
  cells.g =
    cells.g0 + cells.g1 * 2 + ((bitrange psi.val 9 240 : ℕ) : Fp) * 1024 ∧
  cells.h = cells.h0 + cells.h1 * 32

def AssignedYBits (gd pkd : Point Fp) (cells : MessageCells Fp) : Prop :=
  IsLowBit gd.y cells.b2 ∧
    IsLowBit pkd.y cells.d1

def noteChunksOfScalars (gdX gdYbit pkdX pkdYbit v rho psi : ℕ) : List ℕ :=
  noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi

def MessagePiecesEncode (input : Value Input Fp) (cells : Value MessageCells Fp) : Prop :=
  Chain.PieceChunks messagePieceRounds (messagePieces cells)
    (noteScalars input.gd input.pkd input.value input.rho input.psi).chunks

def ProverMessagePiecesEncode (input : ProverValue Input Fp)
    (cells : ProverValue MessageCells Fp) : Prop :=
  Chain.honestChunks messagePieceRounds (messagePieces cells) =
    (noteScalars input.gd input.pkd input.value input.rho input.psi).chunks

def NoteCommitRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : Value Input Fp) (cm : Point Fp) : Prop :=
  ∃ rcm : Fq, ∀ B : SWPoint Pallas.curve,
    hashToPoint G.S Q
        (noteScalars input.gd input.pkd input.value input.rho input.psi).chunks = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue rcm).coords

def ProverNoteCommitRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : ProverValue Input Fp) (cm : Point Fp) : Prop :=
  ∀ B : SWPoint Pallas.curve,
    hashToPoint G.S Q
        (noteScalars input.gd input.pkd input.value input.rho input.psi).chunks = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue input.rcm).coords

namespace AssignMessagePieces

def main (input : Var Input Fp) : Circuit Fp (Var MessageCells Fp) := do
  let gdX := input.gd.x
  let gdY := input.gd.y
  let pkdX := input.pkd.x
  let pkdY := input.pkd.y
  let v := input.value
  let rho := input.rho
  let psi := input.psi

  let b0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 250 4 (by norm_num [K])
    (fun env => eval env gdX)
  let b3 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 4 (by norm_num [K])
    (fun env => eval env pkdX)
  let d2 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 8 (by norm_num [K])
    (fun env => eval env v)
  let e0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 58 6 (by norm_num [K])
    (fun env => eval env v)
  let e1 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 4 (by norm_num [K])
    (fun env => eval env rho)
  let g1 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 9 (by norm_num [K])
    (fun env => eval env psi)
  let h0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 249 5 (by norm_num [K])
    (fun env => eval env psi)
  let b1 ← witnessField fun env => bitrangeSubset (eval env gdX) 254 1
  let b2 ← witnessField fun env => bitrangeSubset (eval env gdY) 0 1
  let d0 ← witnessField fun env => bitrangeSubset (eval env pkdX) 254 1
  let d1 ← witnessField fun env => bitrangeSubset (eval env pkdY) 0 1
  let g0 ← witnessField fun env => bitrangeSubset (eval env rho) 254 1
  let h1 ← witnessField fun env => bitrangeSubset (eval env psi) 254 1

  let b2 ← YCanonicity.circuit { y := gdY, lsb := b2 }
  let d1 ← YCanonicity.circuit { y := pkdY, lsb := d1 }

  let a ← witnessField fun env => bitrangeSubset (eval env gdX) 0 250
  let b ← witnessField fun env =>
    env b0 + env b1 * 2 ^ 4 + env b2 * 2 ^ 5 + env b3 * 2 ^ 6
  let c ← witnessField fun env => bitrangeSubset (eval env pkdX) 4 250
  let d ← witnessField fun env =>
    env d0 + env d1 * 2 + env d2 * 2 ^ 2 +
    bitrangeSubset (eval env v) 8 50 * 2 ^ 10
  let e ← witnessField fun env => env e0 + env e1 * 2 ^ 6
  let f ← witnessField fun env => bitrangeSubset (eval env rho) 4 250
  let g ← witnessField fun env => env g0 + env g1 * 2 +
    bitrangeSubset (eval env psi) 9 240 * 2 ^ 10
  let h ← witnessField fun env => env h0 + env h1 * 2 ^ 5
  return {
    a, b, c, d, e, f, g, h,
    b0, b1, b2, b3,
    d0, d1, d2,
    e0, e1,
    g0, g1,
    h0, h1
  }

instance elaborated : ElaboratedCircuit Fp Input MessageCells main := by
  elaborate_circuit

def Assumptions (_input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  True

def ProverAssumptions (_input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  True

def Spec (input : Value Input Fp) (cells : Value MessageCells Fp)
    (_ : ProverData Fp) : Prop :=
  AssignedYBits input.gd input.pkd cells

def ProverSpec (input : ProverValue Input Fp)
    (cells : ProverValue MessageCells Fp) (_ : ProverHint Fp) : Prop :=
  MessageCellFacts input.gd input.pkd input.value input.rho input.psi cells

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main Assumptions Spec := by
  sorry

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  sorry

def circuit : GeneralFormalCircuit.WithHint Fp Input MessageCells where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec
  soundness := soundness
  completeness := completeness

end AssignMessagePieces

namespace MessagePieceChecks

structure Input (F : Type) where
  cells : MessageCells F
  z1d : F
  z1g : F
deriving ProvableStruct

instance : Inhabited (Var Input Fp) :=
  ⟨{ cells := default, z1d := default, z1g := default }⟩

def main (input : Var Input Fp) : Circuit Fp Unit := do
  let cells := input.cells
  DecomposeB.Gate.circuit
    { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
  DecomposeD.Gate.circuit
    { d := cells.d, d0 := cells.d0, d1 := cells.d1, d2 := cells.d2, d3 := input.z1d }
  DecomposeE.Gate.circuit { e := cells.e, e0 := cells.e0, e1 := cells.e1 }
  DecomposeG.Gate.circuit { g := cells.g, g0 := cells.g0, g1 := cells.g1, g2 := input.z1g }
  DecomposeH.Gate.circuit { h := cells.h, h0 := cells.h0, h1 := cells.h1 }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Spec (input : Input Fp) : Prop :=
  IsBool input.cells.b1 ∧
  IsBool input.cells.b2 ∧
  input.cells.b =
    input.cells.b0 + input.cells.b1 * 16 + input.cells.b2 * 32 + input.cells.b3 * 64 ∧
  IsBool input.cells.d0 ∧
  IsBool input.cells.d1 ∧
  input.cells.d =
    input.cells.d0 + input.cells.d1 * 2 + input.cells.d2 * 4 + input.z1d * 1024 ∧
  input.cells.e = input.cells.e0 + input.cells.e1 * 64 ∧
  IsBool input.cells.g0 ∧
  input.cells.g = input.cells.g0 + input.cells.g1 * 2 + input.z1g * 1024 ∧
  IsBool input.cells.h1 ∧
  input.cells.h = input.cells.h0 + input.cells.h1 * 32

theorem soundness : FormalAssertion.Soundness Fp main (fun _ => True) Spec := by
  circuit_proof_start [DecomposeB.Gate.circuit, DecomposeD.Gate.circuit,
    DecomposeE.Gate.circuit, DecomposeG.Gate.circuit, DecomposeH.Gate.circuit]
  rcases h_holds with ⟨hB, hD, hE, hG, hH⟩
  rcases hB with ⟨hb1, hb2, hb⟩
  rcases hD with ⟨hd0, hd1, hd⟩
  rcases hG with ⟨hg0, hg⟩
  exact ⟨hb1, hb2, hb, hd0, hd1, hd, hE, hg0, hg, hH.1, hH.2⟩

theorem completeness : FormalAssertion.Completeness Fp main (fun _ => True) Spec := by
  circuit_proof_start [DecomposeB.Gate.circuit, DecomposeD.Gate.circuit,
    DecomposeE.Gate.circuit, DecomposeG.Gate.circuit, DecomposeH.Gate.circuit]
  rcases h_spec with ⟨hb1, hb2, hb, hd0, hd1, hd, hE, hg0, hg, hh1, hh⟩
  exact ⟨⟨hb1, hb2, hb⟩, ⟨hd0, hd1, hd⟩, hE, ⟨hg0, hg⟩, ⟨hh1, hh⟩⟩

def circuit : FormalAssertion Fp Input where
  main := main
  elaborated := elaborated
  Spec := Spec
  soundness := soundness
  completeness := completeness

end MessagePieceChecks

namespace Commit

abbrev Input (F : Type) :=
  CommitDomain.Input messagePieceRounds.length F

abbrev Output (F : Type) :=
  CommitDomain.WithZs.Output messagePieceRounds F

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Fp) :
    Circuit Fp (Var Output Fp) :=
  CommitDomain.WithZs.circuit G Q hQ R 24 messagePieceTailRounds input

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp Input Output (main G Q hQ R) := by
  elaborate_circuit

def Assumptions (_G : Generators) (_Q : SWPoint Pallas.curve) (_R : MulFixed.FixedBase)
    (_input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  True

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (output : Value Output Fp) (data : ProverData Fp) : Prop :=
  CommitDomain.WithZs.Spec G Q R 24 messagePieceTailRounds
    input output data

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve)
    (_R : MulFixed.FixedBase) (input : ProverValue Input Fp) (data : ProverData Fp)
    (hint : ProverHint Fp) : Prop :=
  CommitDomain.WithZs.ProverAssumptions G Q 24 messagePieceTailRounds
    input data hint

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (output : ProverValue Output Fp) (hint : ProverHint Fp) :
    Prop :=
  CommitDomain.WithZs.ProverSpec G Q R 24 messagePieceTailRounds
    input output hint

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) (Assumptions G Q R)
      (Spec G Q R) := by
  sorry

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R) (ProverAssumptions G Q R)
      (ProverSpec G Q R) := by
  sorry

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Output where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Assumptions := Assumptions G Q R
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q R
  ProverSpec := ProverSpec G Q R
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end Commit

namespace GdCanonicity

structure Input (F : Type) where
  gdX : F
  a : F
  b0 : F
  b1 : F
  z13A : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp Unit := do
  let a'Zs ← Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit 13
    (input.a + Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const Ecc.tP)
  Gate.circuit
    { gdX := input.gdX, b0 := input.b0, b1 := input.b1, a := input.a,
      a' := a'Zs.z0, z13A := input.z13A, z13A' := a'Zs.zLast }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  IsBool input.b1 ∧ input.a.val < 2 ^ 250 ∧ input.b0.val < 2 ^ 4 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp)

def Spec (input : Input Fp) : Prop :=
  input.a = ((bitrange input.gdX.val 0 250 : ℕ) : Fp) ∧
    input.b0 = ((bitrange input.gdX.val 250 4 : ℕ) : Fp) ∧
    input.b1 = ((bitrange input.gdX.val 254 1 : ℕ) : Fp)

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and, ←sub_eq_add_neg]
  obtain ⟨ ⟨ z0_eq, element_eq ⟩, h_gate ⟩ := h_holds
  rw [z0_eq] at h_gate
  obtain ⟨ h1, h2, h3, _ ⟩ := h_gate ⟨ rfl,  element_eq ⟩
  exact ⟨ h1, h2, h3 ⟩

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and, ←sub_eq_add_neg]
  use h_env.2
  trace_state
  sorry

def circuit : FormalAssertion Fp Input where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end GdCanonicity

namespace PkdCanonicity

structure Input (F : Type) where
  pkdX : F
  b3 : F
  c : F
  d0 : F
  z13C : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp Unit := do
  let b3C'Zs ← Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit 14
    (input.b3 + Expression.const ((2 ^ 4 : ℕ) : Fp) * input.c +
      Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const Ecc.tP)
  Gate.circuit
    { pkdX := input.pkdX, b3 := input.b3, c := input.c, d0 := input.d0,
      b3C' := b3C'Zs.z0, z13C := input.z13C, z14B3C' := b3C'Zs.zLast }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  IsBool input.d0 ∧ input.c.val < 2 ^ 250 ∧ input.b3.val < 2 ^ 4 ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp)

def Spec (input : Input Fp) : Prop :=
  input.b3 = ((bitrange input.pkdX.val 0 4 : ℕ) : Fp) ∧
    input.c = ((bitrange input.pkdX.val 4 250 : ℕ) : Fp) ∧
    input.d0 = ((bitrange input.pkdX.val 254 1 : ℕ) : Fp)

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  sorry

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  sorry

def circuit : FormalAssertion Fp Input where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end PkdCanonicity

namespace ValueCanonicity

structure Input (F : Type) where
  value : F
  d2 : F
  d3 : F
  e0 : F
deriving ProvableStruct

instance : Inhabited (Var Input Fp) :=
  ⟨{ value := default, d2 := default, d3 := default, e0 := default }⟩

def main (input : Var Input Fp) : Circuit Fp Unit :=
  Gate.circuit { value := input.value, d2 := input.d2, d3 := input.d3, e0 := input.e0 }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  Gate.Assumptions { value := input.value, d2 := input.d2, d3 := input.d3, e0 := input.e0 }

def Spec (input : Input Fp) : Prop :=
  Gate.Spec { value := input.value, d2 := input.d2, d3 := input.d3, e0 := input.e0 }

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [Gate.circuit]
  exact h_holds h_assumptions

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  circuit_proof_start [Gate.circuit]
  exact ⟨h_assumptions, h_spec⟩

def circuit : FormalAssertion Fp Input where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end ValueCanonicity

namespace RhoCanonicity

structure Input (F : Type) where
  rho : F
  e1 : F
  f : F
  g0 : F
  z13F : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp Unit := do
  let e1F'Zs ← Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit 14
    (input.e1 + Expression.const ((2 ^ 4 : ℕ) : Fp) * input.f +
      Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const Ecc.tP)
  Gate.circuit
    { rho := input.rho, e1 := input.e1, f := input.f, g0 := input.g0,
      e1F' := e1F'Zs.z0, z13F := input.z13F, z14E1F' := e1F'Zs.zLast }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  IsBool input.g0 ∧ input.f.val < 2 ^ 250 ∧ input.e1.val < 2 ^ 4 ∧
    input.z13F = ((input.f.val / 2 ^ 130 : ℕ) : Fp)

def Spec (input : Input Fp) : Prop :=
  input.e1 = ((bitrange input.rho.val 0 4 : ℕ) : Fp) ∧
    input.f = ((bitrange input.rho.val 4 250 : ℕ) : Fp) ∧
    input.g0 = ((bitrange input.rho.val 254 1 : ℕ) : Fp)

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  sorry

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  sorry

def circuit : FormalAssertion Fp Input where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end RhoCanonicity

namespace PsiCanonicity

structure Input (F : Type) where
  psi : F
  h0 : F
  g1 : F
  h1 : F
  g2 : F
  z13G : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp Unit := do
  let g1G2'Zs ← Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit 13
    (input.g1 + Expression.const ((2 ^ 9 : ℕ) : Fp) * input.g2 +
      Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const Ecc.tP)
  Gate.circuit
    { psi := input.psi, h0 := input.h0, g1 := input.g1, h1 := input.h1, g2 := input.g2,
      g1G2' := g1G2'Zs.z0, z13G := input.z13G,
      z13G1G2' := g1G2'Zs.zLast }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  IsBool input.h1 ∧ input.g1.val < 2 ^ 9 ∧ input.g2.val < 2 ^ 240 ∧
    input.h0.val < 2 ^ 5 ∧
    input.z13G = ((input.g1.val + input.g2.val * 2 ^ 9) / 2 ^ 130 : ℕ)

def Spec (input : Input Fp) : Prop :=
  input.g1 = ((bitrange input.psi.val 0 9 : ℕ) : Fp) ∧
    input.g2 = ((bitrange input.psi.val 9 240 : ℕ) : Fp) ∧
    input.h0 = ((bitrange input.psi.val 249 5 : ℕ) : Fp) ∧
    input.h1 = ((bitrange input.psi.val 254 1 : ℕ) : Fp)

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  sorry

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  sorry

def circuit : FormalAssertion Fp Input where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end PsiCanonicity

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  let cells ← AssignMessagePieces.circuit input
  let out ← Commit.circuit G Q hQ R
    { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
      r := input.rcm }
  let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
  let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
  let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
  let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]
  MessagePieceChecks.circuit { cells, z1d, z1g }
  GdCanonicity.circuit
    { gdX := input.gd.x, a := cells.a, b0 := cells.b0, b1 := cells.b1, z13A := z13a }
  PkdCanonicity.circuit
    { pkdX := input.pkd.x, b3 := cells.b3, c := cells.c, d0 := cells.d0, z13C := z13c }
  ValueCanonicity.circuit { value := input.value, d2 := cells.d2, d3 := z1d, e0 := cells.e0 }
  RhoCanonicity.circuit
    { rho := input.rho, e1 := cells.e1, f := cells.f, g0 := cells.g0, z13F := z13f }
  PsiCanonicity.circuit
    { psi := input.psi, h0 := cells.h0, g1 := cells.g1, h1 := cells.h1, g2 := z1g,
      z13G := z13g }
  return out.point

def mainOutput (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Fp) (offset : ℕ) :
    Var Point Fp :=
  (main G Q hQ R input).output offset

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    ElaboratedCircuit Fp Input Point (main G Q hQ R) := by
  elaborate_circuit

/-- `g_d` and `pk_d` enter the Halo2 gadget as already-assigned non-identity points. In
Clean's point model this is the on-curve half of `NonIdentityEccPoint`; identity is not
representable as an affine point in the source API at this boundary. -/
def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  Pallas.OnCurve input.gd.coords ∧ Pallas.OnCurve input.pkd.coords

/-- `cm` is the Orchard note commitment of the note `(g_d, pk_d, value, rho, psi)` with
randomness `rcm`: `cm = NoteCommit^Orchard_rcm(g★_d || pk★_d || v || rho || psi)`. The
message is the `Sinsemilla` hash of the canonical 109-chunk encoding (the canonicity
gates force the field inputs into that canonical bit-layout) translated by `[rcm] R`. -/
def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (cm : Point Fp) (_ : ProverData Fp) : Prop :=
  NoteCommitRelation G Q R input cm

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve)
    (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  Pallas.OnCurve input.gd.coords ∧
  Pallas.OnCurve input.pkd.coords ∧
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
    noteScalarsOf input.gd input.pkd input.value input.rho input.psi
  ∃ B, hashToPoint G.S Q
    (noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (cm : ProverValue Point Fp)
    (_ : ProverHint Fp) : Prop :=
  ProverNoteCommitRelation G Q R input cm

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) Assumptions (Spec G Q R) := by
  sorry

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q) (ProverSpec G Q R) := by
  sorry

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Point where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Assumptions
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q
  ProverSpec := ProverSpec G Q R
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end Orchard.Action.NoteCommit
