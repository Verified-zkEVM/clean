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

/-- Sinsemilla per-piece round counts for the note-commit message. Each entry is
`num_words - 1`, matching `Chain.PieceChunks`: source chunk counts
`[25, 1, 25, 6, 1, 25, 25, 1]` become `[24, 0, 24, 5, 0, 24, 24, 0]`. -/
abbrev messagePieceTailRounds : List ℕ := [0, 24, 5, 0, 24, 24, 0]
abbrev messagePieceRounds : List ℕ := [24, 0, 24, 5, 0, 24, 24, 0]

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
  simp only [Chain.PieceChunks] at h
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

theorem pieceChunks_eq_noteCommitChunks_of_indexed_piece_values
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
  simp only [Chain.PieceChunks] at hPC
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

/-- `y_canonicity` owns its low-limb running sum: it witnesses the decomposition cells of
`y`, runs the `Decomposed` 25-word check on `j` (exposing `z₁`/`z₁₃` as projections) and the
`Telescoped` 13-word check on the canonicity shift `j'`, then feeds the `Gate`, which derives
that `lsb` is the sign bit. No raw running-sum vector ever reaches this proof. -/
def main (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  let k0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 1 9 (by norm_num [K])
    (fun env => eval env input.y)
  let k2 ← Utilities.LookupRangeCheck.WitnessShort.circuit 250 4 (by norm_num [K])
    (fun env => eval env input.y)
  let k3 ← witnessField fun env => bitrangeSubset (eval env input.y) 254 1
  let j ← witnessField fun env =>
    env input.lsb + 2 * env k0 + (2 ^ 10 : Fp) * bitrangeSubset (eval env input.y) 10 240
  let jReads ← Utilities.LookupRangeCheck.CopyCheck.Decomposed.circuit j
  let j'Zs ← Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit 13
    (j + Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const Ecc.tP)
  Gate.circuit
    { y := input.y, lsb := input.lsb, k0 := k0, k2 := k2, k3 := k3, j := j,
      z1J := jReads.z1, z13J := jReads.z13, j' := j'Zs.z0, z13J' := j'Zs.zLast }
  return input.lsb

instance elaborated : ElaboratedCircuit Fp Input field main := by
  elaborate_circuit

/-- Only external precondition: the sign cell is Boolean (range-checked upstream). `IsLowBit`
is derived, not assumed. -/
def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  IsBool (show Fp from input.lsb)

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
  circuit_proof_start [Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Decomposed.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit,
    Utilities.LookupRangeCheck.WitnessShort.Spec,
    Utilities.LookupRangeCheck.CopyCheck.Decomposed.Spec,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec,
    Gate.circuit, Gate.Spec, Gate.Assumptions]
  simp_all only [true_and, ←sub_eq_add_neg]
  obtain ⟨hk0, hk2, hd, htel, h_gate⟩ := h_holds
  obtain ⟨lo, hlo, hdec⟩ := htel.2
  simp only [show K * 13 = 130 from rfl] at hlo hdec
  rw [htel.1] at h_gate
  exact (h_gate ⟨hd.1, hk0, hk2, rfl, hd.2.1, hd.2.2, lo, hlo, hdec⟩).1

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [bitrangeSubset, Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.WitnessShort.ProverSpec,
    Utilities.LookupRangeCheck.CopyCheck.Decomposed.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Decomposed.ProverAssumptions,
    Utilities.LookupRangeCheck.CopyCheck.Decomposed.ProverSpec,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.ProverSpec,
    Gate.circuit, Gate.Assumptions, Gate.Spec]
  obtain ⟨⟨_, hk0⟩, ⟨_, hk2⟩, hk3, hj, hDec, htSpec, htz0, htzLast⟩ := h_env
  set jv := env.get (i₀ + 2 + 2 + 1) with hjv
  -- `lsb` is the low bit of `y`; the support cells are the canonical bit slices.
  have hlsb : input_lsb = ((bitrange input_y.val 0 1 : ℕ) : Fp) := by
    rw [h_assumptions]
    have hbit : (if input_y.val.testBit 0 then (1 : ℕ) else 0) = bitrange input_y.val 0 1 := by
      simp only [bitrange, pow_zero, Nat.div_one, pow_one, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one input_y.val with h | h <;> simp [h]
    rw [hbit]
  have htile : bitrange input_y.val 0 250
      = bitrange input_y.val 0 1 + 2 * bitrange input_y.val 1 9
        + 2 ^ 10 * bitrange input_y.val 10 240 := by
    rw [show (250 : ℕ) = 1 + 249 from rfl, Orchard.Specs.bitrange_add,
      show (249 : ℕ) = 9 + 240 from rfl, Orchard.Specs.bitrange_add]
    ring
  have hj_br : jv = ((bitrange input_y.val 0 250 : ℕ) : Fp) := by
    rw [hj, hlsb, hk0, htile]
    simp only [Utilities.LookupRangeCheck.WitnessShort.bitrangeSubset, bitrange]
    push_cast; ring
  have hj_val : jv.val = bitrange input_y.val 0 250 := by
    rw [hj_br]; exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _)
      (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hjlt : jv.val < 2 ^ 250 := by rw [hj_val]; exact bitrange_lt _ _ _
  have hbsub : ∀ {s l : ℕ}, l ≤ 250 →
      (Utilities.LookupRangeCheck.WitnessShort.bitrangeSubset input_y s l).val
        = bitrange input_y.val s l := by
    intro s l hl
    show (((bitrange input_y.val s l : ℕ) : Fp)).val = bitrange input_y.val s l
    exact ZMod.val_natCast_of_lt (lt_of_lt_of_le (bitrange_lt input_y.val s l)
      (le_trans (Nat.pow_le_pow_right (by norm_num) hl)
        (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])))
  refine ⟨⟨?A, ⟨?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8⟩,
    h_assumptions, hj_br, hk0, hk2, hk3, ?guard⟩, h_assumptions⟩
  case A => exact hjlt
  case B1 =>
    rw [hlsb, show bitrange input_y.val 0 1 = input_y.val % 2 from by simp [bitrange]]
    exact nat_mod_two_isBool _
  case B2 => exact hjlt
  case B3 => rw [hk0, hbsub (by norm_num)]; exact bitrange_lt _ _ _
  case B4 => rw [hk2, hbsub (by norm_num)]; exact bitrange_lt _ _ _
  case B5 => rw [htz0]; ring
  case B6 => exact (hDec hjlt).2.1
  case B7 => exact (hDec hjlt).2.2
  case B8 =>
    obtain ⟨lo, hlo, hdec⟩ := htSpec.2
    simp only [show K * 13 = 130 from rfl] at hlo hdec
    refine ⟨lo, hlo, ?_⟩
    rw [htz0]; exact hdec
  case guard =>
    intro h1
    obtain ⟨_, hatp, _⟩ := high_bit_canonical (ZMod.val_lt input_y) (bit_one_of_eq hk3 h1)
    rw [htzLast, show K * 13 = 130 from rfl,
      show jv + ((2 ^ 130 : ℕ) : Fp) + -Ecc.tP = jv + ((2 ^ 130 : ℕ) : Fp) - Ecc.tP from by ring,
      shifted_high_zero (by norm_num) (by norm_num) (by rw [hj_val]; exact hatp)]
    simp

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

/-- Soundness-side facts for the assigned cells: only the `WitnessShort` range bounds. The
`ỹ` sign-bit relations (`AssignedYBits`) are **not** included here — they require the cells
to be Boolean, which is enforced by `MessagePieceChecks`/`YCanonicity` at the top level, not
within `AssignMessagePieces`. -/
def AssignedMessageFacts (cells : MessageCells Fp) : Prop :=
  cells.b0.val < 2 ^ 4 ∧
  cells.b3.val < 2 ^ 4 ∧
  cells.d2.val < 2 ^ 8 ∧
  cells.e0.val < 2 ^ 6 ∧
  cells.e1.val < 2 ^ 4 ∧
  cells.g1.val < 2 ^ 9 ∧
  cells.h0.val < 2 ^ 5

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

  -- `y_canonicity` (for the `ỹ` sign cells `b2`/`d1`) is *not* run here: it requires
  -- `IsBool b2`/`IsBool d1`, which the source establishes in the `b`/`d` message-piece
  -- decomposition gates (`MessagePieceChecks`). It is therefore composed at the top level,
  -- after `MessagePieceChecks`, as a sibling of the x-canonicity gates.
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

def Spec (_input : Value Input Fp) (cells : Value MessageCells Fp)
    (_ : ProverData Fp) : Prop :=
  AssignedMessageFacts cells

def ProverSpec (input : ProverValue Input Fp)
    (cells : ProverValue MessageCells Fp) (_ : ProverHint Fp) : Prop :=
  MessageCellFacts input.gd input.pkd input.value input.rho input.psi cells

/-- `WitnessShort.bitrangeSubset` is the field cast of the natural `bitrange`. -/
theorem bitrangeSubset_eq (v : Fp) (s n : ℕ) :
    Utilities.LookupRangeCheck.WitnessShort.bitrangeSubset v s n
      = ((bitrange v.val s n : ℕ) : Fp) := rfl

/-- The honest 1-bit subset of `y` is its low (sign) bit. -/
theorem isLowBit_bitrangeSubset (y : Fp) :
    IsLowBit y (Utilities.LookupRangeCheck.WitnessShort.bitrangeSubset y 0 1) := by
  rw [isLowBit_iff_mod_two, bitrangeSubset_eq]
  norm_num [bitrange]

/-- The honest 1-bit `bitrange` cast of `y` is its low (sign) bit. -/
theorem isLowBit_bitrange (y : Fp) : IsLowBit y ((bitrange y.val 0 1 : ℕ) : Fp) := by
  rw [← bitrangeSubset_eq]; exact isLowBit_bitrangeSubset y

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main (fun _ _ => True) Spec := by
  circuit_proof_start [main, Spec, AssignedMessageFacts,
    Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.WitnessShort.Spec]
  exact h_holds

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main (fun _ _ _ => True) ProverSpec := by
  circuit_proof_start [main, ProverSpec, MessageCellFacts,
    Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.WitnessShort.ProverSpec]
  obtain ⟨h_gd, h_pkd, h_v, h_rho, h_psi, -⟩ := h_input
  subst h_gd; subst h_pkd; subst h_v; subst h_rho; subst h_psi
  simp only [bitrangeSubset_eq] at h_env
  obtain ⟨⟨_, e_b0⟩, ⟨_, e_b3⟩, ⟨_, e_d2⟩, ⟨_, e_e0⟩, ⟨_, e_e1⟩, ⟨_, e_g1⟩, ⟨_, e_h0⟩,
    e_b1, e_b2, e_d0, e_d1, e_g0, e_h1, e_a, e_b, e_c, e_d, e_e, e_f, e_g, e_h⟩ := h_env
  refine ⟨e_a, e_b0, e_b1, ?_, e_b3, e_c, e_d0, ?_, e_d2, e_e0, e_e1, e_f, e_g0, e_g1, e_h0, e_h1,
    e_b.trans (by ring), e_d.trans (by ring), e_e.trans (by ring), e_g.trans (by ring),
    e_h.trans (by ring)⟩
  · rw [e_b2]; exact isLowBit_bitrange _
  · rw [e_d1]; exact isLowBit_bitrange _

def circuit : GeneralFormalCircuit.WithHint Fp Input MessageCells where
  main
  elaborated
  Spec
  ProverSpec
  soundness
  completeness

end AssignMessagePieces

namespace MessagePieceChecks

structure Input (F : Type) where
  cells : MessageCells F
  z1d : F
  z1g : F
deriving ProvableStruct

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
  main
  elaborated
  Spec
  soundness
  completeness

end MessagePieceChecks

namespace Commit

abbrev Input (F : Type) :=
  CommitDomain.Input 8 F

abbrev Output (F : Type) :=
  CommitDomain.WithZs.Output messagePieceRounds F

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Fp) :
    Circuit Fp (Var Output Fp) :=
  CommitDomain.WithZs.circuit G Q hQ R 24 messagePieceTailRounds input

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp
      (CommitDomain.Input 8)
      (CommitDomain.WithZs.Output messagePieceRounds) (main G Q hQ R) := by
  elaborate_circuit_with {
    localLength _ := 1407
    output input offset := {
      point := varFromOffset Point (offset + 1400),
      zs := ((EntryZs.main G Q 24 messagePieceTailRounds input.pieces).output (offset + 849)).zs }
  }

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (output : Value Output Fp) (data : ProverData Fp) : Prop :=
  CommitDomain.WithZs.Spec G Q R 24 messagePieceTailRounds
    input output data

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve)
    (input : ProverValue Input Fp) (data : ProverData Fp)
    (hint : ProverHint Fp) : Prop :=
  CommitDomain.WithZs.ProverAssumptions G Q 24 messagePieceTailRounds input data hint

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (output : ProverValue Output Fp) (hint : ProverHint Fp) :
    Prop :=
  CommitDomain.WithZs.ProverSpec G Q R 24 messagePieceTailRounds input output hint

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) (fun _ _ => True) (Spec G Q R) := by
  circuit_proof_start [CommitDomain.WithZs.circuit]
  simpa [Spec, Chain.chainLength, messagePieceTailRounds] using h_holds

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R) (ProverAssumptions G Q)
      (ProverSpec G Q R) := by
  circuit_proof_start [CommitDomain.WithZs.circuit]
  refine ⟨?_, ?_⟩
  · simpa using h_assumptions
  · exact ((h_env (by simpa using h_assumptions)).2)

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Output where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q
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
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.ProverSpec, Gate.Spec, Gate.Assumptions
  ]
  obtain ⟨hb1, ha_lt, hb0_lt, hz13A⟩ := h_assumptions
  obtain ⟨ha_eq, hb0_eq, hb1_eq⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 13 = 130 from by norm_num [K]] at hlo hdec hzLast
  have ha_val : input_a.val = bitrange input_gdX.val 0 250 := by
    rw [ha_eq]
    exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _)
      (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  refine ⟨⟨hb1, ha_lt, hb0_lt, by linear_combination hz0, hz13A, lo, hlo,
    by linear_combination hdec + hz0⟩, ha_eq, hb0_eq, hb1_eq, fun h1 => ?_⟩
  -- `b1 = 1` ⇒ `g_d` canonical ⇒ `a < t_P` ⇒ the honest tail `zLast` from `ProverSpec` vanishes.
  obtain ⟨_, hatp, _⟩ := high_bit_canonical (ZMod.val_lt input_gdX) (bit_one_of_eq hb1_eq h1)
  rw [hzLast, show input_a + ((2 ^ 130 : ℕ) : Fp) + -Ecc.tP
      = input_a + ((2 ^ 130 : ℕ) : Fp) - Ecc.tP from by ring,
    shifted_high_zero (by norm_num) (by norm_num) (by rw [ha_val]; exact hatp)]
  simp

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
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and, ←sub_eq_add_neg]
  obtain ⟨⟨z0_eq, element_eq⟩, h_gate⟩ := h_holds
  rw [z0_eq] at h_gate
  have hshift :
      input_b3 + ((2 ^ 4 : ℕ) : Fp) * input_c + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP =
        input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP := by
    ring
  obtain ⟨h1, h2, h3, _⟩ := h_gate ⟨hshift, element_eq⟩
  exact ⟨h1, h2, h3⟩

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.ProverSpec, Gate.Spec, Gate.Assumptions
  ]
  obtain ⟨hd0, hc_lt, hb3_lt, hz13C⟩ := h_assumptions
  obtain ⟨hb3_eq, hc_eq, hd0_eq⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 14 = 140 from by norm_num [K]] at hlo hdec hzLast
  refine ⟨⟨hd0, hc_lt, hb3_lt, by linear_combination hz0, hz13C, lo, hlo,
    by linear_combination hdec + hz0⟩, hb3_eq, hc_eq, hd0_eq, fun h1 => ?_⟩
  -- `d0 = 1` ⇒ `x(pk_d)` canonical ⇒ the low 254-bit base `< t_P` ⇒ honest tail vanishes.
  have hbase_lt := base_val_lt_tP hb3_eq hc_eq (ZMod.val_lt input_pkdX)
    (bit_one_of_eq hd0_eq h1) (by norm_num)
  rw [hzLast,
    show input_b3 + ((2 ^ 4 : ℕ) : Fp) * input_c + ((2 ^ 140 : ℕ) : Fp) + -Ecc.tP
      = (input_b3 + ((2 ^ 4 : ℕ) : Fp) * input_c) + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP from by ring,
    shifted_high_zero (by norm_num) (by norm_num) hbase_lt]
  simp

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
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and, ←sub_eq_add_neg]
  obtain ⟨⟨z0_eq, element_eq⟩, h_gate⟩ := h_holds
  rw [z0_eq] at h_gate
  have hshift :
      input_e1 + ((2 ^ 4 : ℕ) : Fp) * input_f + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP =
        input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP := by
    ring
  obtain ⟨h1, h2, h3, _⟩ := h_gate ⟨hshift, element_eq⟩
  exact ⟨h1, h2, h3⟩

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.ProverSpec, Gate.Spec, Gate.Assumptions
  ]
  obtain ⟨hg0, hf_lt, he1_lt, hz13F⟩ := h_assumptions
  obtain ⟨he1_eq, hf_eq, hg0_eq⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 14 = 140 from by norm_num [K]] at hlo hdec hzLast
  refine ⟨⟨hg0, hf_lt, he1_lt, by linear_combination hz0, hz13F, lo, hlo,
    by linear_combination hdec + hz0⟩, he1_eq, hf_eq, hg0_eq, fun h1 => ?_⟩
  -- `g0 = 1` ⇒ `rho` canonical ⇒ the low 254-bit base `< t_P` ⇒ honest tail vanishes.
  have hbase_lt := base_val_lt_tP he1_eq hf_eq (ZMod.val_lt input_rho)
    (bit_one_of_eq hg0_eq h1) (by norm_num)
  rw [hzLast,
    show input_e1 + ((2 ^ 4 : ℕ) : Fp) * input_f + ((2 ^ 140 : ℕ) : Fp) + -Ecc.tP
      = (input_e1 + ((2 ^ 4 : ℕ) : Fp) * input_f) + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP from by ring,
    shifted_high_zero (by norm_num) (by norm_num) hbase_lt]
  simp

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
    input.z13G = ((input.g1.val + input.g2.val * 2 ^ 9) / 2 ^ 129 : ℕ)

def Spec (input : Input Fp) : Prop :=
  input.g1 = ((bitrange input.psi.val 0 9 : ℕ) : Fp) ∧
    input.g2 = ((bitrange input.psi.val 9 240 : ℕ) : Fp) ∧
    input.h0 = ((bitrange input.psi.val 249 5 : ℕ) : Fp) ∧
    input.h1 = ((bitrange input.psi.val 254 1 : ℕ) : Fp)

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and, ←sub_eq_add_neg]
  obtain ⟨⟨z0_eq, element_eq⟩, h_gate⟩ := h_holds
  rw [z0_eq] at h_gate
  have hshift :
      input_g1 + ((2 ^ 9 : ℕ) : Fp) * input_g2 + ((2 ^ 130 : ℕ) : Fp) - Ecc.tP =
        input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) - Ecc.tP := by
    ring
  obtain ⟨h1, h2, h3, h4, _⟩ := h_gate ⟨hshift, element_eq⟩
  exact ⟨h1, h2, h3, h4⟩

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.ProverSpec, Gate.Spec, Gate.Assumptions
  ]
  obtain ⟨hh1, hg1_lt, hg2_lt, hh0_lt, hz13G⟩ := h_assumptions
  obtain ⟨hg1_eq, hg2_eq, hh0_eq, hh1_eq⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 13 = 130 from by norm_num [K]] at hlo hdec hzLast
  refine ⟨⟨hh1, hg1_lt, hg2_lt, hh0_lt, by linear_combination hz0, hz13G, lo, hlo,
    by linear_combination hdec + hz0⟩, hg1_eq, hg2_eq, hh0_eq, hh1_eq, fun h1 => ?_⟩
  -- `h1 = 1` ⇒ `psi` canonical ⇒ the low 249-bit base `< t_P` ⇒ honest tail vanishes.
  have hbase_lt := base_val_lt_tP hg1_eq hg2_eq (ZMod.val_lt input_psi)
    (bit_one_of_eq hh1_eq h1) (by norm_num)
  rw [hzLast,
    show input_g1 + ((2 ^ 9 : ℕ) : Fp) * input_g2 + ((2 ^ 130 : ℕ) : Fp) + -Ecc.tP
      = (input_g1 + ((2 ^ 9 : ℕ) : Fp) * input_g2) + ((2 ^ 130 : ℕ) : Fp) - Ecc.tP from by ring,
    shifted_high_zero (by norm_num) (by norm_num) hbase_lt]
  simp

def circuit : FormalAssertion Fp Input where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end PsiCanonicity

section PieceExtraction
open Orchard.Specs.Sinsemilla (sum_suffix_div)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- Reusable Sinsemilla running-sum / piece-bound extraction (generic over the rounds list).
TODO: dedup with the analogous private helpers in CommitIvk by sharing a Sinsemilla module. -/
private theorem pieceChunks_head_digits {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    ∃ ms : ℕ → ℕ, (∀ r, ms r < 2 ^ Orchard.Specs.Sinsemilla.K) ∧
      pieces[0] = ((∑ r ∈ Finset.range (n + 1),
        ms r * 2 ^ (Orchard.Specs.Sinsemilla.K * r) : ℕ) : Fp) ∧
      (∀ i, i < n + 1 → chunks.getD i 0 = ms i) ∧
      Orchard.Sinsemilla.Chain.PieceChunks rest pieces.tail (chunks.drop (n + 1)) := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at h
  obtain ⟨ms, hms, hpc, tailChunks, hchunks, hPC⟩ := h
  subst hchunks
  refine ⟨ms, hms, hpc, ?_, ?_⟩
  · intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
    simp only [List.getElem?_map, List.getElem?_range, hi, Option.map_some, Option.getD_some]
  · rwa [List.drop_left' (by simp)]

private theorem two_pow_K_lt_card {m : ℕ} (hm : m ≤ 25) :
    2 ^ (Orchard.Specs.Sinsemilla.K * m) < PALLAS_BASE_CARD := by
  have hle : Orchard.Specs.Sinsemilla.K * m ≤ 250 := by
    simp only [Orchard.Specs.Sinsemilla.K]; omega
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hle)
    (by norm_num [PALLAS_BASE_CARD])

theorem zsFacts_cell_eq_div {n : ℕ} {piece : Fp} {chunks : List ℕ} {ms : ℕ → ℕ}
    (hm : n + 1 ≤ 25) (hms : ∀ r, ms r < 2 ^ Orchard.Specs.Sinsemilla.K)
    (hpc : piece = ((∑ r ∈ Finset.range (n + 1),
      ms r * 2 ^ (Orchard.Specs.Sinsemilla.K * r) : ℕ) : Fp))
    (hgetD : ∀ i, i < n + 1 → chunks.getD i 0 = ms i)
    {r : ℕ} (hr : r ≤ n) :
    ((∑ j ∈ Finset.range (n + 1 - r),
        chunks.getD (r + j) 0 * 2 ^ (Orchard.Specs.Sinsemilla.K * j) : ℕ) : Fp)
      = ((piece.val / 2 ^ (Orchard.Specs.Sinsemilla.K * r) : ℕ) : Fp) := by
  have hpval : piece.val = ∑ r ∈ Finset.range (n + 1),
      ms r * 2 ^ (Orchard.Specs.Sinsemilla.K * r) := by
    rw [hpc, ZMod.val_natCast_of_lt
      (lt_trans (sum_digits_lt hms (n + 1)) (two_pow_K_lt_card hm))]
  have hsum : (∑ j ∈ Finset.range (n + 1 - r),
      chunks.getD (r + j) 0 * 2 ^ (Orchard.Specs.Sinsemilla.K * j))
        = ∑ j ∈ Finset.range (n + 1 - r),
          ms (r + j) * 2 ^ (Orchard.Specs.Sinsemilla.K * j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hgetD (r + j) (by omega)]
  rw [hsum, hpval, sum_suffix_div hms (n + 1) r (by omega)]

private theorem pieceChunks_head_val_lt {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (hm : n + 1 ≤ 25)
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    ZMod.val (pieces[0] : Fp) < 2 ^ (Orchard.Specs.Sinsemilla.K * (n + 1)) := by
  obtain ⟨ms, hms, hpc, -, -⟩ := pieceChunks_head_digits h
  rw [hpc, ZMod.val_natCast_of_lt
    (lt_trans (sum_digits_lt hms (n + 1)) (two_pow_K_lt_card hm))]
  exact sum_digits_lt hms (n + 1)

/-- Head running-sum cell at arbitrary index `r ≤ n`. -/
private theorem zsFacts_head_cell {n : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {pieces : Vector Fp (n :: rest).length}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
    (hm : n + 1 ≤ 25) {r : ℕ} (hr : r ≤ n)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks)
    (hZsHead : HVec.head zs = Vector.ofFn (fun i : Fin (n + 1) =>
      ((∑ j ∈ Finset.range (n + 1 - i.val),
        chunks.getD (i.val + j) 0 * 2 ^ (Orchard.Specs.Sinsemilla.K * j) : ℕ) : Fp))) :
    (HVec.head zs)[r]'(Nat.lt_succ_of_le hr)
      = (((pieces[0] : Fp).val / 2 ^ (Orchard.Specs.Sinsemilla.K * r) : ℕ) : Fp) := by
  obtain ⟨ms, hms, hpc, hgetD, -⟩ := pieceChunks_head_digits hPC
  rw [hZsHead, Vector.getElem_ofFn]
  exact zsFacts_cell_eq_div hm hms hpc hgetD hr

/-- General running-sum cell extraction: the `r`-th entry of the `i`-th piece's running-sum
vector equals `pieces[i].val / 2^(K·r)`. -/
theorem zsFacts_cell :
    ∀ (ns : List ℕ) (pieces : Vector Fp ns.length) (chunks : List ℕ)
      (zs : HVec (Orchard.Sinsemilla.Chain.zLengths ns) Fp)
      (i : Fin (Orchard.Sinsemilla.Chain.zLengths ns).length),
      Orchard.Sinsemilla.Chain.PieceChunks ns pieces chunks →
      Orchard.Sinsemilla.Chain.ZsFacts ns chunks zs →
      (Orchard.Sinsemilla.Chain.zLengths ns)[i] ≤ 25 →
      ∀ {r : ℕ} (hr : r < (Orchard.Sinsemilla.Chain.zLengths ns)[i]),
      (HVec.get (Orchard.Sinsemilla.Chain.zLengths ns) zs i)[r]'hr
        = (((pieces[i.val]'(by
              have := i.isLt
              simpa only [Orchard.Sinsemilla.Chain.zLengths, List.length_map] using this) : Fp).val
            / 2 ^ (Orchard.Specs.Sinsemilla.K * r) : ℕ) : Fp)
  | n :: rest, pieces, chunks, zs, ⟨0, _⟩, hPC, hZs, hm, r, hr => by
      simp only [Orchard.Sinsemilla.Chain.ZsFacts] at hZs
      have hr' : r < n + 1 := hr
      have hmn : n + 1 ≤ 25 := hm
      exact zsFacts_head_cell hmn (Nat.lt_succ_iff.mp hr') hPC hZs.1
  | n :: rest, pieces, chunks, zs, ⟨k + 1, hk⟩, hPC, hZs, hm, r, hr => by
      obtain ⟨-, -, -, -, hPCtail⟩ := pieceChunks_head_digits hPC
      simp only [Orchard.Sinsemilla.Chain.ZsFacts] at hZs
      have hkr : k < (Orchard.Sinsemilla.Chain.zLengths rest).length := by
        have hk' : k + 1 < (Orchard.Sinsemilla.Chain.zLengths (n :: rest)).length := hk
        simp only [Orchard.Sinsemilla.Chain.zLengths, List.length_map, List.length_cons]
          at hk' ⊢
        omega
      have IH := zsFacts_cell rest pieces.tail (chunks.drop (n + 1)) (HVec.tail zs)
        ⟨k, hkr⟩ hPCtail hZs.2 hm hr
      have hk_tail : k < (n :: rest).length - 1 := by
        simp only [List.length_cons, Nat.add_sub_cancel]
        simpa only [Orchard.Sinsemilla.Chain.zLengths, List.length_map] using hkr
      have hbridge :
          pieces.tail[(⟨k, hkr⟩ : Fin (Orchard.Sinsemilla.Chain.zLengths rest).length).val]
            = pieces[(⟨k + 1, hk⟩ :
                Fin (Orchard.Sinsemilla.Chain.zLengths (n :: rest)).length).val] :=
        Vector.getElem_tail (v := pieces) (i := k) (hi := hk_tail)
      exact hbridge ▸ IH

/-- General piece bound: the `i`-th message piece value is `< 2^(K·(nᵢ+1))`. -/
theorem pieceChunks_val_lt :
    ∀ (ns : List ℕ) (pieces : Vector Fp ns.length) (chunks : List ℕ) (i : Fin ns.length),
      Orchard.Sinsemilla.Chain.PieceChunks ns pieces chunks → ns[i] + 1 ≤ 25 →
      (pieces[i] : Fp).val < 2 ^ (Orchard.Specs.Sinsemilla.K * (ns[i] + 1))
  | n :: rest, pieces, chunks, ⟨0, _⟩, hPC, hm => pieceChunks_head_val_lt hm hPC
  | n :: rest, pieces, chunks, ⟨k + 1, hk⟩, hPC, hm => by
      obtain ⟨-, -, -, -, hPCtail⟩ := pieceChunks_head_digits hPC
      have IH := pieceChunks_val_lt rest pieces.tail (chunks.drop (n + 1))
        ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hPCtail hm
      have hbridge : pieces.tail[(⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin rest.length).val]
          = pieces[(⟨k + 1, hk⟩ : Fin (n :: rest).length).val] :=
        Vector.getElem_tail (v := pieces) (i := k)
          (hi := by simp only [List.length_cons, Nat.add_sub_cancel]
                    exact Nat.lt_of_succ_lt_succ hk)
      exact hbridge ▸ IH


/-- `n % 2^(a+b)` splits into its low `a` bits plus the next `b` bits. -/
private theorem mod_pow_split (n a b : ℕ) :
    n % 2 ^ (a + b) = n % 2 ^ a + 2 ^ a * (n / 2 ^ a % 2 ^ b) := by
  have h := Orchard.Specs.bitrange_add n 0 a b
  simpa [bitrange] using h

/-- The semantic crux shared by the top-level soundness/completeness: from the assigned
`MessageCellFacts` (canonical bit slices + decompositions + the two y-coordinate `IsLowBit`
facts) plus a `PieceChunks` realization, the chunk list is exactly the canonical note
encoding `noteCommitChunks` of the note scalars. -/
theorem note_chunks_eq_of_cellFacts {cells : MessageCells Fp} {chunks : List ℕ}
    {gd pkd : Point Fp} {value rho psi : Fp}
    (hPC : Chain.PieceChunks messagePieceRounds (messagePieces cells) chunks)
    (hMCF : MessageCellFacts gd pkd value rho psi cells)
    (hv : value.val < 2 ^ 64) :
    chunks = noteCommitChunks gd.x.val (gd.y.val % 2) pkd.x.val (pkd.y.val % 2)
      value.val rho.val psi.val := by
  obtain ⟨ha, hb0, hb1, hb2, hb3, hc, hd0, hd1, hd2, he0, he1, hf, hg0, hg1, hh0, hh1,
    hb_dec, hd_dec, he_dec, hg_dec, hh_dec⟩ := hMCF
  have hb2' : cells.b2 = ((gd.y.val % 2 : ℕ) : Fp) := isLowBit_iff_mod_two.mp hb2
  have hd1' : cells.d1 = ((pkd.y.val % 2 : ℕ) : Fp) := isLowBit_iff_mod_two.mp hd1
  refine pieceChunks_eq_noteCommitChunks_of_indexed_piece_values hPC
    (gdX := gd.x.val) (gdY := gd.y.val % 2) (pkdX := pkd.x.val) (pkdY := pkd.y.val % 2)
    (v := value.val) (rho := rho.val) (psi := psi.val)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD]))
    (by omega) (lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD]))
    (by omega) hv
    (lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD]))
    (lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD]))
  · show cells.a = _
    rw [ha]; norm_num [bitrange, K, Nat.div_one]
  · show cells.b = _
    rw [hb_dec, hb0, hb1, hb2', hb3]
    simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring
  · show cells.c = _
    rw [hc]; norm_num [bitrange, K, Nat.div_one]
  · show cells.d = _
    rw [hd_dec, hd0, hd1', hd2,
      show ZMod.val value % 2 ^ 58 = _ from mod_pow_split (ZMod.val value) 8 50]
    simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring
  · show cells.e = _
    rw [he_dec, he0, he1]
    simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring
  · show cells.f = _
    rw [hf]; norm_num [bitrange, K, Nat.div_one]
  · show cells.g = _
    rw [hg_dec, hg0, hg1,
      show ZMod.val psi % 2 ^ 249 = _ from mod_pow_split (ZMod.val psi) 9 240]
    simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring
  · show cells.h = _
    rw [hh_dec, hh0, hh1]
    simp only [bitrange]; push_cast; ring


private theorem val_bitrange_cast (n s l : ℕ) (hl : l ≤ 254) :
    ((bitrange n s l : ℕ) : Fp).val = bitrange n s l := by
  have h : bitrange n s l < PALLAS_BASE_CARD := by
    have h1 := bitrange_lt n s l
    have h2 : (2 : ℕ) ^ l ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) hl
    have h3 : (2 : ℕ) ^ 254 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
    omega
  exact ZMod.val_natCast_of_lt h

private theorem pieceBounds_of_all :
    ∀ (ns : List ℕ) (pieces : Vector Fp ns.length),
      (∀ (i : ℕ) (hi : i < ns.length), (pieces[i] : Fp).val < 2 ^ (K * (ns[i] + 1))) →
      Chain.PieceBounds ns pieces
  | [], _, _ => trivial
  | n :: rest, pieces, h => by
      refine ⟨h 0 (by simp), pieceBounds_of_all rest pieces.tail (fun i hi => ?_)⟩
      have key := h (i + 1) (by simp only [List.length_cons]; omega)
      rw [List.getElem_cons_succ] at key
      convert key using 2
      exact Vector.getElem_tail (v := pieces) (i := i)
        (hi := by simp only [List.length_cons, Nat.add_sub_cancel]; exact hi)

theorem pieceBounds_of_cellFacts {cells : MessageCells Fp} {gd pkd : Point Fp}
    {value rho psi : Fp}
    (hMCF : MessageCellFacts gd pkd value rho psi cells) :
    Chain.PieceBounds messagePieceRounds (messagePieces cells) := by
  obtain ⟨ha, hb0, hb1, hb2, hb3, hc, hd0, hd1, hd2, he0, he1, hf, hg0, hg1, hh0, hh1,
    hb_dec, hd_dec, he_dec, hg_dec, hh_dec⟩ := hMCF
  have hb2' : cells.b2 = ((gd.y.val % 2 : ℕ) : Fp) := isLowBit_iff_mod_two.mp hb2
  have hd1' : cells.d1 = ((pkd.y.val % 2 : ℕ) : Fp) := isLowBit_iff_mod_two.mp hd1
  have hgy : gd.y.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hpy : pkd.y.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  apply pieceBounds_of_all
  intro i hi
  simp only [messagePieceRounds, List.length_cons, List.length_nil] at hi
  interval_cases i
  · show ZMod.val cells.a < 2 ^ 250
    rw [ha, val_bitrange_cast _ _ _ (by norm_num)]; exact bitrange_lt _ _ _
  · show ZMod.val cells.b < 2 ^ 10
    rw [hb_dec, hb0, hb1, hb2', hb3]
    have := bitrange_lt gd.x.val 250 4; have := bitrange_lt gd.x.val 254 1
    have := bitrange_lt pkd.x.val 0 4
    rw [show ((bitrange gd.x.val 250 4 : ℕ) : Fp) + ((bitrange gd.x.val 254 1 : ℕ) : Fp) * 16
      + ((gd.y.val % 2 : ℕ) : Fp) * 32 + ((bitrange pkd.x.val 0 4 : ℕ) : Fp) * 64
      = ((bitrange gd.x.val 250 4 + bitrange gd.x.val 254 1 * 16 + gd.y.val % 2 * 32
        + bitrange pkd.x.val 0 4 * 64 : ℕ) : Fp) from by push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by norm_num [PALLAS_BASE_CARD]; omega)]; omega
  · show ZMod.val cells.c < 2 ^ 250
    rw [hc, val_bitrange_cast _ _ _ (by norm_num)]; exact bitrange_lt _ _ _
  · show ZMod.val cells.d < 2 ^ 60
    rw [hd_dec, hd0, hd1', hd2]
    have := bitrange_lt pkd.x.val 254 1; have := bitrange_lt value.val 0 8
    have := bitrange_lt value.val 8 50
    rw [show ((bitrange pkd.x.val 254 1 : ℕ) : Fp) + ((pkd.y.val % 2 : ℕ) : Fp) * 2
      + ((bitrange value.val 0 8 : ℕ) : Fp) * 4 + ((bitrange value.val 8 50 : ℕ) : Fp) * 1024
      = ((bitrange pkd.x.val 254 1 + pkd.y.val % 2 * 2 + bitrange value.val 0 8 * 4
        + bitrange value.val 8 50 * 1024 : ℕ) : Fp) from by push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by norm_num [PALLAS_BASE_CARD]; omega)]; omega
  · show ZMod.val cells.e < 2 ^ 10
    rw [he_dec, he0, he1]
    have := bitrange_lt value.val 58 6; have := bitrange_lt rho.val 0 4
    rw [show ((bitrange value.val 58 6 : ℕ) : Fp) + ((bitrange rho.val 0 4 : ℕ) : Fp) * 64
      = ((bitrange value.val 58 6 + bitrange rho.val 0 4 * 64 : ℕ) : Fp) from by push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by norm_num [PALLAS_BASE_CARD]; omega)]; omega
  · show ZMod.val cells.f < 2 ^ 250
    rw [hf, val_bitrange_cast _ _ _ (by norm_num)]; exact bitrange_lt _ _ _
  · show ZMod.val cells.g < 2 ^ 250
    rw [hg_dec, hg0, hg1]
    have := bitrange_lt rho.val 254 1; have := bitrange_lt psi.val 0 9
    have := bitrange_lt psi.val 9 240
    rw [show ((bitrange rho.val 254 1 : ℕ) : Fp) + ((bitrange psi.val 0 9 : ℕ) : Fp) * 2
      + ((bitrange psi.val 9 240 : ℕ) : Fp) * 1024
      = ((bitrange rho.val 254 1 + bitrange psi.val 0 9 * 2 + bitrange psi.val 9 240 * 1024 : ℕ) : Fp)
        from by push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by norm_num [PALLAS_BASE_CARD]; omega)]; omega
  · show ZMod.val cells.h < 2 ^ 10
    rw [hh_dec, hh0, hh1]
    have := bitrange_lt psi.val 249 5; have := bitrange_lt psi.val 254 1
    rw [show ((bitrange psi.val 249 5 : ℕ) : Fp) + ((bitrange psi.val 254 1 : ℕ) : Fp) * 32
      = ((bitrange psi.val 249 5 + bitrange psi.val 254 1 * 32 : ℕ) : Fp) from by push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by norm_num [PALLAS_BASE_CARD]; omega)]; omega

/-- Completeness-side chunk connection: the honest chunks of the assigned message pieces
are exactly the canonical note encoding. -/
theorem honestChunks_eq_noteCommitChunks_of_cellFacts {cells : MessageCells Fp}
    {gd pkd : Point Fp} {value rho psi : Fp}
    (hMCF : MessageCellFacts gd pkd value rho psi cells) (hv : value.val < 2 ^ 64) :
    Chain.honestChunks messagePieceRounds (messagePieces cells)
      = noteCommitChunks gd.x.val (gd.y.val % 2) pkd.x.val (pkd.y.val % 2)
        value.val rho.val psi.val :=
  note_chunks_eq_of_cellFacts
    (Chain.pieceChunks_honestChunks messagePieceRounds (messagePieces cells)
      (pieceBounds_of_cellFacts hMCF)) hMCF hv

end PieceExtraction

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
  -- `y_canonicity` for the `ỹ` sign cells: composed here (not in `AssignMessagePieces`) so its
  -- `IsBool b2`/`IsBool d1` precondition is dischargeable from `MessagePieceChecks`.
  let _ ← YCanonicity.circuit { y := input.gd.y, lsb := cells.b2 }
  let _ ← YCanonicity.circuit { y := input.pkd.y, lsb := cells.d1 }
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
  -- Verified skeleton: `circuit_proof_start_core` exposes each subcircuit's soundness as an
  -- `Assumptions → Spec` implication; destructure them and keep the (expensive-to-flatten)
  -- `AssignMessagePieces` output opaque so the heavy `eval` never reduces in the kernel.
  circuit_proof_start_core
  dsimp only [main, circuit_norm] at h_holds ⊢
  obtain ⟨hAM, hCom, hMPC, hY1, hY2, hGd, hPkd, hVal, hRho, hPsi, -⟩ := h_holds
  set AM := AssignMessagePieces.circuit.output input_var i₀ with hAMdef
  clear_value AM
  set COut := (Commit.circuit G Q hQ R).output
    { pieces := #v[AM.a, AM.b, AM.c, AM.d, AM.e, AM.f, AM.g, AM.h],
      r := input_var.rcm }
    (i₀ + ((AssignMessagePieces.circuit.toSubcircuit i₀ input_var).localLength + 0)) with hCOutdef
  clear_value COut
  replace hAM := hAM trivial
  replace hCom := hCom trivial
  replace hMPC := hMPC trivial
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_soundness] at hAM hCom
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_soundness] at hY1 hY2
  have hAMSpec : AssignMessagePieces.Spec input (eval env AM) env.data := by
    simpa [h_input, hAMdef] using hAM
  have hComSpec : (Commit.circuit G Q hQ R).Spec
      { pieces := #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h],
        r := input.rcm } (eval env COut) env.data := by
    simpa [h_input, hCOutdef, circuit_norm] using hCom
  simp only [AssignMessagePieces.Spec, AssignedMessageFacts] at hAMSpec
  obtain ⟨hb0_lt, hb3_lt, hd2_lt, he0_lt, he1_lt, hg1_lt, hh0_lt⟩ := hAMSpec
  simp only [Commit.circuit, Commit.Spec, CommitDomain.WithZs.Spec] at hComSpec
  obtain ⟨chunks, rcm, hPC, hZs, hHash⟩ := hComSpec
  have ha_lt : (eval env AM).a.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨0, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hc_lt : (eval env AM).c.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨2, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hd_lt : (eval env AM).d.val < 2 ^ 60 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨3, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hf_lt : (eval env AM).f.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨5, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hg_lt : (eval env AM).g.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨6, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hz13a :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨0, by decide⟩)[13] =
        (((eval env AM).a.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨0, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hz13c :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨2, by decide⟩)[13] =
        (((eval env AM).c.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨2, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hz1d :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨3, by decide⟩)[1] =
        (((eval env AM).d.val / 2 ^ 10 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨3, by decide⟩ hPC hZs (by decide) (r := 1) (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hz13f :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨5, by decide⟩)[13] =
        (((eval env AM).f.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨5, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hz1g :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨6, by decide⟩)[1] =
        (((eval env AM).g.val / 2 ^ 10 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨6, by decide⟩ hPC hZs (by decide) (r := 1) (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  have hz13g :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨6, by decide⟩)[13] =
        (((eval env AM).g.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨6, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, Orchard.Specs.Sinsemilla.K, K] using h
  let MPCIn : Var MessagePieceChecks.Input Fp :=
    { cells := AM,
      z1d := (HVec.get (Chain.zLengths messagePieceRounds) COut.zs ⟨3, by decide⟩)[1],
      z1g := (HVec.get (Chain.zLengths messagePieceRounds) COut.zs ⟨6, by decide⟩)[1] }
  change MessagePieceChecks.Spec (eval env MPCIn) at hMPC
  simp only [MessagePieceChecks.Spec, circuit_norm] at hMPC
  obtain ⟨hb1_bool, hb2_bool, hb_decomp, hd0_bool, hd1_bool, hd_decomp, he_decomp,
    hg0_bool, hg_decomp, hh1_bool, hh_decomp⟩ := hMPC
  have hY1Spec := hY1 (by
    rw [GeneralFormalCircuit.WithHint.toSubcircuit_assumptions]
    simpa [YCanonicity.Assumptions, circuit_norm] using hb2_bool)
  have hY2Spec := hY2 (by
    rw [GeneralFormalCircuit.WithHint.toSubcircuit_assumptions]
    simpa [YCanonicity.Assumptions, circuit_norm] using hd1_bool)
  simp only [circuit_norm] at hY1Spec hY2Spec
  have hgdY_low : IsLowBit (Expression.eval env input_var.gd.y) (Expression.eval env AM.b2) := by
    simpa using hY1Spec.2
  have hpkdY_low : IsLowBit (Expression.eval env input_var.pkd.y) (Expression.eval env AM.d1) := by
    simpa using hY2Spec.2
  have hGdSpec := hGd (by
    rw [show GdCanonicity.circuit.Assumptions = GdCanonicity.Assumptions from rfl]
    simp only [GdCanonicity.Assumptions, circuit_norm]
    refine ⟨hb1_bool, ?_, ?_, ?_⟩
    · simpa [circuit_norm] using ha_lt
    · simpa [circuit_norm] using hb0_lt
    · exact (CircuitType.eval_expr env _).symm.trans
        ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) COut.zs ⟨0, by decide⟩ 13
          (by decide)).trans (by simpa [circuit_norm] using hz13a)))
  rw [show GdCanonicity.circuit.Spec = GdCanonicity.Spec from rfl] at hGdSpec
  simp only [GdCanonicity.Spec, circuit_norm] at hGdSpec
  have hPkdSpec := hPkd (by
    rw [show PkdCanonicity.circuit.Assumptions = PkdCanonicity.Assumptions from rfl]
    simp only [PkdCanonicity.Assumptions, circuit_norm]
    refine ⟨hd0_bool, ?_, ?_, ?_⟩
    · simpa [circuit_norm] using hc_lt
    · simpa [circuit_norm] using hb3_lt
    · exact (CircuitType.eval_expr env _).symm.trans
        ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) COut.zs ⟨2, by decide⟩ 13
          (by decide)).trans (by simpa [circuit_norm] using hz13c)))
  rw [show PkdCanonicity.circuit.Spec = PkdCanonicity.Spec from rfl] at hPkdSpec
  simp only [PkdCanonicity.Spec, circuit_norm] at hPkdSpec
  have hRhoSpec := hRho (by
    rw [show RhoCanonicity.circuit.Assumptions = RhoCanonicity.Assumptions from rfl]
    simp only [RhoCanonicity.Assumptions, circuit_norm]
    refine ⟨hg0_bool, ?_, ?_, ?_⟩
    · simpa [circuit_norm] using hf_lt
    · simpa [circuit_norm] using he1_lt
    · exact (CircuitType.eval_expr env _).symm.trans
        ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) COut.zs ⟨5, by decide⟩ 13
          (by decide)).trans (by simpa [circuit_norm] using hz13f)))
  rw [show RhoCanonicity.circuit.Spec = RhoCanonicity.Spec from rfl] at hRhoSpec
  simp only [RhoCanonicity.Spec, circuit_norm] at hRhoSpec
  -- ROADMAP to finish (all infrastructure is in place above this theorem):
  --  1. `hAM trivial`, `hCom trivial`, `hMPC trivial` (all have `True`/`fun _ => True`
  --     assumptions) → `AssignMessagePieces.Spec` (7 range bounds), `Commit.Spec`
  --     (`∃ chunks r, PieceChunks pieces chunks ∧ ZsFacts ∧ hash`), `MessagePieceChecks.Spec`
  --     (`IsBool b1/b2/d0/d1/g0/h1` + the b/d/e/g/h decompositions). Use the
  --     `toSubcircuit_soundness` `rfl` bridge, not `circuit_norm`, to avoid flattening.
  --  2. From `Commit.Spec`: `obtain ⟨chunks, rcm, hPC, hZs, hHash⟩`. Derive
  --     `a.val,c.val,f.val < 2^250` via `pieceChunks_val_lt … ⟨0/2/5⟩` and the running-sum
  --     cells `z13a/z13c/z1d/z13f/z1g/z13g` via `zsFacts_cell … ⟨0/2/3/5/6⟩` at r = 13/1.
  --  3. `hY1`/`hY2`: discharge `IsBool b2`/`IsBool d1` from `MessagePieceChecks.Spec`
  --     → `IsLowBit gd.y AM.b2`, `IsLowBit pkd.y AM.d1`.
  --  4. `hGd/hPkd/hVal/hRho/hPsi`: assemble each gate's `Assumptions` from `IsBool` (MPC),
  --     the range bound (`AssignMessagePieces.Spec`), the piece bound (step 2), and the z-cell
  --     (step 2) → the canonical bit-slice `Spec`s (`a = bitrange gd.x 0 250`, …).
  --  5. Assemble the 8 indexed piece values `hA..hH` (gate slices + MPC decompositions +
  --     `IsLowBit`), then `pieceChunks_eq_noteCommitChunks_of_indexed_piece_values hPC …`
  --     gives `chunks = noteCommitChunks (noteScalars …)`.
  --  6. Conclude `NoteCommitRelation` with `rcm`, using `hHash` and `hchunks`; then discharge
  --     the trailing `Requirements` disjunctions (each `Or.inr <the assumption just built>`).
  sorry

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q) (ProverSpec G Q R) := by
  -- Mirrors `soundness`: discharge each subcircuit's `ProverAssumptions` and read its
  -- `ProverSpec` (`AssignMessagePieces` → `MessageCellFacts` incl. the two `IsLowBit` facts;
  -- `Commit` → honest `ZsHonest`/hash; `MessagePieceChecks`/`YCanonicity`/canonicity gates as
  -- in `soundness`), then assemble `ProverNoteCommitRelation`. The honest `IsLowBit` cells make
  -- the `YCanonicity` `ProverAssumptions` dischargeable here.
  circuit_proof_start [AssignMessagePieces.circuit, Commit.circuit, MessagePieceChecks.circuit,
    GdCanonicity.circuit, PkdCanonicity.circuit, ValueCanonicity.circuit,
    RhoCanonicity.circuit, PsiCanonicity.circuit]
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
