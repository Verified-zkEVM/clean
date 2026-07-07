import Clean.Orchard.Action.Canonicity
import Clean.Orchard.Action.Decompose
import Clean.Orchard.Sinsemilla.CommitDomain
import Clean.Orchard.Specs.Bitrange
import Clean.Orchard.Utilities

/-!
# `gadgets::note_commit` synthesis-level entry

Port of `orchard@0.14.0/src/circuit/note_commit.rs` `gadgets::note_commit` and its
synthesis helpers (`canon_bitshift_130`, `pkd_x_canonicity`, `rho_canonicity`,
`psi_canonicity`, `y_canonicity`, the `Decompose*::decompose` message-piece builders).

The custom-gate `FormalAssertion`s live in `Clean.Orchard.Action.NoteCommitGate` under
`Orchard.Action.NoteCommit`; that module is kept separate (low in the import graph) while
this entry circuit depends on `Sinsemilla.Domain` (the `CommitDomain` hash that
exposes the running sums), which sits above the scalar-multiplication gadgets.
-/

namespace Orchard.Action.NoteCommit

open Orchard.Specs (K)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Ecc
open Orchard.Sinsemilla
open Orchard.Specs (bitrange bitrange_lt bitrange_add cast_bitrange_val)
open Orchard.Specs.Sinsemilla (chunksOf chunksOf_mod chunksOf_eq_of_mod_eq noteCommitMessage noteCommitChunks
  noteCommitChunks_tiling hashToPoint sum_head_shift sum_digits_lt digit_of_sum
  chunksOf_eq_map_of_sum chunksOf_eq_map_of_cast_sum
  chunksOf_one_eq_singleton)

section
set_option exponentiation.threshold 900

private theorem noteCommitChunks_segment_a (gdX gdY pkdX pkdY v rho psi : ℕ) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi) 25 =
      chunksOf gdX 25 :=
  chunksOf_eq_of_mod_eq (by
    unfold noteCommitMessage
    rw [show
        gdX + 2 ^ 255 * gdY + 2 ^ 256 * pkdX + 2 ^ 511 * pkdY +
            2 ^ 512 * v + 2 ^ 576 * rho + 2 ^ 831 * psi =
          gdX + 2 ^ (K * 25) *
            (2 ^ 5 * gdY + 2 ^ 6 * pkdX + 2 ^ 261 * pkdY +
              2 ^ 262 * v + 2 ^ 326 * rho + 2 ^ 581 * psi) by norm_num [K]; ring_nf]
    apply Nat.add_mul_mod_self_left)

private theorem noteCommitChunks_segment_b_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    bitrange (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 250) 0 K =
      bitrange gdX 250 4 + bitrange gdX 254 1 * 16 + gdY * 32 + bitrange pkdX 0 4 * 64 := by
  simp only [bitrange]
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_b (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 250) 1 =
      [bitrange gdX 250 4 + bitrange gdX 254 1 * 16 + gdY * 32 + bitrange pkdX 0 4 * 64] := by
  unfold chunksOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
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
      chunksOf (pkdX / 16) 25 :=
  chunksOf_eq_of_mod_eq (noteCommitChunks_segment_c_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY)

private theorem noteCommitChunks_segment_d_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) (hpkdX : pkdX < 2 ^ 255) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) %
        2 ^ (K * 6) =
      (bitrange pkdX 254 1 + pkdY * 2 + bitrange v 0 58 * 4) % 2 ^ (K * 6) := by
  simp only [bitrange]
  rw [show 2 ^ (K * 6) = 2 ^ 60 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_d (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) (hpkdX : pkdX < 2 ^ 255) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) 6 =
      chunksOf (bitrange pkdX 254 1 + pkdY * 2 + bitrange v 0 58 * 4) 6 :=
  chunksOf_eq_of_mod_eq
    (noteCommitChunks_segment_d_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX)

private theorem noteCommitChunks_segment_e_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    bitrange (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 570) 0 K =
      bitrange v 58 6 + bitrange rho 0 4 * 64 := by
  simp only [bitrange]
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold noteCommitMessage
  norm_num at *
  omega

private theorem noteCommitChunks_segment_e (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    chunksOf
        (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 570) 1 =
      [bitrange v 58 6 + bitrange rho 0 4 * 64] := by
  unfold chunksOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
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
      chunksOf (rho / 16) 25 :=
  chunksOf_eq_of_mod_eq
    (noteCommitChunks_segment_f_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv)

private theorem noteCommitChunks_segment_g_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) :
    (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) %
        2 ^ (K * 25) =
      (bitrange rho 254 1 + bitrange psi 0 249 * 2) % 2 ^ (K * 25) := by
  simp only [bitrange]
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
      chunksOf (bitrange rho 254 1 + bitrange psi 0 249 * 2) 25 :=
  chunksOf_eq_of_mod_eq
    (noteCommitChunks_segment_g_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho)

private theorem noteCommitChunks_segment_h_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    bitrange (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 1080) 0 K =
      bitrange psi 249 5 + bitrange psi 254 1 * 32 := by
  simp only [bitrange]
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
      [bitrange psi 249 5 + bitrange psi 254 1 * 32] := by
  unfold chunksOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
  rw [noteCommitChunks_segment_h_word gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho hpsi]

private theorem noteCommitChunks_tiling_segments (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    noteCommitChunks gdX gdY pkdX pkdY v rho psi =
      chunksOf gdX 25 ++
      [bitrange gdX 250 4 + bitrange gdX 254 1 * 16 + gdY * 32 + bitrange pkdX 0 4 * 64] ++
      chunksOf (pkdX / 16) 25 ++
      chunksOf
        (bitrange pkdX 254 1 + pkdY * 2 + bitrange v 0 58 * 4) 6 ++
      [bitrange v 58 6 + bitrange rho 0 4 * 64] ++
      chunksOf (rho / 16) 25 ++
      chunksOf (bitrange rho 254 1 + bitrange psi 0 249 * 2) 25 ++
      [bitrange psi 249 5 + bitrange psi 254 1 * 32] := by
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
  rcm : UnconstrainedNat F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ gd := default, pkd := default, value := default, rho := default, psi := default,
     rcm := default }⟩

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
  pieces[0] = ((bitrange s.gdX 0 250 : ℕ) : Fp) ∧
  pieces[1] =
    ((bitrange s.gdX 250 4 + bitrange s.gdX 254 1 * 16 + s.gdYbit * 32 +
      bitrange s.pkdX 0 4 * 64 : ℕ) : Fp) ∧
  pieces[2] = ((bitrange s.pkdX 4 250 : ℕ) : Fp) ∧
  pieces[3] =
    ((bitrange s.pkdX 254 1 + s.pkdYbit * 2 + bitrange s.v 0 58 * 4 : ℕ) : Fp) ∧
  pieces[4] = ((bitrange s.v 58 6 + bitrange s.rho 0 4 * 64 : ℕ) : Fp) ∧
  pieces[5] = ((bitrange s.rho 4 250 : ℕ) : Fp) ∧
  pieces[6] =
    ((bitrange s.rho 254 1 + bitrange s.psi 0 249 * 2 : ℕ) : Fp) ∧
  pieces[7] = ((bitrange s.psi 249 5 + bitrange s.psi 254 1 * 32 : ℕ) : Fp) ∧
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
    (hA : ((bitrange gdX 0 250 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp))
    (hB : ((bitrange gdX 250 4 + bitrange gdX 254 1 * 16 + gdY * 32 +
        bitrange pkdX 0 4 * 64 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 1, msB r * 2 ^ (K * r) : ℕ) : Fp))
    (hC : ((bitrange pkdX 4 250 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Fp))
    (hD : ((bitrange pkdX 254 1 + pkdY * 2 + bitrange v 0 58 * 4 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 6, msD r * 2 ^ (K * r) : ℕ) : Fp))
    (hE : ((bitrange v 58 6 + bitrange rho 0 4 * 64 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 1, msE r * 2 ^ (K * r) : ℕ) : Fp))
    (hF : ((bitrange rho 4 250 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msF r * 2 ^ (K * r) : ℕ) : Fp))
    (hG : ((bitrange rho 254 1 + bitrange psi 0 249 * 2 : ℕ) : Fp) =
      ((∑ r ∈ Finset.range 25, msG r * 2 ^ (K * r) : ℕ) : Fp))
    (hH : ((bitrange psi 249 5 + bitrange psi 254 1 * 32 : ℕ) : Fp) =
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
  have hBValueLt : bitrange gdX 250 4 + bitrange gdX 254 1 * 16 + gdY * 32 +
      bitrange pkdX 0 4 * 64 < 2 ^ K := by
    have hb0 : bitrange gdX 250 4 < 16 := by have := bitrange_lt gdX 250 4; omega
    have hb1 : bitrange gdX 254 1 < 2 := by have := bitrange_lt gdX 254 1; omega
    have hb3 : bitrange pkdX 0 4 < 16 := by have := bitrange_lt pkdX 0 4; omega
    norm_num [K]
    omega
  have hDValueLt : bitrange pkdX 254 1 + pkdY * 2 + bitrange v 0 58 * 4 < 2 ^ (K * 6) := by
    have hd0 : bitrange pkdX 254 1 < 2 := by have := bitrange_lt pkdX 254 1; omega
    have hv0 : bitrange v 0 58 < 2 ^ 58 := bitrange_lt _ _ _
    norm_num [K]
    omega
  have hEValueLt : bitrange v 58 6 + bitrange rho 0 4 * 64 < 2 ^ K := by
    have he0 : bitrange v 58 6 < 64 := by have := bitrange_lt v 58 6; omega
    have he1 : bitrange rho 0 4 < 16 := by have := bitrange_lt rho 0 4; omega
    norm_num [K]
    omega
  have hGValueLt : bitrange rho 254 1 + bitrange psi 0 249 * 2 < 2 ^ (K * 25) := by
    have hg0 : bitrange rho 254 1 < 2 := by have := bitrange_lt rho 254 1; omega
    have hg2 : bitrange psi 0 249 < 2 ^ 249 := bitrange_lt _ _ _
    norm_num [K]
    omega
  have hHValueLt : bitrange psi 249 5 + bitrange psi 254 1 * 32 < 2 ^ K := by
    have hh0 : bitrange psi 249 5 < 32 := by have := bitrange_lt psi 249 5; omega
    have hh1 : bitrange psi 254 1 < 2 := by have := bitrange_lt psi 254 1; omega
    norm_num [K]
    omega
  have hChunksA_low := chunksOf_eq_map_of_cast_sum hmsA hA
    (lt_trans (bitrange_lt gdX 0 250) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsA 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksA : chunksOf gdX 25 = (List.range 25).map msA := by
    rw [← chunksOf_mod gdX 25]
    convert hChunksA_low using 2
    simp [bitrange, K]
  have hChunksB := chunksOf_eq_map_of_cast_sum hmsB hB
    (lt_trans hBValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsB 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC_low := chunksOf_eq_map_of_cast_sum hmsC hC
    (lt_trans (bitrange_lt pkdX 4 250) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsC 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC : chunksOf (pkdX / 16) 25 =
      (List.range 25).map msC := by
    rw [← chunksOf_mod (pkdX / 16) 25]
    convert hChunksC_low using 2
  have hChunksD := chunksOf_eq_map_of_cast_sum hmsD hD
    (lt_trans hDValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsD 6) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksE := chunksOf_eq_map_of_cast_sum hmsE hE
    (lt_trans hEValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsE 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksF_low := chunksOf_eq_map_of_cast_sum hmsF hF
    (lt_trans (bitrange_lt rho 4 250) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsF 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksF : chunksOf (rho / 16) 25 =
      (List.range 25).map msF := by
    rw [← chunksOf_mod (rho / 16) 25]
    convert hChunksF_low using 2
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
    (hA : pieces[0] = ((bitrange gdX 0 250 : ℕ) : Fp))
    (hB : pieces[1] =
      ((bitrange gdX 250 4 + bitrange gdX 254 1 * 16 + gdY * 32 +
        bitrange pkdX 0 4 * 64 : ℕ) : Fp))
    (hC : pieces[2] = ((bitrange pkdX 4 250 : ℕ) : Fp))
    (hD : pieces[3] =
      ((bitrange pkdX 254 1 + pkdY * 2 + bitrange v 0 58 * 4 : ℕ) : Fp))
    (hE : pieces[4] =
      ((bitrange v 58 6 + bitrange rho 0 4 * 64 : ℕ) : Fp))
    (hF : pieces[5] = ((bitrange rho 4 250 : ℕ) : Fp))
    (hG : pieces[6] =
      ((bitrange rho 254 1 + bitrange psi 0 249 * 2 : ℕ) : Fp))
    (hH : pieces[7] =
      ((bitrange psi 249 5 + bitrange psi 254 1 * 32 : ℕ) : Fp))
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
    (unconstrained do return input.y)
  let k2 ← Utilities.LookupRangeCheck.WitnessShort.circuit 250 4 (by norm_num [K])
    (unconstrained do return input.y)
  let k3 ← witness (input.y.val.bitrange 254 1).toField
  let j ← witness ((input.lsb + k0 * (2 : Fp) : Expression Fp)
    + (input.y.val.bitrange 10 240).toField * Witgen.FExpr.const (2 ^ 10 : Fp))
  let jReads ← Utilities.LookupRangeCheck.CopyCheck.Decomposed.circuit j
  let j'Zs ← Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit 13
    (j + Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const tP)
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
  simp_all only [true_and]
  obtain ⟨hk0, hk2, hd, htel, h_gate⟩ := h_holds
  obtain ⟨lo, hlo, hdec⟩ := htel.2
  simp only [show K * 13 = 130 from rfl] at hlo hdec
  rw [htel.1] at h_gate
  exact (h_gate ⟨hd.1, hk0, hk2, rfl, hd.2.1, hd.2.2, lo, hlo, hdec⟩).1

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [Utilities.LookupRangeCheck.WitnessShort.circuit,
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
    rw [isLowBit_iff_mod_two.mp h_assumptions,
      show bitrange input_y.val 0 1 = input_y.val % 2 from by simp [bitrange]]
  have htile : bitrange input_y.val 0 250
      = bitrange input_y.val 0 1 + 2 * bitrange input_y.val 1 9
        + 2 ^ 10 * bitrange input_y.val 10 240 := by
    rw [show (250 : ℕ) = 1 + 249 from rfl, Orchard.Specs.bitrange_add,
      show (249 : ℕ) = 9 + 240 from rfl, Orchard.Specs.bitrange_add]
    ring
  -- `hk0` is a `.val = bitrange` fact; lift it to an `Fp` equation on the cell.
  have hk0F : env.get i₀ = ((bitrange input_y.val 1 9 : ℕ) : Fp) := by
    rw [← hk0]; exact (ZMod.natCast_zmod_val _).symm
  have hj_br : jv = ((bitrange input_y.val 0 250 : ℕ) : Fp) := by
    rw [hj, hlsb, hk0F, htile]
    push_cast; ring
  have hj_val : jv.val = bitrange input_y.val 0 250 := by
    rw [hj_br]; apply cast_bitrange_val (by norm_num)
  have hjlt : jv.val < 2 ^ 250 := by rw [hj_val]; exact bitrange_lt _ _ _
  -- `k3`'s direct witness gives the `Fp` value `↑(bitrange y 254 1)`; lift to `.val`.
  have hk3val : (env.get (i₀ + 2 + 2)).val = bitrange input_y.val 254 1 := by
    rw [hk3]; apply cast_bitrange_val (by norm_num)
  refine ⟨⟨?A, ⟨?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8⟩,
    h_assumptions, hj_val, hk0, hk2, hk3val, ?guard⟩,
    h_assumptions⟩
  case A => exact hjlt
  case B1 =>
    rw [hlsb, show bitrange input_y.val 0 1 = input_y.val % 2 from by simp [bitrange]]
    exact nat_mod_two_isBool _
  case B2 => exact hjlt
  case B3 => rw [hk0]; exact bitrange_lt _ _ _
  case B4 => rw [hk2]; exact bitrange_lt _ _ _
  case B5 => rw [htz0]
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
  cells.a.val = bitrange gd.x.val 0 250 ∧
  cells.b0.val = bitrange gd.x.val 250 4 ∧
  cells.b1.val = bitrange gd.x.val 254 1 ∧
  IsLowBit gd.y cells.b2 ∧
  cells.b3.val = bitrange pkd.x.val 0 4 ∧
  cells.c.val = bitrange pkd.x.val 4 250 ∧
  cells.d0.val = bitrange pkd.x.val 254 1 ∧
  IsLowBit pkd.y cells.d1 ∧
  cells.d2.val = bitrange value.val 0 8 ∧
  cells.e0.val = bitrange value.val 58 6 ∧
  cells.e1.val = bitrange rho.val 0 4 ∧
  cells.f.val = bitrange rho.val 4 250 ∧
  cells.g0.val = bitrange rho.val 254 1 ∧
  cells.g1.val = bitrange psi.val 0 9 ∧
  cells.h0.val = bitrange psi.val 249 5 ∧
  cells.h1.val = bitrange psi.val 254 1 ∧
  cells.b =
    cells.b0 + cells.b1 * 16 + cells.b2 * 32 + cells.b3 * 64 ∧
  cells.d =
    cells.d0 + cells.d1 * 2 + cells.d2 * 4 +
      ((bitrange value.val 8 50 : ℕ) : Fp) * 1024 ∧
  cells.e = cells.e0 + cells.e1 * 64 ∧
  cells.g =
    cells.g0 + cells.g1 * 2 + ((bitrange psi.val 9 240 : ℕ) : Fp) * 1024 ∧
  cells.h = cells.h0 + cells.h1 * 32

/-- Bridge a `.val` bit-slice fact back to its `Fp`-cast form. -/
theorem cell_eq_of_val {cell : Fp} {m : ℕ} (h : cell.val = m) :
    cell = (m : Fp) := by
  rw [← h, ZMod.natCast_zmod_val]

/-- Bridge an `Fp`-cast bit-slice fact to its `.val` form. -/
private theorem val_eq_of_cell_eq {cell : Fp} {n s l : ℕ} (hl : l ≤ 254)
    (h : cell = ((bitrange n s l : ℕ) : Fp)) :
    cell.val = bitrange n s l := by
  have hlt : bitrange n s l < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    have h1 := bitrange_lt n s l
    have h2 : (2 : ℕ) ^ l ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) hl
    have h3 : (2 : ℕ) ^ 254 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    omega
  rw [h, ZMod.val_natCast_of_lt hlt]

theorem noteCommitPieceValues_of_messageCellFacts {gd pkd : Point Fp}
    {value rho psi : Fp} {cells : MessageCells Fp}
    (hvalue : value.val < 2 ^ 64)
    (h : MessageCellFacts gd pkd value rho psi cells) :
    NoteCommitPieceValues (noteScalars gd pkd value rho psi) (messagePieces cells) := by
  simp only [MessageCellFacts] at h
  obtain ⟨ha, hb0, hb1, hygd, hb3, hc, hd0, hypkd, hd2, he0, he1, hf, hg0, hg1,
    hh0, hh1, hb, hd, he, hg, hh⟩ := h
  replace ha := cell_eq_of_val ha
  replace hb0 := cell_eq_of_val hb0
  replace hb1 := cell_eq_of_val hb1
  replace hb3 := cell_eq_of_val hb3
  replace hc := cell_eq_of_val hc
  replace hd0 := cell_eq_of_val hd0
  replace hd2 := cell_eq_of_val hd2
  replace he0 := cell_eq_of_val he0
  replace he1 := cell_eq_of_val he1
  replace hf := cell_eq_of_val hf
  replace hg0 := cell_eq_of_val hg0
  replace hg1 := cell_eq_of_val hg1
  replace hh0 := cell_eq_of_val hh0
  replace hh1 := cell_eq_of_val hh1
  have hgdY := isLowBit_iff_mod_two.mp hygd
  have hpkdY := isLowBit_iff_mod_two.mp hypkd
  simp only [NoteCommitPieceValues, noteScalars, messagePieces]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [bitrange, K] using ha
  · have hcell : cells.b =
        ((gd.x.val / 2 ^ 250 % 16 + (gd.x.val / 2 ^ 254 % 2) * 16 +
          (gd.y.val % 2) * 32 + (pkd.x.val % 16) * 64 : ℕ) : Fp) := by
      rw [hb, hb0, hb1, hgdY, hb3]
      simp only [bitrange, pow_zero, Nat.div_one]
      push_cast
      ring_nf
    refine hcell.trans ?_
    congr 1
    norm_num [bitrange]
  · simpa [bitrange, K] using hc
  · have hcell : cells.d =
        ((pkd.x.val / 2 ^ 254 % 2 + (pkd.y.val % 2) * 2 +
          (value.val % 2 ^ 58) * 4 : ℕ) : Fp) := by
      rw [hd, hd0, hpkdY, hd2]
      have hsplit := bitrange_add value.val 0 8 50
      norm_num at hsplit
      have hsplit' :
          value.val % 2 ^ 58 = value.val % 256 + 256 * (value.val / 256 % 2 ^ 50) := by
        simpa [bitrange] using hsplit
      norm_num at hsplit'
      simp only [bitrange, pow_zero, Nat.div_one]
      push_cast
      rw [show ((value.val % 288230376151711744 : ℕ) : Fp) =
          ((value.val % 256 + 256 * (value.val / 256 % 1125899906842624) : ℕ) : Fp) by
        rw [hsplit']]
      push_cast
      ring_nf
    refine hcell.trans ?_
    congr 1
    norm_num [bitrange]
  · have hcell : cells.e =
        ((value.val / 2 ^ 58 % 64 + (rho.val % 16) * 64 : ℕ) : Fp) := by
      rw [he, he0, he1]
      simp only [bitrange, pow_zero, Nat.div_one]
      push_cast
      ring_nf
    refine hcell.trans ?_
    congr 1
    norm_num [bitrange]
  · simpa [bitrange, K] using hf
  · have hcell : cells.g =
        ((rho.val / 2 ^ 254 % 2 + (psi.val % 2 ^ 249) * 2 : ℕ) : Fp) := by
      rw [hg, hg0, hg1]
      have hsplit := bitrange_add psi.val 0 9 240
      norm_num at hsplit
      have hsplit' :
          psi.val % 2 ^ 249 = psi.val % 512 + 512 * (psi.val / 512 % 2 ^ 240) := by
        simpa [bitrange] using hsplit
      norm_num at hsplit'
      simp only [bitrange, pow_zero, Nat.div_one]
      push_cast
      rw [show ((psi.val % 904625697166532776746648320380374280103671755200316906558262375061821325312 : ℕ) : Fp) =
          ((psi.val % 512 +
            512 * (psi.val / 512 %
              1766847064778384329583297500742918515827483896875618958121606201292619776) : ℕ) : Fp) by
        rw [hsplit']]
      push_cast
      ring_nf
    refine hcell.trans ?_
    congr 1
    norm_num [bitrange]
  · have hcell : cells.h =
        ((psi.val / 2 ^ 249 % 32 + (psi.val / 2 ^ 254 % 2) * 32 : ℕ) : Fp) := by
      rw [hh, hh0, hh1]
      simp only [bitrange]
      push_cast
      ring_nf
    refine hcell.trans ?_
    congr 1
  · exact lt_trans (ZMod.val_lt _) (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  · exact Nat.mod_lt _ (by norm_num)
  · exact lt_trans (ZMod.val_lt _) (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  · exact Nat.mod_lt _ (by norm_num)
  · exact hvalue
  · exact lt_trans (ZMod.val_lt _) (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  · exact lt_trans (ZMod.val_lt _) (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

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

def NoteCommitRelation (G : Generators) (Q : Point Fp)
    (R : MulFixed.FixedBase) (input : Value Input Fp) (cm : Point Fp) : Prop :=
  ∃ rcm : Fq, ∀ B : Point Fp,
    hashToPoint G.S Q
        (noteScalars input.gd input.pkd input.value input.rho input.psi).chunks = some B →
      cm = B + rcm • R

def ProverNoteCommitRelation (G : Generators) (Q : Point Fp)
    (R : MulFixed.FixedBase) (input : ProverValue Input Fp) (cm : Point Fp) : Prop :=
  ∀ B : Point Fp,
    hashToPoint G.S Q
        (noteScalars input.gd input.pkd input.value input.rho input.psi).chunks = some B →
      cm = B + ((show ℕ from input.rcm : ℕ) : Fq) • R

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
    (unconstrained do return gdX)
  let b3 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 4 (by norm_num [K])
    (unconstrained do return pkdX)
  let d2 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 8 (by norm_num [K])
    (unconstrained do return v)
  let e0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 58 6 (by norm_num [K])
    (unconstrained do return v)
  let e1 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 4 (by norm_num [K])
    (unconstrained do return rho)
  let g1 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 9 (by norm_num [K])
    (unconstrained do return psi)
  let h0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 249 5 (by norm_num [K])
    (unconstrained do return psi)
  let b1 ← witness (gdX.val.bitrange 254 1).toField
  let b2 ← witness (gdY.val.bitrange 0 1).toField
  let d0 ← witness (pkdX.val.bitrange 254 1).toField
  let d1 ← witness (pkdY.val.bitrange 0 1).toField
  let g0 ← witness (rho.val.bitrange 254 1).toField
  let h1 ← witness (psi.val.bitrange 254 1).toField

  -- `y_canonicity` (for the `ỹ` sign cells `b2`/`d1`) is *not* run here: it requires
  -- `IsBool b2`/`IsBool d1`, which the source establishes in the `b`/`d` message-piece
  -- decomposition gates (`MessagePieceChecks`). It is therefore composed at the top level,
  -- after `MessagePieceChecks`, as a sibling of the x-canonicity gates.
  let a ← witness (gdX.val.bitrange 0 250).toField
  let b ← witness (b0 + b1 * (2 ^ 4 : Fp) + b2 * (2 ^ 5 : Fp) + b3 * (2 ^ 6 : Fp) : Expression Fp)
  let c ← witness (pkdX.val.bitrange 4 250).toField
  let d ← witness ((d0 + d1 * (2 : Fp) + d2 * (2 ^ 2 : Fp) : Expression Fp)
    + (v.val.bitrange 8 50).toField * Witgen.FExpr.const (2 ^ 10 : Fp))
  let e ← witness (e0 + e1 * (2 ^ 6 : Fp) : Expression Fp)
  let f ← witness (rho.val.bitrange 4 250).toField
  let g ← witness ((g0 + g1 * (2 : Fp) : Expression Fp)
    + (psi.val.bitrange 9 240).toField * Witgen.FExpr.const (2 ^ 10 : Fp))
  let h ← witness (h0 + h1 * (2 ^ 5 : Fp) : Expression Fp)
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

/-- The honest 1-bit `bitrange` cast of `y` is its low (sign) bit. -/
theorem isLowBit_bitrange (y : Fp) : IsLowBit y ((bitrange y.val 0 1 : ℕ) : Fp) := by
  unfold IsLowBit
  rw [show bitrange y.val 0 1 = y.val % 2 from by simp [bitrange],
    ZMod.val_natCast_of_lt (lt_trans (Nat.mod_lt _ (by norm_num))
      (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))]

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
  obtain ⟨⟨_, e_b0⟩, ⟨_, e_b3⟩, ⟨_, e_d2⟩, ⟨_, e_e0⟩, ⟨_, e_e1⟩, ⟨_, e_g1⟩, ⟨_, e_h0⟩,
    e_b1, e_b2, e_d0, e_d1, e_g0, e_h1, e_a, e_b, e_c, e_d, e_e, e_f, e_g, e_h⟩ := h_env
  refine ⟨val_eq_of_cell_eq (by norm_num) e_a, e_b0,
    val_eq_of_cell_eq (by norm_num) e_b1, ?_, e_b3,
    val_eq_of_cell_eq (by norm_num) e_c, val_eq_of_cell_eq (by norm_num) e_d0, ?_,
    e_d2, e_e0,
    e_e1, val_eq_of_cell_eq (by norm_num) e_f,
    val_eq_of_cell_eq (by norm_num) e_g0, e_g1,
    e_h0, val_eq_of_cell_eq (by norm_num) e_h1,
    e_b.trans (by ring),
    e_d.trans (by rw [Orchard.Specs.val_Fp]; ring), e_e.trans (by ring),
    e_g.trans (by rw [Orchard.Specs.val_Fp]; ring),
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
  CommitDomain.Output messagePieceRounds F

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (input : Var Input Fp) :
    Circuit Fp (Var Output Fp) :=
  CommitDomain.circuit G Q hQ R 24 messagePieceTailRounds input

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp
      (CommitDomain.Input 8)
      (CommitDomain.Output messagePieceRounds) (main G Q hQ R) := by
  elaborate_circuit_with {
    localLength _ := 1407
    output input offset := {
      point := varFromOffset Point (offset + 1400),
      zs := ((HashToPoint.main G Q 24 messagePieceTailRounds input.pieces).output (offset + 849)).zs }
  }

def Spec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (output : Value Output Fp) (data : ProverData Fp) : Prop :=
  CommitDomain.Spec G Q R 24 messagePieceTailRounds
    input output data

def ProverAssumptions (G : Generators) (Q : Point Fp)
    (input : ProverValue Input Fp) (data : ProverData Fp)
    (hint : ProverHint Fp) : Prop :=
  CommitDomain.ProverAssumptions G Q 24 messagePieceTailRounds input data hint

def ProverSpec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (output : ProverValue Output Fp) (hint : ProverHint Fp) :
    Prop :=
  CommitDomain.ProverSpec G Q R 24 messagePieceTailRounds input output hint

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) (fun _ _ => True) (Spec G Q R) := by
  circuit_proof_start [CommitDomain.circuit]
  simpa [Spec, Chain.chainLength, messagePieceTailRounds] using h_holds

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R) (ProverAssumptions G Q)
      (ProverSpec G Q R) := by
  circuit_proof_start [CommitDomain.circuit]
  refine ⟨?_, ?_⟩
  · simpa using h_assumptions
  · exact ((h_env (by simpa using h_assumptions)).2)

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
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
    (input.a + Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const tP)
  Gate.circuit
    { gdX := input.gdX, b0 := input.b0, b1 := input.b1, a := input.a,
      a' := a'Zs.z0, z13A := input.z13A, z13A' := a'Zs.zLast }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  IsBool input.b1 ∧ input.a.val < 2 ^ 250 ∧ input.b0.val < 2 ^ 4 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp)

def Spec (input : Input Fp) : Prop :=
  input.a.val = bitrange input.gdX.val 0 250 ∧
    input.b0.val = bitrange input.gdX.val 250 4 ∧
    input.b1.val = bitrange input.gdX.val 254 1

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and]
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
  obtain ⟨ha_val, hb0_val, hb1_val⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 13 = 130 from by norm_num [K]] at hlo hdec hzLast
  refine ⟨⟨hb1, ha_lt, hb0_lt, by linear_combination hz0, hz13A, lo, hlo,
    by linear_combination hdec + hz0⟩, ha_val, hb0_val, hb1_val, fun h1 => ?_⟩
  -- `b1 = 1` ⇒ `g_d` canonical ⇒ `a < t_P` ⇒ the honest tail `zLast` from `ProverSpec` vanishes.
  obtain ⟨_, hatp, _⟩ := high_bit_canonical (ZMod.val_lt input_gdX) (bit_one_of_val_eq hb1_val h1)
  rw [hzLast,
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
      Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const tP)
  Gate.circuit
    { pkdX := input.pkdX, b3 := input.b3, c := input.c, d0 := input.d0,
      b3C' := b3C'Zs.z0, z13C := input.z13C, z14B3C' := b3C'Zs.zLast }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  IsBool input.d0 ∧ input.c.val < 2 ^ 250 ∧ input.b3.val < 2 ^ 4 ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp)

def Spec (input : Input Fp) : Prop :=
  input.b3.val = bitrange input.pkdX.val 0 4 ∧
    input.c.val = bitrange input.pkdX.val 4 250 ∧
    input.d0.val = bitrange input.pkdX.val 254 1

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and]
  obtain ⟨⟨z0_eq, element_eq⟩, h_gate⟩ := h_holds
  rw [z0_eq] at h_gate
  have hshift :
      input_b3 + ((2 ^ 4 : ℕ) : Fp) * input_c + ((2 ^ 140 : ℕ) : Fp) - tP =
        input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP := by
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
  obtain ⟨hb3_val, hc_val, hd0_val⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 14 = 140 from by norm_num [K]] at hlo hdec hzLast
  refine ⟨⟨hd0, hc_lt, hb3_lt, by linear_combination hz0, hz13C, lo, hlo,
    by linear_combination hdec + hz0⟩, hb3_val, hc_val, hd0_val, fun h1 => ?_⟩
  -- `d0 = 1` ⇒ `x(pk_d)` canonical ⇒ the low 254-bit base `< t_P` ⇒ honest tail vanishes.
  have hbase_lt := base_val_lt_tP_val hb3_val hc_val (ZMod.val_lt input_pkdX)
    (bit_one_of_val_eq hd0_val h1) (by norm_num)
  rw [hzLast,
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
      Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const tP)
  Gate.circuit
    { rho := input.rho, e1 := input.e1, f := input.f, g0 := input.g0,
      e1F' := e1F'Zs.z0, z13F := input.z13F, z14E1F' := e1F'Zs.zLast }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  IsBool input.g0 ∧ input.f.val < 2 ^ 250 ∧ input.e1.val < 2 ^ 4 ∧
    input.z13F = ((input.f.val / 2 ^ 130 : ℕ) : Fp)

def Spec (input : Input Fp) : Prop :=
  input.e1.val = bitrange input.rho.val 0 4 ∧
    input.f.val = bitrange input.rho.val 4 250 ∧
    input.g0.val = bitrange input.rho.val 254 1

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and]
  obtain ⟨⟨z0_eq, element_eq⟩, h_gate⟩ := h_holds
  rw [z0_eq] at h_gate
  have hshift :
      input_e1 + ((2 ^ 4 : ℕ) : Fp) * input_f + ((2 ^ 140 : ℕ) : Fp) - tP =
        input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP := by
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
  obtain ⟨he1_val, hf_val, hg0_val⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 14 = 140 from by norm_num [K]] at hlo hdec hzLast
  refine ⟨⟨hg0, hf_lt, he1_lt, by linear_combination hz0, hz13F, lo, hlo,
    by linear_combination hdec + hz0⟩, he1_val, hf_val, hg0_val, fun h1 => ?_⟩
  -- `g0 = 1` ⇒ `rho` canonical ⇒ the low 254-bit base `< t_P` ⇒ honest tail vanishes.
  have hbase_lt := base_val_lt_tP_val he1_val hf_val (ZMod.val_lt input_rho)
    (bit_one_of_val_eq hg0_val h1) (by norm_num)
  rw [hzLast,
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
      Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const tP)
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
  input.g1.val = bitrange input.psi.val 0 9 ∧
    input.g2.val = bitrange input.psi.val 9 240 ∧
    input.h0.val = bitrange input.psi.val 249 5 ∧
    input.h1.val = bitrange input.psi.val 254 1

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit, Gate.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Telescoped.Spec, Gate.Spec, Gate.Assumptions
  ]
  simp_all only [true_and]
  obtain ⟨⟨z0_eq, element_eq⟩, h_gate⟩ := h_holds
  rw [z0_eq] at h_gate
  have hshift :
      input_g1 + ((2 ^ 9 : ℕ) : Fp) * input_g2 + ((2 ^ 130 : ℕ) : Fp) - tP =
        input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) - tP := by
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
  obtain ⟨hg1_val, hg2_val, hh0_val, hh1_val⟩ := h_spec
  obtain ⟨⟨hz0, lo, hlo, hdec⟩, _, hzLast⟩ := h_env
  simp only [show K * 13 = 130 from by norm_num [K]] at hlo hdec hzLast
  refine ⟨⟨hh1, hg1_lt, hg2_lt, hh0_lt, by linear_combination hz0, hz13G, lo, hlo,
    by linear_combination hdec + hz0⟩, hg1_val, hg2_val, hh0_val, hh1_val, fun h1 => ?_⟩
  -- `h1 = 1` ⇒ `psi` canonical ⇒ the low 249-bit base `< t_P` ⇒ honest tail vanishes.
  have hbase_lt := base_val_lt_tP_val hg1_val hg2_val (ZMod.val_lt input_psi)
    (bit_one_of_val_eq hh1_val h1) (by norm_num)
  rw [hzLast,
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
    ∃ ms : ℕ → ℕ, (∀ r, ms r < 2 ^ K) ∧
      pieces[0] = ((∑ r ∈ Finset.range (n + 1),
        ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
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
    2 ^ (K * m) < PALLAS_BASE_CARD := by
  have hle : K * m ≤ 250 := by
    simp only [K]; omega
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hle)
    (by norm_num [PALLAS_BASE_CARD])

theorem zsFacts_cell_eq_div {n : ℕ} {piece : Fp} {chunks : List ℕ} {ms : ℕ → ℕ}
    (hm : n + 1 ≤ 25) (hms : ∀ r, ms r < 2 ^ K)
    (hpc : piece = ((∑ r ∈ Finset.range (n + 1),
      ms r * 2 ^ (K * r) : ℕ) : Fp))
    (hgetD : ∀ i, i < n + 1 → chunks.getD i 0 = ms i)
    {r : ℕ} (hr : r ≤ n) :
    ((∑ j ∈ Finset.range (n + 1 - r),
        chunks.getD (r + j) 0 * 2 ^ (K * j) : ℕ) : Fp)
      = ((piece.val / 2 ^ (K * r) : ℕ) : Fp) := by
  have hpval : piece.val = ∑ r ∈ Finset.range (n + 1),
      ms r * 2 ^ (K * r) := by
    rw [hpc, ZMod.val_natCast_of_lt
      (lt_trans (sum_digits_lt hms (n + 1)) (two_pow_K_lt_card hm))]
  have hsum : (∑ j ∈ Finset.range (n + 1 - r),
      chunks.getD (r + j) 0 * 2 ^ (K * j))
        = ∑ j ∈ Finset.range (n + 1 - r),
          ms (r + j) * 2 ^ (K * j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hgetD (r + j) (by omega)]
  rw [hsum, hpval, sum_suffix_div hms (n + 1) r (by omega)]

private theorem pieceChunks_head_val_lt {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (hm : n + 1 ≤ 25)
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    ZMod.val (pieces[0] : Fp) < 2 ^ (K * (n + 1)) := by
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
        chunks.getD (i.val + j) 0 * 2 ^ (K * j) : ℕ) : Fp))) :
    (HVec.head zs)[r]'(Nat.lt_succ_of_le hr)
      = (((pieces[0] : Fp).val / 2 ^ (K * r) : ℕ) : Fp) := by
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
            / 2 ^ (K * r) : ℕ) : Fp)
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
      (pieces[i] : Fp).val < 2 ^ (K * (ns[i] + 1))
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

/-- Honest head running-sum cell at arbitrary index `r ≤ n`. -/
private theorem zsHonest_head_cell {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp} {r : ℕ} (hr : r ≤ n)
    (hhead : HVec.head zs = Vector.ofFn (fun i : Fin (n + 1) =>
      Orchard.Sinsemilla.pieceZ pieces[0] i.val)) :
    (HVec.head zs)[r]'(Nat.lt_succ_of_le hr)
      = (((pieces[0] : Fp).val / 2 ^ (K * r) : ℕ) : Fp) := by
  rw [hhead, Vector.getElem_ofFn]
  rfl

/-- Honest running-sum cell extraction: the `r`-th entry of the `i`-th piece's honest
running-sum vector is `pieces[i].val / 2^(K·r)`. (Completeness analog of `zsFacts_cell`.) -/
theorem zsHonest_cell :
    ∀ (ns : List ℕ) (pieces : Vector Fp ns.length)
      (zs : HVec (Orchard.Sinsemilla.Chain.zLengths ns) Fp)
      (i : Fin (Orchard.Sinsemilla.Chain.zLengths ns).length),
      Orchard.Sinsemilla.Chain.ZsHonest ns pieces zs →
      ∀ {r : ℕ} (hr : r < (Orchard.Sinsemilla.Chain.zLengths ns)[i]),
      (HVec.get (Orchard.Sinsemilla.Chain.zLengths ns) zs i)[r]'hr
        = (((pieces[i.val]'(by
              have := i.isLt
              simpa only [Orchard.Sinsemilla.Chain.zLengths, List.length_map] using this) : Fp).val
            / 2 ^ (K * r) : ℕ) : Fp)
  | n :: rest, pieces, zs, ⟨0, _⟩, hZs, r, hr => by
      simp only [Orchard.Sinsemilla.Chain.ZsHonest] at hZs
      have hr' : r < n + 1 := hr
      exact zsHonest_head_cell (Nat.lt_succ_iff.mp hr') hZs.1
  | n :: rest, pieces, zs, ⟨k + 1, hk⟩, hZs, r, hr => by
      simp only [Orchard.Sinsemilla.Chain.ZsHonest] at hZs
      have hkr : k < (Orchard.Sinsemilla.Chain.zLengths rest).length := by
        have hk' : k + 1 < (Orchard.Sinsemilla.Chain.zLengths (n :: rest)).length := hk
        simp only [Orchard.Sinsemilla.Chain.zLengths, List.length_map, List.length_cons]
          at hk' ⊢
        omega
      have IH := zsHonest_cell rest pieces.tail (HVec.tail zs) ⟨k, hkr⟩ hZs.2 hr
      have hk_tail : k < (n :: rest).length - 1 := by
        simp only [List.length_cons, Nat.add_sub_cancel]
        simpa only [Orchard.Sinsemilla.Chain.zLengths, List.length_map] using hkr
      have hbridge :
          pieces.tail[(⟨k, hkr⟩ : Fin (Orchard.Sinsemilla.Chain.zLengths rest).length).val]
            = pieces[(⟨k + 1, hk⟩ :
                Fin (Orchard.Sinsemilla.Chain.zLengths (n :: rest)).length).val] :=
        Vector.getElem_tail (v := pieces) (i := k) (hi := hk_tail)
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
  replace ha := cell_eq_of_val ha
  replace hb0 := cell_eq_of_val hb0
  replace hb1 := cell_eq_of_val hb1
  replace hb3 := cell_eq_of_val hb3
  replace hc := cell_eq_of_val hc
  replace hd0 := cell_eq_of_val hd0
  replace hd2 := cell_eq_of_val hd2
  replace he0 := cell_eq_of_val he0
  replace he1 := cell_eq_of_val he1
  replace hf := cell_eq_of_val hf
  replace hg0 := cell_eq_of_val hg0
  replace hg1 := cell_eq_of_val hg1
  replace hh0 := cell_eq_of_val hh0
  replace hh1 := cell_eq_of_val hh1
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
    exact ha
  · show cells.b = _
    rw [hb_dec, hb0, hb1, hb2', hb3]
    simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring
  · show cells.c = _
    exact hc
  · show cells.d = _
    rw [hd_dec, hd0, hd1', hd2]
    simp only [bitrange, pow_zero, Nat.div_one]
    rw [show ZMod.val value % 2 ^ 58 = _ from mod_pow_split (ZMod.val value) 8 50]
    push_cast; ring
  · show cells.e = _
    rw [he_dec, he0, he1]
    simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring
  · show cells.f = _
    exact hf
  · show cells.g = _
    rw [hg_dec, hg0, hg1]
    simp only [bitrange, pow_zero, Nat.div_one]
    rw [show ZMod.val psi % 2 ^ 249 = _ from mod_pow_split (ZMod.val psi) 9 240]
    push_cast; ring
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
  replace ha := cell_eq_of_val ha
  replace hb0 := cell_eq_of_val hb0
  replace hb1 := cell_eq_of_val hb1
  replace hb3 := cell_eq_of_val hb3
  replace hc := cell_eq_of_val hc
  replace hd0 := cell_eq_of_val hd0
  replace hd2 := cell_eq_of_val hd2
  replace he0 := cell_eq_of_val he0
  replace he1 := cell_eq_of_val he1
  replace hf := cell_eq_of_val hf
  replace hg0 := cell_eq_of_val hg0
  replace hg1 := cell_eq_of_val hg1
  replace hh0 := cell_eq_of_val hh0
  replace hh1 := cell_eq_of_val hh1
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

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
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

def mainOutput (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (input : Var Input Fp) (offset : ℕ) :
    Var Point Fp :=
  (main G Q hQ R input).output offset

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    ElaboratedCircuit Fp Input Point (main G Q hQ R) := by
  elaborate_circuit

/-- `g_d` and `pk_d` enter the Halo2 gadget as already-assigned non-identity points. In
Clean's point model this is the on-curve half of `NonIdentityEccPoint`; identity is not
representable as an affine point in the source API at this boundary. -/
def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  input.gd.OnCurve ∧ input.pkd.OnCurve

/-- `cm` is the Orchard note commitment of the note `(g_d, pk_d, value, rho, psi)` with
randomness `rcm`: `cm = NoteCommit^Orchard_rcm(g★_d || pk★_d || v || rho || psi)`. The
message is the `Sinsemilla` hash of the canonical 109-chunk encoding (the canonicity
gates force the field inputs into that canonical bit-layout) translated by `[rcm] R`. -/
def Spec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (cm : Point Fp) (_ : ProverData Fp) : Prop :=
  NoteCommitRelation G Q R input cm

def ProverAssumptions (G : Generators) (Q : Point Fp)
    (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  input.gd.OnCurve ∧
  input.pkd.OnCurve ∧
  -- the note's value is a `u64` (the prover commits to a valid note); the `value_canonicity`
  -- gate's constraint `value = d2 + d3·2^8 + e0·2^58` is satisfiable only at such values.
  (show Fp from input.value).val < 2 ^ 64 ∧
  -- the commitment randomness hint is the canonical natural representative of `rcm : Fq`
  (show ℕ from input.rcm) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
    noteScalarsOf input.gd input.pkd input.value input.rho input.psi
  ∃ B, hashToPoint G.S Q
    (noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi) = some B

def ProverSpec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (cm : ProverValue Point Fp)
    (_ : ProverHint Fp) : Prop :=
  ProverNoteCommitRelation G Q R input cm

private theorem z13G_tail_of_decompose_g {g g0 g1 g2 z13G : Fp}
    (hg0_bool : IsBool g0)
    (hg1_lt : g1.val < 2 ^ 9)
    (hg2_lt : g2.val < 2 ^ 240)
    (hg : g = g0 + g1 * 2 + g2 * 1024)
    (hz13 : z13G = ((g.val / 2 ^ 130 : ℕ) : Fp)) :
    z13G = (((g1.val + g2.val * 2 ^ 9) / 2 ^ 129 : ℕ) : Fp) := by
  have hg0_lt : g0.val < 2 := IsBool.val_lt_two hg0_bool
  have h01sum : g0.val + g1.val * 2 ^ 1 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at *
    omega
  have h01val :
      (g0 + g1 * ((2 ^ 1 : ℕ) : Fp)).val = g0.val + g1.val * 2 ^ 1 :=
    val_limb2 1 h01sum
  have hsum :
      (g0 + g1 * ((2 ^ 1 : ℕ) : Fp)).val + g2.val * 2 ^ 10 <
        CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    rw [h01val]
    norm_num at *
    omega
  have hg_val : g.val = g0.val + g1.val * 2 + g2.val * 1024 := by
    rw [hg]
    have hval := val_limb2 (lo := g0 + g1 * ((2 ^ 1 : ℕ) : Fp)) (hi := g2) 10 hsum
    rw [show g0 + g1 * 2 + g2 * 1024 =
        (g0 + g1 * ((2 ^ 1 : ℕ) : Fp)) + g2 * ((2 ^ 10 : ℕ) : Fp) by
      norm_num]
    rw [hval, h01val]
    norm_num
  have hdiv :
      (g0.val + g1.val * 2 + g2.val * 1024) / 2 ^ 130 =
        (g1.val + g2.val * 2 ^ 9) / 2 ^ 129 := by
    norm_num at *
    omega
  rw [hz13, hg_val, hdiv]

theorem valueCanonicity_assumptions_of_commit
    (O : Var Commit.Output Fp) (input_var : Var Input Fp) (cells : Var MessageCells Fp)
    (env : Environment Fp)
    (hd2 : (eval env cells).d2.val < 2 ^ 8)
    (he0 : (eval env cells).e0.val < 2 ^ 6)
    (hd : (eval env cells).d.val < 2 ^ 60)
    (hz1d : (HVec.get (Chain.zLengths messagePieceRounds) (eval env O).zs ⟨3, by decide⟩)[1]
      = (((eval env cells).d.val / 2 ^ 10 : ℕ) : Fp)) :
    ValueCanonicity.circuit.Assumptions
      (eval env
        ({ value := input_var.value, d2 := cells.d2,
           d3 := (HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨3, by decide⟩)[1],
           e0 := cells.e0 } : Var ValueCanonicity.Input Fp)) := by
  rw [show ValueCanonicity.circuit.Assumptions = ValueCanonicity.Assumptions from rfl]
  simp only [ValueCanonicity.Assumptions, ValueCanonicity.Gate.Assumptions, circuit_norm]
  refine ⟨by simpa [circuit_norm] using hd2, ?_, by simpa [circuit_norm] using he0⟩
  have hz1d_eval : Expression.eval env
      ((HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨3, by decide⟩)[1]) =
      (((eval env cells).d.val / 2 ^ 10 : ℕ) : Fp) := by
    exact (CircuitType.eval_expr env _).symm.trans
      ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) O.zs ⟨3, by decide⟩ 1
        (by decide)).trans (by simpa [circuit_norm] using hz1d))
  change (Expression.eval env
      ((HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨3, by decide⟩)[1])).val <
      2 ^ 50
  rw [hz1d_eval]
  rw [ZMod.val_natCast_of_lt]
  · omega
  · have hq : (eval env cells).d.val / 2 ^ 10 < 2 ^ 50 := by
      omega
    exact lt_trans hq (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

theorem psiCanonicity_assumptions_of_commit
    (O : Var Commit.Output Fp) (input_var : Var Input Fp) (cells : Var MessageCells Fp)
    (env : Environment Fp)
    (hh1_bool : IsBool (Expression.eval env cells.h1))
    (hg0_bool : IsBool (Expression.eval env cells.g0))
    (hg_decomp : Expression.eval env cells.g =
      Expression.eval env cells.g0 + Expression.eval env cells.g1 * 2 +
        Expression.eval env ((HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩)[1]) * 1024)
    (hg1_lt : (eval env cells).g1.val < 2 ^ 9)
    (hh0_lt : (eval env cells).h0.val < 2 ^ 5)
    (hg_lt : (eval env cells).g.val < 2 ^ 250)
    (hz1g : (HVec.get (Chain.zLengths messagePieceRounds) (eval env O).zs ⟨6, by decide⟩)[1]
      = (((eval env cells).g.val / 2 ^ 10 : ℕ) : Fp))
    (hz13g : (HVec.get (Chain.zLengths messagePieceRounds) (eval env O).zs ⟨6, by decide⟩)[13]
      = (((eval env cells).g.val / 2 ^ 130 : ℕ) : Fp)) :
    PsiCanonicity.circuit.Assumptions
      (eval env
        ({ psi := input_var.psi, h0 := cells.h0, g1 := cells.g1, h1 := cells.h1,
           g2 := (HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩)[1],
           z13G := (HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩)[13] }
          : Var PsiCanonicity.Input Fp)) := by
  rw [show PsiCanonicity.circuit.Assumptions = PsiCanonicity.Assumptions from rfl]
  simp only [PsiCanonicity.Assumptions, circuit_norm]
  have hz1g_eval : Expression.eval env
      ((HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩)[1]) =
      (((eval env cells).g.val / 2 ^ 10 : ℕ) : Fp) := by
    exact (CircuitType.eval_expr env _).symm.trans
      ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩ 1
        (by decide)).trans (by simpa [circuit_norm] using hz1g))
  have hz13g_eval : Expression.eval env
      ((HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩)[13]) =
      (((eval env cells).g.val / 2 ^ 130 : ℕ) : Fp) := by
    exact (CircuitType.eval_expr env _).symm.trans
      ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩ 13
        (by decide)).trans (by simpa [circuit_norm] using hz13g))
  have hg2_lt : (Expression.eval env
      ((HVec.get (Chain.zLengths messagePieceRounds) O.zs ⟨6, by decide⟩)[1])).val <
      2 ^ 240 := by
    rw [hz1g_eval]
    rw [ZMod.val_natCast_of_lt]
    · omega
    · have hq : (eval env cells).g.val / 2 ^ 10 < 2 ^ 240 := by
        omega
      exact lt_trans hq (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  refine ⟨hh1_bool, by simpa [circuit_norm] using hg1_lt, hg2_lt,
    by simpa [circuit_norm] using hh0_lt, ?_⟩
  exact z13G_tail_of_decompose_g hg0_bool (by simpa [circuit_norm] using hg1_lt) hg2_lt
    hg_decomp (by simpa [circuit_norm] using hz13g_eval)

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
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
  simp only [Commit.circuit, Commit.Spec, CommitDomain.Spec] at hComSpec
  obtain ⟨chunks, rcm, hPC, hZs, hHash⟩ := hComSpec
  have ha_lt : (eval env AM).a.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨0, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hc_lt : (eval env AM).c.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨2, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hd_lt : (eval env AM).d.val < 2 ^ 60 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨3, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hf_lt : (eval env AM).f.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨5, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hg_lt : (eval env AM).g.val < 2 ^ 250 := by
    have h := pieceChunks_val_lt messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks ⟨6, by decide⟩ hPC (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hz13a :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨0, by decide⟩)[13] =
        (((eval env AM).a.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨0, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hz13c :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨2, by decide⟩)[13] =
        (((eval env AM).c.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨2, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hz1d :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨3, by decide⟩)[1] =
        (((eval env AM).d.val / 2 ^ 10 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨3, by decide⟩ hPC hZs (by decide) (r := 1) (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hz13f :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨5, by decide⟩)[13] =
        (((eval env AM).f.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨5, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hz1g :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨6, by decide⟩)[1] =
        (((eval env AM).g.val / 2 ^ 10 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨6, by decide⟩ hPC hZs (by decide) (r := 1) (by decide)
    simpa [messagePieceRounds, K, K] using h
  have hz13g :
      (HVec.get (Chain.zLengths messagePieceRounds) (eval env COut).zs ⟨6, by decide⟩)[13] =
        (((eval env AM).g.val / 2 ^ 130 : ℕ) : Fp) := by
    have h := zsFacts_cell messagePieceRounds
      #v[(eval env AM).a, (eval env AM).b, (eval env AM).c, (eval env AM).d,
        (eval env AM).e, (eval env AM).f, (eval env AM).g, (eval env AM).h]
      chunks (eval env COut).zs ⟨6, by decide⟩ hPC hZs (by decide) (r := 13) (by decide)
    simpa [messagePieceRounds, K, K] using h
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
  have hValSpec := hVal
    (valueCanonicity_assumptions_of_commit COut input_var AM env hd2_lt he0_lt hd_lt hz1d)
  rw [show ValueCanonicity.circuit.Spec = ValueCanonicity.Spec from rfl] at hValSpec
  simp only [ValueCanonicity.Spec, circuit_norm] at hValSpec
  have hPsiSpec := hPsi (psiCanonicity_assumptions_of_commit COut input_var AM env
    (by simpa [MPCIn, circuit_norm] using hh1_bool)
    (by simpa [MPCIn, circuit_norm] using hg0_bool)
    (by simpa [MPCIn, circuit_norm] using hg_decomp)
    hg1_lt hh0_lt hg_lt hz1g hz13g)
  rw [show PsiCanonicity.circuit.Spec = PsiCanonicity.Spec from rfl] at hPsiSpec
  simp only [PsiCanonicity.Spec, circuit_norm] at hPsiSpec
  have hMessageFactsVar : MessageCellFacts
      (eval env input_var.gd) (eval env input_var.pkd)
      (eval env input_var.value) (eval env input_var.rho)
      (eval env input_var.psi) (eval env AM) := by
    simp only [MessageCellFacts]
    refine ⟨by simpa [circuit_norm] using hGdSpec.1,
      by simpa [circuit_norm] using hGdSpec.2.1,
      by simpa [circuit_norm] using hGdSpec.2.2,
      by simpa [circuit_norm] using hgdY_low,
      by simpa [circuit_norm] using hPkdSpec.1,
      by simpa [circuit_norm] using hPkdSpec.2.1,
      by simpa [circuit_norm] using hPkdSpec.2.2,
      by simpa [circuit_norm] using hpkdY_low,
      by simpa [circuit_norm] using hValSpec.2.1,
      by simpa [circuit_norm] using hValSpec.2.2.2,
      by simpa [circuit_norm] using hRhoSpec.1,
      by simpa [circuit_norm] using hRhoSpec.2.1,
      by simpa [circuit_norm] using hRhoSpec.2.2,
      by simpa [circuit_norm] using hPsiSpec.1,
      by simpa [circuit_norm] using hPsiSpec.2.2.1,
      by simpa [circuit_norm] using hPsiSpec.2.2.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [MPCIn, circuit_norm] using hb_decomp
    · rw [show (eval env AM).d =
          (eval env AM).d0 + (eval env AM).d1 * 2 + (eval env AM).d2 * 4 +
            Expression.eval env
              ((HVec.get (Chain.zLengths messagePieceRounds) COut.zs ⟨3, by decide⟩)[1]) *
              1024 by
        simpa [MPCIn, circuit_norm] using hd_decomp]
      rw [show Expression.eval env
          ((HVec.get (Chain.zLengths messagePieceRounds) COut.zs ⟨3, by decide⟩)[1]) =
          ((bitrange (ZMod.val (eval env input_var.value)) 8 50 : ℕ) : Fp) by
        simpa [circuit_norm] using cell_eq_of_val hValSpec.2.2.1]
      ring
    · simpa [MPCIn, circuit_norm] using he_decomp
    · rw [show (eval env AM).g =
          (eval env AM).g0 + (eval env AM).g1 * 2 +
            Expression.eval env
              ((HVec.get (Chain.zLengths messagePieceRounds) COut.zs ⟨6, by decide⟩)[1]) *
              1024 by
        simpa [MPCIn, circuit_norm] using hg_decomp]
      rw [show Expression.eval env
          ((HVec.get (Chain.zLengths messagePieceRounds) COut.zs ⟨6, by decide⟩)[1]) =
          ((bitrange (ZMod.val (eval env input_var.psi)) 9 240 : ℕ) : Fp) by
        simpa [circuit_norm] using cell_eq_of_val hPsiSpec.2.1]
      ring
    · simpa [MPCIn, circuit_norm] using hh_decomp
  have hMessageFacts : MessageCellFacts input.gd input.pkd input.value input.rho input.psi
      (eval env AM) := by
    rw [← h_input]
    simpa [circuit_norm] using hMessageFactsVar
  have hvalue : (show Fp from input.value).val < 2 ^ 64 := by
    rw [← h_input]
    simpa [circuit_norm] using hValSpec.1
  have hPieceValues :=
    noteCommitPieceValues_of_messageCellFacts hvalue hMessageFacts
  have hPCMessage : Chain.PieceChunks messagePieceRounds (messagePieces (eval env AM)) chunks := by
    simpa [messagePieces, messagePieceRounds] using hPC
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hgdX, hgdY, hpkdX, hpkdY, hv, hrho, hpsi⟩ :=
    hPieceValues
  have hchunks : chunks =
      (noteScalars input.gd input.pkd input.value input.rho input.psi).chunks := by
    exact pieceChunks_eq_noteCommitChunks_of_indexed_piece_values hPCMessage hA hB hC hD hE hF hG hH
      hgdX hgdY hpkdX hpkdY hv hrho hpsi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Spec, NoteCommitRelation]
    refine ⟨rcm, ?_⟩
    intro B hBhash
    have hHashB := hHash B (by simpa [hchunks] using hBhash)
    have hCOutPoint :
        COut.point = (varFromOffset Point (i₀ + 28 + 1400) : Var Point Fp) := by
      rw [hCOutdef]
      rfl
    rw [← hCOutPoint]
    simpa only [Point.eval_eq, circuit_norm] using hHashB
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (by
      rw [GeneralFormalCircuit.WithHint.toSubcircuit_assumptions]
      simpa [YCanonicity.Assumptions, circuit_norm] using hb2_bool)
  · exact Or.inr (by
      rw [GeneralFormalCircuit.WithHint.toSubcircuit_assumptions]
      simpa [YCanonicity.Assumptions, circuit_norm] using hd1_bool)
  · exact Or.inr (by
      rw [show GdCanonicity.circuit.Assumptions = GdCanonicity.Assumptions from rfl]
      simp only [GdCanonicity.Assumptions, circuit_norm]
      refine ⟨hb1_bool, ?_, ?_, ?_⟩
      · simpa [circuit_norm] using ha_lt
      · simpa [circuit_norm] using hb0_lt
      · exact (CircuitType.eval_expr env _).symm.trans
          ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) COut.zs ⟨0, by decide⟩ 13
            (by decide)).trans (by simpa [circuit_norm] using hz13a)))
  · exact Or.inr (by
      rw [show PkdCanonicity.circuit.Assumptions = PkdCanonicity.Assumptions from rfl]
      simp only [PkdCanonicity.Assumptions, circuit_norm]
      refine ⟨hd0_bool, ?_, ?_, ?_⟩
      · simpa [circuit_norm] using hc_lt
      · simpa [circuit_norm] using hb3_lt
      · exact (CircuitType.eval_expr env _).symm.trans
          ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) COut.zs ⟨2, by decide⟩ 13
            (by decide)).trans (by simpa [circuit_norm] using hz13c)))
  · exact Or.inr
      (valueCanonicity_assumptions_of_commit COut input_var AM env hd2_lt he0_lt hd_lt hz1d)
  · exact Or.inr (by
      rw [show RhoCanonicity.circuit.Assumptions = RhoCanonicity.Assumptions from rfl]
      simp only [RhoCanonicity.Assumptions, circuit_norm]
      refine ⟨hg0_bool, ?_, ?_, ?_⟩
      · simpa [circuit_norm] using hf_lt
      · simpa [circuit_norm] using he1_lt
      · exact (CircuitType.eval_expr env _).symm.trans
          ((HVec.eval_getElem env (Chain.zLengths messagePieceRounds) COut.zs ⟨5, by decide⟩ 13
            (by decide)).trans (by simpa [circuit_norm] using hz13f)))
  · exact ⟨Or.inr (psiCanonicity_assumptions_of_commit COut input_var AM env
        (by simpa [MPCIn, circuit_norm] using hh1_bool)
        (by simpa [MPCIn, circuit_norm] using hg0_bool)
        (by simpa [MPCIn, circuit_norm] using hg_decomp)
        hg1_lt hh0_lt hg_lt hz1g hz13g), trivial⟩

/-- A message piece `P = lo + slice·2^10` whose low part is below the shift has its
honest round-1 running-sum cell `P.val / 2^10` equal to the `slice` value. -/
theorem cell_div_pow10_eq {P lo : Fp} {slice M : ℕ}
    (hdec : P = lo + ((slice : ℕ) : Fp) * 1024)
    (hlo : lo.val < 1024) (hslice : slice < 2 ^ M) (hM : M ≤ 244) :
    P.val / 2 ^ 10 = slice := by
  have hcard : lo.val + slice * 1024 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    have hshift : slice * 1024 < 2 ^ (M + 10) := by
      calc slice * 1024 < 2 ^ M * 1024 := by gcongr
        _ = 2 ^ (M + 10) := by rw [pow_add]; norm_num
    have hle : (2 : ℕ) ^ (M + 10) ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 254 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    omega
  have hP : P = ((lo.val + slice * 1024 : ℕ) : Fp) := by
    rw [hdec]; push_cast [ZMod.natCast_zmod_val]; ring
  rw [hP, ZMod.val_natCast_of_lt hcard]
  omega

/-- Low-part bound for the `d`-piece decomposition (`d0 + d1·2 + d2·4 < 2^10`). -/
theorem lo3_lt {a b c : Fp} (ha : a.val < 2) (hb : b.val < 2) (hc : c.val < 2 ^ 8) :
    (a + b * 2 + c * 4 : Fp).val < 1024 := by
  have hcast : (a + b * 2 + c * 4 : Fp) = ((a.val + b.val * 2 + c.val * 4 : ℕ) : Fp) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [hcast, ZMod.val_natCast_of_lt (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]; omega)]
  omega

/-- Low-part bound for the `g`-piece decomposition (`g0 + g1·2 < 2^10`). -/
theorem lo2_lt {a b : Fp} (ha : a.val < 2) (hb : b.val < 2 ^ 9) :
    (a + b * 2 : Fp).val < 1024 := by
  have hcast : (a + b * 2 : Fp) = ((a.val + b.val * 2 : ℕ) : Fp) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [hcast, ZMod.val_natCast_of_lt (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]; omega)]
  omega

/-- The psi-canonicity obligation, factored out of `completeness`. From the honest `g`-piece
decomposition (`g = g0 + g1·2 + bitrange(psi,9,240)·2^10`, `g0` a bit, `g1` the 9-bit base)
and the round-1/round-13 running-sum cells (`z1g = g.val/2^10`, `z13g = g.val/2^130`), the
outer `PsiCanonicity` Assumptions and Spec hold for the canonical psi slices. -/
theorem psi_canonicity_obligation {psi g0 g1 h0 h1 g z1g z13g : Fp}
    (hg_dec : g = g0 + g1 * 2 + ((bitrange psi.val 9 240 : ℕ) : Fp) * 1024)
    (hg0 : g0.val < 2) (hg1 : g1.val = bitrange psi.val 0 9)
    (hh0 : h0.val = bitrange psi.val 249 5) (hh1 : h1.val = bitrange psi.val 254 1)
    (hz1g : z1g = ((g.val / 2 ^ 10 : ℕ) : Fp))
    (hz13g : z13g = ((g.val / 2 ^ 130 : ℕ) : Fp)) :
    PsiCanonicity.Assumptions
        { psi := psi, h0 := h0, g1 := g1, h1 := h1, g2 := z1g, z13G := z13g } ∧
      PsiCanonicity.Spec
        { psi := psi, h0 := h0, g1 := g1, h1 := h1, g2 := z1g, z13G := z13g } := by
  have hg1_lt : g1.val < 2 ^ 9 := hg1 ▸ bitrange_lt _ _ _
  have hgdiv : g.val / 2 ^ 10 = bitrange psi.val 9 240 :=
    cell_div_pow10_eq hg_dec (lo2_lt hg0 hg1_lt) (bitrange_lt _ _ _) (by norm_num)
  have hz1g_val : z1g.val = bitrange psi.val 9 240 := by
    rw [hz1g, ZMod.val_natCast_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt _)), hgdiv]
  simp only [PsiCanonicity.Assumptions, PsiCanonicity.Spec]
  refine ⟨⟨?_, hg1_lt, ?_, ?_, ?_⟩, hg1, hz1g_val, hh0, hh1⟩
  · rw [cell_eq_of_val hh1]; exact bitrange_one_isBool _ _
  · rw [hz1g_val]; exact bitrange_lt _ _ _
  · rw [hh0]; exact bitrange_lt _ _ _
  · rw [hz13g]; congr 1
    rw [hz1g_val, show (2 : ℕ) ^ 130 = 2 ^ 10 * 2 ^ 120 from by norm_num,
      ← Nat.div_div_eq_div_mul, hgdiv,
      show (2 : ℕ) ^ 129 = 2 ^ 9 * 2 ^ 120 from by norm_num, ← Nat.div_div_eq_div_mul]
    congr 1
    omega

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q) (ProverSpec G Q R) := by
  circuit_proof_start [AssignMessagePieces.circuit, Commit.circuit, MessagePieceChecks.circuit,
    GdCanonicity.circuit, PkdCanonicity.circuit, ValueCanonicity.circuit,
    RhoCanonicity.circuit, PsiCanonicity.circuit]
  obtain ⟨⟨-, hAMProver⟩, hComImpl, -⟩ := h_env
  obtain ⟨-, -, hvalue, hrcm, hHashEx⟩ := h_assumptions
  have hMCF := hAMProver
  simp only [AssignMessagePieces.ProverSpec, circuit_norm] at hMCF
  have hPB := pieceBounds_of_cellFacts hMCF
  have hHonestEq := honestChunks_eq_noteCommitChunks_of_cellFacts hMCF hvalue
  have hCPA : (Commit.circuit G Q hQ R).ProverAssumptions
      { pieces := ?pcs, r := input_rcm } env.data env.hint := by
    refine ⟨by simpa [messagePieces, messagePieceRounds] using hPB, ?_, hrcm⟩
    obtain ⟨B, hB⟩ := hHashEx
    refine ⟨B, ?_⟩
    have hHonestEqCommit :
        Chain.honestChunks (24 :: messagePieceTailRounds)
            (show ProverValue Commit.Input Fp from {
              pieces := ?pcs,
              r := input_rcm
            }).pieces =
          noteCommitChunks (show Fp from input_gd.x).val ((show Fp from input_gd.y).val % 2)
            (show Fp from input_pkd.x).val ((show Fp from input_pkd.y).val % 2)
            (show Fp from input_value).val (show Fp from input_rho).val
            (show Fp from input_psi).val := by
      simpa only [messagePieces, messagePieceRounds, messagePieceTailRounds] using hHonestEq
    rw [hHonestEqCommit]
    exact hB
  obtain ⟨hComSpec, hZsHonest, hHashHonest⟩ := hComImpl hCPA
  have hPC := Chain.pieceChunks_honestChunks _ _ hPB
  -- piece bounds
  have ha_lt := pieceChunks_val_lt messagePieceRounds _ _ ⟨0, by decide⟩ hPC (by decide)
  have hc_lt := pieceChunks_val_lt messagePieceRounds _ _ ⟨2, by decide⟩ hPC (by decide)
  have hd_lt := pieceChunks_val_lt messagePieceRounds _ _ ⟨3, by decide⟩ hPC (by decide)
  have hf_lt := pieceChunks_val_lt messagePieceRounds _ _ ⟨5, by decide⟩ hPC (by decide)
  have hg_lt := pieceChunks_val_lt messagePieceRounds _ _ ⟨6, by decide⟩ hPC (by decide)
  simp only [messagePieces, messagePieceRounds, K, circuit_norm]
    at ha_lt hc_lt hd_lt hf_lt hg_lt
  -- honest running-sum z-cells
  have hz13a := zsHonest_cell messagePieceRounds _ _ ⟨0, by decide⟩ hZsHonest (r := 13) (by decide)
  have hz13c := zsHonest_cell messagePieceRounds _ _ ⟨2, by decide⟩ hZsHonest (r := 13) (by decide)
  have hz1d := zsHonest_cell messagePieceRounds _ _ ⟨3, by decide⟩ hZsHonest (r := 1) (by decide)
  have hz13f := zsHonest_cell messagePieceRounds _ _ ⟨5, by decide⟩ hZsHonest (r := 13) (by decide)
  have hz1g := zsHonest_cell messagePieceRounds _ _ ⟨6, by decide⟩ hZsHonest (r := 1) (by decide)
  have hz13g := zsHonest_cell messagePieceRounds _ _ ⟨6, by decide⟩ hZsHonest (r := 13) (by decide)
  simp only [messagePieceRounds, K, circuit_norm]
    at hz13a hz13c hz1d hz13f hz1g hz13g
  -- cell facts
  obtain ⟨ha_v, hb0_v, hb1_v, hb2_low, hb3_v, hc_v, hd0_v, hd1_low, hd2_v, he0_v, he1_v, hf_v,
    hg0_v, hg1_v, hh0_v, hh1_v, hb_dec, hd_dec, he_dec, hg_dec, hh_dec⟩ := hMCF
  dsimp only [] at ha_v hb0_v hb1_v hb2_low hb3_v hc_v hd0_v hd1_low hd2_v he0_v he1_v hf_v hg0_v hg1_v hh0_v hh1_v hb_dec hd_dec he_dec hg_dec hh_dec
  refine ⟨⟨?cpa, ?mpc, ?y1, ?y2, ?gd, ?pkd, ?val, ?rho, ?psi⟩, ?rel⟩
  case cpa => exact hCPA
  case gd =>
    refine ⟨?_, ?_⟩
    · simp only [GdCanonicity.Assumptions, circuit_norm]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [cell_eq_of_val hb1_v]; exact bitrange_one_isBool _ _
      · simpa using ha_lt
      · rw [hb0_v]; exact bitrange_lt _ _ _
      · exact (CircuitType.eval_expr env.toEnvironment _).symm.trans
          ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨0, by decide⟩ 13
            (by decide)).trans (by simpa [circuit_norm] using hz13a))
    · simp only [GdCanonicity.Spec, circuit_norm]
      simp only [← h_input, circuit_norm] at ha_v hb0_v hb1_v
      exact ⟨ha_v, hb0_v, hb1_v⟩
  case pkd =>
    refine ⟨?_, ?_⟩
    · simp only [PkdCanonicity.Assumptions, circuit_norm]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [cell_eq_of_val hd0_v]; exact bitrange_one_isBool _ _
      · simpa using hc_lt
      · rw [hb3_v]; exact bitrange_lt _ _ _
      · exact (CircuitType.eval_expr env.toEnvironment _).symm.trans
          ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨2, by decide⟩ 13
            (by decide)).trans (by simpa [circuit_norm] using hz13c))
    · simp only [PkdCanonicity.Spec, circuit_norm]
      simp only [← h_input, circuit_norm] at hb3_v hc_v hd0_v
      exact ⟨hb3_v, hc_v, hd0_v⟩
  case rho =>
    refine ⟨?_, ?_⟩
    · simp only [RhoCanonicity.Assumptions, circuit_norm]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [cell_eq_of_val hg0_v]; exact bitrange_one_isBool _ _
      · simpa using hf_lt
      · rw [he1_v]; exact bitrange_lt _ _ _
      · exact (CircuitType.eval_expr env.toEnvironment _).symm.trans
          ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨5, by decide⟩ 13
            (by decide)).trans (by simpa [circuit_norm] using hz13f))
    · simp only [RhoCanonicity.Spec, circuit_norm]
      exact ⟨he1_v, hf_v, hg0_v⟩
  case y1 =>
    simp only [YCanonicity.circuit, YCanonicity.ProverAssumptions, circuit_norm]
    simpa [← h_input, circuit_norm] using hb2_low
  case y2 =>
    simp only [YCanonicity.circuit, YCanonicity.ProverAssumptions, circuit_norm]
    simpa [← h_input, circuit_norm] using hd1_low
  case rel =>
    intro B hBhash
    have hHashB := hHashHonest B (by
      simp only [messagePieces, messagePieceRounds, messagePieceTailRounds] at hHonestEq ⊢
      rw [hHonestEq]; exact hBhash)
    simpa only [circuit_norm] using hHashB
  case val =>
    refine ⟨?_, ?_⟩
    · simp only [ValueCanonicity.Assumptions, ValueCanonicity.Gate.Assumptions,
        circuit_norm]
      refine ⟨by rw [hd2_v]; exact bitrange_lt _ _ _, ?_, by rw [he0_v]; exact bitrange_lt _ _ _⟩
      change (Expression.eval env.toEnvironment
        ((HVec.get (Chain.zLengths messagePieceRounds) _ ⟨3, by decide⟩)[1])).val < 2 ^ 50
      rw [(CircuitType.eval_expr env.toEnvironment _).symm.trans
        ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨3, by decide⟩ 1
          (by decide)).trans (by simpa [circuit_norm] using hz1d)), ZMod.val_natCast_of_lt]
      · refine Nat.div_lt_of_lt_mul ?_
        simpa [← pow_add] using hd_lt
      · exact lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt _)
    · simp only [ValueCanonicity.Spec, ValueCanonicity.Gate.Spec, circuit_norm]
      refine ⟨hvalue, hd2_v, ?_, he0_v⟩
      change (Expression.eval env.toEnvironment
        ((HVec.get (Chain.zLengths messagePieceRounds) _ ⟨3, by decide⟩)[1])).val
          = bitrange (ZMod.val (show Fp from input_value)) 8 50
      rw [(CircuitType.eval_expr env.toEnvironment _).symm.trans
        ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨3, by decide⟩ 1
          (by decide)).trans (by simpa [circuit_norm] using hz1d)), ZMod.val_natCast_of_lt]
      · exact cell_div_pow10_eq hd_dec
          (lo3_lt (by rw [hd0_v]; exact bitrange_lt _ _ _)
            (isBool_of_isLowBit hd1_low).val_lt_two (by rw [hd2_v]; exact bitrange_lt _ _ _))
          (bitrange_lt _ _ _) (by norm_num)
      · exact lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt _)
  case psi =>
    exact psi_canonicity_obligation hg_dec (by rw [hg0_v]; exact bitrange_lt _ _ _)
      hg1_v hh0_v hh1_v
      ((CircuitType.eval_expr env.toEnvironment _).symm.trans
        ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨6, by decide⟩ 1
          (by decide)).trans (by simpa [circuit_norm] using hz1g)))
      ((CircuitType.eval_expr env.toEnvironment _).symm.trans
        ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨6, by decide⟩ 13
          (by decide)).trans (by simpa [circuit_norm] using hz13g)))
  case mpc =>
    simp only [MessagePieceChecks.Spec, circuit_norm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cell_eq_of_val hb1_v]; exact bitrange_one_isBool _ _
    · exact isBool_of_isLowBit hb2_low
    · exact hb_dec
    · rw [cell_eq_of_val hd0_v]; exact bitrange_one_isBool _ _
    · exact isBool_of_isLowBit hd1_low
    · rw [hd_dec, add_right_inj, mul_eq_mul_right_iff]
      refine Or.inl ?_
      exact (((CircuitType.eval_expr env.toEnvironment _).symm.trans
        ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨3, by decide⟩ 1
          (by decide)).trans (by simpa [circuit_norm] using hz1d))).trans
        (congrArg Nat.cast (cell_div_pow10_eq hd_dec
          (lo3_lt (by rw [hd0_v]; exact bitrange_lt _ _ _)
            (isBool_of_isLowBit hd1_low).val_lt_two (by rw [hd2_v]; exact bitrange_lt _ _ _))
          (bitrange_lt _ _ _) (by norm_num)))).symm
    · exact he_dec
    · rw [cell_eq_of_val hg0_v]; exact bitrange_one_isBool _ _
    · rw [hg_dec, add_right_inj, mul_eq_mul_right_iff]
      refine Or.inl ?_
      exact (((CircuitType.eval_expr env.toEnvironment _).symm.trans
        ((HVec.eval_getElem env.toEnvironment (Chain.zLengths messagePieceRounds) _ ⟨6, by decide⟩ 1
          (by decide)).trans (by simpa [circuit_norm] using hz1g))).trans
        (congrArg Nat.cast (cell_div_pow10_eq hg_dec
          (lo2_lt (by rw [hg0_v]; exact bitrange_lt _ _ _) (by rw [hg1_v]; exact bitrange_lt _ _ _))
          (bitrange_lt _ _ _) (by norm_num)))).symm
    · rw [cell_eq_of_val hh1_v]; exact bitrange_one_isBool _ _
    · exact hh_dec
def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
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
