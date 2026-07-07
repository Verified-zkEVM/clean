import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Specs.Bitrange
import Clean.Orchard.Sinsemilla.HashToPoint
import Clean.Orchard.Ecc

/-!
# `commit_ivk` message-piece chunk bridge

Port of the `note_commit` message-piece chunk bridge (`Clean.Orchard.Action.NoteCommit`)
to the simpler `commit_ivk` message `ak + 2^255 * nk` (2 scalar fields, 4 Sinsemilla
pieces with word counts `25, 1, 24, 1`).
-/

namespace Orchard.Action.CommitIvk

open Orchard.Specs (bitrange bitrange_lt bitrange_add bitrange_mod)
open Orchard.Specs (K)
open Orchard.Specs.Sinsemilla (chunksOf chunksOf_mod chunksOf_eq_of_mod_eq commitIvkMessage commitIvkChunks
  commitIvkChunks_tiling sum_head_shift sum_digits_lt digit_of_sum
  chunksOf_eq_map_of_sum chunksOf_eq_map_of_cast_sum chunksOf_one_eq_singleton)

section
set_option exponentiation.threshold 900

theorem commitIvkChunks_segment_a (ak nk : ℕ) :
    chunksOf (commitIvkMessage ak nk) 25 = chunksOf ak 25 :=
  chunksOf_eq_of_mod_eq (by
    unfold commitIvkMessage
    rw [show ak + 2 ^ 255 * nk = ak + 2 ^ (K * 25) * (2 ^ 5 * nk) by norm_num [K]; ring_nf]
    apply Nat.add_mul_mod_self_left)

theorem commitIvkChunks_segment_b_word (ak nk : ℕ) (hak : ak < 2 ^ 255) :
    bitrange (commitIvkMessage ak nk / 2 ^ 250) 0 K
      = bitrange ak 250 4 + bitrange ak 254 1 * 16 + bitrange nk 0 5 * 32 := by
  simp only [bitrange]
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold commitIvkMessage
  norm_num at *
  omega

theorem commitIvkChunks_segment_b (ak nk : ℕ) (hak : ak < 2 ^ 255) :
    chunksOf (commitIvkMessage ak nk / 2 ^ 250) 1
      = [bitrange ak 250 4 + bitrange ak 254 1 * 16 + bitrange nk 0 5 * 32] := by
  unfold chunksOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
  rw [commitIvkChunks_segment_b_word ak nk hak]

theorem commitIvkChunks_segment_c_mod (ak nk : ℕ) (hak : ak < 2 ^ 255) :
    commitIvkMessage ak nk / 2 ^ 260 % 2 ^ (K * 24) = (nk / 2 ^ 5) % 2 ^ (K * 24) := by
  rw [show 2 ^ (K * 24) = 2 ^ 240 by norm_num [K]]
  unfold commitIvkMessage
  norm_num at *
  omega

theorem commitIvkChunks_segment_c (ak nk : ℕ) (hak : ak < 2 ^ 255) :
    chunksOf (commitIvkMessage ak nk / 2 ^ 260) 24 = chunksOf (nk / 2 ^ 5) 24 :=
  chunksOf_eq_of_mod_eq (commitIvkChunks_segment_c_mod ak nk hak)

theorem commitIvkChunks_segment_d_word (ak nk : ℕ) (hak : ak < 2 ^ 255) (hnk : nk < 2 ^ 255) :
    bitrange (commitIvkMessage ak nk / 2 ^ 500) 0 K
      = bitrange nk 245 9 + bitrange nk 254 1 * 512 := by
  simp only [bitrange]
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold commitIvkMessage
  norm_num at *
  omega

theorem commitIvkChunks_segment_d (ak nk : ℕ) (hak : ak < 2 ^ 255) (hnk : nk < 2 ^ 255) :
    chunksOf (commitIvkMessage ak nk / 2 ^ 500) 1 =
      [bitrange nk 245 9 + bitrange nk 254 1 * 512] := by
  unfold chunksOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
  rw [commitIvkChunks_segment_d_word ak nk hak hnk]

theorem commitIvkChunks_tiling_segments (ak nk : ℕ) (hak : ak < 2 ^ 255) (hnk : nk < 2 ^ 255) :
    commitIvkChunks ak nk =
      chunksOf ak 25
      ++ [bitrange ak 250 4 + bitrange ak 254 1 * 16 + bitrange nk 0 5 * 32]
      ++ chunksOf (nk / 2 ^ 5) 24
      ++ [bitrange nk 245 9 + bitrange nk 254 1 * 512] := by
  rw [commitIvkChunks_tiling]
  rw [commitIvkChunks_segment_a]
  rw [commitIvkChunks_segment_b _ _ hak]
  rw [commitIvkChunks_segment_c _ _ hak]
  rw [commitIvkChunks_segment_d _ _ hak hnk]

end

theorem commitIvkChunks_eq_of_piece_digit_sums {msA msB msC msD : ℕ → ℕ} {ak nk : ℕ}
    (hmsA : ∀ r, msA r < 2 ^ K) (hmsB : ∀ r, msB r < 2 ^ K)
    (hmsC : ∀ r, msC r < 2 ^ K) (hmsD : ∀ r, msD r < 2 ^ K)
    (hA : ((ak % 2 ^ (K * 25) : ℕ) : Fp) = ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp))
    (hB : ((bitrange ak 250 4 + bitrange ak 254 1 * 16 + bitrange nk 0 5 * 32 : ℕ) : Fp)
            = ((∑ r ∈ Finset.range 1, msB r * 2 ^ (K * r) : ℕ) : Fp))
    (hC : (((nk / 2 ^ 5) % 2 ^ (K * 24) : ℕ) : Fp) = ((∑ r ∈ Finset.range 24, msC r * 2 ^ (K * r) : ℕ) : Fp))
    (hD : ((bitrange nk 245 9 + bitrange nk 254 1 * 512 : ℕ) : Fp)
            = ((∑ r ∈ Finset.range 1, msD r * 2 ^ (K * r) : ℕ) : Fp))
    (hak : ak < 2 ^ 255) (hnk : nk < 2 ^ 255) :
    (List.range 25).map msA ++ (List.range 1).map msB
      ++ (List.range 24).map msC ++ (List.range 1).map msD
      = commitIvkChunks ak nk := by
  have hBValueLt : bitrange ak 250 4 + bitrange ak 254 1 * 16 + bitrange nk 0 5 * 32 < 2 ^ K := by
    have hb0 : bitrange ak 250 4 < 16 := by have := bitrange_lt ak 250 4; omega
    have hb1 : bitrange ak 254 1 < 2 := by have := bitrange_lt ak 254 1; omega
    have hb2 : bitrange nk 0 5 < 2 ^ 5 := bitrange_lt _ _ _
    norm_num [K]
    omega
  have hDValueLt : bitrange nk 245 9 + bitrange nk 254 1 * 512 < 2 ^ K := by
    have hd0 : bitrange nk 245 9 < 2 ^ 9 := bitrange_lt _ _ _
    have hd1 : bitrange nk 254 1 < 2 := by have := bitrange_lt nk 254 1; omega
    norm_num [K]
    omega
  have hChunksA_low := chunksOf_eq_map_of_cast_sum hmsA hA
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsA 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksA : chunksOf ak 25 = (List.range 25).map msA := by
    rw [← chunksOf_mod ak 25]
    exact hChunksA_low
  have hChunksB := chunksOf_eq_map_of_cast_sum hmsB hB
    (lt_trans hBValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsB 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC_low := chunksOf_eq_map_of_cast_sum hmsC hC
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 24))) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsC 24) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC : chunksOf (nk / 2 ^ 5) 24 = (List.range 24).map msC := by
    rw [← chunksOf_mod (nk / 2 ^ 5) 24]
    exact hChunksC_low
  have hChunksD := chunksOf_eq_map_of_cast_sum hmsD hD
    (lt_trans hDValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsD 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  rw [← hChunksA, ← hChunksB, ← hChunksC, ← hChunksD]
  rw [chunksOf_one_eq_singleton hBValueLt, chunksOf_one_eq_singleton hDValueLt]
  exact (commitIvkChunks_tiling_segments ak nk hak hnk).symm

theorem pieceChunks_commitIvkRounds_chunks
    {pieces : Vector Fp 4} {chunks : List ℕ}
    (h : Orchard.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0] pieces chunks) :
    ∃ msA msB msC msD : ℕ → ℕ,
      (∀ r, msA r < 2 ^ K) ∧ (∀ r, msB r < 2 ^ K) ∧ (∀ r, msC r < 2 ^ K) ∧ (∀ r, msD r < 2 ^ K) ∧
      chunks = (List.range 25).map msA ++ (List.range 1).map msB
        ++ (List.range 24).map msC ++ (List.range 1).map msD := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at h
  obtain ⟨msA, hA, _hpA, tailA, rfl, h⟩ := h
  obtain ⟨msB, hB, _hpB, tailB, rfl, h⟩ := h
  obtain ⟨msC, hC, _hpC, tailC, rfl, h⟩ := h
  obtain ⟨msD, hD, _hpD, tailD, rfl, h⟩ := h
  subst tailD
  exact ⟨msA, msB, msC, msD, hA, hB, hC, hD,
    by simp only [List.append_nil, List.append_assoc]⟩

theorem pieceChunks_eq_commitIvkChunks_of_indexed_piece_values
    {pieces : Vector Fp 4} {chunks : List ℕ} {ak nk : ℕ}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0] pieces chunks)
    (hA : pieces[0] = ((ak % 2 ^ (K * 25) : ℕ) : Fp))
    (hB : pieces[1] = ((bitrange ak 250 4 + bitrange ak 254 1 * 16 + bitrange nk 0 5 * 32 : ℕ) : Fp))
    (hC : pieces[2] = (((nk / 2 ^ 5) % 2 ^ (K * 24) : ℕ) : Fp))
    (hD : pieces[3] = ((bitrange nk 245 9 + bitrange nk 254 1 * 512 : ℕ) : Fp))
    (hak : ak < 2 ^ 255) (hnk : nk < 2 ^ 255) :
    chunks = commitIvkChunks ak nk := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at hPC
  obtain ⟨msA, hmsA, hpA, tailA, rfl, hPC⟩ := hPC
  obtain ⟨msB, hmsB, hpB, tailB, rfl, hPC⟩ := hPC
  obtain ⟨msC, hmsC, hpC, tailC, rfl, hPC⟩ := hPC
  obtain ⟨msD, hmsD, hpD, tailD, rfl, hPC⟩ := hPC
  subst tailD
  have ht1 : pieces.tail[0] = pieces[1] :=
    Vector.getElem_tail (v := pieces) (i := 0) (hi := by decide)
  have ht2 : pieces.tail.tail[0] = pieces[2] := by
    exact (Vector.getElem_tail (v := pieces.tail) (i := 0) (hi := by decide)).trans
      (Vector.getElem_tail (v := pieces) (i := 1) (hi := by decide))
  have ht3 : pieces.tail.tail.tail[0] = pieces[3] := by
    exact (Vector.getElem_tail (v := pieces.tail.tail) (i := 0) (hi := by decide)).trans
      ((Vector.getElem_tail (v := pieces.tail) (i := 1) (hi := by decide)).trans
        (Vector.getElem_tail (v := pieces) (i := 2) (hi := by decide)))
  exact commitIvkChunks_eq_of_piece_digit_sums hmsA hmsB hmsC hmsD
    (hA.symm.trans hpA)
    ((ht1.trans hB).symm.trans hpB)
    ((ht2.trans hC).symm.trans hpC)
    ((ht3.trans hD).symm.trans hpD)
    hak hnk

/-- Completeness-direction identification: the honest chunk values of pieces that decode
`ak`/`nk` are exactly `commitIvkChunks ak nk`. Reuses the soundness bridge via
`pieceChunks_honestChunks` (the honest chunks always realize `PieceChunks` when the pieces
are in range). -/
theorem honestChunks_eq_commitIvkChunks
    {pieces : Vector Fp 4} {ak nk : ℕ}
    (hbounds : Orchard.Sinsemilla.Chain.PieceBounds [24, 0, 23, 0] pieces)
    (hA : pieces[0] = ((ak % 2 ^ (K * 25) : ℕ) : Fp))
    (hB : pieces[1] = ((bitrange ak 250 4 + bitrange ak 254 1 * 16 + bitrange nk 0 5 * 32 : ℕ) : Fp))
    (hC : pieces[2] = (((nk / 2 ^ 5) % 2 ^ (K * 24) : ℕ) : Fp))
    (hD : pieces[3] = ((bitrange nk 245 9 + bitrange nk 254 1 * 512 : ℕ) : Fp))
    (hak : ak < 2 ^ 255) (hnk : nk < 2 ^ 255) :
    Orchard.Sinsemilla.Chain.honestChunks [24, 0, 23, 0] pieces = commitIvkChunks ak nk :=
  pieceChunks_eq_commitIvkChunks_of_indexed_piece_values
    (Orchard.Sinsemilla.Chain.pieceChunks_honestChunks [24, 0, 23, 0] pieces hbounds)
    hA hB hC hD hak hnk

end Orchard.Action.CommitIvk
