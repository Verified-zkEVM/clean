import Clean.Orchard.NoteCommit
import Clean.Orchard.Sinsemilla.Domain
import Clean.Orchard.Utilities

/-!
# `gadgets::note_commit` synthesis-level entry

Port of `orchard@0.14.0/src/circuit/note_commit.rs` `gadgets::note_commit` and its
synthesis helpers (`canon_bitshift_130`, `pkd_x_canonicity`, `rho_canonicity`,
`psi_canonicity`, `y_canonicity`, the `Decompose*::decompose` message-piece builders).

This lives in its own module — separate from `Clean.Orchard.NoteCommit` (the custom-gate
`FormalAssertion`s) — because `NoteCommit.lean` is a low-level dependency of
`Ecc.ScalarMul.Defs`, whereas the gadget needs `Sinsemilla.Domain` (the
`CommitDomain.WithZs` hash that exposes the running sums) which sits above `ScalarMul`.
-/

namespace Orchard.NoteCommit

open Utilities.LookupRangeCheck (K)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Ecc (Point)
open Orchard.Ecc.ScalarMul
open Orchard.Sinsemilla

/-- Telescoping a `K`-bit running-sum chain: `f 0` splits into `K·k` low bits and
`2^(K·k) · f k`. (Mirrors `Mul.OverflowCheck.chain_telescope`.) -/
private theorem chain_telescope (f : ℕ → Ecc.Fp) :
    ∀ k : ℕ,
    (∀ i, i < k → ∃ w : ℕ, w < 2 ^ K ∧ f i = 2 ^ K * f (i + 1) + (w : Ecc.Fp)) →
    ∃ lo : ℕ, lo < 2 ^ (K * k) ∧ f 0 = (lo : Ecc.Fp) + 2 ^ (K * k) * f k
  | 0, _ => ⟨0, by norm_num, by norm_num⟩
  | k + 1, h => by
    obtain ⟨lo, hlt, heq⟩ := chain_telescope f k fun i hi => h i (by omega)
    obtain ⟨w, hw, hstep⟩ := h k (by omega)
    refine ⟨lo + w * 2 ^ (K * k), ?_, ?_⟩
    · have hbound : lo + w * 2 ^ (K * k) < (w + 1) * 2 ^ (K * k) := by
        have := Nat.two_pow_pos (K * k); nlinarith
      have : (w + 1) * 2 ^ (K * k) ≤ 2 ^ K * 2 ^ (K * k) :=
        Nat.mul_le_mul_right _ (by omega)
      have hsplit : (2 : ℕ) ^ (K * (k + 1)) = 2 ^ K * 2 ^ (K * k) := by
        rw [← pow_add]; ring_nf
      omega
    · rw [heq, hstep]; push_cast
      rw [show K * (k + 1) = K * k + K from by ring, pow_add]; ring

private theorem sum_head_shift (Kb m : ℕ) (d : ℕ → ℕ) :
    ∑ j ∈ Finset.range (m + 1), d j * 2 ^ (Kb * j)
      = d 0 + 2 ^ Kb * ∑ j ∈ Finset.range m, d (j + 1) * 2 ^ (Kb * j) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have hstep : ∀ j : ℕ,
      d (j + 1) * 2 ^ (Kb * (j + 1)) = 2 ^ Kb * (d (j + 1) * 2 ^ (Kb * j)) := by
    intro j
    rw [show Kb * (j + 1) = Kb + Kb * j from by ring, pow_add]
    ring
  simp only [hstep, Nat.mul_zero, pow_zero, Nat.mul_one]
  ring

private theorem sum_digits_lt {Kb : ℕ} {d : ℕ → ℕ} (hd : ∀ j, d j < 2 ^ Kb) (n : ℕ) :
    ∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j) < 2 ^ (Kb * n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hterm : d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) ≤ 2 ^ (Kb * (m + 1)) := by
      rw [show Kb * (m + 1) = Kb * m + Kb from by ring, pow_add]
      calc d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) = (d m + 1) * 2 ^ (Kb * m) := by ring
        _ ≤ 2 ^ Kb * 2 ^ (Kb * m) := Nat.mul_le_mul_right _ (hd m)
        _ = 2 ^ (Kb * m) * 2 ^ Kb := by ring
    omega

private theorem sum_digits_split (Kb r n : ℕ) (hr : r ≤ n) (d : ℕ → ℕ) :
    ∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j) =
      (∑ j ∈ Finset.range r, d j * 2 ^ (Kb * j)) +
        2 ^ (Kb * r) *
          ∑ j ∈ Finset.range (n - r), d (r + j) * 2 ^ (Kb * j) := by
  rw [show n = r + (n - r) by omega, Finset.sum_range_add]
  congr 1
  rw [Finset.mul_sum]
  rw [show r + (n - r) - r = n - r by omega]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show Kb * (r + j) = Kb * r + Kb * j by ring, pow_add]
  ring

private theorem digit_of_sum (Kb : ℕ) :
    ∀ (i n : ℕ) (d : ℕ → ℕ), (∀ j, d j < 2 ^ Kb) → i < n →
      (∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j)) / 2 ^ (Kb * i) % 2 ^ Kb = d i := by
  intro i
  induction i with
  | zero =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift, Nat.mul_zero, pow_zero, Nat.div_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0)]
  | succ i ih =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift,
      show Kb * (i + 1) = Kb + Kb * i from by ring, pow_add,
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos Kb),
      Nat.div_eq_of_lt (hd 0), Nat.zero_add]
    exact ih m (fun j => d (j + 1)) (fun j => hd (j + 1)) (by omega)

private theorem pieceWord_eq_of_sum {piece : Ecc.Fp} {n : ℕ} {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    (hpiece : piece =
      ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hcard : (∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) <
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    {i : ℕ} (hi : i < n) :
    Orchard.Sinsemilla.pieceWord piece i = ms i := by
  have hval : piece.val =
      ∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) := by
    rw [hpiece, ZMod.val_natCast_of_lt hcard]
  unfold Orchard.Sinsemilla.pieceWord
  rw [hval]
  exact digit_of_sum K i n ms hms hi

private theorem map_pieceWord_eq_of_sum {piece : Ecc.Fp} {n : ℕ} {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    (hpiece : piece =
      ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hcard : (∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) <
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) :
    (List.range n).map (Orchard.Sinsemilla.pieceWord piece) = (List.range n).map ms := by
  exact List.map_congr_left fun i hi => by
    simp only [List.mem_range] at hi
    exact pieceWord_eq_of_sum hms hpiece hcard hi

private theorem chunksOf_eq_map_of_sum {value n : ℕ} {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    (hvalue : value = ∑ r ∈ Finset.range n, ms r * 2 ^ (K * r)) :
    Orchard.Specs.Sinsemilla.chunksOf value n = (List.range n).map ms := by
  apply List.ext_getElem
  · simp [Orchard.Specs.Sinsemilla.chunksOf]
  intro i hi hi'
  have hin : i < n := by
    simp only [Orchard.Specs.Sinsemilla.chunksOf, List.length_map, List.length_range] at hi
    exact hi
  rw [show (Orchard.Specs.Sinsemilla.chunksOf value n)[i]
      = value / 2 ^ (K * i) % 2 ^ K from by
        simp [Orchard.Specs.Sinsemilla.chunksOf]
        norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [hvalue]
  simp only [List.getElem_map, List.getElem_range]
  exact digit_of_sum K i n ms hms hin

private theorem chunksOf_eq_map_of_field_sum {piece : Ecc.Fp} {value n : ℕ} {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    (hvalue : piece = (value : Ecc.Fp))
    (hpiece : piece =
      ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hvalueCard : value < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hsumCard : (∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) <
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) :
    Orchard.Specs.Sinsemilla.chunksOf value n = (List.range n).map ms := by
  apply chunksOf_eq_map_of_sum hms
  have hcast :
      (value : Ecc.Fp) =
        ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp) :=
    hvalue.symm.trans hpiece
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hvalueCard, ZMod.val_natCast_of_lt hsumCard] at hval
  exact hval

private theorem chunksOf_eq_map_of_cast_sum {value n : ℕ} {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    (hcast :
      (value : Ecc.Fp) =
        ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hvalueCard : value < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hsumCard : (∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) <
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) :
    Orchard.Specs.Sinsemilla.chunksOf value n = (List.range n).map ms := by
  apply chunksOf_eq_map_of_sum hms
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hvalueCard, ZMod.val_natCast_of_lt hsumCard] at hval
  exact hval

private theorem two_pow_K_mul_25_lt_p :
    (2 : ℕ) ^ (K * 25) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
  norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

private theorem two_pow_K_mul_6_lt_p :
    (2 : ℕ) ^ (K * 6) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
  exact lt_trans (by norm_num [K]) two_pow_K_mul_25_lt_p

private theorem two_pow_K_lt_p :
    (2 : ℕ) ^ K < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
  exact lt_trans (by norm_num [K]) two_pow_K_mul_25_lt_p

private theorem natCast_injective_of_lt {a b : ℕ}
    (ha : a < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hb : b < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (h : (a : Ecc.Fp) = (b : Ecc.Fp)) :
    a = b := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv

private def tPNat : ℕ := 45560315531419706090280762371685220353

private theorem isBool_val_lt_two {x : Ecc.Fp} (h : NoteCommit.IsBool x) :
    x.val < 2 := by
  rcases h with h | h
  · rw [h, ZMod.val_zero]
    norm_num
  · rw [h, ZMod.val_one]
    norm_num

private theorem isBool_val_eq_zero_or_one {x : Ecc.Fp} (h : NoteCommit.IsBool x) :
    x.val = 0 ∨ x.val = 1 := by
  rcases h with h | h
  · left
    rw [h, ZMod.val_zero]
  · right
    rw [h, ZMod.val_one]

private theorem decomposeB_value_lt {b b0 b1 b2 b3 : Ecc.Fp}
    (hb0 : b0.val < 2 ^ 4) (hb1 : NoteCommit.IsBool b1)
    (hb2 : NoteCommit.IsBool b2) (hb3 : b3.val < 2 ^ 4)
    (hdec : b = b0 + b1 * 16 + b2 * 32 + b3 * 64) :
    b.val < 2 ^ K := by
  have hb1lt := isBool_val_lt_two hb1
  have hb2lt := isBool_val_lt_two hb2
  let packed := b0.val + b1.val * 16 + b2.val * 32 + b3.val * 64
  have hPackedLt : packed < 2 ^ K := by
    norm_num [K] at hb0 hb3 ⊢
    omega
  have hPackedCard : packed < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD :=
    lt_trans hPackedLt two_pow_K_lt_p
  have hcast : b = (packed : Ecc.Fp) := by
    rw [hdec]
    dsimp only [packed]
    rw [← ZMod.natCast_zmod_val b0, ← ZMod.natCast_zmod_val b1,
      ← ZMod.natCast_zmod_val b2, ← ZMod.natCast_zmod_val b3]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt b0), ZMod.val_natCast_of_lt (ZMod.val_lt b1),
      ZMod.val_natCast_of_lt (ZMod.val_lt b2), ZMod.val_natCast_of_lt (ZMod.val_lt b3)]
  rw [hcast, ZMod.val_natCast_of_lt hPackedCard]
  exact hPackedLt

private theorem decomposeE_value_lt {e e0 e1 : Ecc.Fp}
    (he0 : e0.val < 2 ^ 6) (he1 : e1.val < 2 ^ 4)
    (hdec : e = e0 + e1 * 64) :
    e.val < 2 ^ K := by
  let packed := e0.val + e1.val * 64
  have hPackedLt : packed < 2 ^ K := by
    norm_num [K] at he0 he1 ⊢
    omega
  have hPackedCard : packed < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD :=
    lt_trans hPackedLt two_pow_K_lt_p
  have hcast : e = (packed : Ecc.Fp) := by
    rw [hdec]
    dsimp only [packed]
    rw [← ZMod.natCast_zmod_val e0, ← ZMod.natCast_zmod_val e1]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt e0), ZMod.val_natCast_of_lt (ZMod.val_lt e1)]
  rw [hcast, ZMod.val_natCast_of_lt hPackedCard]
  exact hPackedLt

private theorem decomposeH_value_lt {h h0 h1 : Ecc.Fp}
    (hh0 : h0.val < 2 ^ 5) (hh1 : NoteCommit.IsBool h1)
    (hdec : h = h0 + h1 * 32) :
    h.val < 2 ^ K := by
  have hh1lt := isBool_val_lt_two hh1
  let packed := h0.val + h1.val * 32
  have hPackedLt : packed < 2 ^ K := by
    norm_num [K] at hh0 ⊢
    omega
  have hPackedCard : packed < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD :=
    lt_trans hPackedLt two_pow_K_lt_p
  have hcast : h = (packed : Ecc.Fp) := by
    rw [hdec]
    dsimp only [packed]
    rw [← ZMod.natCast_zmod_val h0, ← ZMod.natCast_zmod_val h1]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt h0), ZMod.val_natCast_of_lt (ZMod.val_lt h1)]
  rw [hcast, ZMod.val_natCast_of_lt hPackedCard]
  exact hPackedLt

private theorem value_from_parts_val_eq {value d2 d3 e0 : Ecc.Fp}
    (hd2 : d2.val < 2 ^ 8) (hd3 : d3.val < 2 ^ (K * 5)) (he0 : e0.val < 2 ^ 6)
    (hdec : value = d2 + d3 * 256 + e0 * 288230376151711744) :
    value.val = d2.val + d3.val * 256 + e0.val * 288230376151711744 := by
  let packed := d2.val + d3.val * 256 + e0.val * 288230376151711744
  have hPackedLt : packed < 2 ^ 64 := by
    norm_num [K] at hd2 hd3 he0 ⊢
    omega
  have hPackedCard : packed < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    exact lt_trans hPackedLt (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hcast : value = (packed : Ecc.Fp) := by
    rw [hdec]
    dsimp only [packed]
    rw [← ZMod.natCast_zmod_val d2, ← ZMod.natCast_zmod_val d3,
      ← ZMod.natCast_zmod_val e0]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt d2),
      ZMod.val_natCast_of_lt (ZMod.val_lt d3), ZMod.val_natCast_of_lt (ZMod.val_lt e0)]
  rw [hcast, ZMod.val_natCast_of_lt hPackedCard]

private theorem value_from_parts_lt {value d2 d3 e0 : Ecc.Fp}
    (hd2 : d2.val < 2 ^ 8) (hd3 : d3.val < 2 ^ (K * 5)) (he0 : e0.val < 2 ^ 6)
    (hdec : value = d2 + d3 * 256 + e0 * 288230376151711744) :
    value.val < 2 ^ 64 := by
  rw [value_from_parts_val_eq hd2 hd3 he0 hdec]
  norm_num [K] at hd2 hd3 he0 ⊢
  omega

private theorem e1_f_low_lt_of_f_130 {e1 f : Ecc.Fp}
    (he1 : e1.val < 2 ^ 4) (hf : f.val < 2 ^ (K * 13)) :
    e1.val + f.val * 16 < 2 ^ 134 := by
  norm_num [K] at he1 hf ⊢
  omega

private theorem g1_g2_low_lt_of_g_piece_130 {g0 g1 g2 : Ecc.Fp}
    (hg0 : NoteCommit.IsBool g0) (hg1 : g1.val < 2 ^ 9)
    (hg2 : g2.val < 2 ^ (K * 24))
    (hg : (g0 + g1 * 2 + g2 * 1024).val < 2 ^ (K * 13)) :
    g1.val + g2.val * 512 < 2 ^ 130 := by
  have hg0lt := isBool_val_lt_two hg0
  have hltCard : g0.val + g1.val * 2 + g2.val * 1024 <
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at hg0lt hg1 hg2 ⊢
    omega
  have hdec : g0 + g1 * 2 + g2 * 1024 =
      ((g0.val + g1.val * 2 + g2.val * 1024 : ℕ) : Ecc.Fp) := by
    rw [← ZMod.natCast_zmod_val g0, ← ZMod.natCast_zmod_val g1,
      ← ZMod.natCast_zmod_val g2]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt g0), ZMod.val_natCast_of_lt (ZMod.val_lt g1),
      ZMod.val_natCast_of_lt (ZMod.val_lt g2)]
  have hgVal : g0.val + g1.val * 2 + g2.val * 1024 < 2 ^ (K * 13) := by
    rw [hdec, ZMod.val_natCast_of_lt hltCard] at hg
    exact hg
  norm_num [K] at hg1 hgVal ⊢
  omega

private theorem e1_eq_rho_low_bits_of_parts {rho e1 f g0 e1FPrime z14 : Ecc.Fp}
    (he1 : e1.val < 2 ^ 4) (hf : f.val < 2 ^ (K * 25))
    (hg0 : NoteCommit.IsBool g0)
    (hlowSmall : g0 = 1 → e1.val + f.val * 16 < 2 ^ 134)
    (hrho : rho = e1 + f * 16 + g0 * OfNat.ofNat (2 ^ 254))
    (hprime : e1FPrime = e1 + f * 16 + OfNat.ofNat (2 ^ 140) - NoteCommit.tP)
    (hz14 : g0 = 0 ∨ z14 = 0)
    (hz14Lt : z14 = 0 → e1FPrime.val < 2 ^ (K * 14)) :
    e1 = ((rho.val % 16 : ℕ) : Ecc.Fp) := by
  have hfLow : e1.val + f.val * 16 < 2 ^ 254 := by
    norm_num [K] at he1 hf ⊢
    omega
  have hlowCard : e1.val + f.val * 16 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    exact lt_trans hfLow (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hlowField :
      e1 + f * 16 = ((e1.val + f.val * 16 : ℕ) : Ecc.Fp) := by
    rw [← ZMod.natCast_zmod_val e1, ← ZMod.natCast_zmod_val f]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt e1), ZMod.val_natCast_of_lt (ZMod.val_lt f)]
  have hlowMod : (e1.val + f.val * 16) % 16 = e1.val := by
    norm_num at he1 ⊢
    omega
  have he1Card : e1.val < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := ZMod.val_lt e1
  rcases hg0 with hg0zero | hg0one
  · have hrhoVal : rho.val = e1.val + f.val * 16 := by
      rw [hg0zero, zero_mul, _root_.add_zero] at hrho
      rw [hrho, hlowField, ZMod.val_natCast_of_lt hlowCard]
    rw [← ZMod.natCast_zmod_val e1]
    congr
    rw [hrhoVal, hlowMod]
  · have hz14zero : z14 = 0 := by
      rcases hz14 with hz | hz
      · exfalso
        exact zero_ne_one (by rw [← hz, hg0one])
      · exact hz
    have hprimeValLt := hz14Lt hz14zero
    let low := e1.val + f.val * 16
    have hprimeField : e1FPrime = (low + 2 ^ 140 - tPNat : ℕ) := by
      rw [hprime]
      dsimp only [low]
      rw [hlowField]
      push_cast [NoteCommit.tP, tPNat]
      ring
    have hprimeValEq : e1FPrime.val = low + 2 ^ 140 - tPNat := by
      have hlt : low + 2 ^ 140 - tPNat < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
        dsimp only [low]
        have hsmall := hlowSmall hg0one
        norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at hsmall ⊢
        omega
      rw [hprimeField, ZMod.val_natCast_of_lt hlt]
    have hlowLtTP : low < tPNat := by
      dsimp only [low] at hprimeValEq hprimeValLt
      rw [hprimeValEq] at hprimeValLt
      norm_num [K] at hprimeValLt ⊢
      omega
    have hpackedLt :
        e1.val + f.val * 16 + 2 ^ 254 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      dsimp only [low] at hlowLtTP
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at hlowLtTP ⊢
      omega
    have hrhoVal :
        rho.val = e1.val + f.val * 16 + 2 ^ 254 := by
      let low := e1.val + f.val * 16
      have hrhoCast : rho = ((low + 2 ^ 254 : ℕ) : Ecc.Fp) := by
        rw [hrho, hg0one]
        dsimp only [low]
        rw [hlowField]
        norm_num
      dsimp only [low] at hrhoCast
      rw [hrhoCast, ZMod.val_natCast_of_lt hpackedLt]
    rw [← ZMod.natCast_zmod_val e1]
    congr
    rw [hrhoVal]
    norm_num at he1 ⊢
    omega

private theorem g1_g2_eq_psi_low_bits_of_parts {psi g1 g2 h0 h1 g1G2Prime z13 : Ecc.Fp}
    (hg1 : g1.val < 2 ^ 9) (hg2 : g2.val < 2 ^ (K * 24))
    (hh0 : h0.val < 2 ^ 5) (hh1 : NoteCommit.IsBool h1)
    (hlowSmall : h1 = 1 → g1.val + g2.val * 512 < 2 ^ 130)
    (hpsi : psi =
      g1 + g2 * 512 + h0 * OfNat.ofNat (2 ^ 249) + h1 * OfNat.ofNat (2 ^ 254))
    (hprime : g1G2Prime = g1 + g2 * 512 + OfNat.ofNat (2 ^ 130) - NoteCommit.tP)
    (hh0zero : h1 = 0 ∨ h0 = 0)
    (hz13 : h1 = 0 ∨ z13 = 0)
    (hz13Lt : z13 = 0 → g1G2Prime.val < 2 ^ (K * 13)) :
    g1 + g2 * 512 = ((psi.val % 2 ^ 249 : ℕ) : Ecc.Fp) := by
  let low := g1.val + g2.val * 512
  have hlowLt249 : low < 2 ^ 249 := by
    dsimp only [low]
    norm_num [K] at hg1 hg2 ⊢
    omega
  have hlowCard : low < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    exact lt_trans hlowLt249 (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hlowField : g1 + g2 * 512 = (low : Ecc.Fp) := by
    dsimp only [low]
    rw [← ZMod.natCast_zmod_val g1, ← ZMod.natCast_zmod_val g2]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt g1), ZMod.val_natCast_of_lt (ZMod.val_lt g2)]
  rw [hlowField]
  congr
  rcases hh1 with hh1zero | hh1one
  · have hpackedLt :
        low + h0.val * 2 ^ 249 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      dsimp only [low] at hlowLt249
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at hlowLt249 hh0 ⊢
      omega
    have hpsiVal : psi.val = low + h0.val * 2 ^ 249 := by
      have hpsiCast : psi = ((low + h0.val * 2 ^ 249 : ℕ) : Ecc.Fp) := by
        rw [hpsi, hh1zero, zero_mul, _root_.add_zero, hlowField]
        rw [← ZMod.natCast_zmod_val h0]
        push_cast
        rw [ZMod.val_natCast_of_lt (ZMod.val_lt h0)]
      rw [hpsiCast, ZMod.val_natCast_of_lt hpackedLt]
    rw [hpsiVal]
    rw [Nat.mul_comm h0.val (2 ^ 249)]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt hlowLt249]
  · have hh0zero' : h0 = 0 := by
      rcases hh0zero with hz | hz
      · exfalso
        exact zero_ne_one (by rw [← hz, hh1one])
      · exact hz
    have hz13zero : z13 = 0 := by
      rcases hz13 with hz | hz
      · exfalso
        exact zero_ne_one (by rw [← hz, hh1one])
      · exact hz
    have hprimeValLt := hz13Lt hz13zero
    have hprimeField : g1G2Prime = (low + 2 ^ 130 - tPNat : ℕ) := by
      rw [hprime]
      rw [hlowField]
      push_cast [NoteCommit.tP, tPNat]
      ring
    have hprimeValEq : g1G2Prime.val = low + 2 ^ 130 - tPNat := by
      have hlt : low + 2 ^ 130 - tPNat < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
        dsimp only [low]
        have hsmall := hlowSmall hh1one
        norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at hsmall ⊢
        omega
      rw [hprimeField, ZMod.val_natCast_of_lt hlt]
    have hlowLtTP : low < tPNat := by
      rw [hprimeValEq] at hprimeValLt
      norm_num [K] at hprimeValLt ⊢
      omega
    have hpackedLt :
        low + 2 ^ 254 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at hlowLtTP ⊢
      omega
    have hpsiVal : psi.val = low + 2 ^ 254 := by
      have hpsiCast : psi = ((low + 2 ^ 254 : ℕ) : Ecc.Fp) := by
        rw [hpsi, hh0zero', hh1one]
        rw [zero_mul, one_mul, _root_.add_zero, hlowField]
        norm_num
      rw [hpsiCast, ZMod.val_natCast_of_lt hpackedLt]
    rw [hpsiVal]
    rw [show (2 : ℕ) ^ 254 = 2 ^ 249 * 32 by norm_num]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt hlowLt249]

private theorem low_58_from_low_middle (v : ℕ) :
    v % 256 + (v / 256 % 2 ^ (K * 5)) * 256 = v % 2 ^ 58 := by
  norm_num [K]
  omega

private theorem d2_eq_value_low_bits {value d2 d3 e0 : Ecc.Fp}
    (hd2 : d2.val < 2 ^ 8) (hd3 : d3.val < 2 ^ (K * 5)) (he0 : e0.val < 2 ^ 6)
    (hdec : value = d2 + d3 * 256 + e0 * 288230376151711744) :
    d2 = ((value.val % 256 : ℕ) : Ecc.Fp) := by
  rw [← ZMod.natCast_zmod_val d2]
  congr
  rw [value_from_parts_val_eq hd2 hd3 he0 hdec]
  norm_num [K] at hd2 hd3 he0 ⊢
  omega

private theorem d3_eq_value_middle_bits {value d2 d3 e0 : Ecc.Fp}
    (hd2 : d2.val < 2 ^ 8) (hd3 : d3.val < 2 ^ (K * 5)) (he0 : e0.val < 2 ^ 6)
    (hdec : value = d2 + d3 * 256 + e0 * 288230376151711744) :
    d3 = ((value.val / 256 % 2 ^ (K * 5) : ℕ) : Ecc.Fp) := by
  rw [← ZMod.natCast_zmod_val d3]
  congr
  rw [value_from_parts_val_eq hd2 hd3 he0 hdec]
  norm_num [K] at hd2 hd3 he0 ⊢
  omega

private theorem e0_eq_value_high_bits {value d2 d3 e0 : Ecc.Fp}
    (hd2 : d2.val < 2 ^ 8) (hd3 : d3.val < 2 ^ (K * 5)) (he0 : e0.val < 2 ^ 6)
    (hdec : value = d2 + d3 * 256 + e0 * 288230376151711744) :
    e0 = ((value.val / 2 ^ 58 % 64 : ℕ) : Ecc.Fp) := by
  rw [← ZMod.natCast_zmod_val e0]
  congr
  rw [value_from_parts_val_eq hd2 hd3 he0 hdec]
  norm_num [K] at hd2 hd3 he0 ⊢
  omega

private theorem chunksOf_add_high {low high n : ℕ} (hlow : low < 2 ^ (K * n)) :
    Orchard.Specs.Sinsemilla.chunksOf (low + 2 ^ (K * n) * high) n =
      Orchard.Specs.Sinsemilla.chunksOf low n := by
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod (low + 2 ^ (K * n) * high) n]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * n) = 2 ^ (K * n) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]

private theorem chunksOf_add_high_mod {low high n : ℕ} :
    Orchard.Specs.Sinsemilla.chunksOf (low + 2 ^ (K * n) * high) n =
      Orchard.Specs.Sinsemilla.chunksOf low n := by
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod (low + 2 ^ (K * n) * high) n]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * n) = 2 ^ (K * n) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [Nat.add_mul_mod_self_left]
  exact Orchard.Specs.Sinsemilla.chunksOf_mod low n

private theorem chunksOf_eq_of_mod {x y n : ℕ}
    (h : x % 2 ^ (K * n) = y % 2 ^ (K * n)) :
    Orchard.Specs.Sinsemilla.chunksOf x n = Orchard.Specs.Sinsemilla.chunksOf y n := by
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod x n,
    ← Orchard.Specs.Sinsemilla.chunksOf_mod y n]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * n) = 2 ^ (K * n) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [h]

private theorem chunksOf_one_eq_singleton {x : ℕ} (hx : x < 2 ^ K) :
    Orchard.Specs.Sinsemilla.chunksOf x 1 = [x] := by
  unfold Orchard.Specs.Sinsemilla.chunksOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [Nat.mod_eq_of_lt hx]

private theorem chunksOf_one_eq_singleton_mod {x : ℕ} :
    Orchard.Specs.Sinsemilla.chunksOf x 1 = [x % 2 ^ K] := by
  unfold Orchard.Specs.Sinsemilla.chunksOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_a (gdX gdY pkdX pkdY v rho psi : ℕ) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi) 25 =
      Orchard.Specs.Sinsemilla.chunksOf gdX 25 := by
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  rw [show
      gdX + 2 ^ 255 * gdY + 2 ^ 256 * pkdX + 2 ^ 511 * pkdY +
          2 ^ 512 * v + 2 ^ 576 * rho + 2 ^ 831 * psi =
        gdX + 2 ^ (K * 25) *
          (2 ^ 5 * gdY + 2 ^ 6 * pkdX + 2 ^ 261 * pkdY +
            2 ^ 262 * v + 2 ^ 326 * rho + 2 ^ 581 * psi) by
    norm_num [K]
    ring_nf]
  exact chunksOf_add_high_mod

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_b_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 250) %
        2 ^ K =
      gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 + (pkdX % 16) * 64 := by
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  norm_num at *
  omega

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_b (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 250) 1 =
      [gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 + (pkdX % 16) * 64] := by
  rw [chunksOf_one_eq_singleton_mod,
    noteCommitChunks_segment_b_word gdX gdY pkdX pkdY v rho psi hgdX hgdY]

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_c_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 260) %
        2 ^ (K * 25) =
      (pkdX / 16) % 2 ^ (K * 25) := by
  rw [show 2 ^ (K * 25) = 2 ^ 250 by norm_num [K]]
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  norm_num at *
  omega

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_c (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 260) 25 =
      Orchard.Specs.Sinsemilla.chunksOf (pkdX / 16) 25 := by
  exact chunksOf_eq_of_mod
    (noteCommitChunks_segment_c_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY)

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_d_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) (hpkdX : pkdX < 2 ^ 255) :
    (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) %
        2 ^ (K * 6) =
      (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) % 2 ^ (K * 6) := by
  rw [show 2 ^ (K * 6) = 2 ^ 60 by norm_num [K]]
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  norm_num at *
  omega

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_d (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2) (hpkdX : pkdX < 2 ^ 255) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) 6 =
      Orchard.Specs.Sinsemilla.chunksOf
        (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) 6 := by
  exact chunksOf_eq_of_mod
    (noteCommitChunks_segment_d_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX)

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_e_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 570) %
        2 ^ K =
      v / 2 ^ 58 % 64 + (rho % 16) * 64 := by
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  norm_num at *
  omega

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_e (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 570) 1 =
      [v / 2 ^ 58 % 64 + (rho % 16) * 64] := by
  rw [chunksOf_one_eq_singleton_mod,
    noteCommitChunks_segment_e_word gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv]

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_f_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 580) %
        2 ^ (K * 25) =
      (rho / 16) % 2 ^ (K * 25) := by
  rw [show 2 ^ (K * 25) = 2 ^ 250 by norm_num [K]]
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  norm_num at *
  omega

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_f (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2) (hv : v < 2 ^ 64) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 580) 25 =
      Orchard.Specs.Sinsemilla.chunksOf (rho / 16) 25 := by
  exact chunksOf_eq_of_mod
    (noteCommitChunks_segment_f_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv)

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_g_mod (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) :
    (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) %
        2 ^ (K * 25) =
      (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) % 2 ^ (K * 25) := by
  rw [show 2 ^ (K * 25) = 2 ^ 250 by norm_num [K]]
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  norm_num at *
  omega

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_g (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) 25 =
      Orchard.Specs.Sinsemilla.chunksOf
        (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) 25 := by
  exact chunksOf_eq_of_mod
    (noteCommitChunks_segment_g_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho)

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_h_word (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 1080) %
        2 ^ K =
      psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 := by
  rw [show 2 ^ K = 1024 by norm_num [K]]
  unfold Orchard.Specs.Sinsemilla.noteCommitMessage
  norm_num at *
  omega

set_option exponentiation.threshold 900 in
private theorem noteCommitChunks_segment_h (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    Orchard.Specs.Sinsemilla.chunksOf
        (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 1080) 1 =
      [psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32] := by
  rw [chunksOf_one_eq_singleton_mod,
    noteCommitChunks_segment_h_word gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho hpsi]

private theorem noteCommitChunks_tiling_segments (gdX gdY pkdX pkdY v rho psi : ℕ)
    (hgdX : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdY pkdX pkdY v rho psi =
      Orchard.Specs.Sinsemilla.chunksOf gdX 25 ++
      [gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 + (pkdX % 16) * 64] ++
      Orchard.Specs.Sinsemilla.chunksOf (pkdX / 16) 25 ++
      Orchard.Specs.Sinsemilla.chunksOf
        (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) 6 ++
      [v / 2 ^ 58 % 64 + (rho % 16) * 64] ++
      Orchard.Specs.Sinsemilla.chunksOf (rho / 16) 25 ++
      Orchard.Specs.Sinsemilla.chunksOf (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) 25 ++
      [psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32] := by
  rw [Orchard.Specs.Sinsemilla.noteCommitChunks_tiling]
  rw [noteCommitChunks_segment_a]
  rw [noteCommitChunks_segment_b _ _ _ _ _ _ _ hgdX hgdY]
  rw [noteCommitChunks_segment_c _ _ _ _ _ _ _ hgdX hgdY]
  rw [noteCommitChunks_segment_d _ _ _ _ _ _ _ hgdX hgdY hpkdX]
  rw [noteCommitChunks_segment_e _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv]
  rw [noteCommitChunks_segment_f _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv]
  rw [noteCommitChunks_segment_g _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv hrho]
  rw [noteCommitChunks_segment_h _ _ _ _ _ _ _ hgdX hgdY hpkdX hpkdY hv hrho hpsi]

/-! ### Canonicity bound helpers (note_commit.rs:1804-1954)

Each witnesses a "prime" value (the element shifted up by `2^130`/`2^140` minus `t_P`)
and runs a `LookupRangeCheck` running-sum decomposition (`CopyCheck`), returning the
prime cell (`z_0`) and the final running sum (`z_13`/`z_14`). `prime` decomposes as
`prime = lo + 2^(K·n) · z_last` with `lo < 2^(K·n)`, so `z_last = 0 ⟹ prime < 2^(K·n)` —
the canonicity bound the `*Canonicity` gates consume. These are plain synthesis helpers
(not bundled circuits): the `prime = element + 2^… - t_P` link is enforced by the gate.

`copyCheck` is `LookupRangeCheck.CopyCheck.circuit`. `tP = T_P`. -/

/-- `canon_bitshift_130(a)`: returns `(a_prime, z_13)` for `a_prime = a + 2^130 - t_P`. -/
def canonBitshift130 (a : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let aPrime ← witnessField fun env => env a + (2 ^ 130 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 aPrime
  return (zs[0], zs[13])

/-- `pkd_x_canonicity(b_3, c)`: returns `(b3_c_prime, z_14)` for
`b3_c_prime = b_3 + 2^4·c + 2^140 - t_P`. -/
def pkdXCanonicity (b3 c : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let prime ← witnessField fun env =>
    env b3 + (2 ^ 4 : Ecc.Fp) * env c + (2 ^ 140 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14 prime
  return (zs[0], zs[14])

/-- `rho_canonicity(e_1, f)`: returns `(e1_f_prime, z_14)` for
`e1_f_prime = e_1 + 2^4·f + 2^140 - t_P`. -/
def rhoCanonicity (e1 f : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let prime ← witnessField fun env =>
    env e1 + (2 ^ 4 : Ecc.Fp) * env f + (2 ^ 140 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14 prime
  return (zs[0], zs[14])

/-- `psi_canonicity(g_1, g_2)`: returns `(g1_g2_prime, z_13)` for
`g1_g2_prime = g_1 + 2^9·g_2 + 2^130 - t_P`. -/
def psiCanonicity (g1 g2 : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let prime ← witnessField fun env =>
    env g1 + (2 ^ 9 : Ecc.Fp) * env g2 + (2 ^ 130 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 prime
  return (zs[0], zs[13])

/-! ### Subpiece witnessing helpers -/

/-- `bitrangeSubset value start numBits = (value.val >> start) mod 2^numBits`. -/
abbrev bitrangeSubset : Ecc.Fp → ℕ → ℕ → Ecc.Fp :=
  Utilities.LookupRangeCheck.WitnessShort.bitrangeSubset

/-- `RangeConstrained::witness_short` reading the source from a constrained cell:
witness `bitrangeSubset src start numBits` and short-range-check it to `numBits`. -/
def witnessShort (src : Var field Ecc.Fp) (start numBits : ℕ) (h : numBits ≤ Utilities.LookupRangeCheck.K) :
    Circuit Ecc.Fp (Var field Ecc.Fp) := do
  Utilities.LookupRangeCheck.WitnessShort.circuit start numBits h
    (fun env => bitrangeSubset (Expression.eval env src) start numBits)

/-- `RangeConstrained::bitrange_of`: witness `bitrangeSubset src start numBits` with no
range check (it is bool/decomposition-constrained downstream). -/
def witnessBitrange (src : Var field Ecc.Fp) (start numBits : ℕ) :
    Circuit Ecc.Fp (Var field Ecc.Fp) :=
  witnessField fun env => bitrangeSubset (Expression.eval env src) start numBits

/-! ### `y_canonicity` (note_commit.rs:1962)

Decomposes `y = lsb || k_0 || k_1 || k_2 || k_3`, range-decomposes `j = lsb + 2·k_0 +
2^10·k_1` (strict, 25 words), reuses `canon_bitshift_130` on `j`, and wires the
`YCanonicity` gate. Returns the `lsb` (the `ỹ` sign bit) it was given. -/
def yCanonicity (y lsb : Var field Ecc.Fp) : Circuit Ecc.Fp (Var field Ecc.Fp) := do
  let k0 ← witnessShort y 1 9 (by norm_num [K])
  let k2 ← witnessShort y 250 4 (by norm_num [K])
  let k3 ← witnessBitrange y 254 1
  let j ← witnessField fun env =>
    env lsb + 2 * env k0 + (2 ^ 10 : Ecc.Fp) * bitrangeSubset (Expression.eval env y) 10 240
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 25 j
  -- strict: the running sum must vanish (the value fits exactly in 250 bits)
  assertZero zs[25]
  let (jPrime, z13JPrime) ← canonBitshift130 zs[0]
  let yrow : Var NoteCommit.YCanonicity.Row Ecc.Fp :=
    { y := y, lsb := lsb, k0 := k0, k2 := k2, k3 := k3, j := zs[0], z1J := zs[1],
      z13J := zs[13], jPrime := jPrime, z13JPrime := z13JPrime }
  NoteCommit.YCanonicity.circuit yrow
  return lsb

instance witnessShortExplicit (src : Var field Ecc.Fp) (start numBits : ℕ)
    (h : numBits ≤ Utilities.LookupRangeCheck.K) :
    ExplicitCircuit (witnessShort src start numBits h) := by
  unfold witnessShort
  infer_explicit_circuit

instance witnessBitrangeExplicit (src : Var field Ecc.Fp) (start numBits : ℕ) :
    ExplicitCircuit (witnessBitrange src start numBits) := by
  unfold witnessBitrange
  infer_explicit_circuit

instance canonBitshift130Explicit (a : Var field Ecc.Fp) :
    ExplicitCircuit (canonBitshift130 a) := by
  unfold canonBitshift130
  infer_explicit_circuit

instance pkdXCanonicityExplicit (b3 c : Var field Ecc.Fp) :
    ExplicitCircuit (pkdXCanonicity b3 c) := by
  unfold pkdXCanonicity
  infer_explicit_circuit

instance rhoCanonicityExplicit (e1 f : Var field Ecc.Fp) :
    ExplicitCircuit (rhoCanonicity e1 f) := by
  unfold rhoCanonicity
  infer_explicit_circuit

instance psiCanonicityExplicit (g1 g2 : Var field Ecc.Fp) :
    ExplicitCircuit (psiCanonicity g1 g2) := by
  unfold psiCanonicity
  infer_explicit_circuit

instance yCanonicityExplicit (y lsb : Var field Ecc.Fp) :
    ExplicitCircuit (yCanonicity y lsb) := by
  unfold yCanonicity
  infer_explicit_circuit

attribute [explicit_circuit_no_unfold] witnessShort witnessBitrange canonBitshift130
  pkdXCanonicity rhoCanonicity psiCanonicity yCanonicity

@[circuit_norm] theorem witnessShort_localLength (src : Var field Ecc.Fp) (start numBits : ℕ)
    (h : numBits ≤ Utilities.LookupRangeCheck.K) (offset : ℕ) :
    (witnessShort src start numBits h).localLength offset = 2 := by
  unfold witnessShort
  simp only [circuit_norm, Utilities.LookupRangeCheck.WitnessShort.circuit]

@[circuit_norm] theorem witnessBitrange_localLength (src : Var field Ecc.Fp) (start numBits : ℕ)
    (offset : ℕ) :
    (witnessBitrange src start numBits).localLength offset = 1 := rfl

@[circuit_norm] theorem canonBitshift130_localLength (a : Var field Ecc.Fp) (offset : ℕ) :
    (canonBitshift130 a).localLength offset = 15 := rfl

@[circuit_norm] theorem pkdXCanonicity_localLength (b3 c : Var field Ecc.Fp) (offset : ℕ) :
    (pkdXCanonicity b3 c).localLength offset = 16 := rfl

@[circuit_norm] theorem rhoCanonicity_localLength (e1 f : Var field Ecc.Fp) (offset : ℕ) :
    (rhoCanonicity e1 f).localLength offset = 16 := rfl

@[circuit_norm] theorem psiCanonicity_localLength (g1 g2 : Var field Ecc.Fp) (offset : ℕ) :
    (psiCanonicity g1 g2).localLength offset = 15 := rfl

@[circuit_norm] theorem yCanonicity_localLength (y lsb : Var field Ecc.Fp) (offset : ℕ) :
    (yCanonicity y lsb).localLength offset = 47 := by
  unfold yCanonicity
  simp only [circuit_norm, Utilities.LookupRangeCheck.CopyCheck.circuit,
    YCanonicity.circuit]

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

instance : Inhabited (Var Input Ecc.Fp) :=
  ⟨{ gd := default, pkd := default, value := default, rho := default, psi := default,
     rcm := fun _ => default }⟩

structure MessageCells where
  a : Var field Ecc.Fp
  b : Var field Ecc.Fp
  c : Var field Ecc.Fp
  d : Var field Ecc.Fp
  e : Var field Ecc.Fp
  f : Var field Ecc.Fp
  g : Var field Ecc.Fp
  h : Var field Ecc.Fp
  b0 : Var field Ecc.Fp
  b1 : Var field Ecc.Fp
  b2 : Var field Ecc.Fp
  b3 : Var field Ecc.Fp
  d0 : Var field Ecc.Fp
  d1 : Var field Ecc.Fp
  d2 : Var field Ecc.Fp
  e0 : Var field Ecc.Fp
  e1 : Var field Ecc.Fp
  g0 : Var field Ecc.Fp
  g1 : Var field Ecc.Fp
  h0 : Var field Ecc.Fp
  h1 : Var field Ecc.Fp

structure MessageSubpieces where
  b0 : Var field Ecc.Fp
  b1 : Var field Ecc.Fp
  b2 : Var field Ecc.Fp
  b3 : Var field Ecc.Fp
  d0 : Var field Ecc.Fp
  d1 : Var field Ecc.Fp
  d2 : Var field Ecc.Fp
  e0 : Var field Ecc.Fp
  e1 : Var field Ecc.Fp
  g0 : Var field Ecc.Fp
  g1 : Var field Ecc.Fp
  h0 : Var field Ecc.Fp
  h1 : Var field Ecc.Fp

/-- Sinsemilla per-piece round counts for the note-commit message. Each entry is
`num_words - 1`, matching `Chain.PieceChunks`: source chunk counts
`[25, 1, 25, 6, 1, 25, 25, 1]` become `[24, 0, 24, 5, 0, 24, 24, 0]`. -/
abbrev messagePieceTailRounds : List ℕ := [0, 24, 5, 0, 24, 24, 0]
abbrev messagePieceRounds : List ℕ := 24 :: messagePieceTailRounds

private theorem noteCommitChunks_eq_of_piece_digit_sums
    {msA msB msC msD msE msF msG msH : ℕ → ℕ}
    {gdX gdY pkdX pkdY v rho psi : ℕ}
    (hmsA : ∀ r, msA r < 2 ^ K) (hmsB : ∀ r, msB r < 2 ^ K)
    (hmsC : ∀ r, msC r < 2 ^ K) (hmsD : ∀ r, msD r < 2 ^ K)
    (hmsE : ∀ r, msE r < 2 ^ K) (hmsF : ∀ r, msF r < 2 ^ K)
    (hmsG : ∀ r, msG r < 2 ^ K) (hmsH : ∀ r, msH r < 2 ^ K)
    (hA : ((gdX % 2 ^ (K * 25) : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hB : ((gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 +
        (pkdX % 16) * 64 : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 1, msB r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hC : (((pkdX / 16) % 2 ^ (K * 25) : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hD : ((pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4 : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 6, msD r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hE : ((v / 2 ^ 58 % 64 + (rho % 16) * 64 : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 1, msE r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hF : (((rho / 16) % 2 ^ (K * 25) : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 25, msF r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hG : ((rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2 : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 25, msG r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hH : ((psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 : ℕ) : Ecc.Fp) =
      ((∑ r ∈ Finset.range 1, msH r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
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
      Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdY pkdX pkdY v rho psi := by
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
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) two_pow_K_mul_25_lt_p)
    (lt_trans (sum_digits_lt hmsA 25) two_pow_K_mul_25_lt_p)
  have hChunksA : Orchard.Specs.Sinsemilla.chunksOf gdX 25 = (List.range 25).map msA := by
    rw [← Orchard.Specs.Sinsemilla.chunksOf_mod gdX 25]
    exact hChunksA_low
  have hChunksB := chunksOf_eq_map_of_cast_sum hmsB hB
    (lt_trans hBValueLt two_pow_K_lt_p)
    (lt_trans (sum_digits_lt hmsB 1) two_pow_K_lt_p)
  have hChunksC_low := chunksOf_eq_map_of_cast_sum hmsC hC
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) two_pow_K_mul_25_lt_p)
    (lt_trans (sum_digits_lt hmsC 25) two_pow_K_mul_25_lt_p)
  have hChunksC : Orchard.Specs.Sinsemilla.chunksOf (pkdX / 16) 25 =
      (List.range 25).map msC := by
    rw [← Orchard.Specs.Sinsemilla.chunksOf_mod (pkdX / 16) 25]
    exact hChunksC_low
  have hChunksD := chunksOf_eq_map_of_cast_sum hmsD hD
    (lt_trans hDValueLt two_pow_K_mul_6_lt_p)
    (lt_trans (sum_digits_lt hmsD 6) two_pow_K_mul_6_lt_p)
  have hChunksE := chunksOf_eq_map_of_cast_sum hmsE hE
    (lt_trans hEValueLt two_pow_K_lt_p)
    (lt_trans (sum_digits_lt hmsE 1) two_pow_K_lt_p)
  have hChunksF_low := chunksOf_eq_map_of_cast_sum hmsF hF
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) two_pow_K_mul_25_lt_p)
    (lt_trans (sum_digits_lt hmsF 25) two_pow_K_mul_25_lt_p)
  have hChunksF : Orchard.Specs.Sinsemilla.chunksOf (rho / 16) 25 =
      (List.range 25).map msF := by
    rw [← Orchard.Specs.Sinsemilla.chunksOf_mod (rho / 16) 25]
    exact hChunksF_low
  have hChunksG := chunksOf_eq_map_of_cast_sum hmsG hG
    (lt_trans hGValueLt two_pow_K_mul_25_lt_p)
    (lt_trans (sum_digits_lt hmsG 25) two_pow_K_mul_25_lt_p)
  have hChunksH := chunksOf_eq_map_of_cast_sum hmsH hH
    (lt_trans hHValueLt two_pow_K_lt_p)
    (lt_trans (sum_digits_lt hmsH 1) two_pow_K_lt_p)
  rw [← hChunksA, ← hChunksB, ← hChunksC, ← hChunksD,
    ← hChunksE, ← hChunksF, ← hChunksG, ← hChunksH]
  rw [chunksOf_one_eq_singleton hBValueLt, chunksOf_one_eq_singleton hEValueLt,
    chunksOf_one_eq_singleton hHValueLt]
  exact (noteCommitChunks_tiling_segments gdX gdY pkdX pkdY v rho psi
    hgdX255 hgdY hpkdX255 hpkdY hv hrho hpsi).symm

theorem pieceChunks_messagePieceRounds_chunks
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    (h : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks) :
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
  simp only [messagePieceTailRounds, Orchard.Sinsemilla.Chain.PieceChunks] at h
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

private theorem zsFacts_head_get {n : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Ecc.Fp}
    (h : Orchard.Sinsemilla.Chain.ZsFacts (n :: rest) chunks zs) (r : Fin (n + 1)) :
    (HVec.head zs)[r] =
      ((∑ j ∈ Finset.range (n + 1 - r.val),
        chunks.getD (r.val + j) 0 * 2 ^ (K * j) : ℕ) : Ecc.Fp) := by
  simp only [Orchard.Sinsemilla.Chain.ZsFacts] at h
  rw [h.1]
  simp only
  norm_num [Orchard.Specs.Sinsemilla.K, K]

private theorem zsFacts_tail {n : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Ecc.Fp}
    (h : Orchard.Sinsemilla.Chain.ZsFacts (n :: rest) chunks zs) :
    Orchard.Sinsemilla.Chain.ZsFacts rest (chunks.drop (n + 1)) (HVec.tail zs) := by
  simp only [Orchard.Sinsemilla.Chain.ZsFacts] at h
  exact h.2

private theorem pieceChunks_tail_drop {n : ℕ} {rest : List ℕ}
    {pieces : Vector Ecc.Fp (n :: rest).length} {chunks : List ℕ}
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    Orchard.Sinsemilla.Chain.PieceChunks rest pieces.tail (chunks.drop (n + 1)) := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at h
  obtain ⟨ms, _hms, _hpiece, tailChunks, hchunks, htail⟩ := h
  rw [hchunks, Orchard.Sinsemilla.Chain.chunks_drop_append ms tailChunks]
  exact htail

private theorem pieceChunks_head_val_lt {n : ℕ} {rest : List ℕ}
    {pieces : Vector Ecc.Fp (n :: rest).length} {chunks : List ℕ}
    (hpow : 2 ^ (K * (n + 1)) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    (pieces[0]).val < 2 ^ (K * (n + 1)) := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at h
  obtain ⟨ms, hms, hpiece, _tailChunks, _hchunks, _htail⟩ := h
  have hsumLt := sum_digits_lt hms (n + 1)
  rw [hpiece, ZMod.val_natCast_of_lt (lt_trans hsumLt hpow)]
  exact hsumLt

private theorem pieceChunks_head_val_lt_of_z_zero {n r : ℕ} {rest : List ℕ}
    {pieces : Vector Ecc.Fp (n :: rest).length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Ecc.Fp}
    (hr : r < n + 1)
    (hpowLow : 2 ^ (K * r) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hpowHigh : 2 ^ (K * (n + 1 - r)) <
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts (n :: rest) chunks zs)
    (hz : (HVec.head zs)[r]'hr = 0) :
    (pieces[0]).val < 2 ^ (K * r) := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at hPC
  obtain ⟨ms, hms, hpiece, tailChunks, hchunks, _hPCtail⟩ := hPC
  let low : ℕ := ∑ j ∈ Finset.range r, ms j * 2 ^ (K * j)
  let high : ℕ := ∑ j ∈ Finset.range (n + 1 - r), ms (r + j) * 2 ^ (K * j)
  have hhighCast :
      (high : Ecc.Fp) = 0 := by
    have hz' := zsFacts_head_get hZs ⟨r, hr⟩
    simp only at hz'
    have hzFin : (HVec.head zs)[r]'hr = 0 := by
      exact hz
    have hz'' : (HVec.head zs)[r]'hr =
        ((∑ j ∈ Finset.range (n + 1 - r),
          chunks.getD (r + j) 0 * 2 ^ (K * j) : ℕ) : Ecc.Fp) := by
      exact hz'
    rw [hz''] at hzFin
    have hsum :
        (∑ j ∈ Finset.range (n + 1 - r),
          chunks.getD (r + j) 0 * 2 ^ (K * j)) = high := by
      rw [hchunks]
      dsimp only [high]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : r + j < n + 1 := by
        simp only [Finset.mem_range] at hj
        omega
      rw [Orchard.Sinsemilla.Chain.chunks_head_getD ms tailChunks (r + j) hj']
    rw [← hsum]
    simpa only [Orchard.Specs.Sinsemilla.K, K] using hzFin
  have hhighLt : high < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    dsimp only [high]
    exact lt_trans (sum_digits_lt (fun j => hms (r + j)) (n + 1 - r)) hpowHigh
  have hhighZero : high = 0 := by
    exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp hhighCast) hhighLt
  have hlowLt : low < 2 ^ (K * r) := by
    dsimp only [low]
    exact sum_digits_lt hms r
  have hpieceLow :
      pieces[0] = (low : Ecc.Fp) := by
    have hsplit := sum_digits_split K r (n + 1) (by omega) ms
    have hpieceK :
        pieces[0] = ((∑ j ∈ Finset.range (n + 1), ms j * 2 ^ (K * j) : ℕ) : Ecc.Fp) := by
      simpa only [Orchard.Specs.Sinsemilla.K, K] using hpiece
    have hsplitLow :
        (∑ j ∈ Finset.range (n + 1), ms j * 2 ^ (K * j)) = low := by
      rw [hsplit]
      change (∑ j ∈ Finset.range r, ms j * 2 ^ (K * j)) +
          2 ^ (K * r) * high = low
      rw [hhighZero, mul_zero, Nat.add_zero]
    rw [hpieceK, hsplitLow]
  rw [hpieceLow, ZMod.val_natCast_of_lt (lt_trans hlowLt hpowLow)]
  exact hlowLt

private theorem pieceChunks_large_piece_bounds
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks) :
    (pieces[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail.tail[0]).val < 2 ^ (K * 6) ∧
      (pieces.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 25) := by
  have hA := pieceChunks_head_val_lt (n := 24) (rest := messagePieceTailRounds)
    two_pow_K_mul_25_lt_p hPC
  have hPC1 := pieceChunks_tail_drop hPC
  have hPC2 := pieceChunks_tail_drop hPC1
  have hC := pieceChunks_head_val_lt (n := 24) (rest := [5, 0, 24, 24, 0])
    two_pow_K_mul_25_lt_p hPC2
  have hPC3 := pieceChunks_tail_drop hPC2
  have hD := pieceChunks_head_val_lt (n := 5) (rest := [0, 24, 24, 0])
    two_pow_K_mul_6_lt_p hPC3
  have hPC4 := pieceChunks_tail_drop hPC3
  have hPC5 := pieceChunks_tail_drop hPC4
  have hF := pieceChunks_head_val_lt (n := 24) (rest := [24, 0])
    two_pow_K_mul_25_lt_p hPC5
  have hPC6 := pieceChunks_tail_drop hPC5
  have hG := pieceChunks_head_val_lt (n := 24) (rest := [0])
    two_pow_K_mul_25_lt_p hPC6
  exact ⟨hA, hC, hD, hF, hG⟩

private theorem pieceChunks_f_val_lt_of_z13_zero
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Ecc.Fp}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13f :
      (HVec.head (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail zs))))))[13]'(by decide)
        = 0) :
    (pieces.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 13) := by
  have hPC1 := pieceChunks_tail_drop hPC
  have hZs1 := zsFacts_tail hZs
  have hPC2 := pieceChunks_tail_drop hPC1
  have hZs2 := zsFacts_tail hZs1
  have hPC3 := pieceChunks_tail_drop hPC2
  have hZs3 := zsFacts_tail hZs2
  have hPC4 := pieceChunks_tail_drop hPC3
  have hZs4 := zsFacts_tail hZs3
  have hPC5 := pieceChunks_tail_drop hPC4
  have hZs5 := zsFacts_tail hZs4
  exact pieceChunks_head_val_lt_of_z_zero
    (n := 24) (r := 13) (rest := [24, 0])
    (hr := by norm_num)
    (hpowLow := by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (hpowHigh := by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    hPC5 hZs5 hz13f

private theorem pieceChunks_e1_f_low_lt_of_z13_zero
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Ecc.Fp}
    {e1 : Ecc.Fp}
    (he1 : e1.val < 2 ^ 4)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13f :
      (HVec.head (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail zs))))))[13]'(by decide)
        = 0) :
    e1.val + (pieces.tail.tail.tail.tail.tail[0]).val * 16 < 2 ^ 134 := by
  exact e1_f_low_lt_of_f_130 he1 (pieceChunks_f_val_lt_of_z13_zero hPC hZs hz13f)

private theorem e1_f_low_lt_of_piece_z13_zero {e1 f : Ecc.Fp}
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Ecc.Fp}
    (he1 : e1.val < 2 ^ 4)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13f :
      (HVec.head (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail zs))))))[13]'(by decide)
        = 0)
    (hf : pieces.tail.tail.tail.tail.tail[0] = f) :
    e1.val + f.val * 16 < 2 ^ 134 := by
  have hlow := pieceChunks_e1_f_low_lt_of_z13_zero he1 hPC hZs hz13f
  have hfVal := congrArg ZMod.val hf
  rw [hfVal] at hlow
  exact hlow

private theorem pieceChunks_g_val_lt_of_z13_zero
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Ecc.Fp}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13g :
      (HVec.head (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail zs)))))))[13]'(by decide)
        = 0) :
    (pieces.tail.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 13) := by
  have hPC1 := pieceChunks_tail_drop hPC
  have hZs1 := zsFacts_tail hZs
  have hPC2 := pieceChunks_tail_drop hPC1
  have hZs2 := zsFacts_tail hZs1
  have hPC3 := pieceChunks_tail_drop hPC2
  have hZs3 := zsFacts_tail hZs2
  have hPC4 := pieceChunks_tail_drop hPC3
  have hZs4 := zsFacts_tail hZs3
  have hPC5 := pieceChunks_tail_drop hPC4
  have hZs5 := zsFacts_tail hZs4
  have hPC6 := pieceChunks_tail_drop hPC5
  have hZs6 := zsFacts_tail hZs5
  exact pieceChunks_head_val_lt_of_z_zero
    (n := 24) (r := 13) (rest := [0])
    (hr := by norm_num)
    (hpowLow := by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (hpowHigh := by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    hPC6 hZs6 hz13g

private theorem g1_g2_low_lt_of_piece_z13_zero {g0 g1 g2 : Ecc.Fp}
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Ecc.Fp}
    (hg0 : NoteCommit.IsBool g0) (hg1 : g1.val < 2 ^ 9)
    (hg2 : g2.val < 2 ^ (K * 24))
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13g :
      (HVec.head (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail zs)))))))[13]'(by decide)
        = 0)
    (hgPiece : pieces.tail.tail.tail.tail.tail.tail[0] = g0 + g1 * 2 + g2 * 1024) :
    g1.val + g2.val * 512 < 2 ^ 130 := by
  have hg := pieceChunks_g_val_lt_of_z13_zero hPC hZs hz13g
  rw [hgPiece] at hg
  exact g1_g2_low_lt_of_g_piece_130 hg0 hg1 hg2 hg

private theorem z1_head_val_lt {n : ℕ} {rest : List ℕ}
    {pieces : Vector Ecc.Fp (n :: rest).length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Ecc.Fp}
    (hn : 1 < n + 1)
    (hpow : 2 ^ (K * n) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts (n :: rest) chunks zs) :
    ((HVec.head zs)[1]'hn).val < 2 ^ (K * n) := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at hPC
  obtain ⟨ms, hms, _hpiece, tailChunks, hchunks, _hPCtail⟩ := hPC
  have hz := zsFacts_head_get hZs ⟨1, hn⟩
  have hsum :
      (∑ j ∈ Finset.range n, chunks.getD (j + 1) 0 * 2 ^ (K * j)) =
        ∑ j ∈ Finset.range n, ms (j + 1) * 2 ^ (K * j) := by
    rw [hchunks]
    simpa only [Orchard.Specs.Sinsemilla.K, K] using
      (Orchard.Sinsemilla.Chain.z1Facts_head_sum (n := n) ms tailChunks)
  have hsumLt : (∑ j ∈ Finset.range n, ms (j + 1) * 2 ^ (K * j)) < 2 ^ (K * n) :=
    sum_digits_lt (fun j => hms (j + 1)) n
  simp only at hz
  rw [show n + 1 - 1 = n by omega] at hz
  have hz' :
      (HVec.head zs)[1] =
        ((∑ j ∈ Finset.range n, chunks.getD (j + 1) 0 * 2 ^ (K * j) : ℕ) : Ecc.Fp) := by
    simpa only [Nat.add_comm] using hz
  rw [hz']
  rw [hsum]
  rw [ZMod.val_natCast_of_lt (lt_trans hsumLt hpow)]
  exact hsumLt

private theorem pieceChunks_eq_noteCommitChunks_of_indexed_piece_values
    {pieces : Vector Ecc.Fp messagePieceRounds.length} {chunks : List ℕ}
    {gdX gdY pkdX pkdY v rho psi : ℕ}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hA : pieces[0] = ((gdX % 2 ^ (K * 25) : ℕ) : Ecc.Fp))
    (hB : pieces[1] =
      ((gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdY * 32 +
        (pkdX % 16) * 64 : ℕ) : Ecc.Fp))
    (hC : pieces[2] = (((pkdX / 16) % 2 ^ (K * 25) : ℕ) : Ecc.Fp))
    (hD : pieces[3] =
      ((pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4 : ℕ) : Ecc.Fp))
    (hE : pieces[4] =
      ((v / 2 ^ 58 % 64 + (rho % 16) * 64 : ℕ) : Ecc.Fp))
    (hF : pieces[5] = (((rho / 16) % 2 ^ (K * 25) : ℕ) : Ecc.Fp))
    (hG : pieces[6] =
      ((rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2 : ℕ) : Ecc.Fp))
    (hH : pieces[7] =
      ((psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 : ℕ) : Ecc.Fp))
    (hgdX255 : gdX < 2 ^ 255) (hgdY : gdY < 2)
    (hpkdX255 : pkdX < 2 ^ 255) (hpkdY : pkdY < 2)
    (hv : v < 2 ^ 64) (hrho : rho < 2 ^ 255) (hpsi : psi < 2 ^ 255) :
    chunks = Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdY pkdX pkdY v rho psi := by
  simp only [messagePieceTailRounds, Orchard.Sinsemilla.Chain.PieceChunks] at hPC
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

def assignSubpieces (input : Var Input Ecc.Fp) : Circuit Ecc.Fp MessageSubpieces := do
  let gdX := input.gd.x
  let gdY := input.gd.y
  let pkdX := input.pkd.x
  let pkdY := input.pkd.y
  let v := input.value
  let rho := input.rho
  let psi := input.psi
  let b0 ← witnessShort gdX 250 4 (by norm_num [K])
  let b3 ← witnessShort pkdX 0 4 (by norm_num [K])
  let d2 ← witnessShort v 0 8 (by norm_num [K])
  let e0 ← witnessShort v 58 6 (by norm_num [K])
  let e1 ← witnessShort rho 0 4 (by norm_num [K])
  let g1 ← witnessShort psi 0 9 (by norm_num [K])
  let h0 ← witnessShort psi 249 5 (by norm_num [K])
  -- bitrange-only subpieces (bool/decomposition-constrained in the gates)
  let b1 ← witnessBitrange gdX 254 1
  let b2 ← witnessBitrange gdY 0 1
  let d0 ← witnessBitrange pkdX 254 1
  let d1 ← witnessBitrange pkdY 0 1
  let g0 ← witnessBitrange rho 254 1
  let h1 ← witnessBitrange psi 254 1
  return { b0, b1, b2, b3, d0, d1, d2, e0, e1, g0, g1, h0, h1 }

def constrainYSubpieces (input : Var Input Ecc.Fp) (subpieces : MessageSubpieces) :
    Circuit Ecc.Fp MessageSubpieces := do
  let b2 ← yCanonicity input.gd.y subpieces.b2
  let d1 ← yCanonicity input.pkd.y subpieces.d1
  return { subpieces with b2, d1 }

def assignMessagePieces (input : Var Input Ecc.Fp) (subpieces : MessageSubpieces) :
    Circuit Ecc.Fp MessageCells := do
  let gdX := input.gd.x
  let pkdX := input.pkd.x
  let v := input.value
  let rho := input.rho
  let psi := input.psi
  let a ← witnessBitrange gdX 0 250
  let b ← witnessField fun env =>
    env subpieces.b0 + env subpieces.b1 * 2 ^ 4 + env subpieces.b2 * 2 ^ 5 +
      env subpieces.b3 * 2 ^ 6
  let c ← witnessBitrange pkdX 4 250
  let d ← witnessField fun env =>
    env subpieces.d0 + env subpieces.d1 * 2 + env subpieces.d2 * 2 ^ 2 +
    bitrangeSubset (Expression.eval env v) 8 50 * 2 ^ 10
  let e ← witnessField fun env => env subpieces.e0 + env subpieces.e1 * 2 ^ 6
  let f ← witnessBitrange rho 4 250
  let g ← witnessField fun env => env subpieces.g0 + env subpieces.g1 * 2 +
    bitrangeSubset (Expression.eval env psi) 9 240 * 2 ^ 10
  let h ← witnessField fun env => env subpieces.h0 + env subpieces.h1 * 2 ^ 5
  return {
    a, b, c, d, e, f, g, h,
    b0 := subpieces.b0, b1 := subpieces.b1, b2 := subpieces.b2, b3 := subpieces.b3,
    d0 := subpieces.d0, d1 := subpieces.d1, d2 := subpieces.d2,
    e0 := subpieces.e0, e1 := subpieces.e1,
    g0 := subpieces.g0, g1 := subpieces.g1,
    h0 := subpieces.h0, h1 := subpieces.h1
  }

def assignMessageCells (input : Var Input Ecc.Fp) : Circuit Ecc.Fp MessageCells := do
  let subpieces ← assignSubpieces input
  let subpieces ← constrainYSubpieces input subpieces
  assignMessagePieces input subpieces

def commitWithZs (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) (cells : MessageCells) :
    Circuit Ecc.Fp (Var (Sinsemilla.CommitDomain.WithZs.Output messagePieceRounds) Ecc.Fp) := do
  _root_.Orchard.Sinsemilla.CommitDomain.WithZs.circuit G Q hQ R 24 messagePieceTailRounds
    { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
      r := input.rcm }

def constrainCommitment (input : Var Input Ecc.Fp) (cells : MessageCells)
    (out : Var (Sinsemilla.CommitDomain.WithZs.Output messagePieceRounds) Ecc.Fp) :
    Circuit Ecc.Fp (Var Point Ecc.Fp) := do
  let gdX := input.gd.x
  let pkdX := input.pkd.x
  let v := input.value
  let rho := input.rho
  let psi := input.psi
  let cm := out.point
  -- running-sum cells needed for canonicity (note_commit.rs:1702-1708)
  let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
  let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
  let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
  let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]
  -- canonicity bounds
  let (aPrime, z13aPrime) ← canonBitshift130 cells.a
  let (b3cPrime, z14b3c) ← pkdXCanonicity cells.b3 cells.c
  let (e1fPrime, z14e1f) ← rhoCanonicity cells.e1 cells.f
  let (g1g2Prime, z13g1g2) ← psiCanonicity cells.g1 z1g
  -- the NoteCommit decomposition + canonicity gates
  NoteCommit.DecomposeB.circuit
    { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
  NoteCommit.DecomposeD.circuit
    { d := cells.d, d0 := cells.d0, d1 := cells.d1, d2 := cells.d2, d3 := z1d }
  NoteCommit.DecomposeE.circuit { e := cells.e, e0 := cells.e0, e1 := cells.e1 }
  NoteCommit.DecomposeG.circuit { g := cells.g, g0 := cells.g0, g1 := cells.g1, g2 := z1g }
  NoteCommit.DecomposeH.circuit { h := cells.h, h0 := cells.h0, h1 := cells.h1 }
  NoteCommit.GdCanonicity.circuit
    { gdX := gdX, b0 := cells.b0, b1 := cells.b1, a := cells.a, aPrime := aPrime, z13A := z13a,
      z13APrime := z13aPrime }
  NoteCommit.PkdCanonicity.circuit
    { pkdX := pkdX, b3 := cells.b3, c := cells.c, d0 := cells.d0, b3CPrime := b3cPrime,
      z13C := z13c, z14B3CPrime := z14b3c }
  NoteCommit.ValueCanonicity.circuit { value := v, d2 := cells.d2, d3 := z1d, e0 := cells.e0 }
  NoteCommit.RhoCanonicity.circuit
    { rho := rho, e1 := cells.e1, f := cells.f, g0 := cells.g0, e1FPrime := e1fPrime, z13F := z13f,
      z14E1FPrime := z14e1f }
  NoteCommit.PsiCanonicity.circuit
    { psi := psi, h0 := cells.h0, g1 := cells.g1, h1 := cells.h1, g2 := z1g,
      g1G2Prime := g1g2Prime, z13G := z13g, z13G1G2Prime := z13g1g2 }
  return cm

def commitAndConstrain (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) (cells : MessageCells) :
    Circuit Ecc.Fp (Var Point Ecc.Fp) := do
  let out ← commitWithZs G Q hQ R input cells
  constrainCommitment input cells out

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) :
    Circuit Ecc.Fp (Var Point Ecc.Fp) := do
  let cells ← assignMessageCells input
  commitAndConstrain G Q hQ R input cells

instance assignSubpiecesExplicit (input : Var Input Ecc.Fp) :
    ExplicitCircuit (assignSubpieces input) := by
  unfold assignSubpieces
  infer_explicit_circuit

instance constrainYSubpiecesExplicit (input : Var Input Ecc.Fp) (subpieces : MessageSubpieces) :
    ExplicitCircuit (constrainYSubpieces input subpieces) := by
  unfold constrainYSubpieces
  infer_explicit_circuit

instance assignMessagePiecesExplicit (input : Var Input Ecc.Fp) (subpieces : MessageSubpieces) :
    ExplicitCircuit (assignMessagePieces input subpieces) := by
  unfold assignMessagePieces
  infer_explicit_circuit

instance assignMessageCellsExplicit (input : Var Input Ecc.Fp) :
    ExplicitCircuit (assignMessageCells input) := by
  unfold assignMessageCells
  infer_explicit_circuit

instance commitWithZsExplicit (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp)
    (cells : MessageCells) :
    ExplicitCircuit (commitWithZs G Q hQ R input cells) := by
  unfold commitWithZs
  infer_explicit_circuit

instance constrainCommitmentExplicit (input : Var Input Ecc.Fp) (cells : MessageCells)
    (out : Var (Sinsemilla.CommitDomain.WithZs.Output messagePieceRounds) Ecc.Fp) :
    ExplicitCircuit (constrainCommitment input cells out) := by
  unfold constrainCommitment
  infer_explicit_circuit

instance commitAndConstrainExplicit (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp)
    (cells : MessageCells) :
    ExplicitCircuit (commitAndConstrain G Q hQ R input cells) := by
  unfold commitAndConstrain
  infer_explicit_circuit

attribute [explicit_circuit_no_unfold] assignSubpieces constrainYSubpieces assignMessagePieces
  assignMessageCells commitAndConstrain commitWithZs constrainCommitment

@[circuit_norm] theorem assignSubpieces_localLength (input : Var Input Ecc.Fp) (offset : ℕ) :
    (assignSubpieces input).localLength offset = 20 := by
  unfold assignSubpieces
  simp only [circuit_norm]

@[circuit_norm] theorem constrainYSubpieces_localLength (input : Var Input Ecc.Fp)
    (subpieces : MessageSubpieces) (offset : ℕ) :
    (constrainYSubpieces input subpieces).localLength offset = 94 := by
  unfold constrainYSubpieces
  simp only [circuit_norm]

@[circuit_norm] theorem assignMessagePieces_localLength (input : Var Input Ecc.Fp)
    (subpieces : MessageSubpieces) (offset : ℕ) :
    (assignMessagePieces input subpieces).localLength offset = 8 := by
  unfold assignMessagePieces
  simp only [circuit_norm]

@[circuit_norm] theorem assignMessageCells_localLength (input : Var Input Ecc.Fp)
    (offset : ℕ) :
    (assignMessageCells input).localLength offset = 122 := by
  unfold assignMessageCells
  simp only [circuit_norm]

@[circuit_norm] theorem constrainCommitment_localLength (input : Var Input Ecc.Fp)
    (cells : MessageCells)
    (out : Var (Sinsemilla.CommitDomain.WithZs.Output messagePieceRounds) Ecc.Fp)
    (offset : ℕ) :
    (constrainCommitment input cells out).localLength offset = 62 := by
  unfold constrainCommitment
  simp only [circuit_norm, DecomposeB.circuit, DecomposeD.circuit, DecomposeE.circuit,
    DecomposeG.circuit, DecomposeH.circuit, GdCanonicity.circuit, PkdCanonicity.circuit,
    ValueCanonicity.circuit, RhoCanonicity.circuit, PsiCanonicity.circuit]

@[circuit_norm] theorem commitWithZs_localLength (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp)
    (cells : MessageCells) (offset : ℕ) :
    (commitWithZs G Q hQ R input cells).localLength offset = 1407 := by
  unfold commitWithZs
  simp only [circuit_norm, Sinsemilla.CommitDomain.WithZs.circuit]
  norm_num [messagePieceTailRounds, Chain.chainLength]

@[circuit_norm] theorem commitAndConstrain_localLength (G : Generators)
    (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (R : MulFixed.FixedBase)
    (input : Var Input Ecc.Fp) (cells : MessageCells) (offset : ℕ) :
    (commitAndConstrain G Q hQ R input cells).localLength offset = 1469 := by
  unfold commitAndConstrain
  simp only [circuit_norm]

instance mainExplicit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ExplicitCircuits (main G Q hQ R) := by
  infer_explicit_circuits

def mainOutput (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) (offset : ℕ) :
    Var Point Ecc.Fp :=
  let cells := (assignMessageCells input).output offset
  (commitAndConstrain G Q hQ R input cells).output
    (offset + (assignMessageCells input).localLength offset)

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    ElaboratedCircuit Ecc.Fp Input Point (main G Q hQ R) where
  localLength _ := 1591
  localLength_eq := by
    intro input offset
    unfold main
    simp only [circuit_norm]
  output := mainOutput G Q hQ R
  output_eq input offset := by
    unfold main mainOutput
    simp only [Circuit.output, Circuit.bind_def, Circuit.localLength]
  subcircuitsConsistent input offset :=
    (mainExplicit G Q hQ R).subcircuitsConsistent input offset
  channelsLawful input offset := by
    convert (mainExplicit G Q hQ R).channelsLawful input offset

/-- The note's seven field-element scalars, as `ℕ`, extracted from a circuit value.
`g_d`/`pk_d` contribute their `x` and the `ỹ` sign bit (`y mod 2`). -/
def noteScalars (input : Value Input Ecc.Fp) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let gdX : Ecc.Fp := input.gd.x
  let gdY : Ecc.Fp := input.gd.y
  let pkdX : Ecc.Fp := input.pkd.x
  let pkdY : Ecc.Fp := input.pkd.y
  let v : Ecc.Fp := input.value
  let rho : Ecc.Fp := input.rho
  let psi : Ecc.Fp := input.psi
  (gdX.val, gdY.val % 2, pkdX.val, pkdY.val % 2, v.val, rho.val, psi.val)

def proverNoteScalars (input : ProverValue Input Ecc.Fp) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let gdX : Ecc.Fp := input.gd.x
  let gdY : Ecc.Fp := input.gd.y
  let pkdX : Ecc.Fp := input.pkd.x
  let pkdY : Ecc.Fp := input.pkd.y
  let v : Ecc.Fp := input.value
  let rho : Ecc.Fp := input.rho
  let psi : Ecc.Fp := input.psi
  (gdX.val, gdY.val % 2, pkdX.val, pkdY.val % 2, v.val, rho.val, psi.val)

/-- `g_d` and `pk_d` enter the Halo2 gadget as already-assigned non-identity points. In
Clean's point model this is the on-curve half of `NonIdentityEccPoint`; identity is not
representable as an affine point in the source API at this boundary. -/
def Assumptions (input : Value Input Ecc.Fp) (_ : ProverData Ecc.Fp) : Prop :=
  Pallas.OnCurve input.gd.coords ∧ Pallas.OnCurve input.pkd.coords

/-- `cm` is the Orchard note commitment of the note `(g_d, pk_d, value, rho, psi)` with
randomness `rcm`: `cm = NoteCommit^Orchard_rcm(g★_d || pk★_d || v || rho || psi)`. The
message is the `Sinsemilla` hash of the canonical 109-chunk encoding (the canonicity
gates force the field inputs into that canonical bit-layout) translated by `[rcm] R`. -/
def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Ecc.Fp) (cm : Point Ecc.Fp) (_ : ProverData Ecc.Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := noteScalars input
  ∃ rcm : Fq, ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi)
      = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue rcm).coords

theorem spec_of_commitWithZs_spec (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (inputVar : Var Input Ecc.Fp) (input : Value Input Ecc.Fp) (cells : MessageCells)
    (commitOffset : ℕ) (cm : Point Ecc.Fp)
    (houtput : cm =
      (eval env ((commitWithZs G Q hQ R inputVar cells).output commitOffset)).point)
    (hcommit :
      let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
        { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
          r := inputVar.rcm }
      Sinsemilla.CommitDomain.WithZs.Spec G Q R 24 messagePieceTailRounds
        (eval env commitInput)
        (eval env ((commitWithZs G Q hQ R inputVar cells).output commitOffset)) env.data)
    (hchunks : ∀ chunks,
      let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
        { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
          r := inputVar.rcm }
      Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds (eval env commitInput).pieces chunks →
        chunks =
          let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := noteScalars input
          Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi) :
    Spec G Q R input cm env.data := by
  unfold Spec
  obtain ⟨chunks, r, hPC, _hZs, hfun⟩ := hcommit
  refine ⟨r, ?_⟩
  intro B hB
  have hc := hchunks chunks hPC
  simp only [noteScalars] at hc
  rw [← hc] at hB
  rw [houtput]
  exact hfun B hB

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve)
    (input : ProverValue Input Ecc.Fp) (_ : ProverData Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  Pallas.OnCurve input.gd.coords ∧
  Pallas.OnCurve input.pkd.coords ∧
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := proverNoteScalars input
  ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
    (Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Ecc.Fp) (cm : ProverValue Point Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := proverNoteScalars input
  ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi)
      = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue input.rcm).coords

/-- Split the commitment/gate phase into the Sinsemilla commit that exposes running sums
and the NoteCommit decomposition/canonicity gates that consume those sums. -/
theorem commitAndConstrain_soundness_constraints_iff (G : Generators)
    (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (R : MulFixed.FixedBase)
    (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp) (cells : MessageCells)
    (offset : ℕ) :
    ConstraintsHold.Soundness env ((commitAndConstrain G Q hQ R input cells).operations offset) ↔
      ConstraintsHold.Soundness env ((commitWithZs G Q hQ R input cells).operations offset) ∧
      ConstraintsHold.Soundness env
        ((constrainCommitment input cells ((commitWithZs G Q hQ R input cells).output offset)).operations
          (offset + (commitWithZs G Q hQ R input cells).localLength offset)) := by
  unfold commitAndConstrain ConstraintsHold.Soundness
  rw [Circuit.bind_forAllNoOffset]

theorem commitAndConstrain_requirements_iff (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (cells : MessageCells) (offset : ℕ) :
    Operations.Requirements env ((commitAndConstrain G Q hQ R input cells).operations offset) ↔
      Operations.Requirements env ((commitWithZs G Q hQ R input cells).operations offset) ∧
      Operations.Requirements env
        ((constrainCommitment input cells ((commitWithZs G Q hQ R input cells).output offset)).operations
          (offset + (commitWithZs G Q hQ R input cells).localLength offset)) := by
  unfold commitAndConstrain Operations.Requirements
  rw [Circuit.bind_forAllNoOffset]

theorem commitAndConstrain_completeness_constraints_iff (G : Generators)
    (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (R : MulFixed.FixedBase)
    (env : ProverEnvironment Ecc.Fp) (input : Var Input Ecc.Fp) (cells : MessageCells)
    (offset : ℕ) :
    ConstraintsHold.Completeness env
        ((commitAndConstrain G Q hQ R input cells).operations offset) ↔
      ConstraintsHold.Completeness env ((commitWithZs G Q hQ R input cells).operations offset) ∧
      ConstraintsHold.Completeness env
        ((constrainCommitment input cells ((commitWithZs G Q hQ R input cells).output offset)).operations
          (offset + (commitWithZs G Q hQ R input cells).localLength offset)) := by
  unfold commitAndConstrain ConstraintsHold.Completeness
  rw [Circuit.bind_forAllNoOffset]

theorem commitAndConstrain_usesLocalWitnesses_iff (G : Generators)
    (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (R : MulFixed.FixedBase)
    (env : ProverEnvironment Ecc.Fp) (input : Var Input Ecc.Fp) (cells : MessageCells)
    (offset : ℕ) :
    env.UsesLocalWitnessesCompleteness offset
        ((commitAndConstrain G Q hQ R input cells).operations offset) ↔
      env.UsesLocalWitnessesCompleteness offset
        ((commitWithZs G Q hQ R input cells).operations offset) ∧
      env.UsesLocalWitnessesCompleteness
        (offset + (commitWithZs G Q hQ R input cells).localLength offset)
        ((constrainCommitment input cells ((commitWithZs G Q hQ R input cells).output offset)).operations
          (offset + (commitWithZs G Q hQ R input cells).localLength offset)) := by
  unfold commitAndConstrain
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses]

theorem commitWithZs_spec_of_soundness (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (cells : MessageCells) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((commitWithZs G Q hQ R input cells).operations offset)) :
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    Sinsemilla.CommitDomain.WithZs.Spec G Q R 24 messagePieceTailRounds
      (eval env commitInput)
      (eval env ((commitWithZs G Q hQ R input cells).output offset)) env.data := by
  let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
    { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
      r := input.rcm }
  change ConstraintsHold.Soundness env
    ([.subcircuit ((Sinsemilla.CommitDomain.WithZs.circuit G Q hQ R 24 messagePieceTailRounds).toSubcircuit
      offset commitInput)]) at h
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset,
    GeneralFormalCircuit.WithHint.toSubcircuit_soundness] at h
  exact h.1 trivial

private theorem formalAssertion_spec_of_soundness {Row : TypeMap} [ProvableType Row]
    (circuit : FormalAssertion Ecc.Fp Row) (env : Environment Ecc.Fp)
    (row : Var Row Ecc.Fp) (offset : ℕ)
    (hAssumptions : circuit.Assumptions (eval env row))
    (h : ConstraintsHold.Soundness env ((assertion circuit row).operations offset)) :
    circuit.Spec (eval env row) := by
  simp only [ConstraintsHold.Soundness, assertion, Circuit.operations,
    Operations.forAllNoOffset, FormalAssertion.toSubcircuit_soundness] at h
  exact h.1 hAssumptions

private theorem withHint_spec_of_soundness {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint Ecc.Fp Input Output)
    (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp) (offset : ℕ)
    (hAssumptions : circuit.Assumptions (eval env input) env.data)
    (h : ConstraintsHold.Soundness env ((circuit input).operations offset)) :
    circuit.Spec (eval env input) (eval env (circuit.output input offset)) env.data := by
  simp only [ConstraintsHold.Soundness, subcircuitWithHintAssertion, Circuit.operations,
    Operations.forAllNoOffset, GeneralFormalCircuit.WithHint.toSubcircuit_soundness] at h
  exact h.1 hAssumptions

private theorem copyCheck14_zlast_zero_val_lt (env : Environment Ecc.Fp)
    (element : Var field Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env
      ((Utilities.LookupRangeCheck.CopyCheck.circuit 14 element).operations offset))
    (hzLast : (eval env ((Utilities.LookupRangeCheck.CopyCheck.circuit 14).output element offset))[14]
        = 0) :
    (show Ecc.Fp from eval env element).val < 2 ^ (K * 14) := by
  let zs : fields 15 Ecc.Fp :=
    eval env ((Utilities.LookupRangeCheck.CopyCheck.circuit 14).output element offset)
  let f : ℕ → Ecc.Fp := fun i => if hi : i < 15 then zs[i]'hi else 0
  have hspec := withHint_spec_of_soundness
    (Utilities.LookupRangeCheck.CopyCheck.circuit 14) env element offset trivial h
  simp only at hspec
  rcases hspec with ⟨hz0, hchain⟩
  have hsteps :
      ∀ i, i < 14 →
        ∃ w : ℕ, w < 2 ^ K ∧ f i = 2 ^ K * f (i + 1) + (w : Ecc.Fp) := by
    intro i hi
    obtain ⟨w, hw, hstep⟩ := hchain ⟨i, hi⟩
    refine ⟨w, hw, ?_⟩
    dsimp only [f]
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact hstep
  obtain ⟨lo, hlo, heq⟩ := chain_telescope f 14 hsteps
  have hf0 : f 0 = (show Ecc.Fp from eval env element) := by
    dsimp only [f, zs]
    rw [dif_pos (by omega), hz0]
  have hf14 : f 14 = 0 := by
    dsimp only [f, zs]
    rw [dif_pos (by omega)]
    exact hzLast
  rw [hf0, hf14, mul_zero, _root_.add_zero] at heq
  have hCard : lo < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    exact lt_trans hlo (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [heq, ZMod.val_natCast_of_lt hCard]
  exact hlo

private theorem witnessShort_spec_of_soundness (env : Environment Ecc.Fp)
    (src : Var field Ecc.Fp) (start numBits : ℕ)
    (hNumBits : numBits ≤ Utilities.LookupRangeCheck.K) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((witnessShort src start numBits hNumBits).operations offset)) :
    (show Ecc.Fp from
      eval env ((witnessShort src start numBits hNumBits).output offset)).val < 2 ^ numBits := by
  unfold witnessShort at h ⊢
  exact withHint_spec_of_soundness
    (Utilities.LookupRangeCheck.WitnessShort.circuit start numBits hNumBits) env
    (fun env => bitrangeSubset (Expression.eval env src) start numBits) offset trivial h

theorem assignSubpieces_short_range_specs (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((assignSubpieces input).operations offset)) :
    let subpieces := (assignSubpieces input).output offset
    (show Ecc.Fp from eval env subpieces.b0).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env subpieces.b3).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env subpieces.d2).val < 2 ^ 8 ∧
      (show Ecc.Fp from eval env subpieces.e0).val < 2 ^ 6 ∧
      (show Ecc.Fp from eval env subpieces.e1).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env subpieces.g1).val < 2 ^ 9 ∧
      (show Ecc.Fp from eval env subpieces.h0).val < 2 ^ 5 := by
  unfold assignSubpieces at h
  simp only [ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset] at h
  exact ⟨
    witnessShort_spec_of_soundness env input.gd.x 250 4 (by norm_num [K]) _ h.1,
    witnessShort_spec_of_soundness env input.pkd.x 0 4 (by norm_num [K]) _ h.2.1,
    witnessShort_spec_of_soundness env input.value 0 8 (by norm_num [K]) _ h.2.2.1,
    witnessShort_spec_of_soundness env input.value 58 6 (by norm_num [K]) _ h.2.2.2.1,
    witnessShort_spec_of_soundness env input.rho 0 4 (by norm_num [K]) _ h.2.2.2.2.1,
    witnessShort_spec_of_soundness env input.psi 0 9 (by norm_num [K]) _ h.2.2.2.2.2.1,
    witnessShort_spec_of_soundness env input.psi 249 5 (by norm_num [K]) _ h.2.2.2.2.2.2.1⟩

theorem assignMessageCells_short_range_specs (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((assignMessageCells input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    (show Ecc.Fp from eval env cells.b0).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env cells.b3).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env cells.d2).val < 2 ^ 8 ∧
      (show Ecc.Fp from eval env cells.e0).val < 2 ^ 6 ∧
      (show Ecc.Fp from eval env cells.e1).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env cells.g1).val < 2 ^ 9 ∧
      (show Ecc.Fp from eval env cells.h0).val < 2 ^ 5 := by
  unfold assignMessageCells at h
  simp only [ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset] at h
  have hs := assignSubpieces_short_range_specs env input offset h.1
  simpa only [assignMessageCells, assignMessagePieces, constrainYSubpieces, Circuit.output,
    Circuit.bind_def] using hs

theorem constrainCommitment_decomposeB_spec (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (cells : MessageCells)
    (out : Var (Sinsemilla.CommitDomain.WithZs.Output messagePieceRounds) Ecc.Fp)
    (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((constrainCommitment input cells out).operations offset)) :
    let row : Var NoteCommit.DecomposeB.Row Ecc.Fp :=
      { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
    NoteCommit.DecomposeB.Spec (eval env row) := by
  let row : Var NoteCommit.DecomposeB.Row Ecc.Fp :=
    { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
  unfold constrainCommitment at h
  simp only [ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset,
    DecomposeB.circuit] at h
  exact formalAssertion_spec_of_soundness NoteCommit.DecomposeB.circuit env row _ trivial
    h.2.2.2.2.1

theorem constrainCommitment_decompose_specs (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (cells : MessageCells)
    (out : Var (Sinsemilla.CommitDomain.WithZs.Output messagePieceRounds) Ecc.Fp)
    (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((constrainCommitment input cells out).operations offset)) :
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
    let rowB : Var NoteCommit.DecomposeB.Row Ecc.Fp :=
      { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
    let rowD : Var NoteCommit.DecomposeD.Row Ecc.Fp :=
      { d := cells.d, d0 := cells.d0, d1 := cells.d1, d2 := cells.d2, d3 := z1d }
    let rowE : Var NoteCommit.DecomposeE.Row Ecc.Fp :=
      { e := cells.e, e0 := cells.e0, e1 := cells.e1 }
    let rowG : Var NoteCommit.DecomposeG.Row Ecc.Fp :=
      { g := cells.g, g0 := cells.g0, g1 := cells.g1, g2 := z1g }
    let rowH : Var NoteCommit.DecomposeH.Row Ecc.Fp :=
      { h := cells.h, h0 := cells.h0, h1 := cells.h1 }
    NoteCommit.DecomposeB.Spec (eval env rowB) ∧
      NoteCommit.DecomposeD.Spec (eval env rowD) ∧
      NoteCommit.DecomposeE.Spec (eval env rowE) ∧
      NoteCommit.DecomposeG.Spec (eval env rowG) ∧
      NoteCommit.DecomposeH.Spec (eval env rowH) := by
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
  let rowB : Var NoteCommit.DecomposeB.Row Ecc.Fp :=
    { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
  let rowD : Var NoteCommit.DecomposeD.Row Ecc.Fp :=
    { d := cells.d, d0 := cells.d0, d1 := cells.d1, d2 := cells.d2, d3 := z1d }
  let rowE : Var NoteCommit.DecomposeE.Row Ecc.Fp :=
    { e := cells.e, e0 := cells.e0, e1 := cells.e1 }
  let rowG : Var NoteCommit.DecomposeG.Row Ecc.Fp :=
    { g := cells.g, g0 := cells.g0, g1 := cells.g1, g2 := z1g }
  let rowH : Var NoteCommit.DecomposeH.Row Ecc.Fp :=
    { h := cells.h, h0 := cells.h0, h1 := cells.h1 }
  unfold constrainCommitment at h
  simp only [ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset,
    DecomposeB.circuit, DecomposeD.circuit, DecomposeE.circuit, DecomposeG.circuit,
    DecomposeH.circuit] at h
  exact ⟨
    formalAssertion_spec_of_soundness NoteCommit.DecomposeB.circuit env rowB _ trivial
      h.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.DecomposeD.circuit env rowD _ trivial
      h.2.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.DecomposeE.circuit env rowE _ trivial
      h.2.2.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.DecomposeG.circuit env rowG _ trivial
      h.2.2.2.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.DecomposeH.circuit env rowH _ trivial
      h.2.2.2.2.2.2.2.2.1⟩

theorem constrainCommitment_canonicity_specs (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (cells : MessageCells)
    (out : Var (Sinsemilla.CommitDomain.WithZs.Output messagePieceRounds) Ecc.Fp)
    (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((constrainCommitment input cells out).operations offset)) :
    let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
    let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
    let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
    let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]
    let aBounds := (canonBitshift130 cells.a).output offset
    let pkdOffset := offset + (canonBitshift130 cells.a).localLength offset
    let b3cBounds := (pkdXCanonicity cells.b3 cells.c).output pkdOffset
    let rhoOffset := pkdOffset + (pkdXCanonicity cells.b3 cells.c).localLength pkdOffset
    let e1fBounds := (rhoCanonicity cells.e1 cells.f).output rhoOffset
    let psiOffset := rhoOffset + (rhoCanonicity cells.e1 cells.f).localLength rhoOffset
    let g1g2Bounds := (psiCanonicity cells.g1 z1g).output psiOffset
    let rowGd : Var NoteCommit.GdCanonicity.Row Ecc.Fp :=
      { gdX := input.gd.x, b0 := cells.b0, b1 := cells.b1, a := cells.a,
        aPrime := aBounds.1, z13A := z13a, z13APrime := aBounds.2 }
    let rowPkd : Var NoteCommit.PkdCanonicity.Row Ecc.Fp :=
      { pkdX := input.pkd.x, b3 := cells.b3, c := cells.c, d0 := cells.d0,
        b3CPrime := b3cBounds.1, z13C := z13c, z14B3CPrime := b3cBounds.2 }
    let rowValue : Var NoteCommit.ValueCanonicity.Row Ecc.Fp :=
      { value := input.value, d2 := cells.d2, d3 := z1d, e0 := cells.e0 }
    let rowRho : Var NoteCommit.RhoCanonicity.Row Ecc.Fp :=
      { rho := input.rho, e1 := cells.e1, f := cells.f, g0 := cells.g0,
        e1FPrime := e1fBounds.1, z13F := z13f, z14E1FPrime := e1fBounds.2 }
    let rowPsi : Var NoteCommit.PsiCanonicity.Row Ecc.Fp :=
      { psi := input.psi, h0 := cells.h0, g1 := cells.g1, h1 := cells.h1, g2 := z1g,
        g1G2Prime := g1g2Bounds.1, z13G := z13g, z13G1G2Prime := g1g2Bounds.2 }
    NoteCommit.GdCanonicity.Spec (eval env rowGd) ∧
      NoteCommit.PkdCanonicity.Spec (eval env rowPkd) ∧
      NoteCommit.ValueCanonicity.Spec (eval env rowValue) ∧
      NoteCommit.RhoCanonicity.Spec (eval env rowRho) ∧
      NoteCommit.PsiCanonicity.Spec (eval env rowPsi) := by
  let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
  let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
  let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
  let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]
  let aBounds := (canonBitshift130 cells.a).output offset
  let pkdOffset := offset + (canonBitshift130 cells.a).localLength offset
  let b3cBounds := (pkdXCanonicity cells.b3 cells.c).output pkdOffset
  let rhoOffset := pkdOffset + (pkdXCanonicity cells.b3 cells.c).localLength pkdOffset
  let e1fBounds := (rhoCanonicity cells.e1 cells.f).output rhoOffset
  let psiOffset := rhoOffset + (rhoCanonicity cells.e1 cells.f).localLength rhoOffset
  let g1g2Bounds := (psiCanonicity cells.g1 z1g).output psiOffset
  let rowGd : Var NoteCommit.GdCanonicity.Row Ecc.Fp :=
    { gdX := input.gd.x, b0 := cells.b0, b1 := cells.b1, a := cells.a,
      aPrime := aBounds.1, z13A := z13a, z13APrime := aBounds.2 }
  let rowPkd : Var NoteCommit.PkdCanonicity.Row Ecc.Fp :=
    { pkdX := input.pkd.x, b3 := cells.b3, c := cells.c, d0 := cells.d0,
      b3CPrime := b3cBounds.1, z13C := z13c, z14B3CPrime := b3cBounds.2 }
  let rowValue : Var NoteCommit.ValueCanonicity.Row Ecc.Fp :=
    { value := input.value, d2 := cells.d2, d3 := z1d, e0 := cells.e0 }
  let rowRho : Var NoteCommit.RhoCanonicity.Row Ecc.Fp :=
    { rho := input.rho, e1 := cells.e1, f := cells.f, g0 := cells.g0,
      e1FPrime := e1fBounds.1, z13F := z13f, z14E1FPrime := e1fBounds.2 }
  let rowPsi : Var NoteCommit.PsiCanonicity.Row Ecc.Fp :=
    { psi := input.psi, h0 := cells.h0, g1 := cells.g1, h1 := cells.h1, g2 := z1g,
      g1G2Prime := g1g2Bounds.1, z13G := z13g, z13G1G2Prime := g1g2Bounds.2 }
  unfold constrainCommitment at h
  simp only [ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset,
    GdCanonicity.circuit, PkdCanonicity.circuit, ValueCanonicity.circuit,
    RhoCanonicity.circuit, PsiCanonicity.circuit] at h
  exact ⟨
    formalAssertion_spec_of_soundness NoteCommit.GdCanonicity.circuit env rowGd _ trivial
      h.2.2.2.2.2.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.PkdCanonicity.circuit env rowPkd _ trivial
      h.2.2.2.2.2.2.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.ValueCanonicity.circuit env rowValue _ trivial
      h.2.2.2.2.2.2.2.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.RhoCanonicity.circuit env rowRho _ trivial
      h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    formalAssertion_spec_of_soundness NoteCommit.PsiCanonicity.circuit env rowPsi _ trivial
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem commitAndConstrain_output_eq (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp)
    (cells : MessageCells) (offset : ℕ) :
    (commitAndConstrain G Q hQ R input cells).output offset =
      ((commitWithZs G Q hQ R input cells).output offset).point := by
  unfold commitAndConstrain constrainCommitment
  simp only [Circuit.output, Circuit.bind_def]

theorem main_output_eq_commitWithZs_point (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) (offset : ℕ) :
    (main G Q hQ R input).output offset =
      let cells := (assignMessageCells input).output offset
      let commitOffset := offset + (assignMessageCells input).localLength offset
      ((commitWithZs G Q hQ R input cells).output commitOffset).point := by
  unfold main commitAndConstrain constrainCommitment
  simp only [Circuit.output, Circuit.bind_def]

/-- Split the top-level source-shaped `main` soundness constraints into the message-cell
assignment phase and the commitment/gate phase. This is intentionally used instead of
globally unfolding `main` in `circuit_proof_start`, which expands the whole gadget. -/
theorem main_soundness_constraints_iff (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ) :
    ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset) ↔
      ConstraintsHold.Soundness env ((assignMessageCells input).operations offset) ∧
      ConstraintsHold.Soundness env
        ((commitAndConstrain G Q hQ R input ((assignMessageCells input).output offset)).operations
          (offset + (assignMessageCells input).localLength offset)) := by
  unfold main ConstraintsHold.Soundness
  rw [Circuit.bind_forAllNoOffset]

theorem main_requirements_iff (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp)
    (offset : ℕ) :
    Operations.Requirements env ((main G Q hQ R input).operations offset) ↔
      Operations.Requirements env ((assignMessageCells input).operations offset) ∧
      Operations.Requirements env
        ((commitAndConstrain G Q hQ R input ((assignMessageCells input).output offset)).operations
          (offset + (assignMessageCells input).localLength offset)) := by
  unfold main Operations.Requirements
  rw [Circuit.bind_forAllNoOffset]

theorem main_completeness_constraints_iff (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : ProverEnvironment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ) :
    ConstraintsHold.Completeness env ((main G Q hQ R input).operations offset) ↔
      ConstraintsHold.Completeness env ((assignMessageCells input).operations offset) ∧
      ConstraintsHold.Completeness env
        ((commitAndConstrain G Q hQ R input ((assignMessageCells input).output offset)).operations
          (offset + (assignMessageCells input).localLength offset)) := by
  unfold main ConstraintsHold.Completeness
  rw [Circuit.bind_forAllNoOffset]

theorem main_usesLocalWitnesses_iff (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : ProverEnvironment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ) :
    env.UsesLocalWitnessesCompleteness offset ((main G Q hQ R input).operations offset) ↔
      env.UsesLocalWitnessesCompleteness offset ((assignMessageCells input).operations offset) ∧
      env.UsesLocalWitnessesCompleteness (offset + (assignMessageCells input).localLength offset)
        ((commitAndConstrain G Q hQ R input ((assignMessageCells input).output offset)).operations
          (offset + (assignMessageCells input).localLength offset)) := by
  unfold main
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses]

theorem main_commitWithZs_spec_of_soundness (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    Sinsemilla.CommitDomain.WithZs.Spec G Q R 24 messagePieceTailRounds
      (eval env commitInput)
      (eval env ((commitWithZs G Q hQ R input cells).output commitOffset)) env.data := by
  rw [main_soundness_constraints_iff] at h
  rcases h with ⟨_, h_commit⟩
  rw [commitAndConstrain_soundness_constraints_iff] at h_commit
  exact commitWithZs_spec_of_soundness G Q hQ R env input ((assignMessageCells input).output offset)
    (offset + (assignMessageCells input).localLength offset) h_commit.1

theorem main_commitWithZs_pieceChunks_zsFacts_of_soundness (G : Generators)
    (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (R : MulFixed.FixedBase)
    (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    ∃ chunks : List ℕ,
      Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds (eval env commitInput).pieces chunks ∧
      Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds (chunks)
        (eval env out).zs := by
  have hcommit := main_commitWithZs_spec_of_soundness G Q hQ R env input offset h
  obtain ⟨chunks, _r, hPC, hZs, _hfun⟩ := hcommit
  refine ⟨chunks, ?_, ?_⟩
  · simpa only [messagePieceRounds] using hPC
  · simpa only [messagePieceRounds] using hZs

theorem main_pieceChunks_digits_of_soundness (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    ∃ chunks : List ℕ,
    ∃ msA msB msC msD msE msF msG msH : ℕ → ℕ,
      Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds (eval env commitInput).pieces chunks ∧
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
  obtain ⟨chunks, hPC, _hZs⟩ :=
    main_commitWithZs_pieceChunks_zsFacts_of_soundness G Q hQ R env input offset h
  obtain ⟨msA, msB, msC, msD, msE, msF, msG, msH,
    hA, hB, hC, hD, hE, hF, hG, hH, hchunks⟩ :=
    pieceChunks_messagePieceRounds_chunks hPC
  exact ⟨chunks, msA, msB, msC, msD, msE, msF, msG, msH, hPC,
    hA, hB, hC, hD, hE, hF, hG, hH, hchunks⟩

theorem main_pieceChunks_flat_chunks_of_soundness (G : Generators)
    (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (R : MulFixed.FixedBase)
    (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    ∃ chunks : List ℕ,
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
  obtain ⟨chunks, msA, msB, msC, msD, msE, msF, msG, msH, _hPC,
    hA, hB, hC, hD, hE, hF, hG, hH, hchunks⟩ :=
    main_pieceChunks_digits_of_soundness G Q hQ R env input offset h
  exact ⟨chunks, msA, msB, msC, msD, msE, msF, msG, msH,
    hA, hB, hC, hD, hE, hF, hG, hH, hchunks⟩

theorem main_assignMessageCells_short_range_specs (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    (show Ecc.Fp from eval env cells.b0).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env cells.b3).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env cells.d2).val < 2 ^ 8 ∧
      (show Ecc.Fp from eval env cells.e0).val < 2 ^ 6 ∧
      (show Ecc.Fp from eval env cells.e1).val < 2 ^ 4 ∧
      (show Ecc.Fp from eval env cells.g1).val < 2 ^ 9 ∧
      (show Ecc.Fp from eval env cells.h0).val < 2 ^ 5 := by
  rw [main_soundness_constraints_iff] at h
  exact assignMessageCells_short_range_specs env input offset h.1

theorem main_constrainCommitment_decompose_specs (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
    let rowB : Var NoteCommit.DecomposeB.Row Ecc.Fp :=
      { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
    let rowD : Var NoteCommit.DecomposeD.Row Ecc.Fp :=
      { d := cells.d, d0 := cells.d0, d1 := cells.d1, d2 := cells.d2, d3 := z1d }
    let rowE : Var NoteCommit.DecomposeE.Row Ecc.Fp :=
      { e := cells.e, e0 := cells.e0, e1 := cells.e1 }
    let rowG : Var NoteCommit.DecomposeG.Row Ecc.Fp :=
      { g := cells.g, g0 := cells.g0, g1 := cells.g1, g2 := z1g }
    let rowH : Var NoteCommit.DecomposeH.Row Ecc.Fp :=
      { h := cells.h, h0 := cells.h0, h1 := cells.h1 }
    NoteCommit.DecomposeB.Spec (eval env rowB) ∧
      NoteCommit.DecomposeD.Spec (eval env rowD) ∧
      NoteCommit.DecomposeE.Spec (eval env rowE) ∧
      NoteCommit.DecomposeG.Spec (eval env rowG) ∧
      NoteCommit.DecomposeH.Spec (eval env rowH) := by
  rw [main_soundness_constraints_iff] at h
  rcases h with ⟨_, h_commit⟩
  rw [commitAndConstrain_soundness_constraints_iff] at h_commit
  exact constrainCommitment_decompose_specs env input ((assignMessageCells input).output offset)
    ((commitWithZs G Q hQ R input ((assignMessageCells input).output offset)).output
      (offset + (assignMessageCells input).localLength offset))
    (offset + (assignMessageCells input).localLength offset +
      (commitWithZs G Q hQ R input ((assignMessageCells input).output offset)).localLength
        (offset + (assignMessageCells input).localLength offset))
    h_commit.2

theorem main_constrainCommitment_canonicity_specs (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
    let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
    let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
    let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]
    let gateOffset := commitOffset + (commitWithZs G Q hQ R input cells).localLength commitOffset
    let aBounds := (canonBitshift130 cells.a).output gateOffset
    let pkdOffset := gateOffset + (canonBitshift130 cells.a).localLength gateOffset
    let b3cBounds := (pkdXCanonicity cells.b3 cells.c).output pkdOffset
    let rhoOffset := pkdOffset + (pkdXCanonicity cells.b3 cells.c).localLength pkdOffset
    let e1fBounds := (rhoCanonicity cells.e1 cells.f).output rhoOffset
    let psiOffset := rhoOffset + (rhoCanonicity cells.e1 cells.f).localLength rhoOffset
    let g1g2Bounds := (psiCanonicity cells.g1 z1g).output psiOffset
    let rowGd : Var NoteCommit.GdCanonicity.Row Ecc.Fp :=
      { gdX := input.gd.x, b0 := cells.b0, b1 := cells.b1, a := cells.a,
        aPrime := aBounds.1, z13A := z13a, z13APrime := aBounds.2 }
    let rowPkd : Var NoteCommit.PkdCanonicity.Row Ecc.Fp :=
      { pkdX := input.pkd.x, b3 := cells.b3, c := cells.c, d0 := cells.d0,
        b3CPrime := b3cBounds.1, z13C := z13c, z14B3CPrime := b3cBounds.2 }
    let rowValue : Var NoteCommit.ValueCanonicity.Row Ecc.Fp :=
      { value := input.value, d2 := cells.d2, d3 := z1d, e0 := cells.e0 }
    let rowRho : Var NoteCommit.RhoCanonicity.Row Ecc.Fp :=
      { rho := input.rho, e1 := cells.e1, f := cells.f, g0 := cells.g0,
        e1FPrime := e1fBounds.1, z13F := z13f, z14E1FPrime := e1fBounds.2 }
    let rowPsi : Var NoteCommit.PsiCanonicity.Row Ecc.Fp :=
      { psi := input.psi, h0 := cells.h0, g1 := cells.g1, h1 := cells.h1, g2 := z1g,
        g1G2Prime := g1g2Bounds.1, z13G := z13g, z13G1G2Prime := g1g2Bounds.2 }
    NoteCommit.GdCanonicity.Spec (eval env rowGd) ∧
      NoteCommit.PkdCanonicity.Spec (eval env rowPkd) ∧
      NoteCommit.ValueCanonicity.Spec (eval env rowValue) ∧
      NoteCommit.RhoCanonicity.Spec (eval env rowRho) ∧
      NoteCommit.PsiCanonicity.Spec (eval env rowPsi) := by
  rw [main_soundness_constraints_iff] at h
  rcases h with ⟨_, h_commit⟩
  rw [commitAndConstrain_soundness_constraints_iff] at h_commit
  exact constrainCommitment_canonicity_specs env input ((assignMessageCells input).output offset)
    ((commitWithZs G Q hQ R input ((assignMessageCells input).output offset)).output
      (offset + (assignMessageCells input).localLength offset))
    (offset + (assignMessageCells input).localLength offset +
      (commitWithZs G Q hQ R input ((assignMessageCells input).output offset)).localLength
        (offset + (assignMessageCells input).localLength offset))
    h_commit.2

theorem main_message_piece_decomposition_facts (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
    (NoteCommit.IsBool (eval env cells.b1) ∧
      NoteCommit.IsBool (eval env cells.b2) ∧
      eval env cells.b =
        eval env cells.b0 + eval env cells.b1 * 16 + eval env cells.b2 * 32 +
          eval env cells.b3 * 64) ∧
      (NoteCommit.IsBool (eval env cells.d0) ∧
        NoteCommit.IsBool (eval env cells.d1) ∧
        eval env cells.d =
          eval env cells.d0 + eval env cells.d1 * 2 + eval env cells.d2 * 4 +
            eval env z1d * 1024) ∧
      eval env cells.e = eval env cells.e0 + eval env cells.e1 * 64 ∧
      (NoteCommit.IsBool (eval env cells.g0) ∧
        eval env cells.g =
          eval env cells.g0 + eval env cells.g1 * 2 + eval env z1g * 1024) ∧
      NoteCommit.IsBool (eval env cells.h1) ∧
      eval env cells.h = eval env cells.h0 + eval env cells.h1 * 32 := by
  have hs := main_constrainCommitment_decompose_specs G Q hQ R env input offset h
  simpa only [circuit_norm, NoteCommit.DecomposeB.Spec, NoteCommit.DecomposeD.Spec,
    NoteCommit.DecomposeE.Spec, NoteCommit.DecomposeG.Spec, NoteCommit.DecomposeH.Spec]
    using hs

theorem main_input_canonicity_facts (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
    let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
    let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
    let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]
    let gateOffset := commitOffset + (commitWithZs G Q hQ R input cells).localLength commitOffset
    let aBounds := (canonBitshift130 cells.a).output gateOffset
    let pkdOffset := gateOffset + (canonBitshift130 cells.a).localLength gateOffset
    let b3cBounds := (pkdXCanonicity cells.b3 cells.c).output pkdOffset
    let rhoOffset := pkdOffset + (pkdXCanonicity cells.b3 cells.c).localLength pkdOffset
    let e1fBounds := (rhoCanonicity cells.e1 cells.f).output rhoOffset
    let psiOffset := rhoOffset + (rhoCanonicity cells.e1 cells.f).localLength rhoOffset
    let g1g2Bounds := (psiCanonicity cells.g1 z1g).output psiOffset
    (eval env input.gd.x =
        eval env cells.a + eval env cells.b0 * OfNat.ofNat (2 ^ 250) +
          eval env cells.b1 * OfNat.ofNat (2 ^ 254) ∧
      eval env aBounds.1 = eval env cells.a + OfNat.ofNat (2 ^ 130) - NoteCommit.tP ∧
      (eval env cells.b1 = 0 ∨ eval env cells.b0 = 0) ∧
      (eval env cells.b1 = 0 ∨ eval env z13a = 0) ∧
      (eval env cells.b1 = 0 ∨ eval env aBounds.2 = 0)) ∧
      (eval env input.pkd.x =
          eval env cells.b3 + eval env cells.c * 16 +
            eval env cells.d0 * OfNat.ofNat (2 ^ 254) ∧
        eval env b3cBounds.1 =
          eval env cells.b3 + eval env cells.c * 16 + OfNat.ofNat (2 ^ 140) -
            NoteCommit.tP ∧
        (eval env cells.d0 = 0 ∨ eval env z13c = 0) ∧
        (eval env cells.d0 = 0 ∨ eval env b3cBounds.2 = 0)) ∧
      eval env input.value =
        eval env cells.d2 + eval env z1d * 256 +
          eval env cells.e0 * 288230376151711744 ∧
      (eval env input.rho =
          eval env cells.e1 + eval env cells.f * 16 +
            eval env cells.g0 * OfNat.ofNat (2 ^ 254) ∧
        eval env e1fBounds.1 =
          eval env cells.e1 + eval env cells.f * 16 + OfNat.ofNat (2 ^ 140) -
            NoteCommit.tP ∧
        (eval env cells.g0 = 0 ∨ eval env z13f = 0) ∧
        (eval env cells.g0 = 0 ∨ eval env e1fBounds.2 = 0)) ∧
      (eval env input.psi =
          eval env cells.g1 + eval env z1g * 512 +
            eval env cells.h0 * OfNat.ofNat (2 ^ 249) +
            eval env cells.h1 * OfNat.ofNat (2 ^ 254) ∧
        eval env g1g2Bounds.1 =
          eval env cells.g1 + eval env z1g * 512 + OfNat.ofNat (2 ^ 130) -
            NoteCommit.tP ∧
        (eval env cells.h1 = 0 ∨ eval env cells.h0 = 0) ∧
        (eval env cells.h1 = 0 ∨ eval env z13g = 0) ∧
        (eval env cells.h1 = 0 ∨ eval env g1g2Bounds.2 = 0)) := by
  have hs := main_constrainCommitment_canonicity_specs G Q hQ R env input offset h
  simpa only [circuit_norm, NoteCommit.GdCanonicity.Spec, NoteCommit.PkdCanonicity.Spec,
    NoteCommit.ValueCanonicity.Spec, NoteCommit.RhoCanonicity.Spec,
    NoteCommit.PsiCanonicity.Spec] using hs

theorem main_one_word_piece_bounds (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    (show Ecc.Fp from eval env cells.b).val < 2 ^ K ∧
      (show Ecc.Fp from eval env cells.e).val < 2 ^ K ∧
      (show Ecc.Fp from eval env cells.h).val < 2 ^ K := by
  have hrange := main_assignMessageCells_short_range_specs G Q hQ R env input offset h
  have hdecomp := main_message_piece_decomposition_facts G Q hQ R env input offset h
  simp only at hrange hdecomp ⊢
  rcases hrange with ⟨hb0, hb3, _hd2, he0, he1, _hg1, hh0⟩
  rcases hdecomp with
    ⟨⟨hb1, hb2, hB⟩, _hD, hE, _hG, hh1, hH⟩
  exact ⟨
    decomposeB_value_lt hb0 hb1 hb2 hb3 hB,
    decomposeE_value_lt he0 he1 hE,
    decomposeH_value_lt hh0 hh1 hH⟩

theorem input_field_255_bounds (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp) :
    (show Ecc.Fp from eval env input.gd.x).val < 2 ^ 255 ∧
      (show Ecc.Fp from eval env input.pkd.x).val < 2 ^ 255 ∧
      (show Ecc.Fp from eval env input.rho).val < 2 ^ 255 ∧
      (show Ecc.Fp from eval env input.psi).val < 2 ^ 255 := by
  have hp : CompElliptic.Fields.Pasta.PALLAS_BASE_CARD < 2 ^ 255 := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  exact ⟨
    lt_trans (ZMod.val_lt (show Ecc.Fp from eval env input.gd.x)) hp,
    lt_trans (ZMod.val_lt (show Ecc.Fp from eval env input.pkd.x)) hp,
    lt_trans (ZMod.val_lt (show Ecc.Fp from eval env input.rho)) hp,
    lt_trans (ZMod.val_lt (show Ecc.Fp from eval env input.psi)) hp⟩

theorem main_z1d_z1g_bounds (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let outValue := eval env out
    let z1d := (HVec.get _ outValue.zs ⟨3, by decide⟩)[1]
    let z1g := (HVec.get _ outValue.zs ⟨6, by decide⟩)[1]
    z1d.val < 2 ^ (K * 5) ∧ z1g.val < 2 ^ (K * 24) := by
  obtain ⟨chunks, hPC, hZs⟩ :=
    main_commitWithZs_pieceChunks_zsFacts_of_soundness G Q hQ R env input offset h
  have hPC1 := pieceChunks_tail_drop hPC
  have hZs1 := zsFacts_tail hZs
  have hPC2 := pieceChunks_tail_drop hPC1
  have hZs2 := zsFacts_tail hZs1
  have hPC3 := pieceChunks_tail_drop hPC2
  have hZs3 := zsFacts_tail hZs2
  have hD := z1_head_val_lt (n := 5) (rest := [0, 24, 24, 0])
    (hn := by norm_num)
    (hpow := lt_trans (by norm_num [K]) two_pow_K_mul_25_lt_p)
    hPC3 hZs3
  have hPC4 := pieceChunks_tail_drop hPC3
  have hZs4 := zsFacts_tail hZs3
  have hPC5 := pieceChunks_tail_drop hPC4
  have hZs5 := zsFacts_tail hZs4
  have hPC6 := pieceChunks_tail_drop hPC5
  have hZs6 := zsFacts_tail hZs5
  have hG := z1_head_val_lt (n := 24) (rest := [0])
    (hn := by norm_num)
    (hpow := lt_trans (by norm_num [K]) two_pow_K_mul_25_lt_p)
    hPC6 hZs6
  dsimp only
  simp only [messagePieceRounds, messagePieceTailRounds]
  exact ⟨hD, hG⟩

theorem main_value_bound (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    (show Ecc.Fp from eval env input.value).val < 2 ^ 64 := by
  let cells := (assignMessageCells input).output offset
  let commitOffset := offset + (assignMessageCells input).localLength offset
  let out := (commitWithZs G Q hQ R input cells).output commitOffset
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  have hrange := main_assignMessageCells_short_range_specs G Q hQ R env input offset h
  have hcanon := main_input_canonicity_facts G Q hQ R env input offset h
  have hzBounds := main_z1d_z1g_bounds G Q hQ R env input offset h
  simp only at hrange hcanon hzBounds
  rcases hrange with ⟨_hb0, _hb3, hd2, he0, _he1, _hg1, _hh0⟩
  rcases hcanon with ⟨_hgd, _hpkd, hvalue, _hrho, _hpsi⟩
  have hz1d : (show Ecc.Fp from eval env z1d).val < 2 ^ (K * 5) := by
    have hzEval :
        eval env z1d =
          (HVec.get (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds)
            (eval env out.zs) ⟨3, by decide⟩)[1] := by
      dsimp only [z1d, out]
      exact HVec.eval_getElem env (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds)
        out.zs ⟨3, by decide⟩ 1 (by decide)
    rw [hzEval]
    rw [← _root_.Orchard.Sinsemilla.CommitDomain.WithZs.eval_zs env messagePieceRounds out]
    exact hzBounds.1
  exact value_from_parts_lt hd2 hz1d he0 hvalue

theorem main_value_subpiece_bits (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    (show Ecc.Fp from eval env cells.d2) =
        (((show Ecc.Fp from eval env input.value).val % 256 : ℕ) : Ecc.Fp) ∧
      (show Ecc.Fp from eval env z1d) =
        (((show Ecc.Fp from eval env input.value).val / 256 % 2 ^ (K * 5) : ℕ) : Ecc.Fp) ∧
      (show Ecc.Fp from eval env cells.e0) =
        (((show Ecc.Fp from eval env input.value).val / 2 ^ 58 % 64 : ℕ) : Ecc.Fp) := by
  let cells := (assignMessageCells input).output offset
  let commitOffset := offset + (assignMessageCells input).localLength offset
  let out := (commitWithZs G Q hQ R input cells).output commitOffset
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  have hrange := main_assignMessageCells_short_range_specs G Q hQ R env input offset h
  have hcanon := main_input_canonicity_facts G Q hQ R env input offset h
  have hzBounds := main_z1d_z1g_bounds G Q hQ R env input offset h
  simp only at hrange hcanon hzBounds
  rcases hrange with ⟨_hb0, _hb3, hd2, he0, _he1, _hg1, _hh0⟩
  rcases hcanon with ⟨_hgd, _hpkd, hvalue, _hrho, _hpsi⟩
  have hz1d : (show Ecc.Fp from eval env z1d).val < 2 ^ (K * 5) := by
    have hzEval :
        eval env z1d =
          (HVec.get (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds)
            (eval env out.zs) ⟨3, by decide⟩)[1] := by
      dsimp only [z1d, out]
      exact HVec.eval_getElem env (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds)
        out.zs ⟨3, by decide⟩ 1 (by decide)
    rw [hzEval]
    rw [← _root_.Orchard.Sinsemilla.CommitDomain.WithZs.eval_zs env messagePieceRounds out]
    exact hzBounds.1
  exact ⟨
    d2_eq_value_low_bits hd2 hz1d he0 hvalue,
    d3_eq_value_middle_bits hd2 hz1d he0 hvalue,
    e0_eq_value_high_bits hd2 hz1d he0 hvalue⟩

theorem main_d2_eq_value_low_bits (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    (show Ecc.Fp from eval env cells.d2) =
      (((show Ecc.Fp from eval env input.value).val % 256 : ℕ) : Ecc.Fp) := by
  exact (main_value_subpiece_bits G Q hQ R env input offset h).1

theorem main_z1d_eq_value_middle_bits (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    (show Ecc.Fp from eval env z1d) =
      (((show Ecc.Fp from eval env input.value).val / 256 % 2 ^ (K * 5) : ℕ) : Ecc.Fp) := by
  exact (main_value_subpiece_bits G Q hQ R env input offset h).2.1

theorem main_value_low_58_bits (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitOffset := offset + (assignMessageCells input).localLength offset
    let out := (commitWithZs G Q hQ R input cells).output commitOffset
    let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
    (show Ecc.Fp from eval env cells.d2) + (show Ecc.Fp from eval env z1d) * 256 =
      (((show Ecc.Fp from eval env input.value).val % 2 ^ 58 : ℕ) : Ecc.Fp) := by
  have hv := main_value_subpiece_bits G Q hQ R env input offset h
  dsimp only at hv ⊢
  rw [hv.1, hv.2.1]
  rw [← low_58_from_low_middle (show Ecc.Fp from eval env input.value).val]
  push_cast
  ring

theorem main_e0_eq_value_high_bits (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    (show Ecc.Fp from eval env cells.e0) =
      (((show Ecc.Fp from eval env input.value).val / 2 ^ 58 % 64 : ℕ) : Ecc.Fp) := by
  exact (main_value_subpiece_bits G Q hQ R env input offset h).2.2

theorem main_noteScalar_bounds (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := noteScalars (eval env input)
    gdX < 2 ^ 255 ∧ gdYbit < 2 ∧ pkdX < 2 ^ 255 ∧ pkdYbit < 2 ∧
      v < 2 ^ 64 ∧ rho < 2 ^ 255 ∧ psi < 2 ^ 255 := by
  have hfields := input_field_255_bounds env input
  have hv := main_value_bound G Q hQ R env input offset h
  simp only [noteScalars, circuit_norm] at hfields hv ⊢
  exact ⟨
    hfields.1,
    Nat.mod_lt _ (by norm_num),
    hfields.2.1,
    Nat.mod_lt _ (by norm_num),
    hv,
    hfields.2.2.1,
    hfields.2.2.2⟩

theorem main_commitInput_piece_values (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp)
    (offset : ℕ) :
    let cells := (assignMessageCells input).output offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    let pieces : Vector Ecc.Fp 8 := (eval env commitInput).pieces
    pieces[0] = eval env cells.a ∧ pieces[1] = eval env cells.b ∧
      pieces[2] = eval env cells.c ∧ pieces[3] = eval env cells.d ∧
      pieces[4] = eval env cells.e ∧ pieces[5] = eval env cells.f ∧
      pieces[6] = eval env cells.g ∧ pieces[7] = eval env cells.h := by
  simp only [circuit_norm]

theorem main_commitInput_f_tail_value (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp)
    (offset : ℕ) :
    let cells := (assignMessageCells input).output offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    let pieces : Vector Ecc.Fp 8 := (eval env commitInput).pieces
    pieces.tail.tail.tail.tail.tail[0] = eval env cells.f := by
  simp only [circuit_norm, Vector.getElem_tail, Nat.reduceAdd]

theorem main_commitInput_g_tail_value (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp)
    (offset : ℕ) :
    let cells := (assignMessageCells input).output offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    let pieces : Vector Ecc.Fp 8 := (eval env commitInput).pieces
    pieces.tail.tail.tail.tail.tail.tail[0] = eval env cells.g := by
  simp only [circuit_norm, Vector.getElem_tail, Nat.reduceAdd]

theorem main_commitInput_h_tail_value (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp)
    (offset : ℕ) :
    let cells := (assignMessageCells input).output offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    let pieces : Vector Ecc.Fp 8 := (eval env commitInput).pieces
    pieces.tail.tail.tail.tail.tail.tail.tail[0] = eval env cells.h := by
  simp only [circuit_norm, Vector.getElem_tail, Nat.reduceAdd]

theorem main_large_piece_bounds (G : Generators) (Q : SWPoint Pallas.curve)
    (hQ : Q ≠ 0) (R : MulFixed.FixedBase) (env : Environment Ecc.Fp)
    (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    let pieces : Vector Ecc.Fp 8 := (eval env commitInput).pieces
    (pieces[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail.tail[0]).val < 2 ^ (K * 6) ∧
      (pieces.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 25) := by
  obtain ⟨chunks, hPC, _hZs⟩ :=
    main_commitWithZs_pieceChunks_zsFacts_of_soundness G Q hQ R env input offset h
  let cells := (assignMessageCells input).output offset
  let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
    { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
      r := input.rcm }
  let pieces : Vector Ecc.Fp 8 := (eval env commitInput).pieces
  exact pieceChunks_large_piece_bounds hPC

theorem main_chunks_eq_noteCommitChunks_of_piece_values (G : Generators)
    (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (R : MulFixed.FixedBase)
    (env : Environment Ecc.Fp) (input : Var Input Ecc.Fp) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main G Q hQ R input).operations offset)) :
    let cells := (assignMessageCells input).output offset
    let commitInput : Var (Sinsemilla.CommitDomain.Input 8) Ecc.Fp :=
      { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
        r := input.rcm }
    let pieces : Vector Ecc.Fp 8 := (eval env commitInput).pieces
    let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := noteScalars (eval env input)
    ∀ chunks,
      Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks →
      pieces[0] = ((gdX % 2 ^ (K * 25) : ℕ) : Ecc.Fp) →
      pieces[1] =
        ((gdX / 2 ^ 250 % 16 + (gdX / 2 ^ 254 % 2) * 16 + gdYbit * 32 +
          (pkdX % 16) * 64 : ℕ) : Ecc.Fp) →
      pieces[2] = (((pkdX / 16) % 2 ^ (K * 25) : ℕ) : Ecc.Fp) →
      pieces[3] =
        ((pkdX / 2 ^ 254 % 2 + pkdYbit * 2 + (v % 2 ^ 58) * 4 : ℕ) : Ecc.Fp) →
      pieces[4] = ((v / 2 ^ 58 % 64 + (rho % 16) * 64 : ℕ) : Ecc.Fp) →
      pieces[5] = (((rho / 16) % 2 ^ (K * 25) : ℕ) : Ecc.Fp) →
      pieces[6] = ((rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2 : ℕ) : Ecc.Fp) →
      pieces[7] = ((psi / 2 ^ 249 % 32 + (psi / 2 ^ 254 % 2) * 32 : ℕ) : Ecc.Fp) →
      chunks =
        Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi := by
  dsimp only
  intro chunks hPC hA hB hC hD hE hF hG hH
  have hbounds := main_noteScalar_bounds G Q hQ R env input offset h
  exact pieceChunks_eq_noteCommitChunks_of_indexed_piece_values hPC hA hB hC hD hE hF hG hH
    hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1 hbounds.2.2.2.2.1
    hbounds.2.2.2.2.2.1 hbounds.2.2.2.2.2.2

-- TODO(note_commit): bundle into a `GeneralFormalCircuit.WithHint`. Blocked on:
--   (1) `soundness` (prime-`p` canonicity: the gates force the inputs canonical, and the
--       pieces equal `noteCommitChunks`'s tiling via `noteCommitChunks_tiling`) +
--       `completeness`. This is the largest remaining proof.

end Orchard.NoteCommit
