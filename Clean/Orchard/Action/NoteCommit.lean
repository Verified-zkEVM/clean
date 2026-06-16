import Clean.Orchard.Action.NoteCommitGate
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
        simp [Orchard.Specs.Sinsemilla.chunksOf, Orchard.Specs.bitrange]
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

private theorem natCast_injective_of_lt {a b : ℕ}
    (ha : a < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hb : b < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (h : (a : Ecc.Fp) = (b : Ecc.Fp)) :
    a = b := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv

private theorem isBool_val_lt_two {x : Ecc.Fp} (h : IsBool x) :
    x.val < 2 := by
  rcases h with h | h
  · rw [h, ZMod.val_zero]
    norm_num
  · rw [h, ZMod.val_one]
    norm_num

private theorem decomposeB_value_lt {b b0 b1 b2 b3 : Ecc.Fp}
    (hb0 : b0.val < 2 ^ 4) (hb1 : IsBool b1)
    (hb2 : IsBool b2) (hb3 : b3.val < 2 ^ 4)
    (hdec : b = b0 + b1 * 16 + b2 * 32 + b3 * 64) :
    b.val < 2 ^ K := by
  have hb1lt := isBool_val_lt_two hb1
  have hb2lt := isBool_val_lt_two hb2
  let packed := b0.val + b1.val * 16 + b2.val * 32 + b3.val * 64
  have hPackedLt : packed < 2 ^ K := by
    norm_num [K] at hb0 hb3 ⊢
    omega
  have hPackedCard : packed < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD :=
    lt_trans hPackedLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
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
    lt_trans hPackedLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hcast : e = (packed : Ecc.Fp) := by
    rw [hdec]
    dsimp only [packed]
    rw [← ZMod.natCast_zmod_val e0, ← ZMod.natCast_zmod_val e1]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt e0), ZMod.val_natCast_of_lt (ZMod.val_lt e1)]
  rw [hcast, ZMod.val_natCast_of_lt hPackedCard]
  exact hPackedLt

private theorem decomposeH_value_lt {h h0 h1 : Ecc.Fp}
    (hh0 : h0.val < 2 ^ 5) (hh1 : IsBool h1)
    (hdec : h = h0 + h1 * 32) :
    h.val < 2 ^ K := by
  have hh1lt := isBool_val_lt_two hh1
  let packed := h0.val + h1.val * 32
  have hPackedLt : packed < 2 ^ K := by
    norm_num [K] at hh0 ⊢
    omega
  have hPackedCard : packed < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD :=
    lt_trans hPackedLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
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
    (hg0 : IsBool g0) (hg1 : g1.val < 2 ^ 9)
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
    (hg0 : IsBool g0)
    (hlowSmall : g0 = 1 → e1.val + f.val * 16 < 2 ^ 134)
    (hrho : rho = e1 + f * 16 + g0 * OfNat.ofNat (2 ^ 254))
    (hprime : e1FPrime = e1 + f * 16 + OfNat.ofNat (2 ^ 140) - Ecc.tP)
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
      push_cast [Ecc.tP, tPNat]
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

private theorem g0_eq_rho_high_bit_of_parts {rho e1 f g0 e1FPrime z14 : Ecc.Fp}
    (he1 : e1.val < 2 ^ 4) (hf : f.val < 2 ^ (K * 25))
    (hg0 : IsBool g0)
    (hlowSmall : g0 = 1 → e1.val + f.val * 16 < 2 ^ 134)
    (hrho : rho = e1 + f * 16 + g0 * OfNat.ofNat (2 ^ 254))
    (hprime : e1FPrime = e1 + f * 16 + OfNat.ofNat (2 ^ 140) - Ecc.tP)
    (hz14 : g0 = 0 ∨ z14 = 0)
    (hz14Lt : z14 = 0 → e1FPrime.val < 2 ^ (K * 14)) :
    g0 = ((rho.val / 2 ^ 254 % 2 : ℕ) : Ecc.Fp) := by
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
  rcases hg0 with hg0zero | hg0one
  · have hrhoVal : rho.val = e1.val + f.val * 16 := by
      rw [hg0zero, zero_mul, _root_.add_zero] at hrho
      rw [hrho, hlowField, ZMod.val_natCast_of_lt hlowCard]
    rw [hg0zero]
    rw [hrhoVal]
    rw [Nat.div_eq_of_lt hfLow]
    norm_num
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
      push_cast [Ecc.tP, tPNat]
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
    rw [hg0one]
    rw [hrhoVal]
    have hdiv : (e1.val + f.val * 16 + 2 ^ 254) / 2 ^ 254 = 1 := by
      omega
    rw [hdiv]
    norm_num

private theorem g1_g2_eq_psi_low_bits_of_parts {psi g1 g2 h0 h1 g1G2Prime z13 : Ecc.Fp}
    (hg1 : g1.val < 2 ^ 9) (hg2 : g2.val < 2 ^ (K * 24))
    (hh0 : h0.val < 2 ^ 5) (hh1 : IsBool h1)
    (hlowSmall : h1 = 1 → g1.val + g2.val * 512 < 2 ^ 130)
    (hpsi : psi =
      g1 + g2 * 512 + h0 * OfNat.ofNat (2 ^ 249) + h1 * OfNat.ofNat (2 ^ 254))
    (hprime : g1G2Prime = g1 + g2 * 512 + OfNat.ofNat (2 ^ 130) - Ecc.tP)
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
      push_cast [Ecc.tP, tPNat]
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

private theorem h0_h1_eq_psi_high_bits_of_parts {psi g1 g2 h0 h1 g1G2Prime z13 : Ecc.Fp}
    (hg1 : g1.val < 2 ^ 9) (hg2 : g2.val < 2 ^ (K * 24))
    (hh0 : h0.val < 2 ^ 5) (hh1 : IsBool h1)
    (hlowSmall : h1 = 1 → g1.val + g2.val * 512 < 2 ^ 130)
    (hpsi : psi =
      g1 + g2 * 512 + h0 * OfNat.ofNat (2 ^ 249) + h1 * OfNat.ofNat (2 ^ 254))
    (hprime : g1G2Prime = g1 + g2 * 512 + OfNat.ofNat (2 ^ 130) - Ecc.tP)
    (hh0zero : h1 = 0 ∨ h0 = 0)
    (hz13 : h1 = 0 ∨ z13 = 0)
    (hz13Lt : z13 = 0 → g1G2Prime.val < 2 ^ (K * 13)) :
    h0 + h1 * 32 =
      ((psi.val / 2 ^ 249 % 32 + (psi.val / 2 ^ 254 % 2) * 32 : ℕ) : Ecc.Fp) := by
  let low := g1.val + g2.val * 512
  have hlowLt249 : low < 2 ^ 249 := by
    dsimp only [low]
    norm_num [K] at hg1 hg2 ⊢
    omega
  have hlowField : g1 + g2 * 512 = (low : Ecc.Fp) := by
    dsimp only [low]
    rw [← ZMod.natCast_zmod_val g1, ← ZMod.natCast_zmod_val g2]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt g1), ZMod.val_natCast_of_lt (ZMod.val_lt g2)]
  rcases hh1 with hh1zero | hh1one
  · have hpackedLt : low + h0.val * 2 ^ 249 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
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
    have hsumLt : h0.val < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := ZMod.val_lt h0
    rw [hh1zero, zero_mul, _root_.add_zero, ← ZMod.natCast_zmod_val h0]
    congr
    rw [hpsiVal]
    have hdiv : (low + h0.val * 2 ^ 249) / 2 ^ 249 = h0.val := by
      rw [Nat.mul_comm h0.val (2 ^ 249)]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 249), Nat.div_eq_of_lt hlowLt249,
        Nat.zero_add]
    have hdiv254 : (low + h0.val * 2 ^ 249) / 2 ^ 254 = 0 := by
      apply Nat.div_eq_of_lt
      norm_num at hh0 hlowLt249 ⊢
      omega
    rw [hdiv, hdiv254, Nat.zero_mod, zero_mul, Nat.add_zero]
    exact (Nat.mod_eq_of_lt hh0).symm
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
      push_cast [Ecc.tP, tPNat]
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
    have hpackedLt : low + 2 ^ 254 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at hlowLtTP ⊢
      omega
    have hpsiVal : psi.val = low + 2 ^ 254 := by
      have hpsiCast : psi = ((low + 2 ^ 254 : ℕ) : Ecc.Fp) := by
        rw [hpsi, hh0zero', hh1one]
        rw [zero_mul, one_mul, _root_.add_zero, hlowField]
        norm_num
      rw [hpsiCast, ZMod.val_natCast_of_lt hpackedLt]
    rw [hh0zero', hh1one, _root_.zero_add, one_mul]
    norm_num
    rw [hpsiVal]
    have hdiv249 : (low + 2 ^ 254) / 2 ^ 249 = 32 := by
      rw [show (2 : ℕ) ^ 254 = 2 ^ 249 * 32 by norm_num]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 249), Nat.div_eq_of_lt hlowLt249,
        Nat.zero_add]
    have hdiv254 : (low + 2 ^ 254) / 2 ^ 254 = 1 := by
      nth_rw 1 [show (2 : ℕ) ^ 254 = 2 ^ 254 * 1 by ring]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 254)]
      have hlowLt254 : low < 2 ^ 254 := lt_trans hlowLt249 (by norm_num)
      rw [Nat.div_eq_of_lt hlowLt254, Nat.zero_add]
    rw [show
      904625697166532776746648320380374280103671755200316906558262375061821325312 =
        (2 : ℕ) ^ 249 by norm_num]
    rw [show
      28948022309329048855892746252171976963317496166410141009864396001978282409984 =
        (2 : ℕ) ^ 254 by norm_num]
    rw [hdiv249, hdiv254]
    norm_num

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

private theorem lsb_eq_y_low_bit_of_parts {y lsb k0 k2 k3 j z1J : Ecc.Fp}
    (hlsb : IsBool lsb) (hk0 : k0.val < 2 ^ 9) (hk2 : k2.val < 2 ^ 4)
    (hz1J : z1J.val < 2 ^ (K * 24)) (hk3 : IsBool k3)
    (hj : j = lsb + k0 * 2 + z1J * 1024)
    (hy : y = j + k2 * ((2 ^ 250 : ℕ) : Ecc.Fp) +
      k3 * ((2 ^ 254 : ℕ) : Ecc.Fp))
    (hk2Zero : k3 = 0 ∨ k2 = 0)
    (hjLtTP : k3 = 1 → j.val < tPNat) :
    lsb = ((y.val % 2 : ℕ) : Ecc.Fp) := by
  have hlsbLt := isBool_val_lt_two hlsb
  have hsumLt : lsb.val + k0.val * 2 + z1J.val * 1024 < 2 ^ 250 := by
    norm_num [K] at hlsbLt hk0 hz1J ⊢
    omega
  have hsumCard :
      lsb.val + k0.val * 2 + z1J.val * 1024 <
        CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    exact lt_trans hsumLt (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hjField :
      lsb + k0 * 2 + z1J * 1024 =
        ((lsb.val + k0.val * 2 + z1J.val * 1024 : ℕ) : Ecc.Fp) := by
    rw [← ZMod.natCast_zmod_val lsb, ← ZMod.natCast_zmod_val k0,
      ← ZMod.natCast_zmod_val z1J]
    push_cast
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt lsb),
      ZMod.val_natCast_of_lt (ZMod.val_lt k0), ZMod.val_natCast_of_lt (ZMod.val_lt z1J)]
  have hjVal : j.val = lsb.val + k0.val * 2 + z1J.val * 1024 := by
    rw [hj, hjField, ZMod.val_natCast_of_lt hsumCard]
  have hjMod : j.val % 2 = lsb.val := by
    rw [hjVal]
    norm_num at hlsbLt ⊢
    omega
  rcases hk3 with hk3Zero | hk3One
  · have hpackedLt :
        j.val + k2.val * 2 ^ 250 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      rw [hjVal]
      norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at hlsbLt hk0 hk2 hz1J ⊢
      omega
    have hyVal : y.val = j.val + k2.val * 2 ^ 250 := by
      have hyCast : y = ((j.val + k2.val * 2 ^ 250 : ℕ) : Ecc.Fp) := by
        rw [hy, hk3Zero, zero_mul, _root_.add_zero]
        rw [← ZMod.natCast_zmod_val j, ← ZMod.natCast_zmod_val k2]
        push_cast
        rw [ZMod.val_natCast_of_lt (ZMod.val_lt j), ZMod.val_natCast_of_lt (ZMod.val_lt k2)]
      rw [hyCast, ZMod.val_natCast_of_lt hpackedLt]
    rw [← ZMod.natCast_zmod_val lsb]
    congr
    rw [hyVal]
    rw [show k2.val * 2 ^ 250 = 2 * (k2.val * 2 ^ 249) by ring]
    rw [Nat.add_mul_mod_self_left]
    exact hjMod.symm
  · have hk2Zero' : k2 = 0 := by
      rcases hk2Zero with hk2Zero | hk2Zero
      · exfalso
        exact zero_ne_one (by rw [← hk2Zero, hk3One])
      · exact hk2Zero
    have hpackedLt :
        j.val + 2 ^ 254 < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      have hjSmall := hjLtTP hk3One
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at hjSmall ⊢
      omega
    have hyVal : y.val = j.val + 2 ^ 254 := by
      have hyCast : y = ((j.val + 2 ^ 254 : ℕ) : Ecc.Fp) := by
        rw [hy, hk2Zero', hk3One, zero_mul, one_mul]
        rw [_root_.add_zero, ← ZMod.natCast_zmod_val j]
        norm_num
      rw [hyCast, ZMod.val_natCast_of_lt hpackedLt]
    rw [← ZMod.natCast_zmod_val lsb]
    congr
    rw [hyVal]
    rw [show (2 : ℕ) ^ 254 = 2 * 2 ^ 253 by norm_num]
    rw [Nat.add_mul_mod_self_left]
    exact hjMod.symm

private theorem j_lt_tP_of_prime_bounds {j j' : Ecc.Fp}
    (hj : j.val < 2 ^ (K * 13))
    (hprime : j' = j + ((2 ^ 130 : ℕ) : Ecc.Fp) - Ecc.tP)
    (hprimeLt : j'.val < 2 ^ (K * 13)) :
    j.val < tPNat := by
  by_contra hnot
  have hjGe : tPNat ≤ j.val := Nat.le_of_not_gt hnot
  have hprimeField : j' = ((j.val + 2 ^ 130 - tPNat : ℕ) : Ecc.Fp) := by
    rw [hprime, ← ZMod.natCast_zmod_val j]
    push_cast [Ecc.tP, tPNat]
    rw [ZMod.val_natCast_of_lt (ZMod.val_lt j)]
    ring_nf
  have hprimeValEq : j'.val = j.val + 2 ^ 130 - tPNat := by
    have hlt : j.val + 2 ^ 130 - tPNat < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
      norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, tPNat] at hj ⊢
      omega
    rw [hprimeField, ZMod.val_natCast_of_lt hlt]
  rw [hprimeValEq] at hprimeLt
  norm_num [K] at hj hprimeLt ⊢
  omega

private theorem y_lsb_eq_low_bit_of_row_facts {y lsb k0 k2 k3 j z1J j' : Ecc.Fp}
    (hlsb : IsBool lsb) (hk0 : k0.val < 2 ^ 9) (hk2 : k2.val < 2 ^ 4)
    (hz1J : z1J.val < 2 ^ (K * 24)) (hk3 : IsBool k3)
    (hj : j = lsb + k0 * 2 + z1J * 1024)
    (hy : y = j + k2 * ((2 ^ 250 : ℕ) : Ecc.Fp) +
      k3 * ((2 ^ 254 : ℕ) : Ecc.Fp))
    (hprime : j' = j + ((2 ^ 130 : ℕ) : Ecc.Fp) - Ecc.tP)
    (hk2Zero : k3 = 0 ∨ k2 = 0)
    (hz13 : k3 = 0 ∨ j.val < 2 ^ (K * 13))
    (hz13Prime : k3 = 0 ∨ j'.val < 2 ^ (K * 13)) :
    lsb = ((y.val % 2 : ℕ) : Ecc.Fp) := by
  have hjLtTP : k3 = 1 → j.val < tPNat := by
    intro hk3One
    have hjBound : j.val < 2 ^ (K * 13) := by
      rcases hz13 with hz | hz
      · exfalso
        exact (zero_ne_one : (0 : Ecc.Fp) ≠ 1) (by rw [← hz, hk3One])
      · exact hz
    have hprimeBound : j'.val < 2 ^ (K * 13) := by
      rcases hz13Prime with hz | hz
      · exfalso
        exact (zero_ne_one : (0 : Ecc.Fp) ≠ 1) (by rw [← hz, hk3One])
      · exact hz
    exact j_lt_tP_of_prime_bounds hjBound hprime hprimeBound
  exact lsb_eq_y_low_bit_of_parts hlsb hk0 hk2 hz1J hk3 hj hy hk2Zero hjLtTP

private theorem nat_mod_two_eq_testBit_zero (n : ℕ) :
    (n % 2 : ℕ) = if n.testBit 0 then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlt : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos (n % 2) with h | h
  · simp [h]
  · have h1 : n % 2 = 1 := by omega
    simp [h1]

private theorem low_bit_eq_mod_two {y lsb : Fp}
    (h : lsb = ((if y.val.testBit 0 then 1 else 0 : ℕ) : Fp)) :
    lsb = ((y.val % 2 : ℕ) : Fp) := by
  rw [h, nat_mod_two_eq_testBit_zero]

private theorem chunksOf_add_high {low high n : ℕ} (hlow : low < 2 ^ (K * n)) :
    Orchard.Specs.Sinsemilla.chunksOf (low + 2 ^ (K * n) * high) n =
      Orchard.Specs.Sinsemilla.chunksOf low n := by
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod (low + 2 ^ (K * n) * high) n]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * n) = 2 ^ (K * n) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]

private theorem chunksOf_one_eq_singleton {x : ℕ} (hx : x < 2 ^ K) :
    Orchard.Specs.Sinsemilla.chunksOf x 1 = [x] := by
  unfold Orchard.Specs.Sinsemilla.chunksOf Orchard.Specs.bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [Nat.mod_eq_of_lt hx]

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
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod
    (gdX + 2 ^ (K * 25) *
      (2 ^ 5 * gdY + 2 ^ 6 * pkdX + 2 ^ 261 * pkdY +
        2 ^ 262 * v + 2 ^ 326 * rho + 2 ^ 581 * psi)) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [Nat.add_mul_mod_self_left]
  exact Orchard.Specs.Sinsemilla.chunksOf_mod gdX 25

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
  unfold Orchard.Specs.Sinsemilla.chunksOf Orchard.Specs.bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_b_word gdX gdY pkdX pkdY v rho psi hgdX hgdY]

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
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod
      (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 260) 25,
    ← Orchard.Specs.Sinsemilla.chunksOf_mod (pkdX / 16) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_c_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY]

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
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod
      (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) 6,
    ← Orchard.Specs.Sinsemilla.chunksOf_mod
      (pkdX / 2 ^ 254 % 2 + pkdY * 2 + (v % 2 ^ 58) * 4) 6]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 6) = 2 ^ (K * 6) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_d_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX]

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
  unfold Orchard.Specs.Sinsemilla.chunksOf Orchard.Specs.bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_e_word gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv]

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
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod
      (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 580) 25,
    ← Orchard.Specs.Sinsemilla.chunksOf_mod (rho / 16) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_f_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv]

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
  rw [← Orchard.Specs.Sinsemilla.chunksOf_mod
      (Orchard.Specs.Sinsemilla.noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) 25,
    ← Orchard.Specs.Sinsemilla.chunksOf_mod
      (rho / 2 ^ 254 % 2 + (psi % 2 ^ 249) * 2) 25]
  rw [show 2 ^ (Orchard.Specs.Sinsemilla.K * 25) = 2 ^ (K * 25) by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_g_mod gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho]

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
  unfold Orchard.Specs.Sinsemilla.chunksOf Orchard.Specs.bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show 2 ^ Orchard.Specs.Sinsemilla.K = 2 ^ K by
    norm_num [Orchard.Specs.Sinsemilla.K, K]]
  rw [noteCommitChunks_segment_h_word gdX gdY pkdX pkdY v rho psi hgdX hgdY hpkdX hpkdY hv hrho hpsi]

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
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsA 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksA : Orchard.Specs.Sinsemilla.chunksOf gdX 25 = (List.range 25).map msA := by
    rw [← Orchard.Specs.Sinsemilla.chunksOf_mod gdX 25]
    exact hChunksA_low
  have hChunksB := chunksOf_eq_map_of_cast_sum hmsB hB
    (lt_trans hBValueLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsB 1) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC_low := chunksOf_eq_map_of_cast_sum hmsC hC
    (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos (K * 25))) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
    (lt_trans (sum_digits_lt hmsC 25) (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
  have hChunksC : Orchard.Specs.Sinsemilla.chunksOf (pkdX / 16) 25 =
      (List.range 25).map msC := by
    rw [← Orchard.Specs.Sinsemilla.chunksOf_mod (pkdX / 16) 25]
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
  have hChunksF : Orchard.Specs.Sinsemilla.chunksOf (rho / 16) 25 =
      (List.range 25).map msF := by
    rw [← Orchard.Specs.Sinsemilla.chunksOf_mod (rho / 16) 25]
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
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
    (h : Orchard.Sinsemilla.Chain.ZsFacts (n :: rest) chunks zs) (r : Fin (n + 1)) :
    (HVec.head zs)[r] =
      ((∑ j ∈ Finset.range (n + 1 - r.val),
        chunks.getD (r.val + j) 0 * 2 ^ (K * j) : ℕ) : Fp) := by
  simp only [Orchard.Sinsemilla.Chain.ZsFacts] at h
  rw [h.1]
  simp only
  norm_num [Orchard.Specs.Sinsemilla.K, K]

private theorem zsFacts_tail {n : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
    (h : Orchard.Sinsemilla.Chain.ZsFacts (n :: rest) chunks zs) :
    Orchard.Sinsemilla.Chain.ZsFacts rest (chunks.drop (n + 1)) (HVec.tail zs) := by
  simp only [Orchard.Sinsemilla.Chain.ZsFacts] at h
  exact h.2

private theorem pieceChunks_tail_drop {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    Orchard.Sinsemilla.Chain.PieceChunks rest pieces.tail (chunks.drop (n + 1)) := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at h
  obtain ⟨ms, _hms, _hpiece, tailChunks, hchunks, htail⟩ := h
  rw [hchunks, Orchard.Sinsemilla.Chain.chunks_drop_append ms tailChunks]
  exact htail

private theorem pieceChunks_head_val_lt {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (hpow : 2 ^ (K * (n + 1)) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    (pieces[0]).val < 2 ^ (K * (n + 1)) := by
  simp only [Orchard.Sinsemilla.Chain.PieceChunks] at h
  obtain ⟨ms, hms, hpiece, _tailChunks, _hchunks, _htail⟩ := h
  have hsumLt := sum_digits_lt hms (n + 1)
  rw [hpiece, ZMod.val_natCast_of_lt (lt_trans hsumLt hpow)]
  exact hsumLt

private theorem pieceChunks_head_val_lt_of_z_zero {n r : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
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
      (high : Fp) = 0 := by
    have hz' := zsFacts_head_get hZs ⟨r, hr⟩
    simp only at hz'
    have hzFin : (HVec.head zs)[r]'hr = 0 := by
      exact hz
    have hz'' : (HVec.head zs)[r]'hr =
        ((∑ j ∈ Finset.range (n + 1 - r),
          chunks.getD (r + j) 0 * 2 ^ (K * j) : ℕ) : Fp) := by
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
      pieces[0] = (low : Fp) := by
    have hsplit := sum_digits_split K r (n + 1) (by omega) ms
    have hpieceK :
        pieces[0] = ((∑ j ∈ Finset.range (n + 1), ms j * 2 ^ (K * j) : ℕ) : Fp) := by
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
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks) :
    (pieces[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail.tail[0]).val < 2 ^ (K * 6) ∧
      (pieces.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 25) ∧
      (pieces.tail.tail.tail.tail.tail.tail[0]).val < 2 ^ (K * 25) := by
  have hA := pieceChunks_head_val_lt (n := 24) (rest := messagePieceTailRounds)
    (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) hPC
  have hPC1 := pieceChunks_tail_drop hPC
  have hPC2 := pieceChunks_tail_drop hPC1
  have hC := pieceChunks_head_val_lt (n := 24) (rest := [5, 0, 24, 24, 0])
    (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) hPC2
  have hPC3 := pieceChunks_tail_drop hPC2
  have hD := pieceChunks_head_val_lt (n := 5) (rest := [0, 24, 24, 0])
    (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) hPC3
  have hPC4 := pieceChunks_tail_drop hPC3
  have hPC5 := pieceChunks_tail_drop hPC4
  have hF := pieceChunks_head_val_lt (n := 24) (rest := [24, 0])
    (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) hPC5
  have hPC6 := pieceChunks_tail_drop hPC5
  have hG := pieceChunks_head_val_lt (n := 24) (rest := [0])
    (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) hPC6
  exact ⟨hA, hC, hD, hF, hG⟩

private theorem pieceChunks_f_val_lt_of_z13_zero
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Fp}
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

private theorem pieceChunks_c_val_lt_of_z13_zero
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Fp}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13c :
      (HVec.head (HVec.tail (HVec.tail zs)))[13]'(by decide) = 0) :
    (pieces.tail.tail[0]).val < 2 ^ (K * 13) := by
  have hPC1 := pieceChunks_tail_drop hPC
  have hZs1 := zsFacts_tail hZs
  have hPC2 := pieceChunks_tail_drop hPC1
  have hZs2 := zsFacts_tail hZs1
  exact pieceChunks_head_val_lt_of_z_zero
    (n := 24) (r := 13) (rest := [5, 0, 24, 24, 0])
    (hr := by norm_num)
    (hpowLow := by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (hpowHigh := by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    hPC2 hZs2 hz13c

private theorem b3_c_low_lt_of_piece_z13_zero {b3 c : Fp}
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Fp}
    (hb3 : b3.val < 2 ^ 4)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13c :
      (HVec.head (HVec.tail (HVec.tail zs)))[13]'(by decide) = 0)
    (hc : pieces.tail.tail[0] = c) :
    b3.val + c.val * 16 < 2 ^ 134 := by
  have hcLt := pieceChunks_c_val_lt_of_z13_zero hPC hZs hz13c
  have hcVal := congrArg ZMod.val hc
  rw [hcVal] at hcLt
  norm_num [K] at hb3 hcLt ⊢
  omega

private theorem pieceChunks_e1_f_low_lt_of_z13_zero
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Fp}
    {e1 : Fp}
    (he1 : e1.val < 2 ^ 4)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts messagePieceRounds chunks zs)
    (hz13f :
      (HVec.head (HVec.tail (HVec.tail (HVec.tail (HVec.tail (HVec.tail zs))))))[13]'(by decide)
        = 0) :
    e1.val + (pieces.tail.tail.tail.tail.tail[0]).val * 16 < 2 ^ 134 := by
  exact e1_f_low_lt_of_f_130 he1 (pieceChunks_f_val_lt_of_z13_zero hPC hZs hz13f)

private theorem e1_f_low_lt_of_piece_z13_zero {e1 f : Fp}
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Fp}
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
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Fp}
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

private theorem g1_g2_low_lt_of_piece_z13_zero {g0 g1 g2 : Fp}
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths messagePieceRounds) Fp}
    (hg0 : IsBool g0) (hg1 : g1.val < 2 ^ 9)
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
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
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
        ((∑ j ∈ Finset.range n, chunks.getD (j + 1) 0 * 2 ^ (K * j) : ℕ) : Fp) := by
    simpa only [Nat.add_comm] using hz
  rw [hz']
  rw [hsum]
  rw [ZMod.val_natCast_of_lt (lt_trans hsumLt hpow)]
  exact hsumLt

private theorem pieceChunks_eq_noteCommitChunks_of_indexed_piece_values
    {pieces : Vector Fp messagePieceRounds.length} {chunks : List ℕ}
    {gdX gdY pkdX pkdY v rho psi : ℕ}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds pieces chunks)
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

/-- Dividing the low `a+b` bits by `2^a` exposes the next `b` bits: the honest
running sum's `z_a` cell is the corresponding higher `bitrange`. -/
private theorem bitrange_low_div (n a b : ℕ) :
    bitrange n 0 (a + b) / 2 ^ a = bitrange n a b := by
  simp only [bitrange, pow_zero, Nat.div_one]
  rw [pow_add, Nat.mod_mul_right_div_self]

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
def noteScalarsOf (gd pkd : Point Fp) (value rho psi : Fp) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let gdX : Fp := gd.x
  let gdY : Fp := gd.y
  let pkdX : Fp := pkd.x
  let pkdY : Fp := pkd.y
  let v : Fp := value
  (gdX.val, gdY.val % 2, pkdX.val, pkdY.val % 2, v.val, rho.val, psi.val)

def messagePieces (cells : MessageCells Fp) : Vector Fp messagePieceRounds.length :=
  #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h]

def noteChunksOfScalars (gdX gdYbit pkdX pkdYbit v rho psi : ℕ) : List ℕ :=
  Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi

def MessagePiecesEncode (input : Value Input Fp) (cells : Value MessageCells Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
    noteScalarsOf input.gd input.pkd input.value input.rho input.psi
  Orchard.Sinsemilla.Chain.PieceChunks messagePieceRounds (messagePieces cells)
    (noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi)

def ProverMessagePiecesEncode (input : ProverValue Input Fp)
    (cells : ProverValue MessageCells Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
    noteScalarsOf input.gd input.pkd input.value input.rho input.psi
  Orchard.Sinsemilla.Chain.honestChunks messagePieceRounds (messagePieces cells) =
    noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi

def NoteCommitRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : Value Input Fp) (cm : Point Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
    noteScalarsOf input.gd input.pkd input.value input.rho input.psi
  ∃ rcm : Fq, ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi) = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue rcm).coords

def ProverNoteCommitRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : ProverValue Input Fp) (cm : Point Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
    noteScalarsOf input.gd input.pkd input.value input.rho input.psi
  ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi) = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue input.rcm).coords

namespace AssignMessageCells

def main (input : Var Input Ecc.Fp) : Circuit Ecc.Fp (Var MessageCells Ecc.Fp) := do
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

instance elaborated : ElaboratedCircuit Ecc.Fp Input MessageCells main := by
  elaborate_circuit

def Assumptions (_input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  True

def ProverAssumptions (_input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  True

def Spec (input : Value Input Fp) (cells : Value MessageCells Fp)
    (_ : ProverData Fp) : Prop :=
  MessagePiecesEncode input cells

def ProverSpec (input : ProverValue Input Fp)
    (cells : ProverValue MessageCells Fp) (_ : ProverHint Fp) : Prop :=
  ProverMessagePiecesEncode input cells ∧
    Orchard.Sinsemilla.Chain.PieceBounds messagePieceRounds (messagePieces cells)

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

end AssignMessageCells

namespace CommitAndConstrain

structure Input (F : Type) where
  note : Orchard.Action.NoteCommit.Input F
  cells : MessageCells F
deriving CircuitType

instance : Inhabited (Var Input Ecc.Fp) :=
  ⟨{ note := default, cells := default }⟩

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) :
    Circuit Ecc.Fp (Var Point Ecc.Fp) := do
  let gdX := input.note.gd.x
  let pkdX := input.note.pkd.x
  let v := input.note.value
  let rho := input.note.rho
  let psi := input.note.psi
  let cells := input.cells
  let out ← _root_.Orchard.Sinsemilla.CommitDomain.WithZs.circuit G Q hQ R 24 messagePieceTailRounds
    { pieces := #v[cells.a, cells.b, cells.c, cells.d, cells.e, cells.f, cells.g, cells.h],
      r := input.note.rcm }
  let cm := out.point
  let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
  let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
  let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
  let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]

  let aPrime ← witnessField fun env => env cells.a + (2 ^ 130 : Ecc.Fp) - Ecc.tP
  let aPrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 aPrime
  let b3cPrime ← witnessField fun env =>
    env cells.b3 + (2 ^ 4 : Ecc.Fp) * env cells.c + (2 ^ 140 : Ecc.Fp) - Ecc.tP
  let b3cPrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14 b3cPrime
  let e1fPrime ← witnessField fun env =>
    env cells.e1 + (2 ^ 4 : Ecc.Fp) * env cells.f + (2 ^ 140 : Ecc.Fp) - Ecc.tP
  let e1fPrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14 e1fPrime
  let g1g2Prime ← witnessField fun env =>
    env cells.g1 + (2 ^ 9 : Ecc.Fp) * env z1g + (2 ^ 130 : Ecc.Fp) - Ecc.tP
  let g1g2PrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 g1g2Prime

  Gate.DecomposeB.circuit
    { b := cells.b, b0 := cells.b0, b1 := cells.b1, b2 := cells.b2, b3 := cells.b3 }
  Gate.DecomposeD.circuit
    { d := cells.d, d0 := cells.d0, d1 := cells.d1, d2 := cells.d2, d3 := z1d }
  Gate.DecomposeE.circuit { e := cells.e, e0 := cells.e0, e1 := cells.e1 }
  Gate.DecomposeG.circuit { g := cells.g, g0 := cells.g0, g1 := cells.g1, g2 := z1g }
  Gate.DecomposeH.circuit { h := cells.h, h0 := cells.h0, h1 := cells.h1 }
  Gate.GdCanonicity.circuit
    { gdX, b0 := cells.b0, b1 := cells.b1, a := cells.a, aPrime := aPrimeZs[0], z13A := z13a,
      z13APrime := aPrimeZs[13] }
  Gate.PkdCanonicity.circuit
    { pkdX, b3 := cells.b3, c := cells.c, d0 := cells.d0, b3CPrime := b3cPrimeZs[0], z13C := z13c,
      z14B3CPrime := b3cPrimeZs[14] }
  Gate.ValueCanonicity.circuit { value := v, d2 := cells.d2, d3 := z1d, e0 := cells.e0 }
  Gate.RhoCanonicity.circuit
    { rho, e1 := cells.e1, f := cells.f, g0 := cells.g0, e1FPrime := e1fPrimeZs[0], z13F := z13f,
      z14E1FPrime := e1fPrimeZs[14] }
  Gate.PsiCanonicity.circuit
    { psi, h0 := cells.h0, g1 := cells.g1, h1 := cells.h1, g2 := z1g, g1G2Prime := g1g2PrimeZs[0], z13G := z13g,
      z13G1G2Prime := g1g2PrimeZs[13] }
  return cm

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Ecc.Fp Input Point (main G Q hQ R) := by
  elaborate_circuit

def Assumptions (_G : Generators) (_Q : SWPoint Pallas.curve) (_R : MulFixed.FixedBase)
    (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  MessagePiecesEncode input.note input.cells

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve) (_R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  ProverMessagePiecesEncode input.note input.cells ∧
    Orchard.Sinsemilla.Chain.PieceBounds messagePieceRounds (messagePieces input.cells) ∧
    let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
      noteScalarsOf input.note.gd input.note.pkd input.note.value input.note.rho input.note.psi
    ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
      (noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi) = some B

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (cm : Point Fp) (_ : ProverData Fp) : Prop :=
  NoteCommitRelation G Q R input.note cm

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (cm : ProverValue Point Fp)
    (_ : ProverHint Fp) : Prop :=
  ProverNoteCommitRelation G Q R input.note cm

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
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Point where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Assumptions := Assumptions G Q R
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q R
  ProverSpec := ProverSpec G Q R
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end CommitAndConstrain

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) :
    Circuit Ecc.Fp (Var Point Ecc.Fp) := do
  let cells ← AssignMessageCells.circuit input
  CommitAndConstrain.circuit G Q hQ R { note := input, cells := cells }

instance mainExplicit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ExplicitCircuits (main G Q hQ R) := by
  infer_explicit_circuits

def mainOutput (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) (offset : ℕ) :
    Var Point Ecc.Fp :=
  (main G Q hQ R input).output offset

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    ElaboratedCircuit Ecc.Fp Input Point (main G Q hQ R) := by
  elaborate_circuit

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
  NoteCommitRelation G Q R input cm

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve)
    (input : ProverValue Input Ecc.Fp) (_ : ProverData Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  Pallas.OnCurve input.gd.coords ∧
  Pallas.OnCurve input.pkd.coords ∧
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) :=
    noteScalarsOf input.gd input.pkd input.value input.rho input.psi
  ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
    (noteChunksOfScalars gdX gdYbit pkdX pkdYbit v rho psi) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Ecc.Fp) (cm : ProverValue Point Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  ProverNoteCommitRelation G Q R input cm

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) Assumptions (Spec G Q R) := by
  circuit_proof_start [AssignMessageCells.circuit, CommitAndConstrain.circuit]
  let hMessage := h_holds.1 trivial
  exact h_holds.2 hMessage

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q) (ProverSpec G Q R) := by
  circuit_proof_start [AssignMessageCells.circuit, CommitAndConstrain.circuit,
    ProverAssumptions, ProverSpec, AssignMessageCells.ProverSpec,
    CommitAndConstrain.ProverAssumptions, CommitAndConstrain.ProverSpec]
  let hAssign := (h_env.1 trivial).2
  exact ⟨⟨trivial, hAssign.1, hAssign.2, h_assumptions.2.2⟩,
    (h_env.2 ⟨hAssign.1, hAssign.2, h_assumptions.2.2⟩).2⟩

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

-- TODO(note_commit): replace the placeholder subcircuit specs/proofs above with the real
-- semantic contracts. The parent gadget now composes bundled subcircuits; the remaining
-- proof work is concentrated in `YCanonicity`, `AssignMessageCells`, and
-- `CommitAndConstrain`.

end Orchard.Action.NoteCommit
