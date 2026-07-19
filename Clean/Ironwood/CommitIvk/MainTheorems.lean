import Clean.Ironwood.CommitIvk.GateTheorems
import Clean.Ironwood.CommitIvk.ChunkTheorems
import Clean.Ironwood.Sinsemilla.CommitDomainTheorems
import Clean.Ironwood.Specs.Sinsemilla
import Clean.Ironwood.Specs.SinsemillaBreak
import Clean.Ironwood.Utilities.RunningSum

/-!
# Orchard incoming viewing key commitment

Port of `orchard@0.14.0/src/circuit/commit_ivk.rs` `gadgets::commit_ivk` and its
synthesis helpers (`ak_canonicity`, `nk_canonicity`).

`ivk = Commit^ivk_rivk(I2LEBSP₂₅₅(ak) || I2LEBSP₂₅₅(nk))`, extracting the `x`-coordinate
of the Sinsemilla short commitment. The message is decomposed into four Sinsemilla pieces:

```
a = bits   0..=249 of ak                                            (250 bits, 25 words)
b = b_0 || b_1 || b_2
  = (bits 250..=253 of ak) || (bit 254 of ak) || (bits 0..=4 of nk) (10 bits,  1 word)
c = bits   5..=244 of nk                                            (240 bits, 24 words)
d = d_0 || d_1 = (bits 245..=253 of nk) || (bit 254 of nk)          (10 bits,  1 word)
```

The custom canonicity gate lives in `Clean.Ironwood.CommitIvk.GateTheorems` under
`Halo2.Ironwood.CommitIvk.Gate`; this entry circuit depends on `Sinsemilla.Domain` (the
`CommitDomain` hash exposing the running sums needed for the `ak`/`nk` canonicity
checks).
-/

namespace Halo2.Ironwood.CommitIvk

open Halo2.Ironwood.Specs (K)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Halo2.Ironwood.Specs.Sinsemilla (Generators)
open Halo2.Ironwood.Ecc
open Halo2.Ironwood.Sinsemilla

/-- Inputs of `commit_ivk`: the already-assigned full viewing key cells `ak`, `nk`, and
the prover-side full-width blinding scalar behind the `ScalarFixed` value `rivk`. -/
structure Input (F : Type) where
  ak : F
  nk : F
  rivk : UnconstrainedNat F
deriving CircuitType

open Halo2.Ironwood.Specs (bitrange bitrange_lt cast_bitrange_val)
open Halo2.Ironwood.Specs.Sinsemilla (commitIvkChunks hashToPoint running_sum_telescope
  hashToPointB SpecOrBreak breaksOfGuarded chunksOf_mem_lt)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)
open Halo2.Ironwood.NoteCommit (pallasBaseCard_eq tPNat val_shift high_bit_canonical
  shifted_high_zero)

/-- Semantic statement that the four Sinsemilla pieces `a, b, c, d` are exactly the
`commit_ivk` message pieces for `ak`/`nk`, in the indexed form consumed by the chunk
bridge `pieceChunks_eq_commitIvkChunks_of_indexed_piece_values`. -/
def CommitIvkPieceValues (ak nk : Fp) (a b c d : Fp) : Prop :=
  a = ((ak.val % 2 ^ (K * 25) : ℕ) : Fp) ∧
  b = ((ak.val / 2 ^ 250 % 16 + (ak.val / 2 ^ 254 % 2) * 16 + (nk.val % 2 ^ 5) * 32 : ℕ) : Fp) ∧
  c = (((nk.val / 2 ^ 5) % 2 ^ (K * 24) : ℕ) : Fp) ∧
  d = ((nk.val / 2 ^ 245 % 2 ^ 9 + (nk.val / 2 ^ 254 % 2) * 512 : ℕ) : Fp)

/-- The gate's canonical bit slices are exactly the indexed `commit_ivk` piece values.
`bitrange n s len = n / 2^s % 2^len`, so each slice is the divisor/modulus combination the
chunk bridge expects. -/
theorem commitIvkPieceValues_of_gate_spec (row : Gate.Input Fp) (hSpec : Gate.Spec row) :
    CommitIvkPieceValues row.ak row.nk row.a row.bWhole row.c row.dWhole := by
  simp only [Gate.Spec] at hSpec
  obtain ⟨ha, hb0, hb1, hb2, hc, hd0, hd1, hbW, hdW⟩ := hSpec
  have ha' : row.a = ((bitrange row.ak.val 0 250 : ℕ) : Fp) := by
    rw [← ha]; exact (ZMod.natCast_rightInverse row.a).symm
  have hb0' : row.b0 = ((bitrange row.ak.val 250 4 : ℕ) : Fp) := by
    rw [← hb0]; exact (ZMod.natCast_rightInverse row.b0).symm
  have hb1' : row.b1 = ((bitrange row.ak.val 254 1 : ℕ) : Fp) := by
    rw [← hb1]; exact (ZMod.natCast_rightInverse row.b1).symm
  have hb2' : row.b2 = ((bitrange row.nk.val 0 5 : ℕ) : Fp) := by
    rw [← hb2]; exact (ZMod.natCast_rightInverse row.b2).symm
  have hc' : row.c = ((bitrange row.nk.val 5 240 : ℕ) : Fp) := by
    rw [← hc]; exact (ZMod.natCast_rightInverse row.c).symm
  have hd0' : row.d0 = ((bitrange row.nk.val 245 9 : ℕ) : Fp) := by
    rw [← hd0]; exact (ZMod.natCast_rightInverse row.d0).symm
  have hd1' : row.d1 = ((bitrange row.nk.val 254 1 : ℕ) : Fp) := by
    rw [← hd1]; exact (ZMod.natCast_rightInverse row.d1).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha']; norm_num [bitrange, K]
  · rw [hbW, hb0', hb1', hb2']
    simp only [bitrange, pow_zero, Nat.div_one]
    push_cast; ring
  · rw [hc']; norm_num [bitrange, K]
  · rw [hdW, hd0', hd1']
    simp only [bitrange]
    push_cast; ring

/-! ### `Canonicity`: the `ak`/`nk` canonicity decomposition and gate

Virtual subcircuit (no constraint/VK impact) factoring the two `CopyCheck` running-sum
decompositions and the `CommitIvk` canonicity gate out of the monolithic entry. Modeled on
`NoteCommit.ConstraintChecks`. Its `Spec` is the gate payoff in the indexed-piece-value form
that the chunk bridge consumes. -/
namespace Canonicity

/-- The gate-relevant cells assigned by the entry before the canonicity checks: the input
keys, the four Sinsemilla pieces (`a, b, c, d`), the sub-pieces (`b0, b1, b2, d0, d1`), and
the two fully-decomposed Sinsemilla running-sum tails (`z13A, z13C`). -/
structure Input (F : Type) where
  ak : F
  nk : F
  a : F
  b : F
  c : F
  d : F
  b0 : F
  b1 : F
  b2 : F
  d0 : F
  d1 : F
  z13A : F
  z13C : F
deriving ProvableStruct

/-- A `CopyCheck` running-sum decomposition telescopes: from `zs[0] = element` and the
per-step `zs[i] = 2^K·zs[i+1] + word` facts (each `word < 2^K`), the head and tail cells
satisfy `zs[0] = lo + 2^(K·n)·zs[n]` with `lo < 2^(K·n)`. -/
private theorem copyCheck_telescope {n : ℕ} (zs : Vector Fp (n + 1))
    (hstep : ∀ i : Fin n, ∃ word : ℕ, word < 2 ^ K ∧
      zs[i.val]'(Nat.lt_succ_of_lt i.isLt) =
        2 ^ K * zs[i.val + 1]'(Nat.succ_lt_succ i.isLt) + (word : Fp)) :
    ∃ lo : ℕ, lo < 2 ^ (K * n) ∧
      zs[0]'(Nat.succ_pos n) =
        ((lo : ℕ) : Fp) + ((2 ^ (K * n) : ℕ) : Fp) * zs[n]'(Nat.lt_succ_self n) := by
  have hz : ∀ i, i < n → ∃ w : ℕ, w < 2 ^ K ∧
      (fun j => if hj : j < n + 1 then zs[j]'hj else 0) i =
        ((w : ℕ) : Fp) + ((2 ^ K : ℕ) : Fp) *
          (fun j => if hj : j < n + 1 then zs[j]'hj else 0) (i + 1) := by
    intro i hi
    obtain ⟨word, hword, heq⟩ := hstep ⟨i, hi⟩
    refine ⟨word, hword, ?_⟩
    simp only [dif_pos (Nat.lt_succ_of_lt hi), dif_pos (Nat.succ_lt_succ hi)]
    push_cast
    rw [heq]; ring
  obtain ⟨lo, hlo, hz0⟩ := running_sum_telescope K
    (fun j => if hj : j < n + 1 then zs[j]'hj else 0) n hz
  refine ⟨lo, hlo, ?_⟩
  simp only [dif_pos (Nat.succ_pos n), dif_pos (Nat.lt_succ_self n)] at hz0
  push_cast at hz0 ⊢
  convert hz0 using 2

/-- Rely-conditions provided by the surrounding entry: the short pieces are range-checked,
`b`/`d` are the witnessed sub-piece recombinations, and `z13A`/`z13C` are the fully-decomposed
Sinsemilla running-sum tails of `a`/`c` (canonical because the hash range-checks every word). -/
def Assumptions (input : Input Fp) : Prop :=
  input.a.val < 2 ^ 250 ∧
    input.b0.val < 2 ^ 4 ∧
    input.b2.val < 2 ^ 5 ∧
    input.c.val < 2 ^ 240 ∧
    input.d0.val < 2 ^ 9 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp)

/-- The canonical-decomposition payoff (= `Gate.Spec` spelled over the `Canonicity` cells):
the sub-pieces are the canonical little-endian bit slices of `ak`/`nk`. -/
def Spec (input : Input Fp) : Prop :=
  input.a.val = bitrange input.ak.val 0 250 ∧
    input.b0.val = bitrange input.ak.val 250 4 ∧
    input.b1.val = bitrange input.ak.val 254 1 ∧
    input.b2.val = bitrange input.nk.val 0 5 ∧
    input.c.val = bitrange input.nk.val 5 240 ∧
    input.d0.val = bitrange input.nk.val 245 9 ∧
    input.d1.val = bitrange input.nk.val 254 1 ∧
    input.b = input.b0 + input.b1 * 16 + input.b2 * 32 ∧
    input.d = input.d0 + input.d1 * 512

/-- A `.val` splits as low + `2^k` · high (over the natural-number value, cast to `Fp`). -/
private theorem val_decomp (v k : ℕ) :
    ((v : ℕ) : Fp) = ((v % 2 ^ k : ℕ) : Fp) + ((2 ^ k : ℕ) : Fp) * ((v / 2 ^ k : ℕ) : Fp) := by
  have h : v % 2 ^ k + 2 ^ k * (v / 2 ^ k) = v := Nat.mod_add_div v (2 ^ k)
  have hc := congrArg (Nat.cast (R := Fp)) h
  rw [Nat.cast_add, Nat.cast_mul] at hc
  exact hc.symm

/-- The pure-field bit facts feeding `completeness`: the canonical top bits `b1`/`d1` are
boolean, and once set they force the shifted decompositions `a' = a + 2^130 - t_P` and
`b2c' = b2 + c·2^5 + 2^140 - t_P` to have vanishing high parts. Split out of
`completeness` so that no single declaration exhausts its heartbeat budget (4.30 bump). -/
private theorem completeness_bit_facts {ak nk a b2 c b1 d1 : Fp}
    (ha_val : a.val = bitrange ak.val 0 250)
    (hb1_val : b1.val = bitrange ak.val 254 1)
    (hb2_val : b2.val = bitrange nk.val 0 5)
    (hc_val : c.val = bitrange nk.val 5 240)
    (hd1_val : d1.val = bitrange nk.val 254 1) :
    (b1 = 0 ∨ b1 = 1) ∧ (d1 = 0 ∨ d1 = 1) ∧
      (b1 = 1 → ((a.val / 2 ^ 130 : ℕ) : Fp) = 0 ∧
        (((a + ((2 ^ 130 : ℕ) : Fp) - tP).val / 2 ^ 130 : ℕ) : Fp) = 0) ∧
      (d1 = 1 →
        (((b2 + ((2 ^ 5 : ℕ) : Fp) * c + ((2 ^ 140 : ℕ) : Fp) - tP).val / 2 ^ 140 : ℕ) : Fp)
          = 0) := by
  have hak : ak.val < PALLAS_BASE_CARD := ZMod.val_lt _
  have hnk : nk.val < PALLAS_BASE_CARD := ZMod.val_lt _
  -- Fp-cast forms of the `.val` slice facts, needed for reconstruction/recombination
  have hb1_eq : b1 = ((bitrange ak.val 254 1 : ℕ) : Fp) := by
    rw [← hb1_val]; exact (ZMod.natCast_rightInverse b1).symm
  have hb2_eq : b2 = ((bitrange nk.val 0 5 : ℕ) : Fp) := by
    rw [← hb2_val]; exact (ZMod.natCast_rightInverse b2).symm
  have hc_eq : c = ((bitrange nk.val 5 240 : ℕ) : Fp) := by
    rw [← hc_val]; exact (ZMod.natCast_rightInverse c).symm
  have hd1_eq : d1 = ((bitrange nk.val 254 1 : ℕ) : Fp) := by
    rw [← hd1_val]; exact (ZMod.natCast_rightInverse d1).symm
  -- the low 245-bit `nk` part `b2 + c·2^5` equals `bitrange nk 0 245`
  have hb2c_val : (b2 + ((2 ^ 5 : ℕ) : Fp) * c).val = bitrange nk.val 0 245 := by
    have hcast : b2 + ((2 ^ 5 : ℕ) : Fp) * c
        = ((bitrange nk.val 0 245 : ℕ) : Fp) := by
      rw [hb2_eq, hc_eq, Halo2.Ironwood.Specs.bitrange_add nk.val 0 5 240]; push_cast; ring
    rw [hcast, ZMod.val_natCast_of_lt
      (lt_trans (bitrange_lt _ 0 245) (by norm_num [PALLAS_BASE_CARD]))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `b_1` is `0` or `1`
    have hlt := bitrange_lt ak.val 254 1
    rcases (by omega : bitrange ak.val 254 1 = 0 ∨ bitrange ak.val 254 1 = 1) with h | h
    · left; rw [hb1_eq, h]; simp
    · right; rw [hb1_eq, h]; simp
  · -- `d_1` is `0` or `1`
    have hlt := bitrange_lt nk.val 254 1
    rcases (by omega : bitrange nk.val 254 1 = 0 ∨ bitrange nk.val 254 1 = 1) with h | h
    · left; rw [hd1_eq, h]; simp
    · right; rw [hd1_eq, h]; simp
  · -- `b_1 = 1 → a'.val / 2^130 = 0`
    intro h1
    have hbr : bitrange ak.val 254 1 = 1 := by
      have hlt := bitrange_lt ak.val 254 1
      rcases (by omega : bitrange ak.val 254 1 = 0 ∨ bitrange ak.val 254 1 = 1) with h | h
      · rw [hb1_eq, h] at h1; norm_num at h1
      · exact h
    obtain ⟨_, hlo, _⟩ := high_bit_canonical hak hbr
    refine ⟨?_, ?_⟩
    · rw [ha_val]
      rw [Halo2.Ironwood.NoteCommit.bitrange_low_div ak.val 130 120,
        Halo2.Ironwood.NoteCommit.high_bit_high_zero hak hbr (by norm_num) (by norm_num)]
      simp
    · rw [shifted_high_zero (by norm_num) (by norm_num) (ha_val ▸ hlo)]; simp
  · -- `d_1 = 1 → b2c'.val / 2^140 = 0`
    intro h1
    have hbr : bitrange nk.val 254 1 = 1 := by
      have hlt := bitrange_lt nk.val 254 1
      rcases (by omega : bitrange nk.val 254 1 = 0 ∨ bitrange nk.val 254 1 = 1) with h | h
      · rw [hd1_eq, h] at h1; norm_num at h1
      · exact h
    obtain ⟨_, hlo, _⟩ := high_bit_canonical hnk hbr
    have hlo245 : bitrange nk.val 0 245 < tPNat := by
      have hle : bitrange nk.val 0 245 ≤ bitrange nk.val 0 250 := by
        simp only [bitrange, pow_zero, Nat.div_one]
        calc nk.val % 2 ^ 245 = nk.val % 2 ^ 250 % 2 ^ 245 := by
              rw [Nat.mod_mod_of_dvd _ (by norm_num [pow_dvd_pow])]
          _ ≤ nk.val % 2 ^ 250 := Nat.mod_le _ _
      omega
    rw [shifted_high_zero (by norm_num) (by norm_num) (hb2c_val ▸ hlo245)]; simp

end Canonicity

/-! ### Sinsemilla decomposition helpers (shared by `Commit` and the top-level entry) -/

/-- The head piece of a `PieceChunks` decomposition is a digit sum of `n+1` `K`-bit words,
hence its `.val` is `< 2^(K·(n+1))` and equals that digit sum. -/
private theorem pieceChunks_head_digits {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (h : Halo2.Ironwood.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    ∃ ms : ℕ → ℕ, (∀ r, ms r < 2 ^ K) ∧
      pieces[0] = ((∑ r ∈ Finset.range (n + 1),
        ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
      (∀ i, i < n + 1 → chunks.getD i 0 = ms i) ∧
      Halo2.Ironwood.Sinsemilla.Chain.PieceChunks rest pieces.tail (chunks.drop (n + 1)) := by
  simp only [Halo2.Ironwood.Sinsemilla.Chain.PieceChunks] at h
  obtain ⟨ms, hms, hpc, tailChunks, hchunks, hPC⟩ := h
  subst hchunks
  refine ⟨ms, hms, hpc, ?_, ?_⟩
  · intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
    simp only [List.getElem?_map, List.getElem?_range, hi, Option.map_some, Option.getD_some]
  · rwa [List.drop_left' (by simp)]

open Halo2.Ironwood.Specs.Sinsemilla in
/-- `2^(K·m) < PALLAS_BASE_CARD` for the message piece widths used here (`m ≤ 25`). -/
private theorem two_pow_K_lt_card {m : ℕ} (hm : m ≤ 25) :
    2 ^ (K * m) < PALLAS_BASE_CARD := by
  have hle : K * m ≤ 250 := by
    simp only [K]; omega
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hle)
    (by norm_num [PALLAS_BASE_CARD])

open Halo2.Ironwood.Specs.Sinsemilla in
/-- From the head-piece digit data of a `PieceChunks` decomposition (`ms`, the cast-sum
fact, and `chunks.getD i 0 = ms i` on the head segment), the piece value's `.val` is the
digit sum, hence `< 2^(K·(n+1))`, and the `ZsFacts` running-sum cell at index `r ≤ n`
equals `(piece.val / 2^(K·r) : Fp)`. -/
private theorem zsFacts_cell_eq_div {n : ℕ} {piece : Fp} {chunks : List ℕ} {ms : ℕ → ℕ}
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

open Halo2.Ironwood.Specs.Sinsemilla in
/-- The head piece of a `(n :: rest)` `PieceChunks` decomposition has `.val < 2^(K·(n+1))`
(it is a digit sum of `n+1` `K`-bit words). -/
private theorem pieceChunks_head_val_lt {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (hm : n + 1 ≤ 25)
    (h : Halo2.Ironwood.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    ZMod.val (pieces[0] : Fp) < 2 ^ (K * (n + 1)) := by
  obtain ⟨ms, hms, hpc, -, -⟩ := pieceChunks_head_digits h
  rw [hpc, ZMod.val_natCast_of_lt
    (lt_trans (sum_digits_lt hms (n + 1)) (two_pow_K_lt_card hm))]
  exact sum_digits_lt hms (n + 1)

/-- The `a` (`pieces[0]`) and `c` (`pieces[2]`) message pieces of the `commit_ivk`
decomposition are `< 2^250` and `< 2^240` respectively. -/
private theorem commit_pieceChunks_ac_bounds {pieces : Vector Fp 4} {chunks : List ℕ}
    (hPC : Halo2.Ironwood.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0] pieces chunks) :
    ZMod.val (pieces[0] : Fp) < 2 ^ 250 ∧ ZMod.val (pieces[2] : Fp) < 2 ^ 240 := by
  obtain ⟨-, -, -, -, hPCtail⟩ := pieceChunks_head_digits hPC
  obtain ⟨-, -, -, -, hPCtail2⟩ := pieceChunks_head_digits hPCtail
  have hA := pieceChunks_head_val_lt (by norm_num) hPC
  have hC := pieceChunks_head_val_lt (by norm_num) hPCtail2
  rw [show K * 25 = 250 from by norm_num [K]]
    at hA
  rw [show K * 24 = 240 from by norm_num [K]]
    at hC
  have ht2 : (pieces.tail.tail[0]'(by decide) : Fp) = pieces[2] :=
    (Vector.getElem_tail (v := pieces.tail) (i := 0) (hi := by decide)).trans
      (Vector.getElem_tail (v := pieces) (i := 1) (hi := by decide))
  exact ⟨hA, ht2 ▸ hC⟩

open Halo2.Ironwood.Specs.Sinsemilla in
/-- The `z₁₃` running-sum cell of a head piece (`HVec.head zs`, index 13) is the
`130`-bit-shifted piece value `piece.val / 2^130`. Combines the `ZsFacts` head identity
with the `PieceChunks` digit data via `zsFacts_cell_eq_div` (at `r = 13`). -/
private theorem zsFacts_head_cell_eq_div {n : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {pieces : Vector Fp (n :: rest).length}
    {zs : HVec (Halo2.Ironwood.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
    (hm : n + 1 ≤ 25) (h13 : 13 ≤ n)
    (hPC : Halo2.Ironwood.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks)
    (hZsHead : HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) =>
      ((∑ j ∈ Finset.range (n + 1 - r.val),
        chunks.getD (r.val + j) 0 * 2 ^ (K * j) : ℕ) : Fp))) :
    (HVec.head zs)[13]'(Nat.lt_succ_of_le h13)
      = (((pieces[0] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  obtain ⟨ms, hms, hpc, hgetD, -⟩ := pieceChunks_head_digits hPC
  rw [hZsHead, Vector.getElem_ofFn]
  rw [zsFacts_cell_eq_div hm hms hpc hgetD h13,
    show K * 13 = 130 from by norm_num [K]]

open Halo2.Ironwood.Specs.Sinsemilla in
/-- The `z₁₃` running-sum cell of the `c` piece (`commit_ivk`'s `[24,0,23,0]` index 2) is
`c.val / 2^130`. Recurses into the `ZsFacts`/`PieceChunks` tails twice, then applies the head
cell lemma to the `[23,0]` sub-decomposition. -/
private theorem zsFacts_get2_cell_eq_div {pieces : Vector Fp 4} {chunks : List ℕ}
    {zs : HVec (Halo2.Ironwood.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) Fp}
    (hPC : Halo2.Ironwood.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0] pieces chunks)
    (hZs : Halo2.Ironwood.Sinsemilla.Chain.ZsFacts [24, 0, 23, 0] chunks zs) :
    (HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) zs ⟨2, by decide⟩)[13]'(by decide)
      = (((pieces[2] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  obtain ⟨-, -, -, -, hPCtail⟩ := pieceChunks_head_digits hPC
  obtain ⟨-, -, -, -, hPCtail2⟩ := pieceChunks_head_digits hPCtail
  simp only [Halo2.Ironwood.Sinsemilla.Chain.ZsFacts] at hZs
  obtain ⟨-, -, hZsHeadC, -⟩ := hZs
  have hcell := zsFacts_head_cell_eq_div (n := 23) (by norm_num) (by norm_num) hPCtail2 hZsHeadC
  have ht2 : (pieces.tail.tail[0]'(by decide) : Fp) = pieces[2] :=
    (Vector.getElem_tail (v := pieces.tail) (i := 0) (hi := by decide)).trans
      (Vector.getElem_tail (v := pieces) (i := 1) (hi := by decide))
  exact ht2 ▸ hcell

open Halo2.Ironwood.Specs.Sinsemilla in
/-- The `z₁₃` cell of an honest head running-sum vector is `piece.val / 2^130`
(`pieceZ piece 13`, with `K·13 = 130`). -/
private theorem zsHonest_head_cell_eq_div {n : ℕ} {rest : List ℕ} (h13 : 13 ≤ n)
    {pieces : Vector Fp (n :: rest).length}
    {zs : HVec (Halo2.Ironwood.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
    (hZsHead : HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) =>
      Halo2.Ironwood.Sinsemilla.pieceZ pieces[0] r.val)) :
    (HVec.head zs)[13]'(Nat.lt_succ_of_le h13)
      = (((pieces[0] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  rw [hZsHead, Vector.getElem_ofFn]
  simp only [Halo2.Ironwood.Sinsemilla.pieceZ,
    show K * 13 = 130 from by norm_num [K]]

open Halo2.Ironwood.Specs.Sinsemilla in
/-- The `z₁₃` cell of the honest `c` running-sum vector (index 2 of `[24,0,23,0]`) is
`c.val / 2^130`. -/
private theorem zsHonest_get2_cell_eq_div {pieces : Vector Fp 4}
    {zs : HVec (Halo2.Ironwood.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) Fp}
    (hZs : Halo2.Ironwood.Sinsemilla.Chain.ZsHonest [24, 0, 23, 0] pieces zs) :
    (HVec.get (Halo2.Ironwood.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) zs ⟨2, by decide⟩)[13]'(by decide)
      = (((pieces[2] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  simp only [Halo2.Ironwood.Sinsemilla.Chain.ZsHonest] at hZs
  obtain ⟨-, -, hZsHeadC, -⟩ := hZs
  have hcell := zsHonest_head_cell_eq_div (n := 23) (rest := [0]) (by norm_num)
    (pieces := pieces.tail.tail) hZsHeadC
  have ht2 : (pieces.tail.tail[0]'(by decide) : Fp) = pieces[2] :=
    (Vector.getElem_tail (v := pieces.tail) (i := 0) (hi := by decide)).trans
      (Vector.getElem_tail (v := pieces) (i := 1) (hi := by decide))
  exact ht2 ▸ hcell

/-! ### `Commit`: the witnessing + Sinsemilla hash, isolated behind a clean output

Virtual subcircuit (no constraint/VK impact) wrapping all of `commit_ivk`'s witnessing and
the `CommitDomain` Sinsemilla hash. Factoring it out gives the top-level entry a
single folded `Commit.Output` at a clean offset, instead of the nested `WithZs`+`WitnessShort`
offset chain that the `Canonicity` `FormalAssertion` input would otherwise embed (the
whnf-timeout that blocked the monolithic proof — see `doc/performance-problems.md`). -/
namespace Commit

/-- The scalar cells (point + pieces + sub-pieces), bundled separately so the top-level
`Output` is a 2-component struct `[Cells, HVec]` — exactly the shape of `WithZs.Output`,
whose `eval` reduces cheaply. A flat 11-component struct ending in the `HVec` makes the
ProvableStruct `eval` flattening blow up. -/
structure Cells (F : Type) where
  point : Point F
  a : F
  b : F
  c : F
  d : F
  b0 : F
  b1 : F
  b2 : F
  d0 : F
  d1 : F
deriving ProvableStruct

/-- The output, parametrized over the running-sum list `ns` so its `eval` projection
lemmas (`eval_cells`/`eval_zs`) are proved *generically* — stuck on the symbolic `ns` —
and merely instantiated at the concrete `[24, 0, 23, 0]`. Proving them at the concrete list
forces `ProvableStruct.eval`'s 51-element `HVec` flattening, which whnf-times out. -/
structure OutputGen (ns : List ℕ) (F : Type) where
  cells : Cells F
  zs : HVec (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns) F

instance (ns : List ℕ) : ProvableStruct (OutputGen ns) where
  components := [Cells, HVec (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns)]
  toComponents := fun { cells, zs } => .cons cells (.cons zs .nil)
  fromComponents := fun (.cons cells (.cons zs .nil)) => { cells, zs }

/-- Hand-written analogue of the `deriving ProvableStruct` handler's generated
`fromComponents_cons` simp lemma (the instance above is hand-written, so none is
generated): lets `simp` reduce `fromComponents` applications without going through the
private match auxiliary, which no longer reduces at reducible transparency (4.30 bump). -/
@[circuit_norm]
theorem OutputGen.fromComponents_cons (ns : List ℕ) {F : Type}
    (cells : Cells F) (zs : HVec (Halo2.Ironwood.Sinsemilla.Chain.zLengths ns) F) :
    fromComponents (α := OutputGen ns) (F := F)
      (.cons cells (.cons zs .nil)) = { cells, zs } := rfl

theorem eval_cells (ns : List ℕ) (env : Environment Fp) (out : Var (OutputGen ns) Fp) :
    (eval env out).cells = eval env out.cells := by
  rw [ProvableStruct.eval_eq_eval]
  unfold ProvableStruct.eval
  simp only [circuit_norm]

theorem eval_zs (ns : List ℕ) (env : Environment Fp) (out : Var (OutputGen ns) Fp) :
    (eval env out).zs = eval env out.zs := by
  rw [ProvableStruct.eval_eq_eval]
  unfold ProvableStruct.eval
  simp only [circuit_norm]

theorem withZs_eval_point (env : Environment Fp) (ns : List ℕ)
    (out : Var (CommitDomain.Output ns) Fp) :
    (eval env out).point = eval env out.point := by
  rw [ProvableStruct.eval_eq_eval]
  unfold ProvableStruct.eval
  simp only [circuit_norm]

@[reducible] def Output : TypeMap := OutputGen [24, 0, 23, 0]

/-- The facts the entry needs from the hash: the short range bounds, the wide-piece bounds,
the running-sum tail identities, and the existence of a chunk decomposition whose hash is the
commitment point (blinded by some `rivk`). -/
def Spec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (_input : Value Input Fp) (output : Value Output Fp) (_ : ProverData Fp) : Prop :=
  output.cells.b0.val < 2 ^ 4 ∧ output.cells.b2.val < 2 ^ 5 ∧ output.cells.d0.val < 2 ^ 9 ∧
    output.cells.a.val < 2 ^ 250 ∧ output.cells.c.val < 2 ^ 240 ∧
    (HVec.get _ output.zs ⟨0, by decide⟩)[13] = ((output.cells.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    (HVec.get _ output.zs ⟨2, by decide⟩)[13] = ((output.cells.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ (chunks : List ℕ) (rivk : Fq),
      Halo2.Ironwood.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0]
        #v[output.cells.a, output.cells.b, output.cells.c, output.cells.d] chunks ∧
      (∀ B, hashToPoint G.S Q chunks = some B →
        output.cells.point = B + rivk • R)

def ProverAssumptions (G : Generators) (Q : Point Fp)
    (_R : MulFixed.FixedBase) (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  let ak : Fp := input.ak
  let nk : Fp := input.nk
  (∃ B, hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B) ∧
  -- the blinding-scalar hint is the canonical natural representative of `rivk : Fq`
  (show ℕ from input.rivk) < PALLAS_SCALAR_CARD

def ProverSpec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (output : ProverValue Output Fp) (_ : ProverHint Fp) : Prop :=
  let ak : Fp := input.ak
  let nk : Fp := input.nk
  output.cells.b0.val < 2 ^ 4 ∧ output.cells.b2.val < 2 ^ 5 ∧ output.cells.d0.val < 2 ^ 9 ∧
    output.cells.a.val < 2 ^ 250 ∧ output.cells.c.val < 2 ^ 240 ∧
    (HVec.get _ output.zs ⟨0, by decide⟩)[13] = ((output.cells.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    (HVec.get _ output.zs ⟨2, by decide⟩)[13] = ((output.cells.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    output.cells.a = ((bitrange ak.val 0 250 : ℕ) : Fp) ∧
    output.cells.b0 = ((bitrange ak.val 250 4 : ℕ) : Fp) ∧
    output.cells.b1 = ((bitrange ak.val 254 1 : ℕ) : Fp) ∧
    output.cells.b2 = ((bitrange nk.val 0 5 : ℕ) : Fp) ∧
    output.cells.c = ((bitrange nk.val 5 240 : ℕ) : Fp) ∧
    output.cells.d0 = ((bitrange nk.val 245 9 : ℕ) : Fp) ∧
    output.cells.d1 = ((bitrange nk.val 254 1 : ℕ) : Fp) ∧
    output.cells.b = output.cells.b0 + output.cells.b1 * 16 + output.cells.b2 * 32 ∧
    output.cells.d = output.cells.d0 + output.cells.d1 * 512 ∧
    ∃ (chunks : List ℕ),
      Halo2.Ironwood.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0]
        #v[output.cells.a, output.cells.b, output.cells.c, output.cells.d] chunks ∧
      (∀ B, hashToPoint G.S Q chunks = some B →
        output.cells.point = B + ((show ℕ from input.rivk : ℕ) : Fq) • R)

/-- The honest `commit_ivk` message pieces (canonical bit slices of `ak`/`nk`) satisfy the
`PieceBounds` and their honest chunks are `commitIvkChunks ak.val nk.val`. Stated over the
abstract piece cells (with their honest-slice values) so the heavy WithZs offsets never enter
the kernel-checked term. -/
theorem honest_pieces_facts (ak nk a b c d : Fp)
    (ha : a = ((bitrange ak.val 0 250 : ℕ) : Fp))
    (hb : b = ((bitrange ak.val 250 4 : ℕ) : Fp) + ((bitrange ak.val 254 1 : ℕ) : Fp) * 2 ^ 4
            + ((bitrange nk.val 0 5 : ℕ) : Fp) * 2 ^ 5)
    (hc : c = ((bitrange nk.val 5 240 : ℕ) : Fp))
    (hd : d = ((bitrange nk.val 245 9 : ℕ) : Fp) + ((bitrange nk.val 254 1 : ℕ) : Fp) * 2 ^ 9) :
    Halo2.Ironwood.Sinsemilla.Chain.PieceBounds [24, 0, 23, 0] #v[a, b, c, d] ∧
    Halo2.Ironwood.Sinsemilla.Chain.honestChunks [24, 0, 23, 0] #v[a, b, c, d]
      = Halo2.Ironwood.Specs.Sinsemilla.commitIvkChunks ak.val nk.val := by
  -- the four piece values, recast into the indexed `(divisor/modulus)` form the bridge wants
  have hbN : b = ((ak.val / 2 ^ 250 % 16 + (ak.val / 2 ^ 254 % 2) * 16 + (nk.val % 2 ^ 5) * 32
      : ℕ) : Fp) := by rw [hb]; simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring
  have hdN : d = ((nk.val / 2 ^ 245 % 2 ^ 9 + (nk.val / 2 ^ 254 % 2) * 512 : ℕ) : Fp) := by
    rw [hd]; simp only [bitrange]; push_cast; ring
  have haN : a = ((ak.val % 2 ^ (K * 25) : ℕ) : Fp) := by
    rw [ha]; norm_num [bitrange, K]
  have hcN : c = (((nk.val / 2 ^ 5) % 2 ^ (K * 24) : ℕ) : Fp) := by
    rw [hc]; norm_num [bitrange, K]
  -- the `.val`s of the honest pieces are bounded by their bit widths
  have hak : ak.val < 2 ^ 255 := lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD])
  have hnk : nk.val < 2 ^ 255 := lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD])
  have haval : a.val < 2 ^ (K * 25) := by
    rw [haN, ZMod.val_natCast_of_lt
      (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) (by norm_num [K, PALLAS_BASE_CARD]))]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hcval : c.val < 2 ^ (K * 24) := by
    rw [hcN, ZMod.val_natCast_of_lt
      (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) (by norm_num [K, PALLAS_BASE_CARD]))]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbbound : (ak.val / 2 ^ 250 % 16 + (ak.val / 2 ^ 254 % 2) * 16 + (nk.val % 2 ^ 5) * 32) < 1024 := by
    have h1 : ak.val / 2 ^ 250 % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have h2 : ak.val / 2 ^ 254 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have h3 : nk.val % 2 ^ 5 < 32 := Nat.mod_lt _ (by norm_num)
    omega
  have hbval : b.val < 2 ^ (K * 1) := by
    rw [hbN, ZMod.val_natCast_of_lt (lt_trans hbbound (by norm_num [PALLAS_BASE_CARD]))]
    simpa [K] using hbbound
  have hdbound : (nk.val / 2 ^ 245 % 2 ^ 9 + (nk.val / 2 ^ 254 % 2) * 512) < 1024 := by
    have h1 : nk.val / 2 ^ 245 % 2 ^ 9 < 512 := Nat.mod_lt _ (by norm_num)
    have h2 : nk.val / 2 ^ 254 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have hdval : d.val < 2 ^ (K * 1) := by
    rw [hdN, ZMod.val_natCast_of_lt (lt_trans hdbound (by norm_num [PALLAS_BASE_CARD]))]
    simpa [K] using hdbound
  have hbounds : Halo2.Ironwood.Sinsemilla.Chain.PieceBounds [24, 0, 23, 0] #v[a, b, c, d] := by
    simp only [Halo2.Ironwood.Sinsemilla.Chain.PieceBounds]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · show a.val < _; exact haval
    · show b.val < _; exact hbval
    · show c.val < _; exact hcval
    · show d.val < _; exact hdval
  refine ⟨hbounds, ?_⟩
  exact honestChunks_eq_commitIvkChunks hbounds
    (by simpa using haN) (by simpa [bitrange] using hbN) (by simpa using hcN)
    (by simpa [bitrange] using hdN) hak hnk

end Commit

/-- Breaks-as-data `Commit^ivk` relation (zcash/ironwood#45): either the Sinsemilla
chain over the canonical `commit_ivk` chunks is defined and `ivk` is the extracted
short commitment, or the incomplete-addition escape is exhibited as a valid break.
Projecting the break branch to `⊥` recovers `ivk ∈ {…, ⊥}` (§4.17.4). -/
def Spec (G : Generators) (Q : Point Fp)
    (R : MulFixed.FixedBase) (ak nk ivk : Fp) : Prop :=
  ∃ rivk : Fq,
    SpecOrBreak G.S Q (fun B => ivk = (B + rivk • R).x)
      (hashToPointB G.S Q (commitIvkChunks ak.val nk.val))

/-- Honest-prover version of `Spec`, for the prover's concrete `rivk`. -/
def ProverSpec (G : Generators) (Q : Point Fp)
    (R : MulFixed.FixedBase) (ak nk : Fp) (rivk : Fq) (ivk : Fp) : Prop :=
  ∀ B : Point Fp,
    hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B →
      ivk = (B + rivk • R).x

/-- Honest proving needs the Sinsemilla hash-to-point to succeed for the canonical
`commit_ivk` message. -/
def ProverAssumptions (G : Generators) (Q : Point Fp) (ak nk : Fp) : Prop :=
  ∃ B, hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B

-- The top-level composition of `Commit` (witnessing + the `WithZs` Sinsemilla hash, behind a
-- folded `Commit.Output`) with the `Canonicity` subcircuit (CopyCheck decompositions + gate) is
-- fully proven (soundness + completeness, kernel-checked). The glue (1) reads the `Commit`
-- `ProverSpec`/`Spec` ranges, `z13A/z13C` running-sum tails, and canonical slices, (2) feeds them
-- as the `Canonicity.Assumptions`, (3) reads `Canonicity.Spec` as indexed piece values and applies
-- the chunk bridge `pieceChunks_eq_commitIvkChunks_of_indexed_piece_values` to get
-- `chunks = commitIvkChunks`, and (4) threads the hash relation to the entry output
-- `ivk = out.point.x`. A one-shot `circuit_proof_start` whnf-times-out; the working start is
-- each child spec separately and keeping the `Commit` output opaque (see
-- `doc/performance-problems.md`).
/-- The `Canonicity` canonical-slice spec gives exactly the indexed `commit_ivk` piece
values consumed by the chunk bridge (same content as `commitIvkPieceValues_of_gate_spec`,
spelled over the `Canonicity` cells). -/
private theorem commitIvkPieceValues_of_canonicity_spec (row : Canonicity.Input Fp)
    (hSpec : Canonicity.Spec row) :
    CommitIvkPieceValues row.ak row.nk row.a row.b row.c row.d := by
  simp only [Canonicity.Spec] at hSpec
  obtain ⟨ha, hb0, hb1, hb2, hc, hd0, hd1, hbW, hdW⟩ := hSpec
  have ha' : row.a = ((bitrange row.ak.val 0 250 : ℕ) : Fp) := by
    rw [← ha]; exact (ZMod.natCast_rightInverse row.a).symm
  have hb0' : row.b0 = ((bitrange row.ak.val 250 4 : ℕ) : Fp) := by
    rw [← hb0]; exact (ZMod.natCast_rightInverse row.b0).symm
  have hb1' : row.b1 = ((bitrange row.ak.val 254 1 : ℕ) : Fp) := by
    rw [← hb1]; exact (ZMod.natCast_rightInverse row.b1).symm
  have hb2' : row.b2 = ((bitrange row.nk.val 0 5 : ℕ) : Fp) := by
    rw [← hb2]; exact (ZMod.natCast_rightInverse row.b2).symm
  have hc' : row.c = ((bitrange row.nk.val 5 240 : ℕ) : Fp) := by
    rw [← hc]; exact (ZMod.natCast_rightInverse row.c).symm
  have hd0' : row.d0 = ((bitrange row.nk.val 245 9 : ℕ) : Fp) := by
    rw [← hd0]; exact (ZMod.natCast_rightInverse row.d0).symm
  have hd1' : row.d1 = ((bitrange row.nk.val 254 1 : ℕ) : Fp) := by
    rw [← hd1]; exact (ZMod.natCast_rightInverse row.d1).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha']; norm_num [bitrange, K]
  · rw [hbW, hb0', hb1', hb2']
    simp only [bitrange, pow_zero, Nat.div_one]
    push_cast; ring
  · rw [hc']; norm_num [bitrange, K]
  · rw [hdW, hd0', hd1']
    simp only [bitrange]
    push_cast; ring

end Halo2.Ironwood.CommitIvk
