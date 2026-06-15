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

-- TODO(note_commit): bundle into a `GeneralFormalCircuit.WithHint`. Blocked on:
--   (1) `soundness` (prime-`p` canonicity: the gates force the inputs canonical, and the
--       pieces equal `noteCommitChunks`'s tiling via `noteCommitChunks_tiling`) +
--       `completeness`. This is the largest remaining proof.

end Orchard.NoteCommit
