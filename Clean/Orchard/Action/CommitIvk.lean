import Clean.Orchard.Action.CommitIvkGate
import Clean.Orchard.Action.CommitIvkChunks
import Clean.Orchard.Sinsemilla.CommitDomain
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Utilities

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

The custom canonicity gate lives in `Clean.Orchard.Action.CommitIvkGate` under
`Orchard.Action.CommitIvk.Gate`; this entry circuit depends on `Sinsemilla.Domain` (the
`CommitDomain` hash exposing the running sums needed for the `ak`/`nk` canonicity
checks).
-/

namespace Orchard.Action.CommitIvk

open Orchard.Specs (K)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Ecc
open Orchard.Sinsemilla

/-- Inputs of `commit_ivk`: the already-assigned full viewing key cells `ak`, `nk`, and
the prover-side full-width blinding scalar behind the `ScalarFixed` value `rivk`. -/
structure Input (F : Type) where
  ak : F
  nk : F
  rivk : UnconstrainedNat F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ ak := default, nk := default, rivk := default }⟩

open Orchard.Specs (bitrange bitrange_lt cast_bitrange_val)
open Orchard.Specs.Sinsemilla (commitIvkChunks hashToPoint running_sum_telescope)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)
open Orchard.Action.NoteCommit (pallasBaseCard_eq tPNat val_shift high_bit_canonical
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

instance : Inhabited (Var Input Fp) :=
  ⟨{ ak := default, nk := default, a := default, b := default, c := default, d := default,
     b0 := default, b1 := default, b2 := default, d0 := default, d1 := default,
     z13A := default, z13C := default }⟩

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

def main (input : Var Input Fp) : Circuit Fp Unit := do
  -- a' = a + 2^130 - t_P, decomposed by the 13-word `CopyCheck` (`z₀ <== a'` wires the
  -- shift into the running-sum column, matching halo2's `witness_check(a_prime, …)`).
  let aPrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13
    (input.a + Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const tP)
  let b2cPrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14
    (input.b2 + Expression.const ((2 ^ 5 : ℕ) : Fp) * input.c +
      Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const tP)
  -- The two canonicity guards `b_1 · z13_a_prime = 0` and `d_1 · z14_b2_c_prime = 0`.
  -- Halo2 enables these as part of the `q_commit_ivk` gate; the `Gate` assertion (below)
  -- re-checks them, but it also *assumes* the equivalent `b_1 = 1 → z13_a_prime = 0`
  -- implications, which are only soundly available to the entry from these constraints.
  assertZero (input.b1 * aPrimeZs[13])
  assertZero (input.d1 * b2cPrimeZs[14])
  Gate.circuit
    { ak := input.ak, nk := input.nk, a := input.a, bWhole := input.b, c := input.c,
      dWhole := input.d, b0 := input.b0, b1 := input.b1, b2 := input.b2,
      d0 := input.d0, d1 := input.d1, z13A := input.z13A, z13C := input.z13C,
      aPrime := aPrimeZs[0], b2CPrime := b2cPrimeZs[0],
      z13APrime := aPrimeZs[13], z14B2CPrime := b2cPrimeZs[14] }

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

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

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec,
    Utilities.LookupRangeCheck.CopyCheck.circuit, Gate.circuit]
  obtain ⟨ha_lt, hb0_lt, hb2_lt, hc_lt, hd0_lt, hz13A, hz13C⟩ := h_assumptions
  obtain ⟨hCopyA, hCopyB, hbz, hdz, hGate⟩ := h_holds
  -- name the two `CopyCheck` output vectors and their head/step facts
  simp only [Utilities.LookupRangeCheck.CopyCheck.Spec] at hCopyA hCopyB
  obtain ⟨ha0, hastep⟩ := hCopyA
  obtain ⟨hb0', hbstep⟩ := hCopyB
  -- telescope decompositions over the two `CopyCheck` output vectors (inferred from the steps)
  obtain ⟨loA, hloA, hdecA⟩ := copyCheck_telescope _ hastep
  obtain ⟨loB, hloB, hdecB⟩ := copyCheck_telescope _ hbstep
  -- the gate reads the same head/tail cells; align spellings to `Vector.map`/`getElem`
  simp only [Vector.getElem_map, Vector.getElem_cast] at ha0 hb0' hdecA hdecB hbz hdz
  -- apply the gate: build its 13 assumptions, get the canonical-slice spec
  apply hGate
  simp only [Gate.Assumptions]
  refine ⟨ha_lt, hb0_lt, hb2_lt, hc_lt, hd0_lt, ?_, hz13A, ⟨loA, hloA, ?_⟩, ?_, ?_, hz13C,
    ⟨loB, hloB, ?_⟩, ?_⟩
  · -- aPrime = a + 2^130 - tP
    rw [ha0]
  · -- aPrime = loA + 2^130 · z13APrime
    rw [show (K : ℕ) * 13 = 130 from by norm_num [K]] at hdecA
    convert hdecA using 2
  · -- b1 = 1 → z13APrime = 0
    intro h1
    rcases mul_eq_zero.mp hbz with h | h
    · exact absurd (h1 ▸ h) one_ne_zero
    · exact h
  · -- b2cPrime = b2 + c·2^5 + 2^140 - tP
    rw [hb0']; push_cast; ring
  · -- b2cPrime = loB + 2^140 · z14B2CPrime
    rw [show (K : ℕ) * 14 = 140 from by norm_num [K]] at hdecB
    convert hdecB using 2
  · -- d1 = 1 → z14B2CPrime = 0
    intro h1
    rcases mul_eq_zero.mp hdz with h | h
    · exact absurd (h1 ▸ h) one_ne_zero
    · exact h

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
      rw [hb2_eq, hc_eq, Orchard.Specs.bitrange_add nk.val 0 5 240]; push_cast; ring
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
      rw [Orchard.Action.NoteCommit.bitrange_low_div ak.val 130 120,
        Orchard.Action.NoteCommit.high_bit_high_zero hak hbr (by norm_num) (by norm_num)]
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

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec,
    Utilities.LookupRangeCheck.CopyCheck.circuit,
    Utilities.LookupRangeCheck.CopyCheck.ProverSpec, Gate.circuit, Gate.Assumptions, Gate.Spec]
  obtain ⟨ha_lt, hb0_lt, hb2_lt, hc_lt, hd0_lt, hz13A, hz13C⟩ := h_assumptions
  obtain ⟨ha_val, hb0_val, hb1_val, hb2_val, hc_val, hd0_val, hd1_val, hbWs, hdWs⟩ := h_spec
  -- 4.30 bump: plain projections instead of `obtain` on the big `h_env` conjunction
  -- (rcases motive abstraction is a whnf storm)
  have hCopyA := h_env.1.2
  have hCopyB := h_env.2.2
  clear h_env
  -- the pure-field bit facts, split out into `completeness_bit_facts` (4.30 bump)
  obtain ⟨hb1cases, hd1cases, hImplA, hImplB⟩ :=
    completeness_bit_facts ha_val hb1_val hb2_val hc_val hd1_val
  -- `aPrime`/`b2cPrime` values, and the running-sum tail cells (13th of `a'`, 14th of `b2c'`).
  -- 4.30 bump: no `set aP/bP` here — abstracting the shifted values over the big goal and
  -- context was a ~270k-heartbeat kabstract/defeq storm; the bullets below use the explicit
  -- `input_a + 2^130 - tP` / `input_b2 + 2^5·c + 2^140 - tP` spellings instead
  have hcellA0 := hCopyA ⟨0, by norm_num⟩
  have hcellA13 := hCopyA ⟨13, by norm_num⟩
  have hcellB0 := hCopyB ⟨0, by norm_num⟩
  have hcellB14 := hCopyB ⟨14, by norm_num⟩
  simp only [show (K : ℕ) * 0 = 0 from by norm_num, show (K : ℕ) * 13 = 130 from by norm_num [K],
    show (K : ℕ) * 14 = 140 from by norm_num [K], pow_zero, Nat.div_one]
    at hcellA0 hcellA13 hcellB0 hcellB14
  -- assemble: discharge each gate-assumption / guard conjunct, rewriting cells as needed
  refine ⟨?_, ?_, ?_⟩
  · -- b1 · (a'[13]) = 0
    rw [hcellA13]
    rcases hb1cases with h | h
    · rw [h]; ring
    · rw [(hImplA h).2]; ring
  · -- d1 · (b2c'[14]) = 0
    rw [hcellB14]
    rcases hd1cases with h | h
    · rw [h]; ring
    · rw [hImplB h]; ring
  -- the gate prover-assumption is `Gate.Assumptions ∧ Gate.Spec`; the spec part is `h_spec`
  refine ⟨⟨ha_lt, hb0_lt, hb2_lt, hc_lt, hd0_lt, ?_, hz13A, ?_, ?_, ?_, hz13C, ?_, ?_⟩,
    ha_val, hb0_val, hb1_val, hb2_val, hc_val, hd0_val, hd1_val, hbWs, hdWs⟩
  · -- aPrime = a + 2^130 - t_P
    rw [hcellA0]; exact ZMod.natCast_rightInverse _
  · -- ∃ lo < 2^130, a' = lo + 2^130 · (a'.val/2^130)
    rw [hcellA0, hcellA13]
    refine ⟨(input_a + ((2 ^ 130 : ℕ) : Fp) - tP).val % 2 ^ 130,
      Nat.mod_lt _ (Nat.two_pow_pos 130), ?_⟩
    exact val_decomp (input_a + ((2 ^ 130 : ℕ) : Fp) - tP).val 130
  · -- b1 = 1 → a'[13] = 0
    intro h1; rw [hcellA13, (hImplA h1).2]
  · -- b2cPrime = b2 + c·2^5 + 2^140 - t_P
    rw [hcellB0, ZMod.natCast_rightInverse
      (input_b2 + ((2 ^ 5 : ℕ) : Fp) * input_c + ((2 ^ 140 : ℕ) : Fp) - tP)]
    ring
  · -- ∃ lo < 2^140, b2c' = lo + 2^140 · (b2c'.val/2^140)
    rw [hcellB0, hcellB14]
    refine ⟨(input_b2 + ((2 ^ 5 : ℕ) : Fp) * input_c + ((2 ^ 140 : ℕ) : Fp) - tP).val % 2 ^ 140,
      Nat.mod_lt _ (Nat.two_pow_pos 140), ?_⟩
    exact val_decomp (input_b2 + ((2 ^ 5 : ℕ) : Fp) * input_c + ((2 ^ 140 : ℕ) : Fp) - tP).val 140
  · -- d1 = 1 → b2c'[14] = 0
    intro h1; rw [hcellB14, hImplB h1]

def circuit : FormalAssertion Fp Input where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Canonicity

/-! ### Sinsemilla decomposition helpers (shared by `Commit` and the top-level entry) -/

/-- The head piece of a `PieceChunks` decomposition is a digit sum of `n+1` `K`-bit words,
hence its `.val` is `< 2^(K·(n+1))` and equals that digit sum. -/
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

open Orchard.Specs.Sinsemilla in
/-- `2^(K·m) < PALLAS_BASE_CARD` for the message piece widths used here (`m ≤ 25`). -/
private theorem two_pow_K_lt_card {m : ℕ} (hm : m ≤ 25) :
    2 ^ (K * m) < PALLAS_BASE_CARD := by
  have hle : K * m ≤ 250 := by
    simp only [K]; omega
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hle)
    (by norm_num [PALLAS_BASE_CARD])

open Orchard.Specs.Sinsemilla in
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

open Orchard.Specs.Sinsemilla in
/-- The head piece of a `(n :: rest)` `PieceChunks` decomposition has `.val < 2^(K·(n+1))`
(it is a digit sum of `n+1` `K`-bit words). -/
private theorem pieceChunks_head_val_lt {n : ℕ} {rest : List ℕ}
    {pieces : Vector Fp (n :: rest).length} {chunks : List ℕ}
    (hm : n + 1 ≤ 25)
    (h : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks) :
    ZMod.val (pieces[0] : Fp) < 2 ^ (K * (n + 1)) := by
  obtain ⟨ms, hms, hpc, -, -⟩ := pieceChunks_head_digits h
  rw [hpc, ZMod.val_natCast_of_lt
    (lt_trans (sum_digits_lt hms (n + 1)) (two_pow_K_lt_card hm))]
  exact sum_digits_lt hms (n + 1)

/-- The `a` (`pieces[0]`) and `c` (`pieces[2]`) message pieces of the `commit_ivk`
decomposition are `< 2^250` and `< 2^240` respectively. -/
private theorem commit_pieceChunks_ac_bounds {pieces : Vector Fp 4} {chunks : List ℕ}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0] pieces chunks) :
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

open Orchard.Specs.Sinsemilla in
/-- The `z₁₃` running-sum cell of a head piece (`HVec.head zs`, index 13) is the
`130`-bit-shifted piece value `piece.val / 2^130`. Combines the `ZsFacts` head identity
with the `PieceChunks` digit data via `zsFacts_cell_eq_div` (at `r = 13`). -/
private theorem zsFacts_head_cell_eq_div {n : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {pieces : Vector Fp (n :: rest).length}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
    (hm : n + 1 ≤ 25) (h13 : 13 ≤ n)
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks (n :: rest) pieces chunks)
    (hZsHead : HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) =>
      ((∑ j ∈ Finset.range (n + 1 - r.val),
        chunks.getD (r.val + j) 0 * 2 ^ (K * j) : ℕ) : Fp))) :
    (HVec.head zs)[13]'(Nat.lt_succ_of_le h13)
      = (((pieces[0] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  obtain ⟨ms, hms, hpc, hgetD, -⟩ := pieceChunks_head_digits hPC
  rw [hZsHead, Vector.getElem_ofFn]
  rw [zsFacts_cell_eq_div hm hms hpc hgetD h13,
    show K * 13 = 130 from by norm_num [K]]

open Orchard.Specs.Sinsemilla in
/-- The `z₁₃` running-sum cell of the `c` piece (`commit_ivk`'s `[24,0,23,0]` index 2) is
`c.val / 2^130`. Recurses into the `ZsFacts`/`PieceChunks` tails twice, then applies the head
cell lemma to the `[23,0]` sub-decomposition. -/
private theorem zsFacts_get2_cell_eq_div {pieces : Vector Fp 4} {chunks : List ℕ}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) Fp}
    (hPC : Orchard.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0] pieces chunks)
    (hZs : Orchard.Sinsemilla.Chain.ZsFacts [24, 0, 23, 0] chunks zs) :
    (HVec.get (Orchard.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) zs ⟨2, by decide⟩)[13]'(by decide)
      = (((pieces[2] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  obtain ⟨-, -, -, -, hPCtail⟩ := pieceChunks_head_digits hPC
  obtain ⟨-, -, -, -, hPCtail2⟩ := pieceChunks_head_digits hPCtail
  simp only [Orchard.Sinsemilla.Chain.ZsFacts] at hZs
  obtain ⟨-, -, hZsHeadC, -⟩ := hZs
  have hcell := zsFacts_head_cell_eq_div (n := 23) (by norm_num) (by norm_num) hPCtail2 hZsHeadC
  have ht2 : (pieces.tail.tail[0]'(by decide) : Fp) = pieces[2] :=
    (Vector.getElem_tail (v := pieces.tail) (i := 0) (hi := by decide)).trans
      (Vector.getElem_tail (v := pieces) (i := 1) (hi := by decide))
  exact ht2 ▸ hcell

open Orchard.Specs.Sinsemilla in
/-- The `z₁₃` cell of an honest head running-sum vector is `piece.val / 2^130`
(`pieceZ piece 13`, with `K·13 = 130`). -/
private theorem zsHonest_head_cell_eq_div {n : ℕ} {rest : List ℕ} (h13 : 13 ≤ n)
    {pieces : Vector Fp (n :: rest).length}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths (n :: rest)) Fp}
    (hZsHead : HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) =>
      Orchard.Sinsemilla.pieceZ pieces[0] r.val)) :
    (HVec.head zs)[13]'(Nat.lt_succ_of_le h13)
      = (((pieces[0] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  rw [hZsHead, Vector.getElem_ofFn]
  simp only [Orchard.Sinsemilla.pieceZ,
    show K * 13 = 130 from by norm_num [K]]

open Orchard.Specs.Sinsemilla in
/-- The `z₁₃` cell of the honest `c` running-sum vector (index 2 of `[24,0,23,0]`) is
`c.val / 2^130`. -/
private theorem zsHonest_get2_cell_eq_div {pieces : Vector Fp 4}
    {zs : HVec (Orchard.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) Fp}
    (hZs : Orchard.Sinsemilla.Chain.ZsHonest [24, 0, 23, 0] pieces zs) :
    (HVec.get (Orchard.Sinsemilla.Chain.zLengths [24, 0, 23, 0]) zs ⟨2, by decide⟩)[13]'(by decide)
      = (((pieces[2] : Fp).val / 2 ^ 130 : ℕ) : Fp) := by
  simp only [Orchard.Sinsemilla.Chain.ZsHonest] at hZs
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
  zs : HVec (Orchard.Sinsemilla.Chain.zLengths ns) F

instance (ns : List ℕ) : ProvableStruct (OutputGen ns) where
  components := [Cells, HVec (Orchard.Sinsemilla.Chain.zLengths ns)]
  toComponents := fun { cells, zs } => .cons cells (.cons zs .nil)
  fromComponents := fun (.cons cells (.cons zs .nil)) => { cells, zs }

/-- Hand-written analogue of the `deriving ProvableStruct` handler's generated
`fromComponents_cons` simp lemma (the instance above is hand-written, so none is
generated): lets `simp` reduce `fromComponents` applications without going through the
private match auxiliary, which no longer reduces at reducible transparency (4.30 bump). -/
@[circuit_norm]
theorem OutputGen.fromComponents_cons (ns : List ℕ) {F : Type}
    (cells : Cells F) (zs : HVec (Orchard.Sinsemilla.Chain.zLengths ns) F) :
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

/-- Single-leaf projections of an evaluated `Cells`. Proved generically (stuck on the
ProvableStruct round-trip) so each cell value is one `Expression.eval`, never forcing the
sibling `point` coordinates. -/
theorem eval_cells_leaves (env : Environment Fp) (c : Var Cells Fp) :
    (eval env c).a = Expression.eval env c.a ∧
    (eval env c).b = Expression.eval env c.b ∧
    (eval env c).c = Expression.eval env c.c ∧
    (eval env c).d = Expression.eval env c.d ∧
    (eval env c).b0 = Expression.eval env c.b0 ∧
    (eval env c).b1 = Expression.eval env c.b1 ∧
    (eval env c).b2 = Expression.eval env c.b2 ∧
    (eval env c).d0 = Expression.eval env c.d0 ∧
    (eval env c).d1 = Expression.eval env c.d1 := by
  rw [ProvableStruct.eval_eq_eval]
  unfold ProvableStruct.eval
  simp only [circuit_norm]

theorem eval_cells_point (env : Environment Fp) (c : Var Cells Fp) :
    (eval env c).point = eval env c.point := by
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

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (input : Var Input Fp) : Circuit Fp (Var Output Fp) := do
  let ak := input.ak
  let nk := input.nk

  -- Witness and range-constrain the short subpieces b_0 (4 bits), b_2 (5 bits) of `ak`/`nk`,
  -- and d_0 (9 bits) of `nk`.
  let b0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 250 4 (by norm_num [K])
    (unconstrained do return ak)
  let b2 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 5 (by norm_num [K])
    (unconstrained do return nk)
  let d0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 245 9 (by norm_num [K])
    (unconstrained do return nk)

  -- The single-bit subpieces b_1, d_1 are boolean-constrained in the canonicity gate.
  let b1 ← witness (ak.val.bitrange 254 1).toField
  let d1 ← witness (nk.val.bitrange 254 1).toField

  -- The four Sinsemilla message pieces.
  let a ← witness (ak.val.bitrange 0 250).toField
  let b ← witness (b0 + b1 * (2 ^ 4 : Fp) + b2 * (2 ^ 5 : Fp) : Expression Fp)
  let c ← witness (nk.val.bitrange 5 240).toField
  let d ← witness (d0 + d1 * (2 ^ 9 : Fp) : Expression Fp)

  -- ivk = Commit^ivk_rivk(ak || nk); the short commit also exposes the per-piece running sums.
  let out ← CommitDomain.circuit G Q hQ R 24 [0, 23, 0]
    { pieces := #v[a, b, c, d], r := input.rivk }
  return { cells := { point := out.point, a, b, c, d, b0, b1, b2, d0, d1 }, zs := out.zs }

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp Input Output (main G Q hQ R) := by
  elaborate_circuit

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
      Orchard.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0]
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
      Orchard.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0]
        #v[output.cells.a, output.cells.b, output.cells.c, output.cells.d] chunks ∧
      (∀ B, hashToPoint G.S Q chunks = some B →
        output.cells.point = B + ((show ℕ from input.rivk : ℕ) : Fq) • R)

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) (fun _ _ => True)
      (Spec G Q R) := by
  circuit_proof_start_core
  dsimp only [main, circuit_norm] at h_holds ⊢
  obtain ⟨hB0, hB2, hD0, -, -, -, -, -, -, hWithZs, -⟩ := h_holds
  -- the three WitnessShort range bounds
  replace hB0 := hB0 trivial
  replace hB2 := hB2 trivial
  replace hD0 := hD0 trivial
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_soundness] at hB0 hB2 hD0
  simp only [Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.WitnessShort.Spec, circuit_norm] at hB0 hB2 hD0
  -- the WithZs hash spec
  replace hWithZs := hWithZs trivial
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_soundness] at hWithZs
  rw [show (CommitDomain.circuit G Q hQ R 24 [0, 23, 0]).Spec
      = CommitDomain.Spec G Q R 24 [0, 23, 0] from rfl] at hWithZs
  simp only [CommitDomain.Spec] at hWithZs
  obtain ⟨chunks, r, hPC, hZs, hHash⟩ := hWithZs
  refine ⟨?_, ?_⟩
  swap
  · refine ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, trivial, trivial, trivial, trivial,
      trivial, trivial, Or.inl rfl, trivial⟩
  simp only [Commit.Spec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Commit.eval_cells, (Commit.eval_cells_leaves env _).2.2.2.2.1]; exact hB0
  · rw [Commit.eval_cells, (Commit.eval_cells_leaves env _).2.2.2.2.2.2.1]; exact hB2
  · rw [Commit.eval_cells, (Commit.eval_cells_leaves env _).2.2.2.2.2.2.2.1]; exact hD0
  · rw [Commit.eval_cells, (Commit.eval_cells_leaves env _).1]
    have hAC := commit_pieceChunks_ac_bounds hPC
    convert hAC.1 using 2; simp only [circuit_norm]; rfl
  · rw [Commit.eval_cells, (Commit.eval_cells_leaves env _).2.2.1]
    have hAC := commit_pieceChunks_ac_bounds hPC
    convert hAC.2 using 2; simp only [circuit_norm]; rfl
  · obtain ⟨hZsHeadA, hZsTail⟩ := hZs
    have hz13a := zsFacts_head_cell_eq_div (n := 24) (by norm_num) (by norm_num) hPC hZsHeadA
    rw [Commit.eval_cells, (Commit.eval_cells_leaves env _).1]
    -- align both `zs` spellings to `eval env (… .zs)` (same `EntryZs` term), then the head
    -- cell is one shared `eval`; the head piece value is the entry `a` cell (one cell)
    rw [CommitDomain.eval_zs] at hz13a
    rw [Commit.eval_zs]
    exact hz13a.trans (by simp only [circuit_norm]; rfl)
  · have hz13c := zsFacts_get2_cell_eq_div hPC hZs
    rw [Commit.eval_cells, (Commit.eval_cells_leaves env _).2.2.1]
    rw [CommitDomain.eval_zs] at hz13c
    rw [Commit.eval_zs]
    exact hz13c.trans (by simp only [circuit_norm]; rfl)
  · refine ⟨chunks, r, ?_, fun B hB => ?_⟩
    · -- the four message pieces are the same cells the hash decomposed
      simp only [circuit_norm] at hPC
      convert hPC using 2
      rw [Commit.eval_cells]
      simp only [(Commit.eval_cells_leaves env _).1, (Commit.eval_cells_leaves env _).2.1,
        (Commit.eval_cells_leaves env _).2.2.1, (Commit.eval_cells_leaves env _).2.2.2.1]
      simp only [circuit_norm]
      rfl
    · -- the commitment point coords coincide with the hash output's
      have hpt := hHash B hB
      -- the goal point coords coincide (definitionally, one point) with the hash output's;
      -- align both spellings to `eval env (point Var)` first so the bridge is one cheap `rfl`
      rw [Commit.withZs_eval_point] at hpt
      rw [Commit.eval_cells, Commit.eval_cells_point]
      exact Eq.trans rfl hpt

/-- The honest `commit_ivk` message pieces (canonical bit slices of `ak`/`nk`) satisfy the
`PieceBounds` and their honest chunks are `commitIvkChunks ak.val nk.val`. Stated over the
abstract piece cells (with their honest-slice values) so the heavy WithZs offsets never enter
the kernel-checked term. -/
private theorem honest_pieces_facts (ak nk a b c d : Fp)
    (ha : a = ((bitrange ak.val 0 250 : ℕ) : Fp))
    (hb : b = ((bitrange ak.val 250 4 : ℕ) : Fp) + ((bitrange ak.val 254 1 : ℕ) : Fp) * 2 ^ 4
            + ((bitrange nk.val 0 5 : ℕ) : Fp) * 2 ^ 5)
    (hc : c = ((bitrange nk.val 5 240 : ℕ) : Fp))
    (hd : d = ((bitrange nk.val 245 9 : ℕ) : Fp) + ((bitrange nk.val 254 1 : ℕ) : Fp) * 2 ^ 9) :
    Orchard.Sinsemilla.Chain.PieceBounds [24, 0, 23, 0] #v[a, b, c, d] ∧
    Orchard.Sinsemilla.Chain.honestChunks [24, 0, 23, 0] #v[a, b, c, d]
      = Orchard.Specs.Sinsemilla.commitIvkChunks ak.val nk.val := by
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
  have hbounds : Orchard.Sinsemilla.Chain.PieceBounds [24, 0, 23, 0] #v[a, b, c, d] := by
    simp only [Orchard.Sinsemilla.Chain.PieceBounds]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · show a.val < _; exact haval
    · show b.val < _; exact hbval
    · show c.val < _; exact hcval
    · show d.val < _; exact hdval
  refine ⟨hbounds, ?_⟩
  exact honestChunks_eq_commitIvkChunks hbounds
    (by simpa using haN) (by simpa [bitrange] using hbN) (by simpa using hcN)
    (by simpa [bitrange] using hdN) hak hnk

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q R) (ProverSpec G Q R) := by
  circuit_proof_start_core
  dsimp only [main, circuit_norm] at h_env ⊢
  -- Extract the three `WitnessShort` honest values and the `WithZs` honest spec, via the
  -- `usesLocalWitnesses` rfl bridge (no `circuit_norm`, which would flatten the heavy output).
  have hB0 := h_env.1
  have hB2 := h_env.2.1
  have hD0 := h_env.2.2.1
  have hEb1 := h_env.2.2.2.1
  have hEd1 := h_env.2.2.2.2.1
  have hEa := h_env.2.2.2.2.2.1
  have hEb := h_env.2.2.2.2.2.2.1
  have hEc := h_env.2.2.2.2.2.2.2.1
  have hEd := h_env.2.2.2.2.2.2.2.2.1
  have hWZ := h_env.2.2.2.2.2.2.2.2.2.1
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_usesLocalWitnesses] at hB0 hB2 hD0 hWZ
  clear h_env
  replace hB0 := (hB0 trivial).2
  replace hB2 := (hB2 trivial).2
  replace hD0 := (hD0 trivial).2
  simp +instances only [Utilities.LookupRangeCheck.WitnessShort.circuit,
    Utilities.LookupRangeCheck.WitnessShort.ProverSpec, circuit_norm] at hB0 hB2 hD0
  replace hEb1 := hEb1 ⟨0, by norm_num⟩
  replace hEd1 := hEd1 ⟨0, by norm_num⟩
  replace hEa := hEa ⟨0, by norm_num⟩
  replace hEb := hEb ⟨0, by norm_num⟩
  replace hEc := hEc ⟨0, by norm_num⟩
  replace hEd := hEd ⟨0, by norm_num⟩
  simp +instances only [Utilities.LookupRangeCheck.WitnessShort.circuit, circuit_norm]
    at hEa hEb1 hEc hEd1 hEb hEd
  -- `WitnessShort.ProverSpec` now yields `.val = bitrange`; lift these to the `Fp`-cast form.
  replace hB0 : _ = ((bitrange _ 250 4 : ℕ) : Fp) := (ZMod.natCast_zmod_val _).symm.trans (by rw [hB0])
  replace hB2 : _ = ((bitrange _ 0 5 : ℕ) : Fp) := (ZMod.natCast_zmod_val _).symm.trans (by rw [hB2])
  replace hD0 : _ = ((bitrange _ 245 9 : ℕ) : Fp) := (ZMod.natCast_zmod_val _).symm.trans (by rw [hD0])
  -- the two recombination cells `b`, `d`, expressed through their sub-cells' honest values
  rw [hB0, hEb1, hB2] at hEb
  rw [hD0, hEd1] at hEd
  -- the two key field values (the pieces read the input through `eval`)
  have hak_eq : Expression.eval env.toEnvironment input_var.ak = input.ak := by
    rw [← h_input]; simp only [circuit_norm]
  have hnk_eq : Expression.eval env.toEnvironment input_var.nk = input.nk := by
    rw [← h_input]; simp only [circuit_norm]
  -- apply the `WithZs` honest spec: feed it the `ProverAssumptions` (pieces in range, hash exists)
  have hWZspec := (hWZ (by
    simp +instances only [CommitDomain.circuit, CommitDomain.ProverAssumptions,
      Utilities.LookupRangeCheck.WitnessShort.circuit, circuit_norm, hEa, hEb, hEc, hEd]
    refine ⟨(honest_pieces_facts (Expression.eval env.toEnvironment input_var.ak)
        (Expression.eval env.toEnvironment input_var.nk) _ _ _ _ rfl rfl rfl rfl).1, ?_, ?_⟩
    · rw [(honest_pieces_facts (Expression.eval env.toEnvironment input_var.ak)
        (Expression.eval env.toEnvironment input_var.nk) _ _ _ _ rfl rfl rfl rfl).2,
        hak_eq, hnk_eq]
      exact h_assumptions.1
    · show Witgen.M.evalNat env input_var.rivk < PALLAS_SCALAR_CARD
      rw [show Witgen.M.evalNat env input_var.rivk = input.rivk from by
        rw [← h_input]; simp only [circuit_norm]]
      exact h_assumptions.2)).2
  simp only [CommitDomain.circuit, CommitDomain.ProverSpec] at hWZspec
  obtain ⟨hZsH, hHash⟩ := hWZspec
  refine ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    ?_, trivial⟩, ?_⟩
  · -- WithZs.ProverAssumptions
    rw [GeneralFormalCircuit.WithHint.toSubcircuit_completeness]
    simp +instances only [CommitDomain.circuit, CommitDomain.ProverAssumptions,
      Utilities.LookupRangeCheck.WitnessShort.circuit, circuit_norm, hEa, hEb, hEc, hEd]
    refine ⟨(honest_pieces_facts (Expression.eval env.toEnvironment input_var.ak)
        (Expression.eval env.toEnvironment input_var.nk) _ _ _ _ rfl rfl rfl rfl).1, ?_, ?_⟩
    · rw [(honest_pieces_facts (Expression.eval env.toEnvironment input_var.ak)
        (Expression.eval env.toEnvironment input_var.nk) _ _ _ _ rfl rfl rfl rfl).2,
        hak_eq, hnk_eq]
      exact h_assumptions.1
    · show Witgen.M.evalNat env input_var.rivk < PALLAS_SCALAR_CARD
      rw [show Witgen.M.evalNat env input_var.rivk = input.rivk from by
        rw [← h_input]; simp only [circuit_norm]]
      exact h_assumptions.2
  · -- the strengthened ProverSpec; re-fold the (dsimp-reduced) output to a clean opaque var
    show ProverSpec G Q R input
      (eval env (ElaboratedCircuit.output (main G Q hQ R) input_var i₀)) env.hint
    set O := ElaboratedCircuit.output (main G Q hQ R) input_var i₀ with hO
    -- the honest cell values, projected to single cells (`eval_cells` + per-leaf), via `hO`
    have hOa : (eval env O).cells.a = ((bitrange (Expression.eval env.toEnvironment input_var.ak).val 0 250 : ℕ) : Fp) := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).1, hO]
      exact hEa
    have hOb0 : (eval env O).cells.b0 = ((bitrange (Expression.eval env.toEnvironment input_var.ak).val 250 4 : ℕ) : Fp) := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.1, hO]; exact hB0
    have hOb1 : (eval env O).cells.b1 = ((bitrange (Expression.eval env.toEnvironment input_var.ak).val 254 1 : ℕ) : Fp) := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.2.1, hO]; exact hEb1
    have hOb2 : (eval env O).cells.b2 = ((bitrange (Expression.eval env.toEnvironment input_var.nk).val 0 5 : ℕ) : Fp) := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.2.2.1, hO]; exact hB2
    have hOc : (eval env O).cells.c = ((bitrange (Expression.eval env.toEnvironment input_var.nk).val 5 240 : ℕ) : Fp) := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.1, hO]; exact hEc
    have hOd0 : (eval env O).cells.d0 = ((bitrange (Expression.eval env.toEnvironment input_var.nk).val 245 9 : ℕ) : Fp) := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.2.2.2.1, hO]; exact hD0
    have hOd1 : (eval env O).cells.d1 = ((bitrange (Expression.eval env.toEnvironment input_var.nk).val 254 1 : ℕ) : Fp) := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.2.2.2.2, hO]; exact hEd1
    have hOb : (eval env O).cells.b
        = ((bitrange (Expression.eval env.toEnvironment input_var.ak).val 250 4 : ℕ) : Fp)
          + ((bitrange (Expression.eval env.toEnvironment input_var.ak).val 254 1 : ℕ) : Fp) * 2 ^ 4
          + ((bitrange (Expression.eval env.toEnvironment input_var.nk).val 0 5 : ℕ) : Fp) * 2 ^ 5 := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.1, hO]; exact hEb
    have hOd : (eval env O).cells.d
        = ((bitrange (Expression.eval env.toEnvironment input_var.nk).val 245 9 : ℕ) : Fp)
          + ((bitrange (Expression.eval env.toEnvironment input_var.nk).val 254 1 : ℕ) : Fp) * 2 ^ 9 := by
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.1, hO]; exact hEd
    -- the two running-sum tail cells, identified with `a.val / 2^130` and `c.val / 2^130`
    -- through the honest `ZsHonest` running sums (mirrors the soundness z13a/z13c proofs)
    have hOz13a : (HVec.get _ (eval env O).zs ⟨0, by decide⟩)[13]
        = (((eval env O).cells.a.val / 2 ^ 130 : ℕ) : Fp) := by
      have hz13a := zsHonest_head_cell_eq_div (n := 24) (rest := [0, 23, 0]) (by norm_num) hZsH.1
      rw [CircuitType.eval_var_prover_to_verifier] at hz13a
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment _).1, hO]
      rw [CommitDomain.eval_zs] at hz13a
      rw [Commit.eval_zs]
      exact hz13a.trans (by simp only [circuit_norm]; rfl)
    have hOz13c : (HVec.get _ (eval env O).zs ⟨2, by decide⟩)[13]
        = (((eval env O).cells.c.val / 2 ^ 130 : ℕ) : Fp) := by
      have hz13c := zsHonest_get2_cell_eq_div hZsH
      rw [CircuitType.eval_var_prover_to_verifier] at hz13c
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment _).2.2.1, hO]
      rw [CommitDomain.eval_zs] at hz13c
      rw [Commit.eval_zs]
      exact hz13c.trans (by simp only [circuit_norm]; rfl)
    -- the hash existential: the honest chunks `commitIvkChunks ak nk` whose hash is the point
    have hOpf := honest_pieces_facts
      (Expression.eval env.toEnvironment input_var.ak) (Expression.eval env.toEnvironment input_var.nk)
      (eval env O).cells.a (eval env O).cells.b (eval env O).cells.c (eval env O).cells.d
      hOa hOb hOc hOd
    have hOhash : ∃ (chunks : List ℕ),
        Orchard.Sinsemilla.Chain.PieceChunks [24, 0, 23, 0]
          #v[(eval env O).cells.a, (eval env O).cells.b, (eval env O).cells.c, (eval env O).cells.d] chunks ∧
        (∀ B, hashToPoint G.S Q chunks = some B →
          (eval env O).cells.point = B + ((show ℕ from input.rivk : ℕ) : Fq) • R) := by
      refine ⟨Orchard.Specs.Sinsemilla.commitIvkChunks
        (Expression.eval env.toEnvironment input_var.ak).val
        (Expression.eval env.toEnvironment input_var.nk).val, ?_, ?_⟩
      · rw [← hOpf.2]
        exact Orchard.Sinsemilla.Chain.pieceChunks_honestChunks _ _ hOpf.1
      · intro B hB
        have hpt := hHash B (by
          simp +instances only [Utilities.LookupRangeCheck.WitnessShort.circuit, circuit_norm,
            hEa, hEb, hEc, hEd]
          rw [(honest_pieces_facts (Expression.eval env.toEnvironment input_var.ak)
              (Expression.eval env.toEnvironment input_var.nk) _ _ _ _ rfl rfl rfl rfl).2]
          exact hB)
        rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells, Commit.eval_cells_point, hO]
        rw [CircuitType.eval_var_prover_to_verifier, Commit.withZs_eval_point] at hpt
        simpa only [← h_input, circuit_norm] using hpt
    clear_value O
    unfold ProverSpec
    simp only [show (input.ak : Fp) = Expression.eval env.toEnvironment input_var.ak from hak_eq.symm,
      show (input.nk : Fp) = Expression.eval env.toEnvironment input_var.nk from hnk_eq.symm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hOb0, cast_bitrange_val (by norm_num)]
      exact bitrange_lt _ _ _
    · rw [hOb2, cast_bitrange_val (by norm_num)]
      exact bitrange_lt _ _ _
    · rw [hOd0, cast_bitrange_val (by norm_num)]
      exact bitrange_lt _ _ _
    · rw [hOa, cast_bitrange_val (by norm_num)]
      exact bitrange_lt _ _ _
    · rw [hOc, cast_bitrange_val (by norm_num)]
      exact bitrange_lt _ _ _
    · -- z13a
      exact hOz13a
    · -- z13c
      exact hOz13c
    · exact hOa
    · exact hOb0
    · exact hOb1
    · exact hOb2
    · exact hOc
    · exact hOd0
    · exact hOd1
    · rw [hOb, hOb0, hOb1, hOb2]; ring
    · rw [hOd, hOd0, hOd1]; ring
    · -- the hash existential
      exact hOhash

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Output where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q R
  ProverSpec := ProverSpec G Q R
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end Commit

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  -- All witnessing + the Sinsemilla hash, isolated behind a single folded `Commit.Output`.
  let out1 ← Commit.circuit G Q hQ R input

  -- ak/nk canonicity: the two `CopyCheck` decompositions and the canonicity gate, factored
  -- into the virtual `Canonicity` subcircuit. Its evaluated input is now clean `Commit.Output`
  -- projections (including the running-sum cells indexed from `out1.zs`) at one offset, not the
  -- nested `WithZs`+`WitnessShort` offset chain.
  Canonicity.circuit
    { ak := input.ak, nk := input.nk,
      a := out1.cells.a, b := out1.cells.b, c := out1.cells.c, d := out1.cells.d,
      b0 := out1.cells.b0, b1 := out1.cells.b1, b2 := out1.cells.b2,
      d0 := out1.cells.d0, d1 := out1.cells.d1,
      z13A := (HVec.get _ out1.zs ⟨0, by decide⟩)[13],
      z13C := (HVec.get _ out1.zs ⟨2, by decide⟩)[13] }
  return out1.cells.point.x

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp Input field (main G Q hQ R) := by
  elaborate_circuit

/-- The committed `ivk` is the `x`-coordinate of the Sinsemilla short commitment of the
canonical message `I2LEBSP₂₅₅(ak) || I2LEBSP₂₅₅(nk)`, blinded by `[rivk] CommitIvkR`. -/
def Spec (G : Generators) (Q : Point Fp)
    (R : MulFixed.FixedBase) (ak nk ivk : Fp) : Prop :=
  ∃ rivk : Fq, ∀ B : Point Fp,
    hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B →
      ivk = (B + rivk • R).x

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
-- `circuit_proof_start_core` then `dsimp only [main, circuit_norm] at h_holds/h_env`, projecting
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

/-- Build the `Canonicity` assumptions from the `Commit` hash spec facts, over an opaque
output variable `O`. Factored out so the (expensive) `HVec`-flattening `circuit_norm` cast on
the running-sum cells `z13A`/`z13C` is kernel-checked once here, not inlined into the entry
soundness term (see `doc/performance-problems.md`). -/
private theorem canonicity_assumptions_of_commit
    (O : Var Commit.Output Fp) (input_var : Var Input Fp) (env : Environment Fp)
    (hb0 : (Expression.eval env O.cells.b0).val < 2 ^ 4)
    (hb2 : (Expression.eval env O.cells.b2).val < 2 ^ 5)
    (hd0 : (Expression.eval env O.cells.d0).val < 2 ^ 9)
    (ha : (Expression.eval env O.cells.a).val < 2 ^ 250)
    (hc : (Expression.eval env O.cells.c).val < 2 ^ 240)
    (hz13a : (HVec.get (Chain.zLengths [24, 0, 23, 0]) (eval env O.zs) ⟨0, by decide⟩)[13]
      = (((Expression.eval env O.cells.a).val / 2 ^ 130 : ℕ) : Fp))
    (hz13c : (HVec.get (Chain.zLengths [24, 0, 23, 0]) (eval env O.zs) ⟨2, by decide⟩)[13]
      = (((Expression.eval env O.cells.c).val / 2 ^ 130 : ℕ) : Fp)) :
    Canonicity.circuit.Assumptions
      (eval env
        ({ ak := input_var.ak, nk := input_var.nk,
           a := O.cells.a, b := O.cells.b, c := O.cells.c, d := O.cells.d,
           b0 := O.cells.b0, b1 := O.cells.b1, b2 := O.cells.b2, d0 := O.cells.d0, d1 := O.cells.d1,
           z13A := (HVec.get (Chain.zLengths [24, 0, 23, 0]) O.zs ⟨0, by decide⟩)[13],
           z13C := (HVec.get (Chain.zLengths [24, 0, 23, 0]) O.zs ⟨2, by decide⟩)[13] }
          : Var Canonicity.Input Fp)) := by
  -- Project the `Canonicity.Input` eval field-by-field (cheap: 13 single-field projections),
  -- without ever forcing `eval env O.zs` (the 51-leaf flatten that `circuit_norm` triggers).
  -- Project the evaluated `Canonicity.Input` field-by-field. Crucially this is done with
  -- `ProvableStruct.eval_eq_eval` + the single-field projection only, so the running-sum
  -- fields stay as `Expression.eval env (… O.zs …)[13]` (one var lookup) and the 51-leaf
  -- `O.zs` heterogeneous vector is never flattened (unlike a full `circuit_norm`).
  rw [show Canonicity.circuit.Assumptions = Canonicity.Assumptions from rfl]
  simp only [Canonicity.Assumptions, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha
  · exact hb0
  · exact hb2
  · exact hc
  · exact hd0
  · exact (CircuitType.eval_expr env _).symm.trans
      ((HVec.eval_getElem env (Chain.zLengths [24, 0, 23, 0]) O.zs ⟨0, by decide⟩ 13
        (by decide)).trans hz13a)
  · exact (CircuitType.eval_expr env _).symm.trans
      ((HVec.eval_getElem env (Chain.zLengths [24, 0, 23, 0]) O.zs ⟨2, by decide⟩ 13
        (by decide)).trans hz13c)

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) (fun _ _ => True)
      (fun input ivk _ => Spec G Q R input.ak input.nk ivk) := by
  circuit_proof_start_core
  dsimp only [main, circuit_norm] at h_holds ⊢
  obtain ⟨hCommit, hCanon, -⟩ := h_holds
  -- The Commit subcircuit has trivial assumptions; obtain its Spec (via the `rfl` bridge,
  -- avoiding `circuit_norm`, which would flatten the expensive Commit output `eval`).
  replace hCommit := hCommit trivial
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_soundness] at hCommit
  -- Keep the (expensive-to-flatten) Commit output variable opaque.
  set O := (Commit.circuit G Q hQ R).output input_var i₀ with hO
  clear_value O
  simp only [Commit.circuit, Commit.Spec, Commit.eval_cells, Commit.eval_zs] at hCommit
  obtain ⟨hb0, hb2, hd0, ha, hc, hz13a, hz13c, chunks, rivk, hPC, hHash⟩ := hCommit
  -- Feed the Commit spec facts as the Canonicity assumptions; obtain the canonical slices.
  -- Convert the (small, `HVec`-free) `Cells` projections to the `Expression.eval` spelling the
  -- helper expects; the running-sum cells keep `eval env O.zs` opaque.
  simp only [circuit_norm] at ha hb0 hb2 hc hd0
  rw [show ((eval env O.cells).a : Fp) = Expression.eval env O.cells.a from by
    simp only [circuit_norm]] at hz13a
  rw [show ((eval env O.cells).c : Fp) = Expression.eval env O.cells.c from by
    simp only [circuit_norm]] at hz13c
  have hCanonSpec := hCanon
    (canonicity_assumptions_of_commit O input_var env hb0 hb2 hd0 ha hc hz13a hz13c)
  rw [show Canonicity.circuit.Spec = Canonicity.Spec from rfl] at hCanonSpec
  -- the canonical slices are exactly the indexed `commit_ivk` piece values
  have hPV := commitIvkPieceValues_of_canonicity_spec _ hCanonSpec
  simp only [circuit_norm, CommitIvkPieceValues] at hPV
  obtain ⟨hPVa, hPVb, hPVc, hPVd⟩ := hPV
  -- align the key spellings: `Expression.eval env input_var.{ak,nk}` are the input values
  have hakv : Expression.eval env input_var.ak = input.ak := by
    rw [← h_input]; simp only [circuit_norm]
  have hnkv : Expression.eval env input_var.nk = input.nk := by
    rw [← h_input]; simp only [circuit_norm]
  rw [hakv] at hPVa hPVb
  rw [hnkv] at hPVb hPVc hPVd
  -- bridge the four pieces to the `commit_ivk` chunk list
  set ak : Fp := input.ak with hak_def
  set nk : Fp := input.nk with hnk_def
  have hak : ak.val < 2 ^ 255 := lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD])
  have hnk : nk.val < 2 ^ 255 := lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD])
  have hchunks : chunks = Orchard.Specs.Sinsemilla.commitIvkChunks ak.val nk.val :=
    pieceChunks_eq_commitIvkChunks_of_indexed_piece_values hPC
      (by simp only [circuit_norm, K]; exact hPVa)
      (by simp only [circuit_norm]; simpa [bitrange] using hPVb)
      (by simp only [circuit_norm, K]; exact hPVc)
      (by simp only [circuit_norm]; simpa [bitrange] using hPVd) hak hnk
  -- assemble the entry spec
  refine ⟨?_, ?_⟩
  · refine ⟨rivk, fun B hB => ?_⟩
    have hpt := hHash B (by rw [hchunks]; exact hB)
    have hx := congrArg Point.x hpt
    rw [hO] at hx
    simpa [Point.add, Point.coords, circuit_norm] using hx
  · exact ⟨Or.inl rfl, Or.inl rfl, trivial⟩

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (fun input _ _ => ProverAssumptions G Q input.ak input.nk ∧
        (show ℕ from input.rivk) < PALLAS_SCALAR_CARD)
      (fun input ivk _ =>
        ProverSpec G Q R input.ak input.nk ((show ℕ from input.rivk : ℕ) : Fq) ivk) := by
  circuit_proof_start_core
  dsimp only [main, circuit_norm] at h_env ⊢
  -- Commit's prover assumptions: the hash exists for the honest `commit_ivk` chunks
  have hakv : Expression.eval env.toEnvironment input_var.ak = input.ak := by
    rw [← h_input]; simp only [circuit_norm]
  have hnkv : Expression.eval env.toEnvironment input_var.nk = input.nk := by
    rw [← h_input]; simp only [circuit_norm]
  have hCommitPA : (Commit.circuit G Q hQ R).ProverAssumptions (eval env input_var) env.data env.hint := by
    simp only [Commit.circuit, Commit.ProverAssumptions]
    rw [show ((eval env input_var).ak : Fp) = input.ak from by rw [h_input],
      show ((eval env input_var).nk : Fp) = input.nk from by rw [h_input],
      show (eval env input_var).rivk = input.rivk from by rw [h_input]]
    rcases h_assumptions with ⟨⟨B, hB⟩, hrivk⟩
    exact ⟨⟨B, hB⟩, hrivk⟩
  -- the Commit `ProverSpec`: all the cell values, ranges, z-cells, and the hash existential
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_usesLocalWitnesses] at h_env
  have hCommitPS := (h_env.1 hCommitPA).2
  rw [show (Commit.circuit G Q hQ R).ProverSpec = Commit.ProverSpec G Q R from rfl] at hCommitPS
  simp only [Commit.ProverSpec] at hCommitPS
  obtain ⟨hb0, hb2, hd0, ha, hc, hz13a, hz13c, hSa, hSb0, hSb1, hSb2, hSc, hSd0, hSd1, hSb, hSd,
    chunks, hPC, hHash⟩ := hCommitPS
  -- keep the (expensive-to-flatten) Commit output variable opaque (folds goal + all hyps);
  -- `clear_value` makes `O` genuinely opaque so the heavy `eval` never reduces in the kernel
  set O := (Commit.circuit G Q hQ R).output input_var i₀ with hO
  clear_value O
  -- bridge the Commit `ProverSpec` cell facts into the `Expression.eval env.toEnvironment`
  -- spelling that `canonicity_assumptions_of_commit` consumes (mirrors top soundness 1156–1160)
  have ha' : (Expression.eval env.toEnvironment O.cells.a).val < 2 ^ 250 := by
    rwa [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
      (Commit.eval_cells_leaves env.toEnvironment _).1] at ha
  have hb0' : (Expression.eval env.toEnvironment O.cells.b0).val < 2 ^ 4 := by
    rwa [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
      (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.1] at hb0
  have hb2' : (Expression.eval env.toEnvironment O.cells.b2).val < 2 ^ 5 := by
    rwa [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
      (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.2.2.1] at hb2
  have hc' : (Expression.eval env.toEnvironment O.cells.c).val < 2 ^ 240 := by
    rwa [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
      (Commit.eval_cells_leaves env.toEnvironment _).2.2.1] at hc
  have hd0' : (Expression.eval env.toEnvironment O.cells.d0).val < 2 ^ 9 := by
    rwa [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
      (Commit.eval_cells_leaves env.toEnvironment _).2.2.2.2.2.2.2.1] at hd0
  have hz13a' : (HVec.get (Chain.zLengths [24, 0, 23, 0]) (eval env.toEnvironment O.zs) ⟨0, by decide⟩)[13]
      = (((Expression.eval env.toEnvironment O.cells.a).val / 2 ^ 130 : ℕ) : Fp) := by
    rw [CircuitType.eval_var_prover_to_verifier] at hz13a
    exact (congrArg
      (fun zs => (HVec.get (Chain.zLengths [24, 0, 23, 0]) zs ⟨0, by decide⟩)[13])
      (Commit.eval_zs _ env.toEnvironment O).symm).trans
      (hz13a.trans (congrArg (fun x : Fp => (((x.val / 2 ^ 130 : ℕ) : Fp)))
        (by rw [Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).1])))
  have hz13c' : (HVec.get (Chain.zLengths [24, 0, 23, 0]) (eval env.toEnvironment O.zs) ⟨2, by decide⟩)[13]
      = (((Expression.eval env.toEnvironment O.cells.c).val / 2 ^ 130 : ℕ) : Fp) := by
    rw [CircuitType.eval_var_prover_to_verifier] at hz13c
    exact (congrArg
      (fun zs => (HVec.get (Chain.zLengths [24, 0, 23, 0]) zs ⟨2, by decide⟩)[13])
      (Commit.eval_zs _ env.toEnvironment O).symm).trans
      (hz13c.trans (congrArg (fun x : Fp => (((x.val / 2 ^ 130 : ℕ) : Fp)))
        (by rw [Commit.eval_cells, (Commit.eval_cells_leaves env.toEnvironment _).2.2.1])))
  -- the `Canonicity` assumptions from the bridged Commit facts (helper keeps `O.zs` opaque)
  have hCanonAssump := canonicity_assumptions_of_commit O input_var env.toEnvironment
    hb0' hb2' hd0' ha' hc' hz13a' hz13c'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- Commit.ProverAssumptions (subcircuit form)
    rw [GeneralFormalCircuit.WithHint.toSubcircuit_completeness]
    exact hCommitPA
  · -- (Canonicity.Assumptions ∧ Canonicity.Spec) ∧ True
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · -- Canonicity.Assumptions from the helper (`id` settles the proof-irrelevant `Fin`
      -- indices); the prover/verifier `eval` spellings are definitionally equal.
      rw [CircuitType.eval_var_prover_to_verifier]
      exact id hCanonAssump
    · -- Canonicity.Spec: the 9 canonical slices, straight from the Commit `ProverSpec`
      rw [CircuitType.eval_var_prover_to_verifier,
        show Canonicity.circuit.Spec = Canonicity.Spec from rfl]
      simp only [Canonicity.Spec, circuit_norm]
      -- the goal slices coincide with the Commit `ProverSpec` facts up to the defeq
      -- `Expression.eval env.toEnvironment _ = eval env _` (`convert` settles each leaf by `rfl`)
      rw [hakv, hnkv]
      simp only [show (eval env input_var).ak = input.ak from by rw [h_input],
        show (eval env input_var).nk = input.nk from by rw [h_input]]
        at hSa hSb0 hSb1 hSb2 hSc hSd0 hSd1 hSb hSd
      -- bridge the prover LHS `(eval env O).cells.X` to the verifier `Expression.eval` leaf
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).1] at hSa
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.1] at hSb0
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.1] at hSb1
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.2.1] at hSb2
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.1] at hSc
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.2.2.1] at hSd0
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.2.2.2] at hSd1
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.1,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.1,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.1,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.2.1] at hSb
      rw [CircuitType.eval_var_prover_to_verifier, Commit.eval_cells,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.1,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.2.2.1,
        (Commit.eval_cells_leaves env.toEnvironment O.cells).2.2.2.2.2.2.2.2] at hSd
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hSb, hSd⟩
      · rw [hSa]; apply cast_bitrange_val (by norm_num)
      · rw [hSb0]; apply cast_bitrange_val (by norm_num)
      · rw [hSb1]; apply cast_bitrange_val (by norm_num)
      · rw [hSb2]; apply cast_bitrange_val (by norm_num)
      · rw [hSc]; apply cast_bitrange_val (by norm_num)
      · rw [hSd0]; apply cast_bitrange_val (by norm_num)
      · rw [hSd1]; apply cast_bitrange_val (by norm_num)
  · -- the entry `ProverSpec`: `ivk = (B + blind).x` via the Commit hash relation
    intro B hB
    -- replace the `eval` input keys by the opaque `input.{ak,nk}` (mirrors entry soundness;
    -- keeps the expensive `eval env input_var` out of the chunk bridge's `whnf`)
    simp only [h_input] at hSa hSb0 hSb1 hSb2 hSc hSd0 hSd1 hSb hSd
    -- generalize the four piece cells to opaque `Fp` atoms, so the chunk bridge never reduces
    -- the heavy `eval env O` (see `doc/performance-problems.md`, opaque-variable rule)
    obtain ⟨ca, hca⟩ : ∃ x, (eval env O).cells.a = x := ⟨_, rfl⟩
    obtain ⟨cb, hcb⟩ : ∃ x, (eval env O).cells.b = x := ⟨_, rfl⟩
    obtain ⟨cc, hcc⟩ : ∃ x, (eval env O).cells.c = x := ⟨_, rfl⟩
    obtain ⟨cd, hcd⟩ : ∃ x, (eval env O).cells.d = x := ⟨_, rfl⟩
    rw [hca] at hSa
    rw [hcb] at hSb
    rw [hcc] at hSc
    rw [hcd] at hSd
    simp only [hca, hcb, hcc, hcd] at hPC
    -- the four Commit pieces are the canonical `commit_ivk` slices, so their chunk list is
    -- `commitIvkChunks ak nk` (same bridge as the entry soundness).
    have hchunks : chunks = commitIvkChunks (show Fp from input.ak).val (show Fp from input.nk).val :=
      pieceChunks_eq_commitIvkChunks_of_indexed_piece_values
        (ak := (show Fp from input.ak).val) (nk := (show Fp from input.nk).val) hPC
        (by simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero];
            rw [hSa]; norm_num [bitrange, K])
        (by simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
              List.getElem_cons_zero];
            rw [hSb, hSb0, hSb1, hSb2]; simp only [bitrange, pow_zero, Nat.div_one]; push_cast; ring)
        (by simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
              List.getElem_cons_zero];
            rw [hSc]; norm_num [bitrange, K])
        (by simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
              List.getElem_cons_zero];
            rw [hSd, hSd0, hSd1]; simp only [bitrange]; push_cast; ring)
        (lt_trans (ZMod.val_lt (show Fp from input.ak)) (by norm_num [PALLAS_BASE_CARD]))
        (lt_trans (ZMod.val_lt (show Fp from input.nk)) (by norm_num [PALLAS_BASE_CARD]))
    have hpt := hHash B (by rw [hchunks]; exact hB)
    rw [show input.rivk = (eval env input_var).rivk from by rw [h_input]]
    rw [← congrArg Point.x hpt]
    rw [hO]
    simp only [circuit_norm, Commit.circuit]

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input field where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Spec := fun input ivk _ => Spec G Q R input.ak input.nk ivk
  ProverAssumptions := fun input _ _ => ProverAssumptions G Q input.ak input.nk ∧
    (show ℕ from input.rivk) < PALLAS_SCALAR_CARD
  ProverSpec := fun input ivk _ =>
    ProverSpec G Q R input.ak input.nk ((show ℕ from input.rivk : ℕ) : Fq) ivk
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end Orchard.Action.CommitIvk
