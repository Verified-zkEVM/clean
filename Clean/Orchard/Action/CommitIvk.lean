import Clean.Orchard.Action.CommitIvkGate
import Clean.Orchard.Action.CommitIvkChunks
import Clean.Orchard.Sinsemilla.Domain
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
`CommitDomain.WithZs` hash exposing the running sums needed for the `ak`/`nk` canonicity
checks).
-/

namespace Orchard.Action.CommitIvk

open Utilities.LookupRangeCheck (K)
open Utilities.LookupRangeCheck.WitnessShort (bitrangeSubset)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Ecc (Point)
open Orchard.Ecc.ScalarMul
open Orchard.Sinsemilla

/-- Inputs of `commit_ivk`: the already-assigned full viewing key cells `ak`, `nk`, and
the prover-side full-width blinding scalar behind the `ScalarFixed` value `rivk`. -/
structure Input (F : Type) where
  ak : F
  nk : F
  rivk : Unconstrained Fq F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ ak := default, nk := default, rivk := fun _ => default }⟩

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  let ak := input.ak
  let nk := input.nk

  -- Witness and range-constrain the short subpieces b_0 (4 bits), b_2 (5 bits) of `ak`/`nk`,
  -- and d_0 (9 bits) of `nk`.
  let b0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 250 4 (by norm_num [K])
    (fun env => eval env ak)
  let b2 ← Utilities.LookupRangeCheck.WitnessShort.circuit 0 5 (by norm_num [K])
    (fun env => eval env nk)
  let d0 ← Utilities.LookupRangeCheck.WitnessShort.circuit 245 9 (by norm_num [K])
    (fun env => eval env nk)

  -- The single-bit subpieces b_1, d_1 are boolean-constrained in the canonicity gate.
  let b1 ← witnessField fun env => bitrangeSubset (eval env ak) 254 1
  let d1 ← witnessField fun env => bitrangeSubset (eval env nk) 254 1

  -- The four Sinsemilla message pieces.
  let a ← witnessField fun env => bitrangeSubset (eval env ak) 0 250
  let b ← witnessField fun env => env b0 + env b1 * 2 ^ 4 + env b2 * 2 ^ 5
  let c ← witnessField fun env => bitrangeSubset (eval env nk) 5 240
  let d ← witnessField fun env => env d0 + env d1 * 2 ^ 9

  -- ivk = Commit^ivk_rivk(ak || nk); the short commit also exposes the per-piece running sums.
  let out ← _root_.Orchard.Sinsemilla.CommitDomain.WithZs.circuit G Q hQ R 24 [0, 23, 0]
    { pieces := #v[a, b, c, d], r := input.rivk }
  let ivk := out.point.x
  let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
  let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]

  -- ak canonicity: decompose the low 130 bits of a' = a + 2^130 - t_P.
  let aPrime ← witnessField fun env => env a + (2 ^ 130 : Fp) - Ecc.tP
  let aPrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 aPrime

  -- nk canonicity: decompose the low 140 bits of b2c' = b_2 + c * 2^5 + 2^140 - t_P.
  let b2cPrime ← witnessField fun env =>
    env b2 + (2 ^ 5 : Fp) * env c + (2 ^ 140 : Fp) - Ecc.tP
  let b2cPrimeZs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14 b2cPrime

  Gate.circuit
    { ak, nk, a, bWhole := b, c, dWhole := d,
      b0, b1, b2, d0, d1,
      z13A := z13a, z13C := z13c,
      aPrime := aPrimeZs[0], b2CPrime := b2cPrimeZs[0],
      z13APrime := aPrimeZs[13], z14B2CPrime := b2cPrimeZs[14] }
  return ivk

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp Input field (main G Q hQ R) := by
  elaborate_circuit

/-- The committed `ivk` is the `x`-coordinate of the Sinsemilla short commitment of the
canonical message `I2LEBSP₂₅₅(ak) || I2LEBSP₂₅₅(nk)`, blinded by `[rivk] CommitIvkR`. -/
def CommitIvkRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : Value Input Fp) (ivk : Fp) : Prop :=
  let ak : Fp := input.ak
  let nk : Fp := input.nk
  ∃ rivk : Fq, ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (Orchard.Specs.Sinsemilla.commitIvkChunks ak.val nk.val) = some B →
      ivk = (Pallas.add (B.x, B.y) (R.mulValue rivk).coords).1

def ProverCommitIvkRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : ProverValue Input Fp) (ivk : Fp) : Prop :=
  let ak : Fp := input.ak
  let nk : Fp := input.nk
  ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (Orchard.Specs.Sinsemilla.commitIvkChunks ak.val nk.val) = some B →
      ivk = (Pallas.add (B.x, B.y) (R.mulValue input.rivk).coords).1

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (ivk : Fp) (_ : ProverData Fp) : Prop :=
  CommitIvkRelation G Q R input ivk

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve)
    (_R : MulFixed.FixedBase) (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  let ak : Fp := input.ak
  let nk : Fp := input.nk
  ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
    (Orchard.Specs.Sinsemilla.commitIvkChunks ak.val nk.val) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (ivk : Fp) (_ : ProverHint Fp) : Prop :=
  ProverCommitIvkRelation G Q R input ivk

-- TODO(commit-ivk-proofs): the supporting theory is complete and committed; only the entry
-- integration remains. Available, proven building blocks:
--  * the chunk bridge `pieceChunks_eq_commitIvkChunks_of_indexed_piece_values`
--    (`CommitIvkChunks.lean`): canonical indexed piece values → `chunks = commitIvkChunks`;
--  * the lifted `Gate.circuit` (entry-provable decomposition-form Assumptions) → canonical
--    bit slices `a = bitrange ak 0 250`, …, which are exactly those indexed piece values;
--  * generic `Specs.Sinsemilla.sum_suffix_div` (ZsFacts cell `z13A = a.val/2^130`) and
--    `running_sum_telescope` (CopyCheck decomposition `∃ lo<2^130, aPrime = lo + 2^130·z`).
-- The remaining step is the glue: provide the gate Assumptions from the WithZs `ZsFacts`,
-- the `CopyCheck` running sums and `WitnessShort` ranges, invoke `Gate.soundness`, and
-- thread the hash relation. NOTE: a one-shot `circuit_proof_start` over the whole entry
-- whnf-times-out (too many composed subcircuits); per `doc/performance-problems.md` the
-- entry must first be FACTORED INTO SUBCIRCUITS (a `Commit` part doing WithZs + piece
-- witnessing, and a `Canonicity` part doing the CopyCheck decompositions + gate), each with
-- its own kernel-checked soundness/completeness.
theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) (fun _ _ => True)
      (Spec G Q R) := by
  sorry

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q R) (ProverSpec G Q R) := by
  sorry

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input field where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q R
  ProverSpec := ProverSpec G Q R
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end Orchard.Action.CommitIvk
