import Clean.Orchard.Ecc.ScalarMul.Mul
import Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete
import Clean.Orchard.Ecc.ScalarMul.Mul.Complete
import Clean.Orchard.Ecc.ScalarMul.Mul.Overflow
import Clean.Orchard.Ecc.Add

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul.rs::Config::assign`
(`CircuitVersion::AnchoredBase`).

Variable-base scalar multiplication: computes `[alpha] base` where `alpha : Fp` is a
Pallas base-field element. The working scalar is `k = alpha.val + t_q`, decomposed
MSB-first into 255 bits and processed as

1. `acc = [2]base` via complete addition,
2. a running sum `z` starting at the constant 0,
3. the `hi` incomplete half — 125 double-and-add steps for bits `k_254..k_130`,
4. the `lo` incomplete half — 126 double-and-add steps for bits `k_129..k_4`,
5. three complete-addition bits `k_3..k_1`,
6. the LSB step `k_0` — a correction point (identity if `k_0 = 1`, else `-base`)
   pinned by `GATE LSB check` and added with complete addition,
7. the overflow check on `z_0`, `z_130`, `k_254`.

Soundness rests on the identity `2^254 + t_q ≡ 0 (mod q)`: the double-and-add
accumulates `[2^254 + k] base = [alpha] base`.
-/

namespace Orchard.Ecc.ScalarMul.Mul.Assign

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)
open Incomplete.DoubleAndAdd (BitsHint accScalar)

/-- `t_q` as a natural number (`q = 2^254 + tQNat` for the Pallas group order). -/
def tQNat : ℕ := 45560315531506369815346746415080538113

/-- The working scalar `k = alpha.val + t_q`. -/
def kNat (alpha : Fp) : ℕ := alpha.val + tQNat

/-- MSB-first bits of the working scalar: `kBits alpha i = k_{254-i}`. -/
def kBits (alpha : Fp) : BitsHint := fun i => (kNat alpha).testBit (254 - i)

/-- Inputs of variable-base scalar mul: the scalar cell and the non-identity base. -/
structure Input (F : Type) where
  alpha : F
  base : Ecc.Point F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Ecc.Point Fp) := do
  -- initialize the accumulator `acc = [2]base` using complete addition
  let acc ← Ecc.Add.circuit { p := input.base, q := input.base }
  -- initialize the running sum to zero (`assign_advice_from_constant`)
  let zInit ← witnessField fun _ => 0
  zInit === 0
  -- double-and-add over the `hi` half of the scalar decomposition (125 bits)
  let hi ← Incomplete.DoubleAndAdd.circuit 124 {
    base := input.base, xA := acc.x, yA := acc.y, z := zInit,
    bits := fun env => fun i => kBits (env input.alpha) i }
  -- double-and-add over the `lo` half (126 bits), running sum chained
  let lo ← Incomplete.DoubleAndAdd.circuit 125 {
    base := input.base, xA := hi.xA, yA := hi.yA,
    z := hi.zs[124],
    bits := fun env => fun i => kBits (env input.alpha) (125 + i) }
  -- complete addition for bits `k_3..k_1`
  let comp ← Complete.AssignRegion.circuit {
    base := input.base, xA := lo.xA, yA := lo.yA,
    z := lo.zs[125],
    bits := fun env => fun i => kBits (env input.alpha) (251 + i) }
  -- process the least significant bit: z_0 = 2⋅z_1 + k_0
  let z0 ← witnessField fun env =>
    2 * env (comp.zs[2]) + (if kBits (env input.alpha) 254 then 1 else 0)
  -- copy in base_x, base_y for the LSB gate
  let baseX <== input.base.x
  let baseY <== input.base.y
  -- the correction point: identity if k_0 = 1, else -base
  let corrX ← witnessField fun env =>
    if kBits (env input.alpha) 254 then 0 else env input.base.x
  let corrY ← witnessField fun env =>
    if kBits (env input.alpha) 254 then 0 else -(env input.base.y)
  Mul.circuit { z1 := comp.zs[2], z0, xP := corrX, yP := corrY, baseX, baseY }
  -- the result of the final complete addition is `[alpha] base`
  let result ← Ecc.Add.circuit { p := { x := corrX, y := corrY }, q := comp.acc }
  -- overflow check on z_0 (full sum), z_130 (after the hi half), k_254 (first bit)
  Overflow.OverflowCheck.circuit {
    alpha := input.alpha, z0,
    z130 := hi.zs[124],
    k254 := hi.zs[0] }
  return result

instance elaborated : ElaboratedCircuit Fp Input Ecc.Point main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  Pallas.OnCurve input.base.coords

/-- The circuit computes the variable-base scalar multiplication `[alpha] base`,
with the identity encoded as `(0, 0)` coordinates. -/
def Spec (input : Input Fp) (output : Ecc.Point Fp) : Prop :=
  ∀ B : SWPoint Pallas.curve, B ≠ 0 → input.base.coords = (B.x, B.y) →
    output.coords = ((input.alpha.val • B).x, (input.alpha.val • B).y)

/-! ### Running-sum chains as natural numbers

The circuit's running sum lives in `Fp`; the canonicity argument needs its exact
natural-number value. `chainNat` mirrors `z ↦ 2z + bit` over `ℕ`. -/

/-- The running sum continued from `zin` by `b` steps of `z ↦ 2z + bit`. -/
def chainNat (zin : ℕ) (bits : ℕ → Bool) : ℕ → ℕ
  | 0 => zin
  | b + 1 => 2 * chainNat zin bits b + (if bits b then 1 else 0)

private theorem chainNat_lt (zin : ℕ) (bits : ℕ → Bool) :
    ∀ b, chainNat zin bits b < 2 ^ b * (zin + 1)
  | 0 => by simp [chainNat]
  | b + 1 => by
    have ih := chainNat_lt zin bits b
    have hpow : 2 ^ (b + 1) * (zin + 1) = 2 * (2 ^ b * (zin + 1)) := by ring
    simp only [chainNat, hpow]
    cases bits b <;> simp <;> omega

private theorem chainNat_offset (zin : ℕ) (bits : ℕ → Bool) :
    ∀ b, chainNat zin bits b = 2 ^ b * zin + chainNat 0 bits b
  | 0 => by simp [chainNat]
  | b + 1 => by
    have ih := chainNat_offset zin bits b
    have hpow : 2 ^ (b + 1) * zin = 2 * (2 ^ b * zin) := by ring
    simp only [chainNat, hpow]
    omega

/-- Splitting off the first (most significant) bit of a zero-started chain. -/
private theorem chainNat_msb (bits : ℕ → Bool) :
    ∀ b, chainNat 0 bits (b + 1)
      = 2 ^ b * (if bits 0 then 1 else 0) + chainNat 0 (fun i => bits (i + 1)) b
  | 0 => by simp [chainNat]
  | b + 1 => by
    have ih := chainNat_msb bits b
    rw [show chainNat 0 bits (b + 1 + 1)
        = 2 * chainNat 0 bits (b + 1) + (if bits (b + 1) then 1 else 0) from rfl,
      show chainNat 0 (fun i => bits (i + 1)) (b + 1)
        = 2 * chainNat 0 (fun i => bits (i + 1)) b + (if bits (b + 1) then 1 else 0)
        from rfl,
      ih]
    ring

/-- The field-level running-sum chain delivered by a sub-circuit `Spec` is the cast of
`chainNat`. -/
private theorem chain_cast {n : ℕ} (zs : Vector Fp (n + 1)) (zin : Fp) (Zin : ℕ)
    (bits : ℕ → Bool) (hin : zin = (Zin : Fp))
    (h0 : zs[0] = 2 * zin + (if bits 0 then 1 else 0))
    (hstep : ∀ b : Fin n, zs[b.val + 1]'(by omega) =
      2 * zs[b.val]'(by omega) + (if bits (b.val + 1) then 1 else 0)) :
    ∀ j, (hj : j < n + 1) → zs[j]'hj = (chainNat Zin bits (j + 1) : Fp) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [h0, hin]
    simp only [chainNat]
    cases bits 0 <;> simp
  | succ i ih =>
    intro hj
    rw [hstep ⟨i, by omega⟩, ih (by omega)]
    simp only [chainNat]
    cases bits (i + 1) <;> simp

/-! ### The double-and-add scalar in closed form -/

private theorem accScalar_closed (m : ℕ) (hm : 1 ≤ m) (bits : ℕ → Bool) :
    ∀ b, accScalar m bits b = 2 ^ b * (m - 1) + 2 * chainNat 0 bits b + 1
  | 0 => by simp [accScalar, chainNat]; omega
  | b + 1 => by
    have ih := accScalar_closed m hm bits b
    have hpow : 2 ^ (b + 1) * (m - 1) = 2 * (2 ^ b * (m - 1)) := by ring
    simp only [accScalar, chainNat, hpow]
    cases bits b <;> simp <;> omega

/-! ### Complete-addition steps as scalar multiples -/

/-- One double-and-add group step: `A•B + (±B + A•B) = (2A ± 1)•B`. -/
private theorem nsmul_step (B : SWPoint Pallas.curve) (A : ℕ) (hA : 1 ≤ A)
    (bit : Bool) :
    A • B + ((if bit then B else -B) + A • B)
      = (2 * A + (if bit then 1 else 0) * 2 - 1) • B := by
  cases bit
  · simp only [Bool.false_eq_true, if_false]
    have h2 : (2 * A + 0 * 2 - 1) • B + B = A • B + A • B := by
      rw [← succ_nsmul, show 2 * A + 0 * 2 - 1 + 1 = A + A from by omega, add_nsmul]
    calc A • B + (-B + A • B) = (A • B + A • B) + -B := by abel
      _ = ((2 * A + 0 * 2 - 1) • B + B) + -B := by rw [h2]
      _ = (2 * A + 0 * 2 - 1) • B := by abel
  · simp only [if_true]
    rw [show 2 * A + 1 * 2 - 1 = A + (A + 1) from by omega, add_nsmul, add_nsmul,
      one_nsmul]
    abel

/-- Subtracting the base once: `-B + m•B = (m − 1)•B` for `m ≥ 1`. -/
private theorem neg_add_nsmul (B : SWPoint Pallas.curve) {m : ℕ} (hm : 1 ≤ m) :
    -B + m • B = (m - 1) • B := by
  conv_lhs => rw [show m = (m - 1) + 1 from by omega]
  rw [succ_nsmul]
  abel

/-- The complete-addition accumulator chain of `Complete.AssignRegion` computes
double-and-add on scalar multiples: starting from `[M]B`, after `b` steps it holds
`[accScalar M bits b] B`. Fully general (the identity case is covered by the complete
addition law `Pallas.add_coords`). -/
private theorem accValue_nsmul (B : SWPoint Pallas.curve) (M : ℕ) (hM : 1 ≤ M)
    (bits : ℕ → Bool) :
    ∀ b, Complete.AssignRegion.accValue B.x B.y ((M • B).x, (M • B).y) bits b
      = ((accScalar M bits b • B).x, (accScalar M bits b • B).y)
  | 0 => by simp [Complete.AssignRegion.accValue, accScalar]
  | b + 1 => by
    have ih := accValue_nsmul B M hM bits b
    have hA1 : 1 ≤ accScalar M bits b := by
      rw [accScalar_closed M hM bits b]; omega
    simp only [Complete.AssignRegion.accValue, Complete.AssignRegion.stepValue, ih]
    have hU : ((B.x, if bits b then B.y else -B.y) : Fp × Fp)
        = ((if bits b then B else -B).x, (if bits b then B else -B).y) := by
      cases bits b <;> simp
    rw [hU, Pallas.add_coords, Pallas.add_coords, nsmul_step B _ hA1 (bits b)]
    rfl

/-! ### The overflow-check canonicity argument

The book argument (halo2 book, "variable-base scalar multiplication", overflow check):
the witnessed 255-bit running sum `K` satisfies `K ≡ α + t_q (mod p)`; the auxiliary
constraints exclude both wraparounds, so `K = α + t_q` over `ℕ`. -/

private theorem k_canonical {alpha k254 z130 : Fp} {K Zhi R : ℕ} {b254 : Bool}
    (hk254 : k254 = if b254 then 1 else 0)
    (hz130 : z130 = (Zhi : Fp))
    (hZhiLt : Zhi < 2 ^ 125)
    (hmsbF : b254 = false → Zhi < 2 ^ 124)
    (hRlt : R < 2 ^ 130)
    (hsplit : K = 2 ^ 130 * Zhi + R)
    (hcong : (K : Fp) = alpha + tQ)
    (hdisj2 : k254 = 0 ∨ z130 = (2 ^ 124 : Fp))
    (hex : ∃ (sHi : Fp) (sLo : ℕ), sLo < 2 ^ 130 ∧
      alpha + k254 * (2 ^ 130 : Fp) = (sLo : Fp) + (2 ^ 130 : Fp) * sHi ∧
      (k254 = 0 ∨ sHi = 0) ∧ (k254 = 1 ∨ z130 ≠ 0 ∨ sHi = 0)) :
    K = alpha.val + tQNat := by
  obtain ⟨sHi, sLo, hsLoLt, hsEq, hd1, hd2⟩ := hex
  have hp : PALLAS_BASE_CARD
      = 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
    norm_num [PALLAS_BASE_CARD]
  have halpha : alpha.val
      < 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
    rw [← hp]; exact ZMod.val_lt alpha
  have hav : ((alpha.val : ℕ) : Fp) = alpha := ZMod.natCast_rightInverse alpha
  have htQ : tQNat = 45560315531506369815346746415080538113 := rfl
  -- the main congruence, over ℕ
  have hcong' : K %
        28948022309329048855892746252171976963363056481941560715954676764349967630337
      = (alpha.val + tQNat) %
        28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
    have h : ((K : ℕ) : Fp) = ((alpha.val + tQNat : ℕ) : Fp) := by
      push_cast
      rw [hav, hcong]
      congr 1
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
    unfold Nat.ModEq at h2
    rw [← hp]
    exact h2
  cases hb : b254 with
  | true =>
    rw [hb, if_pos rfl] at hk254
    -- z130 = 2^124, hence Zhi = 2^124 over ℕ
    have hz : z130 = (2 ^ 124 : Fp) := by
      rcases hdisj2 with h | h
      · rw [hk254] at h; exact absurd h one_ne_zero
      · exact h
    have hZhi : Zhi = 2 ^ 124 := by
      have h : ((Zhi : ℕ) : Fp) = ((2 ^ 124 : ℕ) : Fp) := by
        rw [← hz130, hz]; push_cast; ring
      have h' := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      unfold Nat.ModEq at h'
      rw [hp] at h'
      norm_num at h'
      norm_num at hZhiLt
      omega
    -- sHi = 0, hence α ≥ p − 2^130
    have hsHi0 : sHi = 0 := by
      rcases hd1 with h | h
      · rw [hk254] at h; exact absurd h one_ne_zero
      · exact h
    have hs' : (alpha.val + 2 ^ 130) %
          28948022309329048855892746252171976963363056481941560715954676764349967630337
        = sLo %
          28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
      have h : ((alpha.val + 2 ^ 130 : ℕ) : Fp) = ((sLo : ℕ) : Fp) := by
        push_cast
        rw [hav]
        rw [hk254, hsHi0] at hsEq
        linear_combination hsEq
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      unfold Nat.ModEq at h2
      rw [← hp]
      exact h2
    norm_num at hs' hsLoLt hRlt hsplit hZhi
    omega
  | false =>
    rw [hb, if_neg (by simp)] at hk254
    have hKlt : K < 2 ^ 254 := by
      have h := hmsbF hb
      norm_num at h hRlt hsplit ⊢
      omega
    rcases hd2 with h | h | h
    · rw [hk254] at h; exact absurd h.symm one_ne_zero
    · -- z130 ≠ 0 forces K ≥ 2^130, excluding the downward wrap
      have hZhi0 : Zhi ≠ 0 := by
        intro h0
        rw [h0] at hz130
        exact h (by rw [hz130]; norm_num)
      norm_num at hKlt hsplit
      omega
    · -- sHi = 0 forces α < 2^130, so no wrap at all
      have hval : alpha.val = sLo := by
        rw [hk254] at hsEq
        rw [h] at hsEq
        have h' : alpha = (sLo : Fp) := by linear_combination hsEq
        rw [h', ZMod.val_natCast, hp]
        norm_num at hsLoLt
        omega
      norm_num at hKlt hsLoLt
      omega

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [Ecc.Add.circuit, Incomplete.DoubleAndAdd.circuit,
    Complete.AssignRegion.circuit, Mul.circuit, Overflow.OverflowCheck.circuit]
  obtain ⟨hAcc, hz0, hHi, hLo, hComp, hbx, hby, hMul, hAdd2, hOv⟩ := h_holds
  simp only [Incomplete.DoubleAndAdd.Spec] at hHi hLo
  obtain ⟨bitsHi, hHiChain, hHiAcc⟩ := hHi
  obtain ⟨bitsLo, hLoChain, hLoAcc⟩ := hLo
  simp only [Complete.AssignRegion.Spec] at hComp
  obtain ⟨bitsC, hCChain, hCAcc⟩ := hComp
  simp only [Mul.Spec, Mul.SelectedCorrectionPoint, Mul.lsb] at hMul
  obtain ⟨hk0Bool, hCorrNeg, hCorrZero⟩ := hMul
  simp only [Overflow.OverflowCheck.Spec] at hOv
  obtain ⟨hOvZ0, hOvDisj2, hOvEx⟩ := hOv
  intro B hB hcoords
  simp only [Ecc.Add.Assumptions, Ecc.Add.Spec, Ecc.Point.coords] at hAcc hAdd2
  simp only [Ecc.Point.coords] at h_assumptions hcoords ⊢
  -- the doubled base: acc = [2]B
  have hAccPair := (hAcc ⟨Or.inl h_assumptions, Or.inl h_assumptions⟩).2
  rw [hcoords, Pallas.add_coords, ← two_nsmul] at hAccPair
  -- hi half: accumulator [accScalar 2 bitsHi 125]B
  have hHiOut := hHiAcc B 2 hB hcoords hAccPair (le_refl 2) (by norm_num)
  -- running-sum chains, mirrored over ℕ
  have hHiCells := chain_cast _ _ 0 bitsHi (by rw [hz0]; norm_num) hHiChain.1 hHiChain.2
  have hZhiCell := hHiCells 124 (by omega)
  simp only [circuit_norm] at hZhiCell
  have hK254 := hHiCells 0 (by omega)
  simp only [circuit_norm] at hK254
  rw [show ((chainNat 0 bitsHi 1 : ℕ) : Fp) = (if bitsHi 0 then 1 else 0) from by
    simp only [chainNat]; cases bitsHi 0 <;> simp] at hK254
  have hLoCells := chain_cast _ _ (chainNat 0 bitsHi 125) bitsLo hZhiCell
    hLoChain.1 hLoChain.2
  have hZloCell := hLoCells 125 (by omega)
  simp only [circuit_norm] at hZloCell
  have hCCells := chain_cast _ _ (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC
    hZloCell hCChain.1 hCChain.2
  have hZcCell := hCCells 2 (by omega)
  simp only [circuit_norm] at hZcCell
  -- chain bounds
  have hZhiLt : chainNat 0 bitsHi 125 < 2 ^ 125 :=
    lt_of_lt_of_le (chainNat_lt 0 bitsHi 125) (by norm_num)
  have hCloLt : chainNat 0 bitsLo 126 < 2 ^ 126 :=
    lt_of_lt_of_le (chainNat_lt 0 bitsLo 126) (by norm_num)
  have hCcLt : chainNat 0 bitsC 3 < 2 ^ 3 :=
    lt_of_lt_of_le (chainNat_lt 0 bitsC 3) (by norm_num)
  -- the accumulated scalars in closed form
  have hm1 : accScalar 2 bitsHi 125 = 2 ^ 125 + 2 * chainNat 0 bitsHi 125 + 1 := by
    rw [accScalar_closed 2 (by norm_num) bitsHi 125]
    norm_num
  -- lo half: accumulator [accScalar m₁ bitsLo 126]B
  have hLoOut := hLoAcc B (accScalar 2 bitsHi 125) hB hcoords hHiOut
    (by rw [hm1]; omega)
    (by rw [hm1]; have h := hZhiLt; norm_num at h ⊢; omega)
  rw [show accScalar (accScalar 2 bitsHi 125) bitsLo (125 + 1)
    = accScalar (accScalar 2 bitsHi 125) bitsLo 126 from rfl] at hLoOut
  have hm2 : accScalar (accScalar 2 bitsHi 125) bitsLo 126
      = 2 ^ 251 + 2 * chainNat (chainNat 0 bitsHi 125) bitsLo 126 + 1 := by
    rw [accScalar_closed _ (by rw [hm1]; omega) bitsLo 126, hm1,
      chainNat_offset (chainNat 0 bitsHi 125) bitsLo 126]
    norm_num
    omega
  have hZloLt : chainNat (chainNat 0 bitsHi 125) bitsLo 126 < 2 ^ 251 := by
    have h1 := chainNat_lt (chainNat 0 bitsHi 125) bitsLo 126
    have h2 : chainNat 0 bitsHi 125 + 1 ≤ 2 ^ 125 := hZhiLt
    exact lt_of_lt_of_le h1 ((Nat.mul_le_mul le_rfl h2).trans (by norm_num))
  have hm2Lt : accScalar (accScalar 2 bitsHi 125) bitsLo 126 < PALLAS_SCALAR_CARD := by
    rw [hm2]
    have h := hZloLt
    norm_num [PALLAS_SCALAR_CARD] at h ⊢
    omega
  -- complete bits: accumulator [accScalar m₂ bitsC 3]B
  have hCompS := hCAcc
    (by rw [hLoOut]; exact Or.inl (pallas_nsmul_onCurve hB (by rw [hm2]; omega) hm2Lt))
    (Or.inl h_assumptions)
  simp only [Ecc.Point.coords] at hCompS
  obtain ⟨hValidAcc, hCompPair⟩ := hCompS
  have hBx : input_base.x = B.x := congrArg Prod.fst hcoords
  have hBy : input_base.y = B.y := congrArg Prod.snd hcoords
  rw [hBx, hBy, hLoOut,
    accValue_nsmul B (accScalar (accScalar 2 bitsHi 125) bitsLo 126)
      (by rw [hm2]; omega) bitsC 3] at hCompPair
  have hm3 : accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3
      = 2 ^ 254 + 2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3
        + 1 := by
    rw [accScalar_closed _ (by rw [hm2]; omega) bitsC 3, hm2,
      chainNat_offset (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3]
    norm_num
    omega
  -- the canonicity argument: the witnessed scalar is α + t_q over ℕ
  have hKpart : ∀ k0n : ℕ, k0n ≤ 1 →
      ((2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 + k0n : ℕ) : Fp)
        = input_alpha + tQ →
      2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 + k0n
        = ZMod.val input_alpha + tQNat := by
    intro k0n hk0le hcong
    refine k_canonical (R := 2 ^ 4 * chainNat 0 bitsLo 126 + 2 * chainNat 0 bitsC 3 + k0n)
      hK254 hZhiCell hZhiLt ?_ ?_ ?_ hcong hOvDisj2 hOvEx
    · intro hf
      have h := chainNat_msb bitsHi 124
      rw [hf] at h
      have h2 := chainNat_lt 0 (fun i => bitsHi (i + 1)) 124
      norm_num at h h2 ⊢
      omega
    · have h1 := hCloLt
      have h2 := hCcLt
      norm_num at h1 h2 ⊢
      omega
    · have h1 := chainNat_offset (chainNat 0 bitsHi 125) bitsLo 126
      have h2 := chainNat_offset (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3
      norm_num at h1 h2 ⊢
      omega
  -- the final scalar identity: [2^254 + k]B = [α]B
  have hfin : ∀ s : ℕ, s = 2 ^ 254 + ZMod.val input_alpha + tQNat →
      s • B = ZMod.val input_alpha • B := by
    intro s hs
    have hq : PALLAS_SCALAR_CARD = 2 ^ 254 + tQNat := by
      norm_num [PALLAS_SCALAR_CARD, tQNat]
    rw [hs, show 2 ^ 254 + ZMod.val input_alpha + tQNat
        = ZMod.val input_alpha + PALLAS_SCALAR_CARD from by rw [hq]; ring,
      add_nsmul, (pallas_nsmul_eq_zero_iff hB PALLAS_SCALAR_CARD).mpr dvd_rfl,
      _root_.add_zero]
  have hIx : Expression.eval env input_var_base.x = input_base.x :=
    congrArg Ecc.Point.x h_input.2
  have hIy : Expression.eval env input_var_base.y = input_base.y :=
    congrArg Ecc.Point.y h_input.2
  -- the LSB step
  rcases hk0Bool with hk0 | hk0
  · -- k₀ = 0: the correction point is −B, the result is [m₃ − 1]B
    replace hCorrNeg := hCorrNeg hk0
    rw [hbx, hby, hIx, hIy, hBx, hBy,
      show CompElliptic.CurveForms.ShortWeierstrass.neg (B.x, B.y) = ((-B).x, (-B).y)
        from by simp [CompElliptic.CurveForms.ShortWeierstrass.neg]] at hCorrNeg
    have hK := hKpart 0 (by omega)
      (by push_cast; linear_combination hOvZ0 - hk0 - 2 * hZcCell)
    have hAdd2S := (hAdd2 ⟨by
      rw [hCorrNeg]
      exact Or.inl (SWPoint.onCurve_of_ne_zero (neg_ne_zero.mpr hB)), hValidAcc⟩).2
    rw [hCorrNeg, hCompPair, Pallas.add_coords,
      neg_add_nsmul B (by rw [hm3]; omega)] at hAdd2S
    simp only [Nat.add_assoc, Nat.reduceAdd] at hAdd2S ⊢
    rw [hAdd2S,
      hfin (accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 - 1)
        (by rw [hm3]; omega)]
  · -- k₀ = 1: the correction point is the identity, the result is [m₃]B
    replace hCorrZero := hCorrZero hk0
    have hK := hKpart 1 (by omega)
      (by push_cast; linear_combination hOvZ0 - hk0 - 2 * hZcCell)
    have hAdd2S := (hAdd2 ⟨by rw [hCorrZero]; exact Or.inr rfl, hValidAcc⟩).2
    rw [hCorrZero, hCompPair,
      show ((0 : Fp), (0 : Fp))
        = ((0 : SWPoint Pallas.curve).x, (0 : SWPoint Pallas.curve).y) from rfl,
      Pallas.add_coords, _root_.zero_add] at hAdd2S
    simp only [Nat.add_assoc, Nat.reduceAdd] at hAdd2S ⊢
    rw [hAdd2S,
      hfin (accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3)
        (by rw [hm3]; omega)]

theorem completeness : Completeness Fp main Assumptions := by
  sorry

/-- `mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`):
variable-base scalar multiplication by a base-field element. -/
def circuit : FormalCircuit Fp Input Ecc.Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Orchard.Ecc.ScalarMul.Mul.Assign
