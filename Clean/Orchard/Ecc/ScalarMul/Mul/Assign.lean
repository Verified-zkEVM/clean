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

/-! ### Honest-witness helpers: the chain of `kBits` reconstructs `kNat` -/

private theorem chainNat_testBit (K n : ℕ) (hK : K < 2 ^ n) :
    ∀ j, j ≤ n → chainNat 0 (fun i => K.testBit (n - 1 - i)) j = K / 2 ^ (n - j)
  | 0, _ => by
    simp only [chainNat]
    rw [Nat.sub_zero]
    exact (Nat.div_eq_of_lt hK).symm
  | j + 1, hj => by
    have ih := chainNat_testBit K n hK j (by omega)
    have hsplit : K / 2 ^ (n - j) = K / 2 ^ (n - (j + 1)) / 2 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
      congr 2
      omega
    have hbit : (if K.testBit (n - 1 - j) then 1 else 0) = K / 2 ^ (n - (j + 1)) % 2 := by
      rw [show n - 1 - j = n - (j + 1) from by omega, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (K / 2 ^ (n - (j + 1))) with h | h <;> simp [h]
    show 2 * chainNat 0 (fun i => K.testBit (n - 1 - i)) j + _ = _
    rw [ih, hsplit, hbit]
    omega

/-- Chains compose: continuing for `b` more steps from the `a`-step value. -/
private theorem chainNat_append (zin : ℕ) (bits : ℕ → Bool) (a : ℕ) :
    ∀ b, chainNat zin bits (a + b)
      = chainNat (chainNat zin bits a) (fun i => bits (a + i)) b
  | 0 => rfl
  | b + 1 => by
    have ih := chainNat_append zin bits a b
    show 2 * chainNat zin bits (a + b) + (if bits (a + b) then 1 else 0) = _
    rw [ih]
    rfl

private theorem kNat_lt (alpha : Fp) : kNat alpha < 2 ^ 255 := by
  have h := ZMod.val_lt alpha
  norm_num [PALLAS_BASE_CARD] at h
  norm_num [kNat, tQNat]
  omega

/-- The honest running sum after `j` of the 255 steps is the high `j` bits of `k`. -/
private theorem chainNat_kBits (alpha : Fp) (j : ℕ) (hj : j ≤ 255) :
    chainNat 0 (kBits alpha) j = kNat alpha / 2 ^ (255 - j) := by
  have h := chainNat_testBit (kNat alpha) 255 (kNat_lt alpha) j hj
  have hf : (fun i => (kNat alpha).testBit (255 - 1 - i)) = kBits alpha := by
    funext i
    show (kNat alpha).testBit (255 - 1 - i) = (kNat alpha).testBit (254 - i)
    congr 1
  rw [← hf]
  exact h

/-- `zRunValue` is the cast of the natural chain. -/
private theorem zRunValue_chainNat (Zin : ℕ) (bits : ℕ → Bool) :
    ∀ b, Incomplete.DoubleAndAdd.zRunValue (Zin : Fp) bits b
      = (chainNat Zin bits (b + 1) : Fp)
  | 0 => by
    show 2 * (Zin : Fp) + _ = _
    rw [show chainNat Zin bits 1 = 2 * Zin + (if bits 0 then 1 else 0) from rfl]
    cases bits 0 <;> simp
  | b + 1 => by
    have ih := zRunValue_chainNat Zin bits b
    show 2 * Incomplete.DoubleAndAdd.zRunValue (Zin : Fp) bits b + _ = _
    rw [ih, show chainNat Zin bits (b + 1 + 1)
      = 2 * chainNat Zin bits (b + 1) + (if bits (b + 1) then 1 else 0) from rfl]
    cases bits (b + 1) <;> simp

/-! ### The scalar decomposition region as a virtual subcircuit

halo2 inlines the next two regions in `Config::assign`; Clean factors them as
subcircuits. Subcircuits are purely virtual — they add no constraints, witnesses or
wiring, so the cell layout is identical to the inlined form — but each child's proofs
are kernel-checked as their own declarations, which keeps the parent below the kernel's
proof-term size cliff (see `doc/performance-problems.md`). -/

namespace Decompose

/-- Inputs: the base, the doubled accumulator `[2]base`, and the scalar-bit hints. -/
structure Input (F : Type) where
  base : Ecc.Point F
  xA : F
  yA : F
  bits : Unconstrained BitsHint F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ base := { x := default, y := default }, xA := default, yA := default,
     bits := fun _ => default }⟩

/-- Outputs: the accumulator after all 254 double-and-add bits, plus the running-sum
cells the rest of `assign` inspects: `z_1`, `z_130` and `k_254`. -/
structure Output (F : Type) where
  acc : Ecc.Point F
  z1 : F
  z130 : F
  k254 : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Output Fp) := do
  -- initialize the running sum to zero (`assign_advice_from_constant`)
  let zInit ← witnessField fun _ => 0
  zInit === 0
  -- double-and-add over the `hi` half of the scalar decomposition (125 bits)
  let hi ← Incomplete.DoubleAndAdd.circuit 124 {
    base := input.base, xA := input.xA, yA := input.yA, z := zInit,
    bits := fun env => fun i => input.bits env i }
  -- double-and-add over the `lo` half (126 bits), running sum chained
  let lo ← Incomplete.DoubleAndAdd.circuit 125 {
    base := input.base, xA := hi.xA, yA := hi.yA,
    z := hi.zs[124],
    bits := fun env => fun i => input.bits env (125 + i) }
  -- complete addition for bits `k_3..k_1`
  let comp ← Complete.AssignRegion.circuit {
    base := input.base, xA := lo.xA, yA := lo.yA,
    z := lo.zs[125],
    bits := fun env => fun i => input.bits env (251 + i) }
  return { acc := comp.acc, z1 := comp.zs[2], z130 := hi.zs[124], k254 := hi.zs[0] }

instance elaborated : ElaboratedCircuit Fp Input Output main := by
  elaborate_circuit

/-- Soundness contract: some bit assignment explains the exposed running-sum cells
(`k254` is its top bit, `z130`/`z1` its `chainNat` partial sums), and — when the
accumulator input is `[2]B` — the output accumulator is the result of the 254
double-and-add steps. -/
def Spec (input : Value Input Fp) (output : Output Fp) (_ : ProverData Fp) : Prop :=
  ∃ bitsHi bitsLo bitsC : ℕ → Bool,
    output.k254 = (if bitsHi 0 then 1 else 0) ∧
    output.z130 = (chainNat 0 bitsHi 125 : Fp) ∧
    output.z1 = (chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 : Fp) ∧
    ∀ B : SWPoint Pallas.curve, B ≠ 0 →
      (input.base.x, input.base.y) = (B.x, B.y) →
      (input.xA, input.yA) = ((2 • B).x, (2 • B).y) →
      Pallas.Valid output.acc.coords ∧
      output.acc.coords
        = ((accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 • B).x,
           (accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 • B).y)

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  ∃ B : SWPoint Pallas.curve, B ≠ 0 ∧
    (input.base.x, input.base.y) = (B.x, B.y) ∧
    (input.xA, input.yA) = ((2 • B).x, (2 • B).y)

def ProverSpec (input : ProverValue Input Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  output.k254 = (chainNat 0 input.bits 1 : Fp) ∧
  output.z130 = (chainNat 0 input.bits 125 : Fp) ∧
  output.z1 = (chainNat (chainNat (chainNat 0 input.bits 125)
    (fun i => input.bits (125 + i)) 126) (fun i => input.bits (251 + i)) 3 : Fp) ∧
  Pallas.Valid output.acc.coords

/-- Bounds on the hi/lo accumulator scalars, for arbitrary bit assignments. -/
private theorem m_bounds (bits1 bits2 : ℕ → Bool) :
    2 ≤ accScalar 2 bits1 125 ∧
    2 ^ (125 + 2) * (accScalar 2 bits1 125 + 1) ≤ 2 ^ 254 ∧
    1 ≤ accScalar (accScalar 2 bits1 125) bits2 126 ∧
    accScalar (accScalar 2 bits1 125) bits2 126 < PALLAS_SCALAR_CARD ∧
    0 < accScalar (accScalar 2 bits1 125) bits2 126 := by
  have hc1 : chainNat 0 bits1 125 < 2 ^ 125 :=
    lt_of_lt_of_le (chainNat_lt 0 bits1 125) (by norm_num)
  have hc2 : chainNat 0 bits2 126 < 2 ^ 126 :=
    lt_of_lt_of_le (chainNat_lt 0 bits2 126) (by norm_num)
  have hm1 := accScalar_closed 2 (by norm_num) bits1 125
  have hp125 := Nat.two_pow_pos 125
  have h2le : 2 ≤ accScalar 2 bits1 125 := by rw [hm1]; omega
  have hm2 := accScalar_closed (accScalar 2 bits1 125) (by omega) bits2 126
  refine ⟨h2le, ?_, by omega, ?_, by omega⟩
  · rw [hm1]
    norm_num at hc1 ⊢
    omega
  · rw [hm2, hm1]
    norm_num [PALLAS_SCALAR_CARD] at hc1 hc2 ⊢
    omega

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main (fun _ _ => True) Spec := by
  circuit_proof_start [Incomplete.DoubleAndAdd.circuit, Complete.AssignRegion.circuit]
  obtain ⟨hz0, hHi, hLo, hComp⟩ := h_holds
  simp only [Incomplete.DoubleAndAdd.Spec] at hHi hLo
  obtain ⟨bitsHi, hHiChain, hHiAcc⟩ := hHi
  obtain ⟨bitsLo, hLoChain, hLoAcc⟩ := hLo
  simp only [Complete.AssignRegion.Spec] at hComp
  obtain ⟨bitsC, hCChain, hCAcc⟩ := hComp
  -- the running-sum chains, mirrored over ℕ
  have hHiCells := chain_cast _ _ 0 bitsHi (by rw [hz0]; norm_num) hHiChain.1 hHiChain.2
  have hZhiCell := hHiCells 124 (by omega)
  have hK254 := hHiCells 0 (by omega)
  simp only [circuit_norm] at hZhiCell hK254
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
  refine ⟨bitsHi, bitsLo, bitsC, hK254, hZhiCell, ?_, ?_⟩
  · -- the z₁ cell, modulo index respelling
    simp only [Nat.add_assoc, Nat.reduceAdd] at hZcCell ⊢
    exact hZcCell
  -- the accumulator clause
  intro B hB hbase hAccPair
  have hHiOut := hHiAcc B 2 hB hbase hAccPair (le_refl 2) (by norm_num)
  have hmB := m_bounds bitsHi bitsLo
  have hLoOut := hLoAcc B (accScalar 2 bitsHi 125) hB hbase hHiOut hmB.1 hmB.2.1
  rw [show accScalar (accScalar 2 bitsHi 125) bitsLo (125 + 1)
    = accScalar (accScalar 2 bitsHi 125) bitsLo 126 from rfl] at hLoOut
  have hCompS := hCAcc
    (by rw [hLoOut]
        exact Or.inl (pallas_nsmul_onCurve hB hmB.2.2.2.2 hmB.2.2.2.1))
    (by show Pallas.Valid (input_base.x, input_base.y)
        rw [hbase]
        exact Or.inl (SWPoint.onCurve_of_ne_zero hB))
  simp only [Ecc.Point.coords] at hCompS
  obtain ⟨hValidAcc, hCompPair⟩ := hCompS
  rw [show input_base.x = B.x from congrArg Prod.fst hbase,
    show input_base.y = B.y from congrArg Prod.snd hbase, hLoOut,
    accValue_nsmul B (accScalar (accScalar 2 bitsHi 125) bitsLo 126)
      hmB.2.2.1 bitsC 3] at hCompPair
  exact ⟨by simp only [Ecc.Point.coords]; exact hValidAcc,
    by simp only [Ecc.Point.coords]; exact hCompPair⟩

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [Incomplete.DoubleAndAdd.circuit, Complete.AssignRegion.circuit]
  obtain ⟨B, hB, hbase, hAccPair⟩ := h_assumptions
  obtain ⟨hz0w, hHi, hLo, hComp⟩ := h_env
  -- the hi half
  have hHiS := hHi ⟨B, 2, hB, hbase, hAccPair, le_refl 2, by norm_num⟩
  simp only [Incomplete.DoubleAndAdd.ProverSpec] at hHiS
  obtain ⟨-, hHiZs, hHiAcc⟩ := hHiS
  have hHiOut := hHiAcc B 2 hB hbase hAccPair (le_refl 2) (by norm_num)
  rw [show accScalar 2 (fun i => input_bits i) (124 + 1)
    = accScalar 2 (fun i => input_bits i) 125 from rfl] at hHiOut
  have hmB := m_bounds (fun i => input_bits i) (fun i => input_bits (125 + i))
  -- the lo half
  have hLoS := hLo ⟨B, accScalar 2 (fun i => input_bits i) 125, hB, hbase, hHiOut,
    hmB.1, hmB.2.1⟩
  simp only [Incomplete.DoubleAndAdd.ProverSpec] at hLoS
  obtain ⟨-, hLoZs, hLoAcc⟩ := hLoS
  have hLoOut := hLoAcc B (accScalar 2 (fun i => input_bits i) 125) hB hbase hHiOut
    hmB.1 hmB.2.1
  rw [show accScalar (accScalar 2 (fun i => input_bits i) 125)
      (fun i => input_bits (125 + i)) (125 + 1)
    = accScalar (accScalar 2 (fun i => input_bits i) 125)
      (fun i => input_bits (125 + i)) 126 from rfl] at hLoOut
  -- the complete bits
  have hCompS := hComp ⟨by
      rw [hLoOut]
      exact ((accScalar (accScalar 2 (fun i => input_bits i) 125)
        (fun i => input_bits (125 + i)) 126 • B)).onCurve,
    by show Pallas.Valid (input_base.x, input_base.y)
       rw [hbase]
       exact Or.inl (SWPoint.onCurve_of_ne_zero hB)⟩
  simp only [Complete.AssignRegion.ProverSpec] at hCompS
  obtain ⟨-, hCompZs, hCompAcc⟩ := hCompS
  -- the honest running-sum cells
  have h124 := hHiZs ⟨124, by omega⟩
  have h0c := hHiZs ⟨0, by omega⟩
  have h125 := hLoZs ⟨125, by omega⟩
  have h2c := hCompZs ⟨2, by omega⟩
  simp only [circuit_norm] at h124 h0c h125 h2c
  rw [hz0w, show (0 : Fp) = ((0 : ℕ) : Fp) from by norm_num,
    zRunValue_chainNat 0 (fun i => input_bits i) 124,
    show (fun i => input_bits i) = input_bits from rfl,
    show (124 : ℕ) + 1 = 125 from rfl] at h124
  rw [hz0w, show (0 : Fp) = ((0 : ℕ) : Fp) from by norm_num,
    zRunValue_chainNat 0 (fun i => input_bits i) 0,
    show (fun i => input_bits i) = input_bits from rfl,
    show (0 : ℕ) + 1 = 1 from rfl] at h0c
  rw [h124, zRunValue_chainNat (chainNat 0 input_bits 125)
      (fun i => input_bits (125 + i)) 125,
    show (125 : ℕ) + 1 = 126 from rfl] at h125
  rw [h125, zRunValue_chainNat
      (chainNat (chainNat 0 input_bits 125) (fun i => input_bits (125 + i)) 126)
      (fun i => input_bits (251 + i)) 2,
    show (2 : ℕ) + 1 = 3 from rfl] at h2c
  refine ⟨⟨hz0w, ⟨B, 2, hB, hbase, hAccPair, le_refl 2, by norm_num⟩,
    ⟨B, accScalar 2 (fun i => input_bits i) 125, hB, hbase, hHiOut, hmB.1, hmB.2.1⟩,
    by rw [hLoOut]
       exact ((accScalar (accScalar 2 (fun i => input_bits i) 125)
         (fun i => input_bits (125 + i)) 126 • B)).onCurve,
    by show Pallas.Valid (input_base.x, input_base.y)
       rw [hbase]
       exact Or.inl (SWPoint.onCurve_of_ne_zero hB)⟩,
    h0c, h124, ?_, ?_⟩
  · -- the z₁ cell, modulo index respelling
    simp only [Nat.add_assoc, Nat.reduceAdd] at h2c ⊢
    exact h2c
  · -- the honest accumulator is a valid point
    rw [show input_base.x = B.x from congrArg Prod.fst hbase,
      show input_base.y = B.y from congrArg Prod.snd hbase, hLoOut,
      accValue_nsmul B (accScalar (accScalar 2 (fun i => input_bits i) 125)
          (fun i => input_bits (125 + i)) 126)
        hmB.2.2.1 (fun i => input_bits (251 + i)) 3] at hCompAcc
    rw [hCompAcc]
    exact ((accScalar (accScalar (accScalar 2 (fun i => input_bits i) 125)
      (fun i => input_bits (125 + i)) 126)
      (fun i => input_bits (251 + i)) 3 • B)).onCurve

/-- The decomposition section of `mul.rs::Config::assign`: `z_init = 0`, both
incomplete double-and-add halves, and the three complete-addition bits. -/
def circuit : GeneralFormalCircuit.WithHint Fp Input Output where
  main
  Spec
  ProverAssumptions
  ProverSpec
  soundness
  completeness

end Decompose

/-! ### `mul.rs::Config::process_lsb` as a virtual subcircuit -/

namespace ProcessLsb

/-- Inputs: the base, the running-sum cell `z_1`, the accumulator after the complete
rounds, and the prover-side LSB hint. -/
structure Input (F : Type) where
  base : Ecc.Point F
  z1 : F
  acc : Ecc.Point F
  bit : Unconstrained Bool F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ base := { x := default, y := default }, z1 := default,
     acc := { x := default, y := default }, bit := fun _ => default }⟩

structure Output (F : Type) where
  result : Ecc.Point F
  z0 : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Output Fp) := do
  -- z_0 = 2⋅z_1 + k_0
  let z0 ← witnessField fun env =>
    2 * env input.z1 + (if input.bit env then 1 else 0)
  -- copy in base_x, base_y for the LSB gate
  let baseX <== input.base.x
  let baseY <== input.base.y
  -- the correction point: identity if k_0 = 1, else -base
  let corrX ← witnessField fun env =>
    if input.bit env then 0 else env input.base.x
  let corrY ← witnessField fun env =>
    if input.bit env then 0 else -(env input.base.y)
  Mul.circuit { z1 := input.z1, z0, xP := corrX, yP := corrY, baseX, baseY }
  -- complete addition of the correction point
  let result ← Ecc.Add.circuit { p := { x := corrX, y := corrY }, q := input.acc }
  return { result, z0 }

instance elaborated : ElaboratedCircuit Fp Input Output main := by
  elaborate_circuit

/-- Soundness contract: `z_0` extends the running sum by a boolean `k_0`, and the
result adds the matching correction point (the identity for `k_0 = 1`, `-B` for
`k_0 = 0`) to the accumulator. -/
def Spec (input : Value Input Fp) (output : Output Fp) (_ : ProverData Fp) : Prop :=
  ∃ k0 : Fp, IsBool k0 ∧ output.z0 = 2 * input.z1 + k0 ∧
    ∀ B A : SWPoint Pallas.curve, B ≠ 0 →
      (input.base.x, input.base.y) = (B.x, B.y) →
      (input.acc.x, input.acc.y) = (A.x, A.y) →
      output.result.coords
        = (((if k0 = 1 then 0 else -B) + A).x, ((if k0 = 1 then 0 else -B) + A).y)

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  Pallas.OnCurve (input.base.x, input.base.y) ∧ Pallas.Valid (input.acc.x, input.acc.y)

def ProverSpec (input : ProverValue Input Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  output.z0 = 2 * input.z1 + (if input.bit then 1 else 0)

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main (fun _ _ => True) Spec := by
  circuit_proof_start [Mul.circuit, Ecc.Add.circuit]
  obtain ⟨hbx, hby, hMul, hAdd⟩ := h_holds
  simp only [Mul.Spec, Mul.SelectedCorrectionPoint, Mul.lsb] at hMul
  obtain ⟨hk0Bool, hCorrNeg, hCorrZero⟩ := hMul
  simp only [Ecc.Add.Assumptions, Ecc.Add.Spec, Ecc.Point.coords] at hAdd
  refine ⟨env.get i₀ - input_z1 * 2, hk0Bool, by ring, ?_⟩
  intro B A hB hbase hacc
  obtain ⟨hIx, hIy⟩ : Expression.eval env input_var.base.x = input_base.x ∧
      Expression.eval env input_var.base.y = input_base.y := by
    have h := h_input.1
    rw [← h]
    exact ⟨rfl, rfl⟩
  have hBx : input_base.x = B.x := congrArg Prod.fst hbase
  have hBy : input_base.y = B.y := congrArg Prod.snd hbase
  rcases hk0Bool with hk0 | hk0
  · -- k₀ = 0: the correction point is −B
    replace hCorrNeg := hCorrNeg hk0
    rw [hbx, hby, hIx, hIy, hBx, hBy,
      show CompElliptic.CurveForms.ShortWeierstrass.neg (B.x, B.y) = ((-B).x, (-B).y)
        from by simp [CompElliptic.CurveForms.ShortWeierstrass.neg]] at hCorrNeg
    have hAddS := (hAdd ⟨by
      rw [hCorrNeg]
      exact Or.inl (SWPoint.onCurve_of_ne_zero (neg_ne_zero.mpr hB)),
      by rw [hacc]; exact A.onCurve⟩).2
    rw [hCorrNeg, hacc, Pallas.add_coords] at hAddS
    rw [hk0, if_neg (by norm_num : ¬((0 : Fp) = 1))]
    exact hAddS
  · -- k₀ = 1: the correction point is the identity
    replace hCorrZero := hCorrZero hk0
    have hAddS := (hAdd ⟨by rw [hCorrZero]; exact Or.inr rfl,
      by rw [hacc]; exact A.onCurve⟩).2
    rw [hCorrZero, hacc,
      show ((0 : Fp), (0 : Fp))
        = ((0 : SWPoint Pallas.curve).x, (0 : SWPoint Pallas.curve).y) from rfl,
      Pallas.add_coords] at hAddS
    rw [hk0, if_pos rfl]
    exact hAddS

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [Mul.circuit, Ecc.Add.circuit]
  obtain ⟨hz0w, hbxw, hbyw, hcxw, hcyw, -⟩ := h_env
  obtain ⟨hOnC, hValidAcc⟩ := h_assumptions
  obtain ⟨hIx, hIy⟩ : Expression.eval env.toEnvironment input_var.base.x = input_base.x ∧
      Expression.eval env.toEnvironment input_var.base.y = input_base.y := by
    have h := h_input.1
    rw [← h]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨hbxw, hbyw, ?_, ?_, hValidAcc⟩, hz0w⟩
  · -- the LSB gate holds for the honest row
    simp only [Mul.Spec, Mul.SelectedCorrectionPoint, Mul.lsb]
    rw [hz0w, hcxw, hcyw, hbxw, hbyw, hIx, hIy,
      show (2 * input_z1 + (if input_bit then (1 : Fp) else 0)) - input_z1 * 2
        = (if input_bit then (1 : Fp) else 0) from by ring]
    cases input_bit
    · refine ⟨Or.inl (by norm_num), fun _ => ?_, fun h => absurd h (by norm_num)⟩
      norm_num [CompElliptic.CurveForms.ShortWeierstrass.neg]
    · refine ⟨Or.inr (by norm_num), fun h => absurd h (by norm_num), fun _ => ?_⟩
      norm_num
  · -- the honest correction point is valid
    rw [hcxw, hcyw, hIx, hIy]
    cases input_bit
    · norm_num
      refine Or.inl ?_
      simp only [CompElliptic.CurveForms.ShortWeierstrass.OnCurve, Ecc.Point.coords]
        at hOnC ⊢
      linear_combination hOnC
    · norm_num
      exact Or.inr rfl

/-- `mul.rs::Config::process_lsb`: the LSB running-sum step, the `GATE LSB check`
correction point, and its complete addition to the accumulator. -/
def circuit : GeneralFormalCircuit.WithHint Fp Input Output where
  main
  Spec
  ProverAssumptions
  ProverSpec
  soundness
  completeness

end ProcessLsb

/-- Inputs of variable-base scalar mul: the scalar cell and the non-identity base. -/
structure Input (F : Type) where
  alpha : F
  base : Ecc.Point F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Ecc.Point Fp) := do
  -- initialize the accumulator `acc = [2]base` using complete addition
  let acc ← Ecc.Add.circuit { p := input.base, q := input.base }
  -- the 254 double-and-add bits `k_254..k_1`: z_init, hi/lo halves, complete bits
  let dec ← Decompose.circuit {
    base := input.base, xA := acc.x, yA := acc.y,
    bits := fun env => fun i => kBits (env input.alpha) i }
  -- process the least significant bit `k_0`; the result is `[alpha] base`
  let lsb ← ProcessLsb.circuit {
    base := input.base, z1 := dec.z1, acc := dec.acc,
    bit := fun env => kBits (env input.alpha) 254 }
  -- overflow check on z_0 (full sum), z_130 (after the hi half), k_254 (first bit)
  Overflow.OverflowCheck.circuit {
    alpha := input.alpha, z0 := lsb.z0,
    z130 := dec.z130,
    k254 := dec.k254 }
  return lsb.result

instance elaborated : ElaboratedCircuit Fp Input Ecc.Point main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  Pallas.OnCurve input.base.coords

/-- The circuit computes the variable-base scalar multiplication `[alpha] base`,
with the identity encoded as `(0, 0)` coordinates. -/
def Spec (input : Input Fp) (output : Ecc.Point Fp) : Prop :=
  ∀ B : SWPoint Pallas.curve, B ≠ 0 → input.base.coords = (B.x, B.y) →
    output.coords = ((input.alpha.val • B).x, (input.alpha.val • B).y)
theorem soundness : Soundness Fp main Assumptions Spec := by
  sorry

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
