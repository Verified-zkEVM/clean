import Clean.Orchard.Ecc.Mul
import Clean.Orchard.Ecc.Mul.Incomplete
import Clean.Orchard.Ecc.Mul.Complete
import Clean.Orchard.Ecc.Mul.Overflow
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

namespace Orchard.Ecc.Mul

open CompElliptic.CurveForms
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
addition law `sw_add_coords`). -/
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
    rw [hU, sw_add_coords, sw_add_coords, nsmul_step B _ hA1 (bits b)]
    rfl

private theorem point_nsmul_coords_of_swpoint {P : Point Fp} {B : SWPoint Pallas.curve}
    (hPB : P.coords = (B.x, B.y)) (m : ℕ) :
    (m • P).coords = ((m • B).x, (m • B).y) := by
  rw [Point.nsmul_def]
  change smul pallasA m P.coords = ((m • B).x, (m • B).y)
  rw [hPB]
  rw [show pallasA = Pallas.curve.A from rfl]
  rw [← coords_nsmul]

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
  base : Point F
  xA : F
  yA : F
  bits : UnconstrainedNative BitsHint F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ base := { x := default, y := default }, xA := default, yA := default,
     bits := fun _ => default }⟩

/-- Outputs: the accumulator after all 254 double-and-add bits, plus the running-sum
cells the rest of `assign` inspects: `z_1`, `z_130` and `k_254`. -/
structure Output (F : Type) where
  acc : Point F
  z1 : F
  z130 : F
  k254 : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Output Fp) := do
  -- initialize the running sum to zero (`assign_advice_from_constant`)
  let zInit ← witness (0 : Fp)
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
      output.acc.Valid ∧
      output.acc.coords
        = ((accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 • B).x,
           (accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 • B).y)

def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  let base : Point Fp := input.base
  base.OnCurve

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
  output.acc.Valid

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
    GeneralFormalCircuit.WithHint.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [Incomplete.DoubleAndAdd.circuit, Complete.AssignRegion.circuit]
  -- 4.30 bump: `obtain` on the big `h_holds` conjunction triggers a whnf storm during
  -- motive abstraction (re-unifying subcircuit instance args); plain projections avoid it.
  have hz0 := h_holds.1
  have hHi := h_holds.2.1
  have hLo := h_holds.2.2.1
  have hComp := h_holds.2.2.2
  clear h_holds
  have hBaseOnCurve : Point.OnCurve input_base := h_assumptions
  replace hHi := hHi hBaseOnCurve
  replace hLo := hLo hBaseOnCurve
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
  let base : Point Fp := input_base
  have hbaseCoords : base.coords = (B.x, B.y) := hbase
  have hAccPairCoords :
      (input_xA, input_yA) = ((2 • base).x, (2 • base).y) := by
    change (input_xA, input_yA) = (2 • base).coords
    rw [point_nsmul_coords_of_swpoint hbaseCoords 2]
    exact hAccPair
  have hAccPairPoint : Point.ofCoords (input_xA, input_yA) = 2 • base := by
    apply Point.ext_coords
    simp only [Point.ofCoords_coords]
    exact hAccPairCoords
  have hHiOut := hHiAcc 2 hAccPairPoint (le_refl 2) (by norm_num)
  have hmB := m_bounds bitsHi bitsLo
  have hLoOut := hLoAcc (accScalar 2 bitsHi 125) hHiOut hmB.1 hmB.2.1
  rw [show accScalar (accScalar 2 bitsHi 125) bitsLo (125 + 1)
    = accScalar (accScalar 2 bitsHi 125) bitsLo 126 from rfl] at hLoOut
  -- 4.30 bump: derive the lo-half output cells in whatever normal form the framework
  -- leaves them, instead of restating them with hardcoded offsets
  have hLoOutSW := congrArg Point.coords hLoOut
  rw [Point.ofCoords_coords, point_nsmul_coords_of_swpoint hbaseCoords] at hLoOutSW
  have hCompS := hCAcc
    (by
      rw [Point.valid_iff, Point.coords, hLoOutSW]
      exact (accScalar (accScalar 2 bitsHi 125) bitsLo 126 • B).onCurve)
    (by
      rw [Point.valid_iff, Point.coords, hbase]
      exact Or.inl (SWPoint.onCurve_of_ne_zero hB))
  obtain ⟨hValidAcc, hCompPair⟩ := hCompS
  rw [show input_base.x = B.x from congrArg Prod.fst hbase,
    show input_base.y = B.y from congrArg Prod.snd hbase, hLoOutSW,
    accValue_nsmul B (accScalar (accScalar 2 bitsHi 125) bitsLo 126)
      hmB.2.2.1 bitsC 3] at hCompPair
  exact ⟨hValidAcc, hCompPair⟩

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [Incomplete.DoubleAndAdd.circuit, Complete.AssignRegion.circuit]
  -- 4.30 bump: destructuring `obtain`s abstract a motive over the huge goal, which
  -- triggers a whnf storm; peel the existential with `Exists.elim` and the
  -- conjunctions with plain projections instead.
  refine h_assumptions.elim fun B hBrest => ?_
  have hB := hBrest.1
  have hbase := hBrest.2.1
  have hAccPair := hBrest.2.2
  clear hBrest
  have hz0w := h_env.1
  have hHi := h_env.2.1
  have hLo := h_env.2.2.1
  have hComp := h_env.2.2.2
  clear h_env
  let base : Point Fp := input_base
  have hbaseCoords : base.coords = (B.x, B.y) := hbase
  have hBaseOnCurve : base.OnCurve := by
    rw [Point.onCurve_iff, Point.coords, hbase]
    exact SWPoint.onCurve_of_ne_zero hB
  have hAccPairCoords :
      (input_xA, input_yA) = ((2 • base).x, (2 • base).y) := by
    change (input_xA, input_yA) = (2 • base).coords
    rw [point_nsmul_coords_of_swpoint hbaseCoords 2]
    exact hAccPair
  have hAccPairPoint : Point.ofCoords (input_xA, input_yA) = 2 • base := by
    apply Point.ext_coords
    simp only [Point.ofCoords_coords]
    exact hAccPairCoords
  -- the hi half
  have hHiS := hHi ⟨hBaseOnCurve, 2, hAccPairPoint, le_refl 2, by norm_num⟩
  simp only [Incomplete.DoubleAndAdd.ProverSpec] at hHiS
  obtain ⟨-, hHiZs, hHiAcc⟩ := hHiS
  have hHiOut := hHiAcc 2 hAccPairPoint (le_refl 2) (by norm_num)
  rw [show accScalar 2 (fun i => input_bits i) (124 + 1)
    = accScalar 2 (fun i => input_bits i) 125 from rfl] at hHiOut
  have hmB := m_bounds (fun i => input_bits i) (fun i => input_bits (125 + i))
  -- the lo half
  have hLoS := hLo ⟨hBaseOnCurve, accScalar 2 (fun i => input_bits i) 125, hHiOut,
    hmB.1, hmB.2.1⟩
  simp only [Incomplete.DoubleAndAdd.ProverSpec] at hLoS
  obtain ⟨-, hLoZs, hLoAcc⟩ := hLoS
  have hLoOut := hLoAcc (accScalar 2 (fun i => input_bits i) 125) hHiOut
    hmB.1 hmB.2.1
  rw [show accScalar (accScalar 2 (fun i => input_bits i) 125)
      (fun i => input_bits (125 + i)) (125 + 1)
    = accScalar (accScalar 2 (fun i => input_bits i) 125)
      (fun i => input_bits (125 + i)) 126 from rfl] at hLoOut
  -- 4.30 bump: derive the lo-half output cells in whatever normal form the framework
  -- leaves them, instead of restating them with hardcoded offsets
  have hLoOutSW := congrArg Point.coords hLoOut
  rw [Point.ofCoords_coords, point_nsmul_coords_of_swpoint hbaseCoords] at hLoOutSW
  -- the complete bits
  have hCompS := hComp ⟨by
      rw [Point.valid_iff, Point.coords, hLoOutSW]
      exact ((accScalar (accScalar 2 (fun i => input_bits i) 125)
        (fun i => input_bits (125 + i)) 126 • B)).onCurve,
    by
      rw [Point.valid_iff, Point.coords, hbase]
      exact Or.inl (SWPoint.onCurve_of_ne_zero hB)⟩
  simp only [Complete.AssignRegion.ProverSpec] at hCompS
  obtain ⟨hCompValid, hCompZs, hCompAcc⟩ := hCompS
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
  refine ⟨⟨hz0w, ⟨hBaseOnCurve, 2, hAccPairPoint, le_refl 2, by norm_num⟩,
    ⟨hBaseOnCurve, accScalar 2 (fun i => input_bits i) 125, hHiOut, hmB.1, hmB.2.1⟩,
    by
      rw [Point.valid_iff, Point.coords, hLoOutSW]
      exact ((accScalar (accScalar 2 (fun i => input_bits i) 125)
        (fun i => input_bits (125 + i)) 126 • B)).onCurve,
    by
      rw [Point.valid_iff, Point.coords, hbase]
      exact Or.inl (SWPoint.onCurve_of_ne_zero hB)⟩,
    h0c, h124, ?_, ?_⟩
  · -- the z₁ cell, modulo index respelling
    simp only [Nat.add_assoc, Nat.reduceAdd] at h2c ⊢
    exact h2c
  · -- the honest accumulator is a valid point
    simp only [Complete.AssignRegion.Spec] at hCompValid
    obtain ⟨_, _, hValid⟩ := hCompValid
    exact (hValid
      (by
        rw [Point.valid_iff, Point.coords, hLoOutSW]
        exact ((accScalar (accScalar 2 (fun i => input_bits i) 125)
          (fun i => input_bits (125 + i)) 126 • B)).onCurve)
      (by
        rw [Point.valid_iff, Point.coords, hbase]
        exact Or.inl (SWPoint.onCurve_of_ne_zero hB))).1

/-- The decomposition section of `mul.rs::Config::assign`: `z_init = 0`, both
incomplete double-and-add halves, and the three complete-addition bits. -/
def circuit : GeneralFormalCircuit.WithHint Fp Input Output where
  main
  Assumptions
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
  base : Point F
  z1 : F
  acc : Point F
  bit : UnconstrainedNative Bool F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ base := { x := default, y := default }, z1 := default,
     acc := { x := default, y := default }, bit := fun _ => default }⟩

structure Output (F : Type) where
  result : Point F
  z0 : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Output Fp) := do
  -- z_0 = 2⋅z_1 + k_0
  let z0 ← witnessNative fun env =>
    2 * env input.z1 + (if input.bit env then 1 else 0)
  -- copy in base_x, base_y for the LSB gate
  let baseX <== input.base.x
  let baseY <== input.base.y
  -- the correction point: identity if k_0 = 1, else -base
  let corrX ← witnessNative fun env =>
    if input.bit env then 0 else env input.base.x
  let corrY ← witnessNative fun env =>
    if input.bit env then 0 else -(env input.base.y)
  Mul.Gate.circuit { z1 := input.z1, z0, xP := corrX, yP := corrY, baseX, baseY }
  -- complete addition of the correction point
  let result ← Add.circuit { p := { x := corrX, y := corrY }, q := input.acc }
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
  input.base.OnCurve ∧ input.acc.Valid

def ProverSpec (input : ProverValue Input Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  output.z0 = 2 * input.z1 + (if input.bit then 1 else 0)

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main (fun _ _ => True) Spec := by
  circuit_proof_start [Mul.Gate.circuit, Add.circuit]
  -- 4.30 bump: collapse the `Value field` synonym on the intro'd value, so that the
  -- mixed arithmetic statements below elaborate at `Fp`
  change Fp at input_z1
  obtain ⟨hbx, hby, hMul, hAdd⟩ := h_holds
  simp only [Mul.Gate.Spec, Mul.Gate.SelectedCorrectionPoint, Mul.Gate.lsb] at hMul
  obtain ⟨hk0Bool, hCorrNeg, hCorrZero⟩ := hMul
  simp only [Add.Assumptions, Add.Spec] at hAdd
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
      rw [Point.valid_iff, Point.coords, hCorrNeg]
      exact Or.inl (by
        exact SWPoint.onCurve_of_ne_zero (neg_ne_zero.mpr hB)),
      by
        rw [Point.valid_iff, Point.coords, hacc]
        exact A.onCurve⟩).2
    have hAddCoords := congrArg Point.coords hAddS
    rw [Point.coords_add] at hAddCoords
    simp only [Point.coords] at hAddCoords ⊢
    rw [hCorrNeg, hacc] at hAddCoords
    rw [hk0, if_neg (by norm_num : ¬((0 : Fp) = 1))]
    simp only [hAddCoords, SWPoint.add_x, SWPoint.add_y]
    rfl
  · -- k₀ = 1: the correction point is the identity
    replace hCorrZero := hCorrZero hk0
    have hAddS := (hAdd ⟨by
        rw [Point.valid_iff, Point.coords, hCorrZero]
        exact Or.inr rfl,
      by
        rw [Point.valid_iff, Point.coords, hacc]
        exact A.onCurve⟩).2
    have hAddCoords := congrArg Point.coords hAddS
    rw [Point.coords_add] at hAddCoords
    simp only [Point.coords] at hAddCoords ⊢
    rw [hCorrZero, hacc,
      show ((0 : Fp), (0 : Fp)) =
        ((0 : SWPoint Pallas.curve).x, (0 : SWPoint Pallas.curve).y) from rfl,
      ] at hAddCoords
    rw [hk0, if_pos rfl]
    simp only [hAddCoords, SWPoint.add_x, SWPoint.add_y]
    rfl

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [Mul.Gate.circuit, Add.circuit]
  -- 4.30 bump: collapse the `ProverValue` synonyms on the intro'd values, so that the
  -- mixed `ite`/arithmetic statements below elaborate at `Fp`/`Bool`
  change Fp at input_z1
  change Bool at input_bit
  obtain ⟨hz0w, hbxw, hbyw, hcxw, hcyw, -⟩ := h_env
  obtain ⟨hOnC, hValidAcc⟩ := h_assumptions
  obtain ⟨hIx, hIy⟩ : Expression.eval env.toEnvironment input_var.base.x = input_base.x ∧
      Expression.eval env.toEnvironment input_var.base.y = input_base.y := by
    have h := h_input.1
    rw [← h]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨hbxw, hbyw, ?_, ?_, hValidAcc⟩, hz0w⟩
  · -- the LSB gate holds for the honest row
    simp only [Mul.Gate.Spec, Mul.Gate.SelectedCorrectionPoint, Mul.Gate.lsb]
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
      rw [Point.onCurve_iff] at hOnC ⊢
      simp only [CompElliptic.CurveForms.ShortWeierstrass.OnCurve, Point.coords]
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
  base : Point F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Point Fp) := do
  -- initialize the accumulator `acc = [2]base` using complete addition
  let acc ← Add.circuit { p := input.base, q := input.base }
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

instance elaborated : ElaboratedCircuit Fp Input Point main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  input.base.OnCurve

/-- The circuit computes the variable-base scalar multiplication `[alpha] base`,
with the identity encoded as `(0, 0)` coordinates. -/
def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  output = input.alpha.val • input.base

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [Add.circuit, Decompose.circuit, ProcessLsb.circuit,
    Overflow.OverflowCheck.circuit]
  obtain ⟨hAcc, hDec, hLsb, hOv⟩ := h_holds
  replace hDec := hDec h_assumptions
  simp only [Decompose.Spec, Point.coords] at hDec
  obtain ⟨bitsHi, bitsLo, bitsC, hK254, hZ130, hZ1, hAccImpl⟩ := hDec
  simp only [ProcessLsb.Spec, Point.coords] at hLsb
  obtain ⟨k0, hk0Bool, hz0eq, hResImpl⟩ := hLsb
  simp only [Overflow.OverflowCheck.Spec] at hOv
  obtain ⟨hOvZ0, hOvDisj2, hOvEx⟩ := hOv
  let B : SWPoint Pallas.curve :=
    ⟨input_base.x, input_base.y, (Point.valid_iff input_base).mp (Or.inl h_assumptions)⟩
  have hB : B ≠ 0 := by
    intro h0
    have hx : input_base.x = (0 : Fp) := congrArg SWPoint.x h0
    have hy : input_base.y = (0 : Fp) := congrArg SWPoint.y h0
    have hzero : input_base = 0 := by
      rw [Point.mk.injEq]
      exact ⟨hx, hy⟩
    exact Point.not_onCurve_zero (hzero ▸ h_assumptions)
  have hcoords : input_base.coords = (B.x, B.y) := rfl
  have hBaseNsmul : ∀ n : ℕ, ((n • B).x, (n • B).y) = (n • input_base).coords :=
    fun n => (point_nsmul_coords_of_swpoint hcoords n).symm
  apply Point.ext_coords
  simp only [Add.Assumptions, Add.Spec] at hAcc
  simp only [Point.coords] at hcoords ⊢
  -- the doubled base: acc = [2]B
  have hAccPoint := (hAcc ⟨Or.inl h_assumptions, Or.inl h_assumptions⟩).2
  have hAccPair := congrArg Point.coords hAccPoint
  have hcoordsCoords : input_base.coords = (B.x, B.y) := by
    simpa [Point.coords] using hcoords
  rw [Point.coords_add, hcoordsCoords, sw_add_coords, ← two_nsmul] at hAccPair
  -- the decomposition accumulator: [accScalar (accScalar (accScalar 2 ..) ..) ..]B
  have hDecOut := hAccImpl B hB hcoords hAccPair
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
  have hm2 : accScalar (accScalar 2 bitsHi 125) bitsLo 126
      = 2 ^ 251 + 2 * chainNat (chainNat 0 bitsHi 125) bitsLo 126 + 1 := by
    rw [accScalar_closed _ (by rw [hm1]; omega) bitsLo 126, hm1,
      chainNat_offset (chainNat 0 bitsHi 125) bitsLo 126]
    norm_num
    omega
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
      hK254 hZ130 hZhiLt ?_ ?_ ?_ hcong hOvDisj2 hOvEx
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
    have hqzero : PALLAS_SCALAR_CARD • B = 0 := by
      exact (addOrderOf_dvd_iff_nsmul_eq_zero
        (x := B) (n := PALLAS_SCALAR_CARD)).mp (by rw [Point.addOrderOf_eq hB])
    rw [hs, show 2 ^ 254 + ZMod.val input_alpha + tQNat
        = ZMod.val input_alpha + PALLAS_SCALAR_CARD from by rw [hq]; ring,
      add_nsmul, hqzero, _root_.add_zero]
  -- the LSB step pins the result to [2^254 + k]B
  have hRes := hResImpl B
    (accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 • B)
    hB hcoords hDecOut.2
  rcases hk0Bool with hk0 | hk0
  · -- k₀ = 0: the correction point is −B, the result is [m₃ − 1]B
    rw [hk0] at hz0eq
    rw [hk0, if_neg (by norm_num : ¬((0 : Fp) = 1)),
      neg_add_nsmul B (by rw [hm3]; omega)] at hRes
    have hK := hKpart 0 (by omega)
      (by push_cast; linear_combination hOvZ0 - hz0eq - 2 * hZ1)
    rw [hRes, hfin
      (accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 - 1)
      (by rw [hm3]; omega)]
    exact hBaseNsmul _
  · -- k₀ = 1: the correction point is the identity, the result is [m₃]B
    rw [hk0] at hz0eq
    rw [hk0, if_pos rfl, _root_.zero_add] at hRes
    have hK := hKpart 1 (by omega)
      (by push_cast; linear_combination hOvZ0 - hz0eq - 2 * hZ1)
    rw [hRes, hfin
      (accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3)
      (by rw [hm3]; omega)]
    exact hBaseNsmul _

/-- The honest running-sum chains of `kBits` are the shifted values of `k`. -/
private theorem cells_kNat (alpha : Fp) :
    chainNat 0 (kBits alpha) 1 = kNat alpha / 2 ^ 254 ∧
    chainNat 0 (kBits alpha) 125 = kNat alpha / 2 ^ 130 ∧
    chainNat (chainNat (chainNat 0 (kBits alpha) 125) (fun i => kBits alpha (125 + i)) 126)
      (fun i => kBits alpha (251 + i)) 3 = kNat alpha / 2 := by
  have hC130 : chainNat 0 (kBits alpha) 125 = kNat alpha / 2 ^ 130 := by
    rw [chainNat_kBits alpha 125 (by omega)]
  have hC4 : chainNat (kNat alpha / 2 ^ 130) (fun i => kBits alpha (125 + i)) 126
      = kNat alpha / 2 ^ 4 := by
    rw [← hC130, ← chainNat_append 0 (kBits alpha) 125 126,
      show (125 : ℕ) + 126 = 251 from by norm_num,
      chainNat_kBits alpha 251 (by omega)]
  have hC2 : chainNat (kNat alpha / 2 ^ 4) (fun i => kBits alpha (251 + i)) 3
      = kNat alpha / 2 := by
    rw [show kNat alpha / 2 ^ 4 = chainNat 0 (kBits alpha) 251 from by
        rw [chainNat_kBits alpha 251 (by omega)],
      ← chainNat_append 0 (kBits alpha) 251 3,
      show (251 : ℕ) + 3 = 254 from by norm_num,
      chainNat_kBits alpha 254 (by omega)]
    norm_num
  exact ⟨by rw [chainNat_kBits alpha 1 (by omega)], hC130,
    by rw [hC130, hC4]; exact hC2⟩

/-- The honest `z₀` cell reconstructs the working scalar `k`. Stated over opaque cell
values so the heavy cast reasoning is kernel-checked here, not in `completeness`. -/
private theorem z0_cell_value (alpha : Fp) {z1v z0v : Fp}
    (hz1v : z1v = ((kNat alpha / 2 : ℕ) : Fp))
    (hz0w : z0v = 2 * z1v + (if kBits alpha 254 then 1 else 0)) :
    z0v = ((kNat alpha : ℕ) : Fp) := by
  have hbit : (if kBits alpha 254 then (1 : Fp) else 0)
      = ((kNat alpha % 2 : ℕ) : Fp) := by
    rw [show kBits alpha 254 = decide (kNat alpha % 2 = 1) from by unfold kBits; norm_num]
    rcases Nat.mod_two_eq_zero_or_one (kNat alpha) with h | h <;> rw [h] <;> simp
  rw [hz0w, hz1v, hbit, show ((kNat alpha : ℕ) : Fp)
    = ((2 * (kNat alpha / 2) + kNat alpha % 2 : ℕ) : Fp) from by congr 1; omega]
  push_cast
  ring

/-- The honest running-sum cells satisfy the overflow-check contract. -/
private theorem overflow_spec_honest (alpha : Fp) {z0v z130v k254v : Fp}
    (hz0v : z0v = ((kNat alpha : ℕ) : Fp))
    (h130 : z130v = ((kNat alpha / 2 ^ 130 : ℕ) : Fp))
    (h254 : k254v = ((kNat alpha / 2 ^ 254 : ℕ) : Fp)) :
    Overflow.OverflowCheck.Spec
      { alpha := alpha, z0 := z0v, z130 := z130v, k254 := k254v } := by
  have hKlt := kNat_lt alpha
  have hvallt : ZMod.val alpha
      < 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
    have h' := ZMod.val_lt alpha
    norm_num [PALLAS_BASE_CARD] at h'
    exact h'
  have hkdef : kNat alpha = ZMod.val alpha + tQNat := rfl
  have htq : tQNat = 45560315531506369815346746415080538113 := rfl
  have hav : ((ZMod.val alpha : ℕ) : Fp) = alpha := ZMod.natCast_rightInverse alpha
  have h2254 : kNat alpha / 2 ^ 254 = 0 ∨ kNat alpha / 2 ^ 254 = 1 := by
    have h := hKlt
    norm_num at h ⊢
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- z₀ = α + t_q
    rw [hz0v, hkdef]
    push_cast
    rw [hav]
    congr 1
  · -- k₂₅₄ = 0 ∨ z₁₃₀ = 2^124
    rw [h254, h130]
    rcases h2254 with h | h
    · left; rw [h]; norm_num
    · right
      have hval : kNat alpha / 2 ^ 130 = 2 ^ 124 := by
        have h1 := hKlt
        norm_num at h h1 ⊢
        omega
      rw [hval]
      push_cast
      norm_num
  · -- the decomposition of s = α + k₂₅₄·2^130
    rw [h254]
    rcases h2254 with h | h
    · rw [h]
      by_cases hsm : ZMod.val alpha < 2 ^ 130
      · exact ⟨0, ZMod.val alpha, hsm,
          by push_cast; rw [hav]; ring, Or.inr rfl, Or.inr (Or.inr rfl)⟩
      · refine ⟨((ZMod.val alpha / 2 ^ 130 : ℕ) : Fp), ZMod.val alpha % 2 ^ 130,
          Nat.mod_lt _ (by norm_num), ?_, Or.inl (by push_cast; ring), ?_⟩
        · have hsc : ((ZMod.val alpha : ℕ) : Fp)
              = ((ZMod.val alpha % 2 ^ 130 : ℕ) : Fp)
                + 2 ^ 130 * ((ZMod.val alpha / 2 ^ 130 : ℕ) : Fp) := by
            rw [show ((ZMod.val alpha : ℕ) : Fp)
              = ((ZMod.val alpha % 2 ^ 130
                  + 2 ^ 130 * (ZMod.val alpha / 2 ^ 130) : ℕ) : Fp) from by
                congr 1
                omega]
            push_cast
            ring
          push_cast
          linear_combination hsc - hav
        · -- z₁₃₀ ≠ 0, since k ≥ 2^130
          right; left
          rw [h130]
          intro h0
          have hlt : kNat alpha / 2 ^ 130 < 2 ^ 125 := by
            have h1 := hKlt
            norm_num at h1 ⊢
            omega
          have hge : 1 ≤ kNat alpha / 2 ^ 130 := by
            norm_num at hsm hlt ⊢
            omega
          have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp h0
          have hle := Nat.le_of_dvd (by omega) hdvd
          norm_num [PALLAS_BASE_CARD] at hle hlt
          omega
    · -- top bit set: α ≥ p − 2^130, the decomposition wraps once
      rw [h]
      refine ⟨0, ZMod.val alpha + 2 ^ 130
          - 28948022309329048855892746252171976963363056481941560715954676764349967630337,
        ?_, ?_, Or.inr rfl, Or.inl (by push_cast; norm_num)⟩
      · norm_num at h ⊢
        omega
      · have hge : 28948022309329048855892746252171976963363056481941560715954676764349967630337
            ≤ ZMod.val alpha + 2 ^ 130 := by
          norm_num at h ⊢
          omega
        rw [show ((ZMod.val alpha + 2 ^ 130
            - 28948022309329048855892746252171976963363056481941560715954676764349967630337 : ℕ) : Fp)
          = ((ZMod.val alpha + 2 ^ 130 : ℕ) : Fp)
            - ((28948022309329048855892746252171976963363056481941560715954676764349967630337 : ℕ) : Fp)
          from by rw [Nat.cast_sub hge],
          show ((28948022309329048855892746252171976963363056481941560715954676764349967630337 : ℕ) : Fp)
            = 0 from by
            rw [show (28948022309329048855892746252171976963363056481941560715954676764349967630337 : ℕ)
              = PALLAS_BASE_CARD from by norm_num [PALLAS_BASE_CARD]]
            exact ZMod.natCast_self PALLAS_BASE_CARD]
        push_cast
        rw [hav]
        ring

theorem completeness : Completeness Fp main Assumptions := by
  circuit_proof_start [Add.circuit, Decompose.circuit, ProcessLsb.circuit,
    Overflow.OverflowCheck.circuit]
  obtain ⟨hAcc, hDec, hLsb⟩ := h_env
  -- the base as a nonzero curve point
  obtain ⟨B, hB, hBx, hBy⟩ : ∃ B : SWPoint Pallas.curve, B ≠ 0 ∧
      B.x = input_base.x ∧ B.y = input_base.y := by
    refine ⟨⟨input_base.x, input_base.y, (Point.valid_iff input_base).mp (Or.inl h_assumptions)⟩,
      ?_, rfl, rfl⟩
    intro h0
    have hx : input_base.x = (0 : Fp) := congrArg SWPoint.x h0
    have hy : input_base.y = (0 : Fp) := congrArg SWPoint.y h0
    have hzero : input_base = 0 := by
      rw [Point.mk.injEq]
      exact ⟨hx, hy⟩
    exact Point.not_onCurve_zero (hzero ▸ h_assumptions)
  have hbase : (input_base.x, input_base.y) = (B.x, B.y) := by rw [hBx, hBy]
  -- the doubled base: acc = [2]B
  simp only [Add.Assumptions, Add.Spec] at hAcc
  have hAccPoint := (hAcc ⟨Or.inl h_assumptions, Or.inl h_assumptions⟩).2
  have hAccPair := congrArg Point.coords hAccPoint
  have hbaseCoords : input_base.coords = (B.x, B.y) := by
    simpa [Point.coords] using hbase
  rw [Point.coords_add, hbaseCoords, sw_add_coords, ← two_nsmul] at hAccPair
  -- the decomposition prover facts: honest cells as shifted values of k
  have hDecS := hDec ⟨B, hB, hbase, hAccPair⟩
  simp only [Decompose.ProverSpec] at hDecS
  obtain ⟨-, h254, h130, h1c, hValidAcc⟩ := hDecS
  have hck := cells_kNat input_alpha
  rw [show (fun i => kBits input_alpha i) = kBits input_alpha from rfl, hck.1] at h254
  rw [show (fun i => kBits input_alpha i) = kBits input_alpha from rfl, hck.2.1] at h130
  rw [show (fun i => kBits input_alpha i) = kBits input_alpha from rfl, hck.2.2] at h1c
  -- the LSB prover facts: the honest z₀ reconstructs k
  have hLsbS := hLsb ⟨h_assumptions, hValidAcc⟩
  simp only [ProcessLsb.ProverSpec] at hLsbS
  have hz0v := z0_cell_value input_alpha h1c hLsbS.2
  exact ⟨⟨Or.inl h_assumptions, Or.inl h_assumptions⟩, ⟨B, hB, hbase, hAccPair⟩,
    ⟨h_assumptions, hValidAcc⟩, overflow_spec_honest input_alpha hz0v h130 h254⟩

/-- `mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`):
variable-base scalar multiplication by a base-field element. -/
def circuit : FormalCircuit Fp Input Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Orchard.Ecc.Mul
