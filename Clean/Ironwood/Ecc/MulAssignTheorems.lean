import Clean.Ironwood.Ecc.MulTheorems
import Clean.Ironwood.Ecc.MulIncompleteTheorems
import Clean.Ironwood.Ecc.MulCompleteTheorems
import Clean.Ironwood.Ecc.MulOverflowTheorems
import Clean.Ironwood.Ecc.AddTheorems

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

namespace Halo2.Ironwood.Ecc.Mul

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
natural-number value. `chainNat` mirrors `z ↦ 2z + bit` over `ℕ`.

The chain/canonicity lemmas of this file (`chainNat_*`, `chain_cast`, `accScalar_closed`,
`nsmul_step`, `neg_add_nsmul`, `k_canonical`, `m_bounds`, `cells_kNat`, `z0_cell_value`,
`overflow_spec_honest`) are public: the Ironwood region-level port
(`Clean/Ironwood/Ecc/Mul.lean`) consumes them directly. -/

/-- The running sum continued from `zin` by `b` steps of `z ↦ 2z + bit`. -/
def chainNat (zin : ℕ) (bits : ℕ → Bool) : ℕ → ℕ
  | 0 => zin
  | b + 1 => 2 * chainNat zin bits b + (if bits b then 1 else 0)

theorem chainNat_lt (zin : ℕ) (bits : ℕ → Bool) :
    ∀ b, chainNat zin bits b < 2 ^ b * (zin + 1)
  | 0 => by simp [chainNat]
  | b + 1 => by
    have ih := chainNat_lt zin bits b
    have hpow : 2 ^ (b + 1) * (zin + 1) = 2 * (2 ^ b * (zin + 1)) := by ring
    simp only [chainNat, hpow]
    cases bits b <;> simp <;> omega

theorem chainNat_offset (zin : ℕ) (bits : ℕ → Bool) :
    ∀ b, chainNat zin bits b = 2 ^ b * zin + chainNat 0 bits b
  | 0 => by simp [chainNat]
  | b + 1 => by
    have ih := chainNat_offset zin bits b
    have hpow : 2 ^ (b + 1) * zin = 2 * (2 ^ b * zin) := by ring
    simp only [chainNat, hpow]
    omega

/-- Splitting off the first (most significant) bit of a zero-started chain. -/
theorem chainNat_msb (bits : ℕ → Bool) :
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
theorem chain_cast {n : ℕ} (zs : Vector Fp (n + 1)) (zin : Fp) (Zin : ℕ)
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

theorem accScalar_closed (m : ℕ) (hm : 1 ≤ m) (bits : ℕ → Bool) :
    ∀ b, accScalar m bits b = 2 ^ b * (m - 1) + 2 * chainNat 0 bits b + 1
  | 0 => by simp [accScalar, chainNat]; omega
  | b + 1 => by
    have ih := accScalar_closed m hm bits b
    have hpow : 2 ^ (b + 1) * (m - 1) = 2 * (2 ^ b * (m - 1)) := by ring
    simp only [accScalar, chainNat, hpow]
    cases bits b <;> simp <;> omega

/-! ### Complete-addition steps as scalar multiples -/

/-- One double-and-add group step: `A•B + (±B + A•B) = (2A ± 1)•B`. -/
theorem nsmul_step (B : SWPoint Pallas.curve) (A : ℕ) (hA : 1 ≤ A)
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
theorem neg_add_nsmul (B : SWPoint Pallas.curve) {m : ℕ} (hm : 1 ≤ m) :
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

theorem k_canonical {alpha k254 z130 : Fp} {K Zhi R : ℕ} {b254 : Bool}
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

theorem chainNat_testBit (K n : ℕ) (hK : K < 2 ^ n) :
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
theorem chainNat_append (zin : ℕ) (bits : ℕ → Bool) (a : ℕ) :
    ∀ b, chainNat zin bits (a + b)
      = chainNat (chainNat zin bits a) (fun i => bits (a + i)) b
  | 0 => rfl
  | b + 1 => by
    have ih := chainNat_append zin bits a b
    show 2 * chainNat zin bits (a + b) + (if bits (a + b) then 1 else 0) = _
    rw [ih]
    rfl

theorem kNat_lt (alpha : Fp) : kNat alpha < 2 ^ 255 := by
  have h := ZMod.val_lt alpha
  norm_num [PALLAS_BASE_CARD] at h
  norm_num [kNat, tQNat]
  omega

/-- The honest running sum after `j` of the 255 steps is the high `j` bits of `k`. -/
theorem chainNat_kBits (alpha : Fp) (j : ℕ) (hj : j ≤ 255) :
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

/-- Outputs: the accumulator after all 254 double-and-add bits, plus the running-sum
cells the rest of `assign` inspects: `z_1`, `z_130` and `k_254`. -/
structure Output (F : Type) where
  acc : Point F
  z1 : F
  z130 : F
  k254 : F
deriving ProvableStruct

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
theorem m_bounds (bits1 bits2 : ℕ → Bool) :
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

structure Output (F : Type) where
  result : Point F
  z0 : F
deriving ProvableStruct

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

end ProcessLsb

/-- Inputs of variable-base scalar mul: the scalar cell and the non-identity base. -/
structure Input (F : Type) where
  alpha : F
  base : Point F
deriving ProvableStruct

/-- The honest running-sum chains of `kBits` are the shifted values of `k`. -/
theorem cells_kNat (alpha : Fp) :
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
theorem z0_cell_value (alpha : Fp) {z1v z0v : Fp}
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
theorem overflow_spec_honest (alpha : Fp) {z0v z130v k254v : Fp}
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

end Halo2.Ironwood.Ecc.Mul
