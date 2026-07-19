import Clean.Ironwood.Ecc.Defs
import Clean.Ironwood.Utilities.RunningSum

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/overflow.rs`.
-/

namespace Halo2.Ironwood.Ecc.Mul.Overflow

structure Input (F : Type) where
  z0 : F
  z130 : F
  eta : F
  k254 : F
  alpha : F
  sMinusLo130 : F
  s : F
deriving ProvableStruct

def sCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 130)] (row : Input K) : K :=
  row.s - (row.alpha + row.k254 * OfNat.ofNat (2 ^ 130))

def recovery {K : Type} [Sub K] [OfNat K 2]
    [OfNat K 45560315531506369815346746415080538113] (row : Input K) : K :=
  row.z0 - row.alpha - tQ

def loZero {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 124)] (row : Input K) : K :=
  row.k254 * (row.z130 - OfNat.ofNat (2 ^ 124))

def sMinusLo130Check {K : Type} [Mul K] (row : Input K) : K :=
  row.k254 * row.sMinusLo130

def canonicity {K : Type} [One K] [Sub K] [Mul K] (row : Input K) : K :=
  (1 - row.k254) * (1 - row.z130 * row.eta) * row.sMinusLo130

def Spec (row : Input Fp) : Prop :=
  row.s = row.alpha + row.k254 * OfNat.ofNat (2 ^ 130) ∧
    row.z0 = row.alpha + tQ ∧
    (row.k254 = 0 ∨ row.z130 = OfNat.ofNat (2 ^ 124)) ∧
    (row.k254 = 0 ∨ row.sMinusLo130 = 0) ∧
    (row.k254 = 1 ∨ row.z130 * row.eta = 1 ∨ row.sMinusLo130 = 0)

/-!
### `overflow.rs::Config::overflow_check`

Witnesses `s = alpha + k_254 ⋅ 2^130`, decomposes its low 130 bits with thirteen
10-bit lookups (`copy_check`, strict = false), witnesses `η = inv0(z_130)`, and applies
the overflow gate to the copied cells.
-/

namespace OverflowCheck

/-- Inputs: the original scalar cell and the running-sum cells the check inspects,
`z_0` (full sum), `z_130` (after the hi half), and `k_254 = z_254` (first bit). -/
structure Input (F : Type) where
  alpha : F
  z0 : F
  z130 : F
  k254 : F
deriving ProvableStruct

/-- The semantic contract of the overflow check: `z_0` recovers `alpha + t_q`, and the
canonicity disjunctions over the 130-bit decomposition of `s = alpha + k_254 ⋅ 2^130`
hold. The decomposition is existential: some split `s = s_lo + 2^130 ⋅ s_hi` with
`s_lo < 2^130` satisfies the per-case vanishing. -/
def Spec (input : Input Fp) : Prop :=
  input.z0 = input.alpha + tQ ∧
  (input.k254 = 0 ∨ input.z130 = (2 ^ 124 : Fp)) ∧
  ∃ (sHi : Fp) (sLo : ℕ), sLo < 2 ^ 130 ∧
    input.alpha + input.k254 * (2 ^ 130 : Fp) = (sLo : Fp) + (2 ^ 130 : Fp) * sHi ∧
    (input.k254 = 0 ∨ sHi = 0) ∧
    (input.k254 = 1 ∨ input.z130 ≠ 0 ∨ sHi = 0)

/-- Name the evaluation of a vector's cell 13 opaquely; stating this over an abstract
`v` lets the caller instantiate it with a concrete append term whose `getElem` bound
would not elaborate inline. -/
private theorem eval_get13 (env : Environment Fp) (v : Vector (Expression Fp) 14) :
    ∃ z, Expression.eval env v[13] = z := ⟨_, rfl⟩

end OverflowCheck

end Halo2.Ironwood.Ecc.Mul.Overflow
