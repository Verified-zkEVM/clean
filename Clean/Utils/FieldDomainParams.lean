import CompElliptic.Fields.Sqrt
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Certified field parameters for evaluation domains and permutation columns

A multiplicative generator and the two-adic factorization determine both domain roots
and column separators. Their orders, and hence separation of cell labels, are derived
here independently of any circuit.
-/

/-- A chosen domain convention for an odd-characteristic field. The generator is
protocol data: changing the instance changes the roots and permutation-column names. -/
class FieldDomainParams (F : Type*) [Field F] where
  twoAdicity : ℕ
  oddPart : ℕ
  generator : F
  card_eq : Nat.card F = 2 ^ twoAdicity * oddPart + 1
  oddPart_odd : Odd oddPart
  twoAdicity_pos : 0 < twoAdicity
  generator_isPrimitiveRoot : IsPrimitiveRoot generator (Nat.card F - 1)

namespace FieldDomainParams

variable {F : Type*} [Field F] [params : FieldDomainParams F]

/-- The maximal power-of-two root, obtained from the field generator. -/
def rootOfUnity : F := CompElliptic.Fields.fpow params.generator params.oddPart

/-- The odd-order generator used to distinguish permutation columns. -/
def delta : F := CompElliptic.Fields.fpow params.generator (2 ^ params.twoAdicity)

/-- The root for a domain of size `2^k`; support requires `k ≤ twoAdicity`. -/
def omega (k : ℕ) : F :=
  CompElliptic.Fields.fpow rootOfUnity (2 ^ (params.twoAdicity - k))

theorem rootOfUnity_eq_pow : rootOfUnity = params.generator ^ params.oddPart :=
  CompElliptic.Fields.fpow_spec _ _

theorem delta_eq_pow : delta = params.generator ^ (2 ^ params.twoAdicity) :=
  CompElliptic.Fields.fpow_spec _ _

theorem omega_eq_pow (k : ℕ) :
    omega k = (rootOfUnity : F) ^ (2 ^ (params.twoAdicity - k)) :=
  CompElliptic.Fields.fpow_spec _ _

theorem oddPart_pos : 0 < params.oddPart := params.oddPart_odd.pos

/-- Removing the odd factor leaves precisely the maximal power-of-two order. -/
theorem rootOfUnity_isPrimitiveRoot :
    IsPrimitiveRoot (rootOfUnity : F) (2 ^ params.twoAdicity) := by
  rw [rootOfUnity_eq_pow]
  apply params.generator_isPrimitiveRoot.pow
  · rw [params.card_eq, Nat.add_sub_cancel]
    exact Nat.mul_pos (by positivity) oddPart_pos
  · rw [params.card_eq, Nat.add_sub_cancel, Nat.mul_comm]

/-- Removing the power-of-two factor leaves precisely the odd order. -/
theorem delta_isPrimitiveRoot : IsPrimitiveRoot (delta : F) params.oddPart := by
  rw [delta_eq_pow]
  apply params.generator_isPrimitiveRoot.pow
  · rw [params.card_eq, Nat.add_sub_cancel]
    exact Nat.mul_pos (by positivity) oddPart_pos
  · rw [params.card_eq, Nat.add_sub_cancel]

theorem delta_ne_zero : (delta : F) ≠ 0 :=
  (delta_isPrimitiveRoot.isUnit (Nat.ne_of_gt oddPart_pos)).ne_zero

/-- Squaring down the maximal root gives the exact requested domain order. -/
theorem omega_isPrimitiveRoot {k : ℕ} (hSupported : k ≤ params.twoAdicity) :
    IsPrimitiveRoot (omega k : F) (2 ^ k) := by
  rw [omega_eq_pow]
  apply rootOfUnity_isPrimitiveRoot.pow (by positivity)
  rw [← pow_add, Nat.sub_add_cancel hSupported]

/-- Distinct supported columns occupy disjoint cosets of the evaluation subgroup. -/
theorem eq_of_delta_pow_eq_omega_pow_mul {k n : ℕ}
    (hSupported : k ≤ params.twoAdicity) (hColumns : n ≤ params.oddPart)
    (j j' : Fin n) (row : ℕ)
    (h : (delta : F) ^ (j : ℕ) =
      omega k ^ row * delta ^ (j' : ℕ)) : j = j' := by
  have hColumn (i : ℕ) : ((delta : F) ^ i) ^ params.oddPart = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, delta_isPrimitiveRoot.pow_eq_one,
      one_pow]
  have hPowers := congrArg (fun x : F => x ^ params.oddPart) h
  dsimp only at hPowers
  rw [hColumn, mul_pow, hColumn, mul_one, ← pow_mul] at hPowers
  have hRoot := omega_isPrimitiveRoot (F := F) hSupported
  have hCoprime : Nat.Coprime (2 ^ k) params.oddPart :=
    params.oddPart_odd.coprime_two_left.pow_left _
  have hDivides : 2 ^ k ∣ row := hCoprime.dvd_of_dvd_mul_right
    ((hRoot.pow_eq_one_iff_dvd _).mp hPowers.symm)
  rw [(hRoot.pow_eq_one_iff_dvd _).mpr hDivides, one_mul] at h
  exact Fin.ext (delta_isPrimitiveRoot.pow_inj
    (lt_of_lt_of_le j.isLt hColumns) (lt_of_lt_of_le j'.isLt hColumns) h)

/-- The same certified parameters supply CompElliptic's square-root algorithm. -/
def toTonelliShanks [Fintype F] : CompElliptic.Fields.TonelliShanks F where
  twoAdicity := params.twoAdicity
  oddPart := params.oddPart
  rootOfUnity := rootOfUnity
  valid := {
    card_eq := by simpa only [Nat.card_eq_fintype_card] using params.card_eq
    oddPart_odd := params.oddPart_odd
    twoAdicity_pos := params.twoAdicity_pos
    rootOfUnity_order := rootOfUnity_isPrimitiveRoot.eq_orderOf.symm }

end FieldDomainParams
