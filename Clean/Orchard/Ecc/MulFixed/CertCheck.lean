import Clean.Orchard.Specs.PallasCert

/-!
# Nat-level certification checker for concrete fixed-base window tables

The evaluation layer of the concrete-`FixedBase` certification. All checked equations
live over `ℕ` literals (`rfl`-evaluable through GMP kernel arithmetic — the ZMod-stated
equivalents are >200× slower, see `BenchFixedBase.lean`); the soundness lemmas here
bridge each passed check into the `Point Fp` facts (`PallasCert`) the chain induction
consumes. Subtraction is encoded as `(a + P − b) % P`; no inversion or exponentiation
appears — slopes are witnesses.
-/

namespace Orchard.Ecc.MulFixed.Cert

open Orchard (Point Fp pallasA)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- The Pallas base-field modulus (the checker's `ℕ` world). -/
def P : ℕ := PALLAS_BASE_CARD

/-- `a·b mod P`. -/
def mulm (a b : ℕ) : ℕ := a * b % P

/-- `a − b mod P` (offset spelling, total on `ℕ`). -/
def subm (a b : ℕ) : ℕ := (a + P - b) % P

/-! ## Cast bridges (ℕ checks → `Fp` equations) -/

theorem cast_mod (a : ℕ) : ((a % P : ℕ) : Fp) = (a : Fp) := by
  conv_rhs => rw [← Nat.div_add_mod a P]
  push_cast
  rw [show ((P : ℕ) : Fp) = 0 from ZMod.natCast_self P]
  ring

theorem cast_mulm (a b : ℕ) : ((mulm a b : ℕ) : Fp) = (a : Fp) * (b : Fp) := by
  rw [mulm, cast_mod]
  push_cast
  ring

theorem cast_subm {b : ℕ} (a : ℕ) (hb : b ≤ P) :
    ((subm a b : ℕ) : Fp) = (a : Fp) - (b : Fp) := by
  rw [subm, cast_mod, Nat.cast_sub (Nat.le_add_left b a |>.trans (by omega))]
  push_cast
  rw [show ((P : ℕ) : Fp) = 0 from ZMod.natCast_self P]
  ring

theorem cast_inj {a b : ℕ} (ha : a < P) (hb : b < P) (h : (a : Fp) = (b : Fp)) :
    a = b := by
  have h' : ZMod.val (n := PALLAS_BASE_CARD) (a : Fp) = ZMod.val (n := PALLAS_BASE_CARD) (b : Fp) :=
    congrArg _ h
  rwa [ZMod.val_cast_of_lt (show a < PALLAS_BASE_CARD from ha),
    ZMod.val_cast_of_lt (show b < PALLAS_BASE_CARD from hb)] at h'

theorem cast_eq_zero_iff {a : ℕ} (ha : a < P) : ((a : Fp) = 0) ↔ a = 0 := by
  constructor
  · intro h
    exact cast_inj ha (by norm_num [P, PALLAS_BASE_CARD]) (by rw [h]; norm_num)
  · intro h
    rw [h]
    norm_num

/-! ## Single-op checkers -/

/-- Secant addition check: `⟨px,py⟩ + ⟨qx,qy⟩ = ⟨rx,ry⟩` with slope witness `l`. -/
def checkAdd (px py qx qy l rx ry : ℕ) : Bool :=
  px < P && py < P && qx < P && qy < P && l < P && rx < P && ry < P &&
  !(px == 0 && py == 0) && !(qx == 0 && qy == 0) && !(px == qx) &&
  mulm l (subm qx px) == subm qy py &&
  rx == subm (mulm l l) ((px + qx) % P) &&
  ry == subm (mulm l (subm px rx)) py

/-- Tangent doubling check: `⟨px,py⟩ + ⟨px,py⟩ = ⟨rx,ry⟩` with slope witness `l`
(`pallasA = 0`). -/
def checkDouble (px py l rx ry : ℕ) : Bool :=
  px < P && py < P && l < P && rx < P && ry < P &&
  !(px == 0 && py == 0) && !(py == 0) &&
  mulm l (2 * py % P) == 3 * px * px % P &&
  rx == subm (mulm l l) ((px + px) % P) &&
  ry == subm (mulm l (subm px rx)) py

/-- The `Point Fp` of a `ℕ` coordinate pair. -/
def pointOf (c : ℕ × ℕ) : Point Fp := ⟨(c.1 : Fp), (c.2 : Fp)⟩

theorem pointOf_ne_zero {x y : ℕ} (hx : x < P) (hy : y < P)
    (h : ¬(x = 0 ∧ y = 0)) : pointOf (x, y) ≠ 0 := by
  intro h0
  have hx0 : ((x : ℕ) : Fp) = 0 := congrArg Point.x h0
  have hy0 : ((y : ℕ) : Fp) = 0 := congrArg Point.y h0
  exact h ⟨(cast_eq_zero_iff hx).mp hx0, (cast_eq_zero_iff hy).mp hy0⟩

/-- Soundness of `checkAdd`. -/
theorem checkAdd_sound {px py qx qy l rx ry : ℕ}
    (h : checkAdd px py qx qy l rx ry = true) :
    pointOf (px, py) + pointOf (qx, qy) = pointOf (rx, ry) := by
  simp only [checkAdd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpx, hpy⟩, hqx⟩, hqy⟩, hl⟩, hrx⟩, hry⟩, hpz⟩, hqz⟩, hne⟩,
    h1⟩, h2⟩, h3⟩ := h
  have hPle : ∀ {a : ℕ}, a < P → a ≤ P := fun h => Nat.le_of_lt h
  apply Orchard.Point.add_of_witness (l := (l : Fp))
  · exact pointOf_ne_zero hpx hpy (by
      intro ⟨h1', h2'⟩
      simp [h1', h2'] at hpz)
  · exact pointOf_ne_zero hqx hqy (by
      intro ⟨h1', h2'⟩
      simp [h1', h2'] at hqz)
  · show ((px : ℕ) : Fp) ≠ ((qx : ℕ) : Fp)
    intro hc
    exact absurd (cast_inj hpx hqx hc) (by simpa using hne)
  · show (l : Fp) * (((qx : ℕ) : Fp) - ((px : ℕ) : Fp))
      = ((qy : ℕ) : Fp) - ((py : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h1
    rwa [cast_mulm, cast_subm _ (hPle hpx), cast_subm _ (hPle hpy)] at this
  · show ((rx : ℕ) : Fp) = (l : Fp) * (l : Fp) - ((px : ℕ) : Fp) - ((qx : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h2
    rw [cast_subm _ (by
        have : (px + qx) % P < P := Nat.mod_lt _ (by norm_num [P, PALLAS_BASE_CARD])
        omega),
      cast_mulm, cast_mod] at this
    push_cast at this
    rw [this]
    ring
  · show ((ry : ℕ) : Fp)
      = (l : Fp) * (((px : ℕ) : Fp) - ((rx : ℕ) : Fp)) - ((py : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h3
    rwa [cast_subm _ (hPle hpy), cast_mulm, cast_subm _ (hPle hrx)] at this

/-- Soundness of `checkDouble`. -/
theorem checkDouble_sound {px py l rx ry : ℕ}
    (h : checkDouble px py l rx ry = true) :
    pointOf (px, py) + pointOf (px, py) = pointOf (rx, ry) := by
  simp only [checkDouble, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpx, hpy⟩, hl⟩, hrx⟩, hry⟩, hpz⟩, hyz⟩, h1⟩, h2⟩, h3⟩ := h
  have hPle : ∀ {a : ℕ}, a < P → a ≤ P := fun h => Nat.le_of_lt h
  apply Orchard.Point.double_of_witness (l := (l : Fp))
  · exact pointOf_ne_zero hpx hpy (by
      intro ⟨h1', h2'⟩
      simp [h1', h2'] at hpz)
  · show ((py : ℕ) : Fp) ≠ 0
    intro hc
    exact hyz ((cast_eq_zero_iff hpy).mp hc)
  · show (l : Fp) * (2 * ((py : ℕ) : Fp)) = 3 * ((px : ℕ) : Fp) ^ 2 + pallasA
    have := congrArg (Nat.cast (R := Fp)) h1
    rw [cast_mulm, cast_mod] at this
    rw [show ((3 * px * px % P : ℕ) : Fp) = ((3 * px * px : ℕ) : Fp) from cast_mod _]
      at this
    push_cast at this
    rw [this, Orchard.pallasA]
    ring
  · show ((rx : ℕ) : Fp) = (l : Fp) * (l : Fp) - ((px : ℕ) : Fp) - ((px : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h2
    rw [cast_subm _ (by
        have : (px + px) % P < P := Nat.mod_lt _ (by norm_num [P, PALLAS_BASE_CARD])
        omega),
      cast_mulm, cast_mod] at this
    push_cast at this
    rw [this]
    ring
  · show ((ry : ℕ) : Fp)
      = (l : Fp) * (((px : ℕ) : Fp) - ((rx : ℕ) : Fp)) - ((py : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h3
    rwa [cast_subm _ (hPle hpy), cast_mulm, cast_subm _ (hPle hrx)] at this

end Orchard.Ecc.MulFixed.Cert
