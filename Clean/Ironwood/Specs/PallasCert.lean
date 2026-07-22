import Clean.Ironwood.Specs.Pallas

/-!
# Witnessed-operation lemmas for concrete point chains

The per-operation glue of the concrete-`FixedBase` certification: each chain step in a
dumped window table comes with a witnessed slope, and these lemmas turn the three
checked field equations (plus literal disequalities) into the `Point`-level facts
`p + q = r` / `p + p = r` that the chain induction consumes. No field inversion is ever
computed — the slope witness replaces it.
-/

namespace Zcash.Circuits.Point

open CompElliptic.CurveForms

/-- Secant addition from a witnessed slope: if `l·(qx − px) = qy − py` and `r`'s
coordinates satisfy the secant formulas at `l`, then `p + q = r`. -/
theorem add_of_witness {p q r : Point Fp} (l : Fp)
    (hp : p ≠ 0) (hq : q ≠ 0) (hx : p.x ≠ q.x)
    (h1 : l * (q.x - p.x) = q.y - p.y)
    (h2 : r.x = l * l - p.x - q.x)
    (h3 : r.y = l * (p.x - r.x) - p.y) :
    p + q = r := by
  have hd : q.x - p.x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hl : (q.y - p.y) / (q.x - p.x) = l := by
    rw [← h1]
    field_simp
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  rcases r with ⟨rx, ry⟩
  simp only [zero_def, add_def, ofCoords, coords, ShortWeierstrass.add, mk.injEq] at *
  have hp0 : ¬(px, py) = (0, 0) := by grind
  have hq0 : ¬(qx, qy) = (0, 0) := by grind
  rw [if_neg hp0, if_neg hq0, if_neg hx]
  refine ⟨?_, ?_⟩
  · rw [h2, hl]; ring
  · rw [h3, h2, hl]; ring

/-- Tangent doubling from a witnessed slope: if `l·(2·py) = 3·px² + a` and `r`'s
coordinates satisfy the tangent formulas at `l`, then `p + p = r`. -/
theorem double_of_witness {p r : Point Fp} (l : Fp)
    (hp : p ≠ 0) (hy : p.y ≠ 0)
    (h1 : l * (2 * p.y) = 3 * p.x ^ 2 + pallasA)
    (h2 : r.x = l * l - p.x - p.x)
    (h3 : r.y = l * (p.x - r.x) - p.y) :
    p + p = r := by
  have h2y : (2 : Fp) * p.y ≠ 0 :=
    mul_ne_zero two_ne_zero hy
  have hl : (3 * p.x ^ 2 + pallasA) / (2 * p.y) = l := by
    rw [div_eq_iff h2y, ← h1]
  have hyy : ¬(p.y + p.y = 0) := by
    intro h
    exact h2y (by rw [two_mul]; exact h)
  rcases p with ⟨px, py⟩
  rcases r with ⟨rx, ry⟩
  simp only [zero_def, add_def, ofCoords, coords, ShortWeierstrass.add, mk.injEq] at *
  have hp0 : ¬(px, py) = (0, 0) := by grind
  rw [if_neg hp0, if_neg hp0, if_pos trivial, if_neg hyy]
  refine ⟨?_, ?_⟩
  · rw [h2, hl]; ring
  · rw [h3, h2, hl]; ring

/-- Negation from checked coordinates: `r = −p` when `r.x = p.x` and `r.y = −p.y`. -/
theorem neg_of_witness {p r : Point Fp}
    (h1 : r.x = p.x) (h2 : r.y = -p.y) : -p = r := by
  rcases p with ⟨px, py⟩
  rcases r with ⟨rx, ry⟩
  simp only [neg_def, ofCoords, coords, ShortWeierstrass.neg, mk.injEq] at *
  exact ⟨h1.symm, h2.symm⟩

/-- On-curve closure through a checked addition: the result of `p + q = r` is on-curve
whenever both addends are and `r` is not the sentinel. -/
theorem onCurve_of_add_eq {p q r : Point Fp}
    (hp : p.OnCurve) (hq : q.OnCurve) (h : p + q = r) (hr : r ≠ 0) :
    r.OnCurve := by
  have hv : (p + q).Valid := valid_add (Or.inl hp) (Or.inl hq)
  rw [h] at hv
  rcases hv with hv | hv
  · exact hv
  · exact absurd hv hr

end Zcash.Circuits.Point
