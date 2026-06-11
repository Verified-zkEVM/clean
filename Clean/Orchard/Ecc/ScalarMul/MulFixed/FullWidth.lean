import Clean.Orchard.Ecc.ScalarMul.MulFixed

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`.
-/

namespace Orchard.Ecc.ScalarMul.MulFixed.FullWidth

def rangeCheck {K : Type} [One K] [Sub K] [Mul K]
    [OfNat K 2] [OfNat K 3] [OfNat K 4] [OfNat K 5] [OfNat K 6] [OfNat K 7]
    (row : CoordsRow K) : K :=
  row.window * (1 - row.window) * (2 - row.window) * (3 - row.window) *
    (4 - row.window) * (5 - row.window) * (6 - row.window) * (7 - row.window)

def IsWindow (window : Fp) : Prop :=
  window = 0 ∨ window = 1 ∨ window = 2 ∨ window = 3 ∨
    window = 4 ∨ window = 5 ∨ window = 6 ∨ window = 7

def Spec (params : CoordsParams Fp) (row : CoordsRow Fp) :
    Prop :=
  Coords.Spec params row ∧ IsWindow row.window

def main (params : CoordsParams Fp) (row : Var CoordsRow Fp) :
    Circuit Fp Unit := do
  Coords.circuit params row
  assertZero (rangeCheck row)

def circuit (params : CoordsParams Fp) :
    FormalAssertion Fp CoordsRow where
  name := "GATE Full-width fixed-base scalar mul"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, IsWindow, Coords.circuit, Coords.Spec,
      rangeCheck, xCheck, yCheck, onCurve, interpolatedX]
    constructor
    · simpa [sub_eq_add_neg] using h_holds.1
    · have hRange := h_holds.2
      rcases mul_eq_zero.mp hRange with hPrefix | h7
      · rcases mul_eq_zero.mp hPrefix with hPrefix | h6
        · rcases mul_eq_zero.mp hPrefix with hPrefix | h5
          · rcases mul_eq_zero.mp hPrefix with hPrefix | h4
            · rcases mul_eq_zero.mp hPrefix with hPrefix | h3
              · rcases mul_eq_zero.mp hPrefix with hPrefix | h2
                · rcases mul_eq_zero.mp hPrefix with h0 | h1
                  · exact Or.inl h0
                  · exact Or.inr (Or.inl (by linear_combination -h1))
                · exact Or.inr (Or.inr (Or.inl (by linear_combination -h2)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination -h3))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination -h4)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination -h5))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
            linear_combination -h6)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
          linear_combination -h7)))))))
  completeness := by
    circuit_proof_start [main, Spec, IsWindow, Coords.circuit, Coords.Spec,
      rangeCheck, xCheck, yCheck, onCurve, interpolatedX]
    constructor
    · simpa [sub_eq_add_neg] using h_spec.1
    · rcases h_spec.2 with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · simp [h3]
      · simp [h4]
      · simp [h5]
      · simp [h6]
      · simp [h7]

end Orchard.Ecc.ScalarMul.MulFixed.FullWidth
