import Clean.Orchard.Ecc.ScalarMul.MulFixed
import Clean.Orchard.Ecc.AddIncomplete
import Clean.Orchard.Ecc.Add

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`.

`Gate.circuit` is the custom gate enabled on every window row (`q_mul_fixed_full`): the
shared coordinates check plus the 3-bit range check of the witnessed window.

`circuit` is the source-level entry point `full_width.rs::Config::assign`
(`EccInstructions::mul_fixed`, gadget API `FixedPoint::mul`): it witnesses the scalar as
85 three-bit windows, initializes the accumulator with window 0, adds the window-table
points of windows 1..83 with incomplete addition, and adds the offset-corrected most
significant window with complete addition.
-/

namespace Orchard.Ecc.ScalarMul.MulFixed.FullWidth

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

namespace Gate

def rangeCheck {K : Type} [One K] [Sub K] [Mul K]
    [OfNat K 2] [OfNat K 3] [OfNat K 4] [OfNat K 5] [OfNat K 6] [OfNat K 7]
    (row : CoordsRow K) : K :=
  row.window * (1 - row.window) * (2 - row.window) * (3 - row.window) *
    (4 - row.window) * (5 - row.window) * (6 - row.window) * (7 - row.window)

def IsWindow (window : Fp) : Prop :=
  window = 0 ∨ window = 1 ∨ window = 2 ∨ window = 3 ∨
    window = 4 ∨ window = 5 ∨ window = 6 ∨ window = 7

theorem IsWindow.exists_lt {x : Fp} (h : IsWindow x) : ∃ k : ℕ, k < 8 ∧ x = (k : Fp) := by
  rcases h with h | h | h | h | h | h | h | h
  · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨1, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨2, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨3, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨4, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨5, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨6, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨7, by norm_num, by rw [h]; norm_num⟩

theorem isWindow_natCast {k : ℕ} (hk : k < 8) : IsWindow (k : Fp) := by
  unfold IsWindow
  interval_cases k <;> norm_num

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
      rangeCheck, xCheck, yCheck, onCurve, interpolatedX, interpolate]
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
      rangeCheck, xCheck, yCheck, onCurve, interpolatedX, interpolate]
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

end Gate

/-!
### Entry circuit

Value model: `windowVal s w` is window `w` of the base-`8` decomposition of the scalar,
`rowValue` is the honest-prover assignment of one window row, and `partialSum ks w` is
the integer scalar accumulated after processing windows `0..w` — each window `j`
contributes `(ks j + 2)·8^j`, matching `[(k_w + 2)·8^w]B` from `process_lower_bits`.
-/

def windowVal (s : Fq) (w : ℕ) : ℕ := s.val / 8 ^ w % 8

theorem windowVal_lt (s : Fq) (w : ℕ) : windowVal s w < 8 :=
  Nat.mod_lt _ (by norm_num)

/-- The honest-prover row of window `w`: the canonical window value, the coordinates of
its window-table point, and the table square root `u`. -/
def rowValue (B : FixedBase) (s : Fq) (w : ℕ) : CoordsRow Fp where
  window := (windowVal s w : Fp)
  xP := (windowPoint B.point w (windowVal s w)).x
  yP := (windowPoint B.point w (windowVal s w)).y
  u := B.u w (windowVal s w)

/-- `∑_{j ≤ w} (ks j + 2)·8^j`: the scalar accumulated after windows `0..w`. -/
def partialSum (ks : ℕ → ℕ) : ℕ → ℕ
  | 0 => ks 0 + 2
  | w + 1 => partialSum ks w + (ks (w + 1) + 2) * 8 ^ (w + 1)

theorem partialSum_pos (ks : ℕ → ℕ) (w : ℕ) : 0 < partialSum ks w := by
  cases w with
  | zero => simp [partialSum]
  | succ w => simp [partialSum]

theorem partialSum_lt (ks : ℕ → ℕ) :
    ∀ w, (∀ j ≤ w, ks j < 8) → partialSum ks w < 2 * 8 ^ (w + 1)
  | 0, h => by
    have := h 0 (by omega)
    simp only [partialSum]
    omega
  | w + 1, h => by
    have ih := partialSum_lt ks w fun j hj => h j (by omega)
    have hk := h (w + 1) (by omega)
    have hmul : (ks (w + 1) + 2) * 8 ^ (w + 1) ≤ 10 * 8 ^ (w + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h16 : 2 * 8 ^ (w + 1 + 1) = 16 * 8 ^ (w + 1) := by ring
    simp only [partialSum]
    omega

def main (B : FixedBase) (scalar : Var (Unconstrained Fq) Fp) :
    Circuit Fp (Var Point Fp) := do
  let row₀ ← witness fun env => rowValue B (scalar env) 0
  Gate.circuit (B.params 0) row₀
  let acc₀ : Var Point Fp := { x := row₀.xP, y := row₀.yP }
  let acc ← Circuit.foldlRange 83 acc₀ fun acc i => do
    let row ← witness fun env => rowValue B (scalar env) (i.val + 1)
    Gate.circuit (B.params (i.val + 1)) row
    AddIncomplete.circuit { p := { x := row.xP, y := row.yP }, q := acc }
  let row₈₄ ← witness fun env => rowValue B (scalar env) 84
  Gate.circuit (B.params 84) row₈₄
  Add.circuit { p := { x := row₈₄.xP, y := row₈₄.yP }, q := acc }

instance elaborated (B : FixedBase) :
    ElaboratedCircuit Fp (Unconstrained Fq) Point (main B) := by
  elaborate_circuit

def Spec (B : FixedBase) (_ : Unit) (output : Point Fp) (_ : ProverData Fp) : Prop :=
  ∃ s : Fq, output = B.mulValue s

def ProverSpec (B : FixedBase) (scalar : Fq) (output : Point Fp) (_ : ProverHint Fp) :
    Prop :=
  output = B.mulValue scalar

private theorem inv_lt_card {S j : ℕ} (hS : S < 2 * 8 ^ (j + 1)) (hj : j ≤ 83) :
    S < PALLAS_SCALAR_CARD := by
  have hpow : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 84 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 2 * 8 ^ 84 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

private theorem step_sum_lt {S t j : ℕ} (hS : S < 2 * 8 ^ (j + 1))
    (ht : t ≤ 9 * 8 ^ (j + 1)) (hj : j ≤ 82) : S + t < PALLAS_SCALAR_CARD := by
  have hpow : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 83 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 11 * 8 ^ 83 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

private theorem step_lt_next {S t j : ℕ} (hS : S < 2 * 8 ^ (j + 1))
    (ht : t ≤ 9 * 8 ^ (j + 1)) : t + S < 2 * 8 ^ (j + 1 + 1) := by
  have h16 : 2 * 8 ^ (j + 1 + 1) = 16 * 8 ^ (j + 1) := by ring
  omega

/-- The evaluated accumulator entering loop iteration `w` (after windows `0..w-1`,
relative to a circuit starting at offset `i₀`). -/
private def accPt (env : Environment Fp) (i₀ : ℕ) : ℕ → Point Fp
  | 0 => { x := env.get (i₀ + 1), y := env.get (i₀ + 1 + 1) }
  | j + 1 =>
    { x := Expression.eval env (varFromOffset Point (i₀ + 4 + j * 10 + 4 + 2 + 2)).x,
      y := Expression.eval env (varFromOffset Point (i₀ + 4 + j * 10 + 4 + 2 + 2)).y }

theorem soundness (B : FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main B) (fun _ _ => True) (Spec B) := by
  circuit_proof_start [main, Spec, Gate.circuit, Gate.Spec,
    AddIncomplete.circuit, AddIncomplete.Spec, AddIncomplete.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨⟨h_coords0, h_win0⟩, h_loop, ⟨h_coords84, h_win84⟩, h_add⟩ := h_holds
  simp only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul,
    Fin.foldl_const, Fin.val_last] at h_coords84 h_win84 h_add ⊢
  rw [show (if _ : 0 < 83 then (830 : ℕ) else 0) = 830 from rfl] at h_coords84 h_win84 h_add
  -- clean up the per-iteration loop hypothesis: the accumulator entering iteration `j`
  -- is `accPt env i₀ j`
  have h_loop' : ∀ (j : ℕ) (hj : j < 83),
      (Coords.Spec (B.params (j + 1))
          { window := env.get (i₀ + 4 + j * 10), xP := env.get (i₀ + 4 + j * 10 + 1),
            yP := env.get (i₀ + 4 + j * 10 + 1 + 1),
            u := env.get (i₀ + 4 + j * 10 + 1 + 1 + 1) } ∧
        Gate.IsWindow (env.get (i₀ + 4 + j * 10))) ∧
      (Pallas.OnCurve (env.get (i₀ + 4 + j * 10 + 1), env.get (i₀ + 4 + j * 10 + 1 + 1)) ∧
          Pallas.OnCurve (accPt env i₀ j).coords ∧
          ¬env.get (i₀ + 4 + j * 10 + 1) = (accPt env i₀ j).x →
        Pallas.OnCurve (accPt env i₀ (j + 1)).coords ∧
          (accPt env i₀ (j + 1)).coords =
            Pallas.add (env.get (i₀ + 4 + j * 10 + 1), env.get (i₀ + 4 + j * 10 + 1 + 1))
              (accPt env i₀ j).coords) := by
    intro j hj
    have h := h_loop ⟨j, hj⟩
    simp only [List.sum_cons, List.sum_nil, Nat.reduceAdd,
      Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, Fin.val_mk, circuit_norm] at h
    rcases j with _ | j'
    · simp only [Fin.foldl_zero] at h
      exact h
    · simp only [Fin.foldl_const, Fin.val_last] at h
      exact h
  -- inductive invariant: the accumulator after windows `0..w` is a small positive
  -- multiple of the base
  have h_inv : ∀ (w : ℕ), w ≤ 83 →
      ∃ S : ℕ, 0 < S ∧ S < 2 * 8 ^ (w + 1) ∧
        accPt env i₀ w = { x := (S • B.point).x, y := (S • B.point).y } := by
    intro w hw
    induction w with
    | zero =>
      obtain ⟨k₀, hk₀, hwin⟩ := Gate.IsWindow.exists_lt h_win0
      obtain ⟨hpx, hpy⟩ := B.coords_eq_windowPoint (by norm_num) hk₀ hwin h_coords0
      replace hpx : env.get (i₀ + 1) = (windowPoint B.point 0 k₀).x := hpx
      replace hpy : env.get (i₀ + 1 + 1) = (windowPoint B.point 0 k₀).y := hpy
      refine ⟨(windowScalar 0 k₀).val, ?_, ?_, ?_⟩
      · rw [windowScalar_val (by norm_num) hk₀]
        simp only [pow_zero, mul_one]
        omega
      · rw [windowScalar_val (by norm_num) hk₀]
        have h16 : 2 * 8 ^ (0 + 1) = 16 := by norm_num
        simp only [pow_zero, mul_one]
        omega
      · show ({ x := env.get (i₀ + 1), y := env.get (i₀ + 1 + 1) } : Point Fp) = _
        rw [hpx, hpy]
        rfl
    | succ j ih =>
      obtain ⟨S, hS_pos, hS_lt, hacc⟩ := ih (by omega)
      have hj : j < 83 := by omega
      obtain ⟨⟨h_coordsRow, h_winRow⟩, h_inc⟩ := h_loop' j hj
      obtain ⟨k, hk, hwin⟩ := Gate.IsWindow.exists_lt h_winRow
      obtain ⟨hpx, hpy⟩ :=
        B.coords_eq_windowPoint (show j + 1 < 85 by omega) hk hwin h_coordsRow
      replace hpx : env.get (i₀ + 4 + j * 10 + 1) = (windowPoint B.point (j + 1) k).x := hpx
      replace hpy :
        env.get (i₀ + 4 + j * 10 + 1 + 1) = (windowPoint B.point (j + 1) k).y := hpy
      set t := (windowScalar (j + 1) k).val with ht_def
      have hval : t = (k + 2) * 8 ^ (j + 1) := windowScalar_val (by omega) hk
      have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
      have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by omega)
      have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by omega)
      have hS_card : S < PALLAS_SCALAR_CARD := inv_lt_card hS_lt (by omega)
      have hsum_card : S + t < PALLAS_SCALAR_CARD := step_sum_lt hS_lt ht_upper (by omega)
      have hwp : windowPoint B.point (j + 1) k = t • B.point := rfl
      rw [hwp] at hpx hpy
      -- discharge the incomplete-addition assumptions
      have h_spec := h_inc ⟨by
          rw [hpx, hpy]
          exact SWPoint.onCurve_of_ne_zero (B.nsmul_ne_zero (by omega) (by omega)),
        by
          rw [hacc]
          show Pallas.OnCurve ((S • B.point).x, (S • B.point).y)
          exact B.nsmul_onCurve hS_pos hS_card,
        by
          rw [hpx, hacc]
          show (t • B.point).x ≠ (S • B.point).x
          exact B.nsmul_x_ne hS_pos (by omega) hsum_card⟩
      refine ⟨t + S, by omega, step_lt_next hS_lt ht_upper, ?_⟩
      apply Point.ext_coords
      rw [h_spec.2, hpx, hpy, hacc]
      show Pallas.add ((t • B.point).x, (t • B.point).y) ((S • B.point).x, (S • B.point).y)
        = (((t + S) • B.point).x, ((t + S) • B.point).y)
      rw [Pallas.add_coords, ← add_nsmul]
  -- final complete addition of the most significant window
  obtain ⟨S, hS_pos, hS_lt, hacc⟩ := h_inv 83 (by omega)
  replace hacc :
      ({ x := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
         y := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } :
        Point Fp) = { x := (S • B.point).x, y := (S • B.point).y } := hacc
  obtain ⟨k, hk, hwin⟩ := Gate.IsWindow.exists_lt h_win84
  obtain ⟨hpx, hpy⟩ :=
    B.coords_eq_windowPoint (show (84 : ℕ) < 85 by omega) hk hwin h_coords84
  replace hpx : env.get (i₀ + 4 + 830 + 1) = (windowPoint B.point 84 k).x := hpx
  replace hpy : env.get (i₀ + 4 + 830 + 1 + 1) = (windowPoint B.point 84 k).y := hpy
  have hS_card : S < PALLAS_SCALAR_CARD := inv_lt_card hS_lt (by omega)
  have h_spec := h_add ⟨by
      show Pallas.Valid (env.get (i₀ + 4 + 830 + 1), env.get (i₀ + 4 + 830 + 1 + 1))
      rw [hpx, hpy]
      exact Or.inl (SWPoint.onCurve_of_ne_zero (B.windowPoint_ne_zero hk)),
    by
      show Pallas.Valid
        (({ x := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
            y := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } :
          Point Fp)).coords
      rw [hacc]
      exact Or.inl (B.nsmul_onCurve hS_pos hS_card)⟩
  refine ⟨windowScalar 84 k + (S : Fq), ?_⟩
  apply Point.ext_coords
  rw [h_spec.2]
  show Pallas.add
      (({ x := env.get (i₀ + 4 + 830 + 1), y := env.get (i₀ + 4 + 830 + 1 + 1) } :
        Point Fp)).coords
      (({ x := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
          y := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } :
        Point Fp)).coords = _
  rw [show (({ x := env.get (i₀ + 4 + 830 + 1), y := env.get (i₀ + 4 + 830 + 1 + 1) } :
      Point Fp)).coords = (env.get (i₀ + 4 + 830 + 1), env.get (i₀ + 4 + 830 + 1 + 1))
    from rfl, hpx, hpy, hacc]
  show Pallas.add ((windowPoint B.point 84 k).x, (windowPoint B.point 84 k).y)
      ((S • B.point).x, (S • B.point).y) = (B.mulValue _).coords
  rw [Pallas.add_coords]
  show (((windowScalar 84 k).val • B.point + S • B.point).x,
    ((windowScalar 84 k).val • B.point + S • B.point).y) = _
  have hpt : (windowScalar 84 k).val • B.point + S • B.point
      = (windowScalar 84 k + (S : Fq)).val • B.point := by
    rw [← add_nsmul]
    exact (B.add_natCast_val_nsmul _ _).symm
  rw [hpt, B.mulValue_coords]

theorem completeness (B : FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main B) (fun _ _ _ => True)
      (ProverSpec B) := by
  sorry

def circuit (B : FixedBase) : GeneralFormalCircuit.WithHint Fp (Unconstrained Fq) Point where
  main := main B
  Spec := Spec B
  ProverSpec := ProverSpec B
  soundness := soundness B
  completeness := completeness B

end Orchard.Ecc.ScalarMul.MulFixed.FullWidth
