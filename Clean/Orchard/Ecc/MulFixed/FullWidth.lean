import Clean.Orchard.Ecc.MulFixed
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

namespace Orchard.Ecc.MulFixed.FullWidth

open CompElliptic.Curves.Pasta CompElliptic.CurveForms
open ShortWeierstrass (SWPoint)
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

def windowVal (s : ℕ) (w : ℕ) : ℕ := s / 8 ^ w % 8

theorem windowVal_lt (s : ℕ) (w : ℕ) : windowVal s w < 8 :=
  Nat.mod_lt _ (by norm_num)

/-- The honest-prover row of window `w`: the canonical window value, the coordinates of
its window-table point, and the table square root `u`. -/
def rowValue (B : FixedBase) (s : ℕ) (w : ℕ) : CoordsRow Fp where
  window := (windowVal s w : Fp)
  xP := (windowPoint B.point w (windowVal s w)).x
  yP := (windowPoint B.point w (windowVal s w)).y
  u := B.u w (windowVal s w)

theorem offsetAcc_eq : offsetAcc = ∑ j ∈ Finset.range 84, 2 * 8 ^ j := by
  unfold offsetAcc
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_mul]
  norm_num [mul_comm]

/-- The canonical window decomposition recombines to the scalar: the `+2` offsets of the
lower 84 windows cancel against `offset_acc` in the most significant window. -/
theorem windowScalar_partialSum (s : ℕ) (hs : s < PALLAS_SCALAR_CARD) :
    windowScalar 84 (windowVal s 84) + (partialSum (windowVal s) 83 : Fq) = (s : Fq) := by
  have hsplit : partialSum (windowVal s) 83
      = (∑ j ∈ Finset.range 84, windowVal s j * 8 ^ j) + offsetAcc := by
    rw [partialSum_eq_sum, offsetAcc_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : s < 8 ^ 85 :=
    lt_of_lt_of_le hs (by norm_num [PALLAS_SCALAR_CARD])
  have hsum : ∑ j ∈ Finset.range 85, windowVal s j * 8 ^ j = s := by
    have h := sum_base8 s 85
    rwa [Nat.mod_eq_of_lt hval] at h
  have hcast : ((∑ j ∈ Finset.range 85, windowVal s j * 8 ^ j : ℕ) : Fq) = (s : Fq) := by
    rw [hsum]
  rw [Finset.sum_range_succ] at hcast
  push_cast at hcast
  unfold windowScalar
  rw [if_pos rfl, hsplit]
  push_cast
  linear_combination hcast

/-- The honest-prover row of window `w` satisfies the full-width gate. -/
theorem rowValue_spec (B : FixedBase) (s : ℕ) {w : ℕ} (hw : w < 85) :
    Gate.Spec (B.params w) (rowValue B s w) := by
  have hk := windowVal_lt s w
  refine ⟨⟨?_, ?_, ?_⟩, Gate.isWindow_natCast hk⟩
  · exact (B.interpolate_eq w hw _ hk).symm
  · exact B.u_mul_u w hw _ hk
  · have h := B.windowPoint_onCurve (w := w) (k := windowVal s w) hk
    dsimp [Point.OnCurve] at h
    show (windowPoint B.point w (windowVal s w)).y * (windowPoint B.point w (windowVal s w)).y
      = (windowPoint B.point w (windowVal s w)).x * (windowPoint B.point w (windowVal s w)).x
        * (windowPoint B.point w (windowVal s w)).x + 5
    linear_combination h

/-- The witness program of one window row: read the scalar hint, take window `w` of its
base-8 decomposition (`k = s / 8^w % 8`, matching `windowVal` definitionally), and read
the three window-table columns at the computed index `k`. -/
def rowProgram (B : FixedBase) (scalar : Var UnconstrainedNat Fp) (w : ℕ) :
    Witgen.M Fp (CoordsRow (Witgen.FExpr Fp)) := do
  let xs := Vector.ofFn fun k : Fin 8 => (windowPoint B.point w k.val).x
  let ys := Vector.ofFn fun k : Fin 8 => (windowPoint B.point w k.val).y
  let us := Vector.ofFn fun k : Fin 8 => B.u w k.val
  let s ← scalar
  let k := s / (8 ^ w : ℕ) % 8
  return CoordsRow.mk k.toField xs[k] ys[k] us[k]

def main (B : FixedBase) (scalar : Var UnconstrainedNat Fp) :
    Circuit Fp (Var Point Fp) := do
  let row₀ ← witnessProgram (rowProgram B scalar 0)
  Gate.circuit (B.params 0) row₀
  let acc₀ : Var Point Fp := { x := row₀.xP, y := row₀.yP }
  let acc ← Circuit.foldlRange 83 acc₀ fun acc i => do
    let row ← witnessProgram (rowProgram B scalar (i.val + 1))
    Gate.circuit (B.params (i.val + 1)) row
    AddIncomplete.circuit { p := { x := row.xP, y := row.yP }, q := acc }
  let row₈₄ ← witnessProgram (rowProgram B scalar 84)
  Gate.circuit (B.params 84) row₈₄
  Add.circuit { p := { x := row₈₄.xP, y := row₈₄.yP }, q := acc }

-- TODO(4.30 bump): whnf recursion depth grew on the 85-window unrolled circuit
set_option maxRecDepth 4096 in
instance elaborated (B : FixedBase) :
    ElaboratedCircuit Fp UnconstrainedNat Point (main B) := by
  elaborate_circuit_with {
    localLength _ := 849
    output _ offset := varFromOffset Point (offset + 842)
  }

def Spec (B : FixedBase) (_ : Unit) (output : Point Fp) (_ : ProverData Fp) : Prop :=
  ∃ s : Fq, output = s • B

/-- The prover-side scalar hint is the canonical natural representative of an `Fq`
scalar (`ZMod.val` of the scalar the prover multiplies by). -/
def ProverAssumptions (scalar : ℕ) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  scalar < PALLAS_SCALAR_CARD

def ProverSpec (B : FixedBase) (scalar : ℕ) (output : Point Fp) (_ : ProverHint Fp) :
    Prop :=
  output = (scalar : Fq) • B

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

private def winPt (env : Environment Fp) (i₀ j : ℕ) : Point Fp :=
  { x := env.get (i₀ + 4 + j * 10 + 1),
    y := env.get (i₀ + 4 + j * 10 + 1 + 1) }

theorem soundness (B : FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main B) (fun _ _ => True) (Spec B) := by
  circuit_proof_start [main, Spec, Gate.circuit, Gate.Spec,
    AddIncomplete.circuit, AddIncomplete.Spec, AddIncomplete.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨⟨h_coords0, h_win0⟩, h_loop, ⟨h_coords84, h_win84⟩, h_add⟩ := h_holds
  simp +instances only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul,
    Fin.foldl_const, Fin.val_last, circuit_norm,
    ] at h_coords84 h_win84 h_add ⊢
  rw [show (if _ : 0 < 83 then (830 : ℕ) else 0) = 830 from rfl] at h_coords84 h_win84 h_add
  -- clean up the per-iteration loop hypothesis: the accumulator entering iteration `j`
  -- is `accPt env i₀ j`
  have h_loop' : ∀ (j : ℕ) (hj : j < 83),
      (Coords.Spec (B.params (j + 1))
          { window := env.get (i₀ + 4 + j * 10), xP := env.get (i₀ + 4 + j * 10 + 1),
            yP := env.get (i₀ + 4 + j * 10 + 1 + 1),
            u := env.get (i₀ + 4 + j * 10 + 1 + 1 + 1) } ∧
        Gate.IsWindow (env.get (i₀ + 4 + j * 10))) ∧
      ((winPt env i₀ j).OnCurve ∧
          (accPt env i₀ j).OnCurve ∧
          ¬env.get (i₀ + 4 + j * 10 + 1) = (accPt env i₀ j).x →
        (accPt env i₀ (j + 1)).OnCurve ∧
          accPt env i₀ (j + 1) =
            winPt env i₀ j + accPt env i₀ j) := by
    intro j hj
    have h := h_loop ⟨j, hj⟩
    simp +instances only [List.sum_cons, List.sum_nil, Nat.reduceAdd,
      Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, Fin.val_mk, circuit_norm,
      ] at h
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
      have h_inc_assumptions :
          (winPt env i₀ j).OnCurve ∧ (accPt env i₀ j).OnCurve ∧
            ¬env.get (i₀ + 4 + j * 10 + 1) = (accPt env i₀ j).x := by
        refine ⟨?_, ?_, ?_⟩
        · simp only [winPt]
          rw [hpx, hpy]
          exact B.nsmul_onCurve (by omega) (by omega)
        · rw [hacc]
          exact B.nsmul_onCurve hS_pos hS_card
        · rw [hpx, hacc]
          show (t • B.point).x ≠ (S • B.point).x
          exact B.nsmul_x_ne hS_pos (by omega) hsum_card
      have h_spec := h_inc h_inc_assumptions
      refine ⟨t + S, by omega, step_lt_next hS_lt ht_upper, ?_⟩
      apply Point.ext_coords
      rw [h_spec.2]
      simp only [winPt, Point.coords]
      rw [hpx, hpy, hacc]
      show ShortWeierstrass.add pallasA ((t • B.point).x, (t • B.point).y) ((S • B.point).x, (S • B.point).y)
        = (((t + S) • B.point).x, ((t + S) • B.point).y)
      exact B.nsmul_add_coords rfl
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
  have hcurveP :
      ({ x := env.get (i₀ + 4 + 830 + 1),
         y := env.get (i₀ + 4 + 830 + 1 + 1) } : Point Fp).OnCurve := by
    obtain ⟨_, _, hcurve⟩ := h_coords84
    unfold Point.OnCurve
    linear_combination hcurve
  have hValidP :
      ({ x := env.get (i₀ + 4 + 830 + 1),
         y := env.get (i₀ + 4 + 830 + 1 + 1) } : Point Fp).Valid := by
    exact Or.inl hcurveP
  have hValidAcc :
      ({ x := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
         y := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } :
        Point Fp).Valid := by
    rw [hacc]
    apply Or.inl
    exact B.nsmul_onCurve hS_pos hS_card
  have h_spec := h_add ⟨hValidP, hValidAcc⟩
  refine ⟨windowScalar 84 k + (S : Fq), ?_⟩
  apply Point.ext_coords
  rw [h_spec.2]
  simp only [Point.coords]
  show ShortWeierstrass.add pallasA
      (({ x := env.get (i₀ + 4 + 830 + 1), y := env.get (i₀ + 4 + 830 + 1 + 1) } :
        Point Fp)).coords
      (({ x := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
          y := Expression.eval env (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } :
        Point Fp)).coords = _
  rw [show (({ x := env.get (i₀ + 4 + 830 + 1), y := env.get (i₀ + 4 + 830 + 1 + 1) } :
      Point Fp)).coords = (env.get (i₀ + 4 + 830 + 1), env.get (i₀ + 4 + 830 + 1 + 1))
    from rfl, hpx, hpy, hacc]
  show ShortWeierstrass.add pallasA ((windowPoint B.point 84 k).x, (windowPoint B.point 84 k).y)
      ((S • B.point).x, (S • B.point).y) = ((windowScalar 84 k + (S : Fq)) • B).coords
  have hpt : (windowScalar 84 k).val • B.point + S • B.point
      = (windowScalar 84 k + (S : Fq)).val • B.point := by
    rw [Point.nsmul_add_nsmul B.onCurve]
    exact (B.add_natCast_val_nsmul _ _).symm
  exact FixedBase.add_coords_eq hpt

/-- Extract the four field equations from a witnessed `CoordsRow`. Extracting via this
lemma instead of projecting the struct equation at a target component type keeps
elaboration cheap: the `congrArg` projections reduce on the literal side, whereas
unification against a concrete `rowValue` makes `whnf` unfold
`windowScalar`/`offsetAcc` values. -/
private theorem env_get_row {env : ProverEnvironment Fp} {n : ℕ} {r : CoordsRow Fp}
    (h : ({ window := env.get n, xP := env.get (n + 1), yP := env.get (n + 1 + 1),
            u := env.get (n + 1 + 1 + 1) } : CoordsRow Fp) = r) :
    env.get n = r.window ∧ env.get (n + 1) = r.xP ∧
      env.get (n + 1 + 1) = r.yP ∧ env.get (n + 1 + 1 + 1) = r.u :=
  ⟨congrArg CoordsRow.window h, congrArg CoordsRow.xP h,
    congrArg CoordsRow.yP h, congrArg CoordsRow.u h⟩

/-- `rfl` bridges between `rowValue` fields and `windowPoint` coordinates, stated at
symbolic `w` where they are cheap to check: with `w` opaque, `windowScalar`'s `w = 84`
test stays stuck, so neither the elaborator nor the kernel descends into `offsetAcc`
values. Rewriting with these (instead of bridging at `w := 84` by defeq) keeps the
window-84 steps of the completeness proof from blowing up. -/
private theorem rowValue_xP (B : FixedBase) (s : ℕ) (w : ℕ) :
    (rowValue B s w).xP = (windowPoint B.point w (windowVal s w)).x := rfl

private theorem rowValue_yP (B : FixedBase) (s : ℕ) (w : ℕ) :
    (rowValue B s w).yP = (windowPoint B.point w (windowVal s w)).y := rfl

/-- The evaluated row program is the honest `rowValue`, stated at symbolic `w` and an
opaque scalar value `s`, where every reduction is cheap (nothing descends into
`windowScalar 84`/`offsetAcc` values). The LHS is the `circuit_norm` normal form of the
witness-IR completeness hypothesis: `FiniteField.fromNat` from `NExpr.toField`, and one
range-guarded window-table read per column from the `.listGet` evaluation (the
`Vector.ofFn` tables are already indexed away by `Vector.getElem_ofFn`). -/
private theorem rowProgram_value (B : FixedBase) (s w : ℕ) :
    CoordsRow.mk (F := Fp) (FiniteField.fromNat (s / 8 ^ w % 8))
      (if _ : s / 8 ^ w % 8 < 8 then (windowPoint B.point w (s / 8 ^ w % 8)).x else 0)
      (if _ : s / 8 ^ w % 8 < 8 then (windowPoint B.point w (s / 8 ^ w % 8)).y else 0)
      (if _ : s / 8 ^ w % 8 < 8 then B.u w (s / 8 ^ w % 8) else 0)
    = rowValue B s w := by
  have h8 : s / 8 ^ w % 8 < 8 := Nat.mod_lt _ (by norm_num)
  simp only [dif_pos h8]
  rfl

/-- Rebuild a `CoordsRow` from field equations. The eta-expansion `rfl` happens at an
opaque `r`, which the kernel checks cheaply; closing the same goal at
`r := rowValue B s 84` by `rfl` makes the kernel recurse into `offsetAcc` values. -/
private theorem coordsRow_eq {r : CoordsRow Fp} {a b c d : Fp}
    (hw : a = r.window) (hx : b = r.xP) (hy : c = r.yP) (hu : d = r.u) :
    r = { window := a, xP := b, yP := c, u := d } := by
  subst hw hx hy hu
  rfl

-- TODO(4.30 bump): legacy defeq so `circuit_norm`'s witness-IR completeness lemmas
-- (`extendsVector_toIRLiteral` etc.) keep matching through stuck `size`/`localLength`
-- indices (lean4#12179).
set_option backward.isDefEq.respectTransparency false in
theorem completeness (B : FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main B) ProverAssumptions
      (ProverSpec B) := by
  circuit_proof_start [main, rowProgram, ProverSpec, Gate.circuit, Gate.Spec,
    AddIncomplete.circuit, AddIncomplete.Spec, AddIncomplete.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_w0, h_loop_env, h_w84, h_add_env⟩ := h_env
  simp +instances only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul,
    Fin.foldl_const, Fin.val_last, circuit_norm,
    ] at h_add_env ⊢
  rw [show (if _ : 0 < 83 then (830 : ℕ) else 0) = 830 from rfl] at h_add_env ⊢
  -- witnessed row values
  obtain ⟨h0w, h0x, h0y, h0u⟩ := env_get_row (h_w0.trans (rowProgram_value B input 0))
  have hrow : ∀ (j : ℕ) (hj : j < 83),
      env.get (i₀ + 4 + j * 10) = (rowValue B input (j + 1)).window ∧
        env.get (i₀ + 4 + j * 10 + 1) = (rowValue B input (j + 1)).xP ∧
        env.get (i₀ + 4 + j * 10 + 1 + 1) = (rowValue B input (j + 1)).yP ∧
        env.get (i₀ + 4 + j * 10 + 1 + 1 + 1) = (rowValue B input (j + 1)).u :=
    fun j hj => env_get_row ((h_loop_env ⟨j, hj⟩).1.trans (rowProgram_value B input (j + 1)))
  have hrowW := fun j hj => (hrow j hj).1
  have hrowX := fun j hj => (hrow j hj).2.1
  have hrowY := fun j hj => (hrow j hj).2.2.1
  have hrowU := fun j hj => (hrow j hj).2.2.2
  have h84 : env.get (830 + (i₀ + 4)) = (rowValue B input 84).window ∧
      env.get (830 + (i₀ + 4) + 1) = (rowValue B input 84).xP ∧
        env.get (830 + (i₀ + 4) + 1 + 1) = (rowValue B input 84).yP ∧
        env.get (830 + (i₀ + 4) + 1 + 1 + 1) = (rowValue B input 84).u :=
    env_get_row (h_w84.trans (rowProgram_value B input 84))
  rw [Nat.add_comm 830 (i₀ + 4)] at h84
  obtain ⟨h84w, h84x, h84y, h84u⟩ := h84
  have hrow84 : rowValue B input 84
      = { window := env.get (i₀ + 4 + 830), xP := env.get (i₀ + 4 + 830 + 1),
          yP := env.get (i₀ + 4 + 830 + 1 + 1), u := env.get (i₀ + 4 + 830 + 1 + 1 + 1) } :=
    coordsRow_eq h84w h84x h84y h84u
  -- per-iteration incomplete addition, with the accumulator cleaned up
  have h_step' : ∀ (j : ℕ) (hj : j < 83),
      (winPt env.toEnvironment i₀ j).OnCurve ∧
        (accPt env.toEnvironment i₀ j).OnCurve ∧
        ¬env.get (i₀ + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x →
      (accPt env.toEnvironment i₀ (j + 1)).OnCurve ∧
        accPt env.toEnvironment i₀ (j + 1) =
          winPt env.toEnvironment i₀ j + accPt env.toEnvironment i₀ j := by
    intro j hj
    have h := (h_loop_env ⟨j, hj⟩).2
    simp +instances only [List.sum_cons, List.sum_nil, Nat.reduceAdd,
      Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, Fin.val_mk, circuit_norm,
      ] at h
    rcases j with _ | j'
    · simp only [Fin.foldl_zero] at h
      exact h
    · simp only [Fin.foldl_const, Fin.val_last] at h
      exact h
  -- the honest accumulator after windows `0..w` is `[partialSum]B`
  have h_inv : ∀ (w : ℕ), w ≤ 83 →
      accPt env.toEnvironment i₀ w =
        { x := (partialSum (windowVal input) w • B.point).x,
          y := (partialSum (windowVal input) w • B.point).y } := by
    intro w hw
    induction w with
    | zero =>
      have hval0 : (windowScalar 0 (windowVal input 0)).val = partialSum (windowVal input) 0 := by
        rw [windowScalar_val (by norm_num) (windowVal_lt input 0)]
        show (windowVal input 0 + 2) * 8 ^ 0 = windowVal input 0 + 2
        simp
      show ({ x := env.get (i₀ + 1), y := env.get (i₀ + 1 + 1) } : Point Fp) = _
      rw [h0x, h0y]
      show ({ x := (windowPoint B.point 0 (windowVal input 0)).x,
              y := (windowPoint B.point 0 (windowVal input 0)).y } : Point Fp) = _
      unfold windowPoint
      rw [hval0]
    | succ j ih =>
      have hj : j < 83 := by omega
      have hacc := ih (by omega)
      set t := (windowScalar (j + 1) (windowVal input (j + 1))).val with ht_def
      have hval : t = (windowVal input (j + 1) + 2) * 8 ^ (j + 1) :=
        windowScalar_val (by omega) (windowVal_lt input (j + 1))
      have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
      have hS_lt := partialSum_lt (windowVal input) j fun _ _ => windowVal_lt input _
      have hS_pos := partialSum_pos (windowVal input) j
      have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by omega)
      have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
        rw [hval]
        exact Nat.mul_le_mul_right _ (by have := windowVal_lt input (j + 1); omega)
      have hS_card := inv_lt_card hS_lt (by omega)
      have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
      have h_step_assumptions :
          (winPt env.toEnvironment i₀ j).OnCurve ∧
            (accPt env.toEnvironment i₀ j).OnCurve ∧
            ¬env.get (i₀ + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x := by
        refine ⟨?_, ?_, ?_⟩
        · simp only [winPt]
          rw [hrowX j hj, hrowY j hj]
          exact B.windowPoint_onCurve (windowVal_lt input (j + 1))
        · rw [hacc]
          exact B.nsmul_onCurve hS_pos hS_card
        · rw [hrowX j hj, hacc]
          show (t • B.point).x ≠ (partialSum (windowVal input) j • B.point).x
          exact B.nsmul_x_ne hS_pos (by omega) hsum_card
      have h_spec := h_step' j hj h_step_assumptions
      apply Point.ext_coords
      rw [h_spec.2]
      simp only [winPt, Point.coords]
      rw [hrowX j hj, hrowY j hj, hacc]
      show ShortWeierstrass.add pallasA ((t • B.point).x, (t • B.point).y)
          ((partialSum (windowVal input) j • B.point).x,
            (partialSum (windowVal input) j • B.point).y)
        = ((partialSum (windowVal input) (j + 1) • B.point).x,
            (partialSum (windowVal input) (j + 1) • B.point).y)
      exact B.nsmul_add_coords
        (show t + partialSum (windowVal input) j = partialSum (windowVal input) (j + 1) by
          rw [partialSum, hval]; omega)
  -- per-iteration constraint obligations
  have hB : ∀ (j : ℕ) (hj : j < 83),
      (Coords.Spec (B.params (j + 1))
          { window := env.get (i₀ + 4 + j * 10), xP := env.get (i₀ + 4 + j * 10 + 1),
            yP := env.get (i₀ + 4 + j * 10 + 1 + 1),
            u := env.get (i₀ + 4 + j * 10 + 1 + 1 + 1) } ∧
        Gate.IsWindow (env.get (i₀ + 4 + j * 10))) ∧
      (winPt env.toEnvironment i₀ j).OnCurve ∧
      (accPt env.toEnvironment i₀ j).OnCurve ∧
      ¬env.get (i₀ + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x := by
    intro j hj
    have hacc := h_inv j (by omega)
    have hS_lt := partialSum_lt (windowVal input) j fun _ _ => windowVal_lt input _
    have hS_pos := partialSum_pos (windowVal input) j
    have hS_card := inv_lt_card hS_lt (by omega)
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hrowW j hj, hrowX j hj, hrowY j hj, hrowU j hj]
      exact (rowValue_spec B input (by omega)).1
    · rw [hrowW j hj]
      exact (rowValue_spec B input (by omega)).2
    · simp only [winPt]
      rw [hrowX j hj, hrowY j hj]
      exact B.windowPoint_onCurve (windowVal_lt input (j + 1))
    · rw [hacc]
      exact B.nsmul_onCurve hS_pos hS_card
    · rw [hrowX j hj, hacc]
      have hval : (windowScalar (j + 1) (windowVal input (j + 1))).val
          = (windowVal input (j + 1) + 2) * 8 ^ (j + 1) :=
        windowScalar_val (by omega) (windowVal_lt input (j + 1))
      have ht_upper : (windowScalar (j + 1) (windowVal input (j + 1))).val
          ≤ 9 * 8 ^ (j + 1) := by
        rw [hval]
        exact Nat.mul_le_mul_right _ (by have := windowVal_lt input (j + 1); omega)
      have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
      show ((windowScalar (j + 1) (windowVal input (j + 1))).val • B.point).x
        ≠ (partialSum (windowVal input) j • B.point).x
      have ht_lower : 2 * 8 ^ (j + 1)
          ≤ (windowScalar (j + 1) (windowVal input (j + 1))).val := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by omega)
      exact B.nsmul_x_ne hS_pos (by omega) hsum_card
  -- shared facts for the final complete addition
  -- Keep the accumulated scalar opaque from here on: kernel defeq checks must get stuck
  -- on `S83 • B.point` instead of unfolding the 83-step `partialSum` recursion
  -- (soundness gets this for free since its scalar is an existential witness).
  obtain ⟨S83, hS83_def⟩ : ∃ S, partialSum (windowVal input) 83 = S := ⟨_, rfl⟩
  have hS83_lt : S83 < 2 * 8 ^ (83 + 1) := by
    rw [← hS83_def]
    exact partialSum_lt (windowVal input) 83 fun _ _ => windowVal_lt input _
  have hS83_pos : 0 < S83 := by
    rw [← hS83_def]
    exact partialSum_pos (windowVal input) 83
  have hS83_card := inv_lt_card hS83_lt (by omega)
  have hacc83 :
      ({ x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
         y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } : Point Fp)
      = { x := (S83 • B.point).x, y := (S83 • B.point).y } := by
    rw [← hS83_def]
    exact h_inv 83 (by omega)
  obtain ⟨R84, hR84_def⟩ : ∃ R : CoordsRow Fp, rowValue B input 84 = R := ⟨_, rfl⟩
  have h84xR : env.get (i₀ + 4 + 830 + 1) = R84.xP := by
    rw [← hR84_def]
    exact h84x
  have h84yR : env.get (i₀ + 4 + 830 + 1 + 1) = R84.yP := by
    rw [← hR84_def]
    exact h84y
  have hcurveR : R84.yP * R84.yP = R84.xP * R84.xP * R84.xP + 5 := by
    rw [← hR84_def]
    exact (rowValue_spec B input (w := 84) (by norm_num)).1.2.2
  have hValidP :
      ({ x := env.get (i₀ + 4 + 830 + 1),
         y := env.get (i₀ + 4 + 830 + 1 + 1) } : Point Fp).Valid := by
    apply Or.inl
    unfold Point.OnCurve
    rw [h84xR, h84yR]
    linear_combination hcurveR
  have hValidAcc :
      ({ x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
          y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } : Point Fp).Valid := by
    rw [hacc83]
    apply Or.inl
    exact B.nsmul_onCurve hS83_pos hS83_card
  refine ⟨⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, hValidP, hValidAcc⟩, ?_⟩
  · rw [h0w, h0x, h0y, h0u]
    exact (rowValue_spec B input (by norm_num)).1
  · rw [h0w]
    exact (rowValue_spec B input (by norm_num)).2
  · intro i
    obtain ⟨j, hj⟩ := i
    simp +instances only [Nat.reduceAdd, Circuit.FoldlM.foldlAcc, Vector.getElem_finRange,
      Fin.val_mk, circuit_norm]
    rcases j with _ | j'
    · simp only [Fin.foldl_zero]
      exact hB 0 hj
    · simp only [Fin.foldl_const, Fin.val_last]
      exact hB (j' + 1) hj
  · rw [← hrow84]
    exact (rowValue_spec B input (by norm_num)).1
  · rw [h84w]
    exact (rowValue_spec B input (by norm_num)).2
  -- the prover spec: the output is `[input]B`
  · have h_final := h_add_env ⟨hValidP, hValidAcc⟩
    apply Point.ext_coords
    rw [h_final.2]
    simp only [Point.coords]
    show ShortWeierstrass.add pallasA
        (({ x := env.get (i₀ + 4 + 830 + 1), y := env.get (i₀ + 4 + 830 + 1 + 1) } :
          Point Fp)).coords
        (({ x := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).x,
            y := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 4 + 820 + 4 + 2 + 2)).y } : Point Fp)).coords = _
    rw [show (({ x := env.get (i₀ + 4 + 830 + 1), y := env.get (i₀ + 4 + 830 + 1 + 1) } :
        Point Fp)).coords = (env.get (i₀ + 4 + 830 + 1), env.get (i₀ + 4 + 830 + 1 + 1))
      from rfl, h84x, h84y, rowValue_xP, rowValue_yP, hacc83]
    show ShortWeierstrass.add pallasA
        ((windowPoint B.point 84 (windowVal input 84)).x,
          (windowPoint B.point 84 (windowVal input 84)).y)
        ((S83 • B.point).x, (S83 • B.point).y)
      = ((input : Fq) • B).coords
    have hpt : (windowScalar 84 (windowVal input 84)).val • B.point + S83 • B.point
        = (input : Fq).val • B.point := by
      rw [Point.nsmul_add_nsmul B.onCurve, ← hS83_def, ← B.add_natCast_val_nsmul,
        windowScalar_partialSum input h_assumptions]
    exact FixedBase.add_coords_eq hpt

def circuit (B : FixedBase) : GeneralFormalCircuit.WithHint Fp UnconstrainedNat Point where
  main := main B
  elaborated := elaborated B
  Spec := Spec B
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec B
  soundness := soundness B
  completeness := completeness B

end Orchard.Ecc.MulFixed.FullWidth
