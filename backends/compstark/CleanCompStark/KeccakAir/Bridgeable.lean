module

public import CleanCompStark.Gating
public import Clean.Examples.KeccakAir.Component

/-!
# The constraints of the Keccak-f component are admissible

Every constraint of the component's row circuit splits into a gate and a body that reads no
selector, reads cells of the window, and weighs at most `max (3 a) (b + 2 a)` when the rows' cells
and the first-row selector weigh `a` and the transition selector `b` (`admissible_main`). This is
shown step by step: each of the four steps, round control, θ, ρ ∘ π ∘ χ and ι, has its constraints
described by the gadgets it calls (`Gating`), and its inputs are cells of the window
(`WindowShaped`). So the component is bridgeable (`bridgeable_component`), and its lowered
constraints have Plonky3's degree (`KeccakAir.Setup`).
-/

@[expose] public section

namespace CleanCompStark.KeccakAir
open Air.Flat Air.Flat.WitnessGeneration Backends _root_.KeccakAir

/-! ### Cells of a row -/

/-- A property of every cell of a row. -/
structure RowCells {α : Type} (P : α → Prop) (row : Row α) : Prop where
  stepFlags : ∀ i : Fin 24, P row.stepFlags[i]
  exportFlag : P row.exportFlag
  preimage : ∀ i : Fin 100, P row.preimage[i]
  a : ∀ i : Fin 100, P row.a[i]
  c : ∀ i : Fin 320, P row.c[i]
  cPrime : ∀ i : Fin 320, P row.cPrime[i]
  aPrime : ∀ i : Fin 1600, P row.aPrime[i]
  aPrimePrime : ∀ i : Fin 100, P row.aPrimePrime[i]
  aPrimePrime00Bits : ∀ i : Fin 64, P row.aPrimePrime00Bits[i]
  aPrimePrimePrime00Limbs : ∀ i : Fin 4, P row.aPrimePrimePrime00Limbs[i]

/-- A property of the elements of a row is one of its cells. -/
theorem rowCells_of_toElements {α : Type} {P : α → Prop} {row : Row α}
    (h : ∀ x ∈ (toElements row).toList, P x) : RowCells P row := by
  rw [ProvableStruct.toList_toElements] at h
  simp only [ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.componentsToList, List.mem_append, List.append_nil] at h
  have hv {n : ℕ} (v : Vector α n) (hv : ∀ x ∈ v.toList, P x) (i : Fin n) : P v[i] :=
    hv _ (by simp)
  constructor
  all_goals first
    | exact hv _ fun x hx => h x (by simp only [toElements] at *; simp only [hx, true_or, or_true])
    | exact h _ (Or.inr (Or.inl (List.mem_singleton_self _)))

section Cells
variable {α : Type} {P : α → Prop} {row : Row α} (h : RowCells P row)
include h

lemma RowCells.aLimb (y x : Fin 5) (l : Fin 4) : P (row.aLimb y x l) :=
  h.a _
lemma RowCells.cBit (x : Fin 5) (z : Fin 64) : P (row.cBit x z) := h.c _
lemma RowCells.cPrimeBit (x : Fin 5) (z : Fin 64) : P (row.cPrimeBit x z) :=
  h.cPrime _
lemma RowCells.aPrimeBit (y x : Fin 5) (z : Fin 64) : P (row.aPrimeBit y x z) :=
  h.aPrime _
lemma RowCells.b (x y : Fin 5) (z : Fin 64) : P (row.b x y z) := h.aPrime _
lemma RowCells.aPrimePrimeLimb (y x : Fin 5) (l : Fin 4) :
    P (row.aPrimePrimeLimb y x l) :=
  h.aPrimePrime _
lemma RowCells.aPrimePrimePrimeLimb (y x : Fin 5) (l : Fin 4) :
    P (row.aPrimePrimePrimeLimb y x l) := by
  unfold Row.aPrimePrimePrimeLimb
  split
  · exact h.aPrimePrimePrime00Limbs _
  · exact h.aPrimePrime _

end Cells

/-- The shapes of a window's cells: the rows' cells are plain and weigh at most `a`, the first-row
and transition selectors are selectors and weigh at most `a` and `b`. -/
structure WindowShaped {F : Type} (w : ℕ) (wv : ℕ → ℕ) (a b : ℕ)
    (window : Window Row (Expression F)) : Prop where
  current : RowCells (Shaped w wv .plain a) window.current
  next : RowCells (Shaped w wv .plain a) window.next
  isFirstRow : Shaped w wv (.selector .firstRow) a window.isFirstRow
  isTransition : Shaped w wv (.selector .transition) b window.isTransition

/-! ### The constraints of the steps -/

section Steps
variable {p : ℕ} [Fact p.Prime] {w : ℕ} {wv : ℕ → ℕ} {a b : ℕ}

lemma getElem_packLane_bits {α : Type} (bits : Vector α 64) (limbs : Vector α 4) (l : ℕ)
    (hl : l < 4) (k : ℕ) (hk : k < 16) :
    (packLane bits limbs)[l].bits[k] = bits[16 * l + k] := by
  simp [packLane, limbBits, limbBit]

lemma getElem_packLane_value {α : Type} (bits : Vector α 64) (limbs : Vector α 4) (l : ℕ)
    (hl : l < 4) : (packLane bits limbs)[l].value = limbs[l] := by
  simp [packLane]

/-- Packing bits of shape `plain` and weight `d` into limbs of weight `a ≤ d`. -/
lemma shaped_pack {d : ℕ} {bits : Vector (Expression (F p)) 64}
    {limbs : Vector (Expression (F p)) 4}
    (hbits : ∀ z : Fin 64, Shaped w wv .plain d bits[z])
    (hlimbs : ∀ l : Fin 4, Shaped w wv .plain d limbs[l]) (l : Fin 4) :
    Shaped w wv .plain d (Utils.Bits.fieldFromBitsExpr (packLane bits limbs)[l].bits -
      (packLane bits limbs)[l].value) := by
  have hb : Shaped w wv .plain d
      (Utils.Bits.fieldFromBitsExpr (packLane bits limbs)[l].bits) :=
    shaped_fieldFromBitsExpr fun k => by
      rw [Fin.getElem_fin, Fin.getElem_fin, getElem_packLane_bits _ _ _ l.isLt _ k.isLt]
      exact hbits ⟨16 * l.val + k.val, by omega⟩
  have hv : Shaped w wv .plain d (packLane bits limbs)[l].value := by
    rw [Fin.getElem_fin, getElem_packLane_value _ _ _ l.isLt]
    exact hlimbs l
  exact (shaped_sub hb hv).mono (by simp)

lemma shaped_parityCheck {a0 a1 a2 a3 a4 c : Expression (F p)} (h0 : Shaped w wv .plain a a0)
    (h1 : Shaped w wv .plain a a1) (h2 : Shaped w wv .plain a a2) (h3 : Shaped w wv .plain a a3)
    (h4 : Shaped w wv .plain a a4) (h5 : Shaped w wv .plain a c) :
    Shaped w wv .plain (3 * a) (parityCheck a0 a1 a2 a3 a4 c) := by
  have hd := shaped_sub (shaped_add (shaped_add (shaped_add (shaped_add h0 h1) h2) h3) h4) h5
  simp only [max_self] at hd
  have h := shaped_mul (shaped_mul hd (shaped_sub hd (shaped_ofNat (F := F p) 2)))
    (shaped_sub hd (shaped_ofNat (F := F p) 4))
  exact h.mono (by simp only [Nat.max_zero]; omega)

lemma shaped_iotaBit {flags : Vector (Expression (F p)) 24} {bit : Expression (F p)}
    (hflags : ∀ r : Fin 24, Shaped w wv .plain a flags[r]) (hbit : Shaped w wv .plain a bit)
    (z : Fin 64) : Shaped w wv .plain (2 * a) (iotaBit flags bit z) := by
  have hfold (rounds : List (Fin 24)) (sum : Expression (F p)) (hsum : Shaped w wv .plain a sum) :
      Shaped w wv .plain a (rounds.foldl (fun sum (r : Fin 24) => sum + flags[r]) sum) := by
    induction rounds generalizing sum with
    | nil => exact hsum
    | cons r rounds ih =>
      rw [List.foldl_cons]
      exact ih _ ((shaped_add hsum (hflags r)).mono (by simp))
  unfold iotaBit
  split
  · exact hbit.mono (by omega)
  · rename_i r rs _
    exact (shaped_bitXor (hfold rs _ (hflags r)) hbit).mono (by omega)

theorem admissible_rhoPiChi {row : Var Row (F p)} (h : RowCells (Shaped w wv .plain a) row)
    (n : ℕ) : ∀ x ∈ ((RhoPiChi.circuit.main row).operations n).constraints,
      Admissible w wv (max (3 * a) (b + 2 * a)) x := by
  intro x hx
  simp only [RhoPiChi.circuit, RhoPiChi.main, circuit_norm, mem_constraints_forEach,
    constraints_toSubcircuit, mem_constraints_packLimbs, Fin.eta] at hx
  obtain ⟨y, x, l, rfl⟩ := hx
  refine ((shaped_pack (fun z => ?_) (fun l => ?_) l).mono le_rfl |>.mono
    (le_max_left _ _)).admissible trivial
  · simp only [RhoPiChi.chiBits, Fin.getElem_fin, Vector.getElem_ofFn]
    exact (shaped_bitXor (shaped_bitAndNot (h.b _ y _) (h.b _ y _)) (h.b x y _)).mono
      (by omega)
  · simp only [Row.aPrimePrimeLane, Fin.getElem_fin, Vector.getElem_ofFn]
    exact (h.aPrimePrimeLimb y x _).mono (by omega)

lemma shaped_transitionInPermutation {window : Var (Window Row) (F p)}
    (h : WindowShaped w wv a b window) :
    Shaped w wv (.gated .transition) (b + a) (transitionInPermutation window) :=
  (shaped_mul h.isTransition (shaped_sub (shaped_ofNat (F := F p) 1) (h.current.stepFlags 23))).mono
    (by simp)

theorem admissible_roundControl {window : Var (Window Row) (F p)}
    (h : WindowShaped w wv a b window) (n : ℕ) :
    ∀ x ∈ ((RoundControl.circuit.main window).operations n).constraints,
      Admissible w wv (max (3 * a) (b + 2 * a)) x := by
  intro x hx
  simp only [RoundControl.circuit, RoundControl.main, circuit_norm, mem_constraints_forEach,
    constraints_toSubcircuit, mem_constraints_conditionalEquality, List.mem_append,
    List.mem_singleton, Fin.eta] at hx
  have hplain (d : ℕ) (hd : d ≤ 3 * a) {y : Expression (F p)} (hy : Shaped w wv .plain d y) :
      Admissible w wv (max (3 * a) (b + 2 * a)) y :=
    (hy.mono (le_max_of_le_left hd)).admissible trivial
  have hgated (gate : Gate) (d : ℕ) (hd : d ≤ b + 2 * a) {y : Expression (F p)}
      (hy : Shaped w wv (.gated gate) d y) : Admissible w wv (max (3 * a) (b + 2 * a)) y :=
    (hy.mono (le_max_of_le_right hd)).admissible trivial
  have hnext (i : Fin 24) : Shaped w wv .plain a (RoundControl.nextFlags window)[i] := by
    simp only [RoundControl.nextFlags, Fin.getElem_fin, Vector.getElem_ofFn]
    exact h.next.stepFlags _
  have hc := h.current
  rcases hx with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | rfl
  · exact hgated _ _ (by simp; omega)
      (shaped_mul h.isFirstRow (shaped_sub (hc.stepFlags 0) (shaped_ofNat (F := F p) 1)))
  · exact hgated _ _ (by omega) (shaped_mul h.isFirstRow (hc.stepFlags i.succ))
  · exact hgated _ _ (by simp; omega)
      (shaped_mul h.isTransition (shaped_sub (hc.stepFlags i) (hnext i)))
  · exact hplain _ (by simp; omega)
      (shaped_mul (hc.stepFlags 0) (shaped_sub (hc.preimage i) (hc.a i)))
  · exact hgated _ _ (by simp; omega) (shaped_mul (shaped_transitionInPermutation h)
      (shaped_sub (hc.preimage i) (h.next.preimage i)))
  · exact hplain _ (by omega) (shaped_boolCheck hc.exportFlag)
  · exact hplain _ (by simp; omega)
      (shaped_mul (shaped_sub (shaped_ofNat (F := F p) 1) (hc.stepFlags 23)) hc.exportFlag)

theorem admissible_iota {window : Var (Window Row) (F p)}
    (h : WindowShaped w wv a b window) (n : ℕ) :
    ∀ x ∈ ((Iota.circuit.main window).operations n).constraints,
      Admissible w wv (max (3 * a) (b + 2 * a)) x := by
  intro x hx
  simp only [Iota.circuit, Iota.main, circuit_norm, mem_constraints_forEach,
    constraints_toSubcircuit, mem_constraints_packLimbs, mem_constraints_conditionalEquality,
    List.mem_append, List.mem_singleton, Fin.eta] at hx
  have hplain (d : ℕ) (hd : d ≤ 3 * a) {y : Expression (F p)} (hy : Shaped w wv .plain d y) :
      Admissible w wv (max (3 * a) (b + 2 * a)) y :=
    (hy.mono (le_max_of_le_left hd)).admissible trivial
  have hc := h.current
  rcases hx with ⟨i, rfl⟩ | ⟨l, rfl⟩ | ⟨l, rfl⟩ | ⟨x, y, i, rfl⟩
  · exact hplain _ (by omega) (shaped_boolCheck (hc.aPrimePrime00Bits i))
  · refine hplain a (by omega) (shaped_pack (fun z => hc.aPrimePrime00Bits z) (fun l => ?_) l)
    simp only [Row.aPrimePrimeLane, Fin.getElem_fin, Vector.getElem_ofFn]
    exact hc.aPrimePrimeLimb 0 0 _
  · refine hplain (2 * a) (by omega) (shaped_pack (fun z => ?_) (fun l => ?_) l)
    · simp only [Iota.iotaBits, Fin.getElem_fin, Vector.getElem_ofFn]
      exact shaped_iotaBit hc.stepFlags (hc.aPrimePrime00Bits _) _
    · exact (hc.aPrimePrimePrime00Limbs l).mono (by omega)
  · have hl : Shaped w wv .plain a (window.current.aPrimePrimePrimeLane y x)[i.val] := by
      simp only [Row.aPrimePrimePrimeLane, Vector.getElem_ofFn]
      exact hc.aPrimePrimePrimeLimb y x _
    have hr : Shaped w wv .plain a (window.next.aLane y x)[i.val] := by
      simp only [Row.aLane, Vector.getElem_ofFn]
      exact h.next.aLimb y x _
    exact ((shaped_mul (shaped_transitionInPermutation h) (shaped_sub hl hr)).mono
      (le_max_of_le_right (by simp; omega))).admissible trivial

lemma lookups_roundControl (window : Var (Window Row) (F p)) (n : ℕ) :
    ((RoundControl.circuit.main window).operations n).lookups = [] := by
  simp [RoundControl.circuit, RoundControl.main, circuit_norm, lookups_forEach,
    lookups_toSubcircuit, lookups_conditionalEquality]

lemma lookups_rhoPiChi (row : Var Row (F p)) (n : ℕ) :
    ((RhoPiChi.circuit.main row).operations n).lookups = [] := by
  simp [RhoPiChi.circuit, RhoPiChi.main, circuit_norm, lookups_forEach, lookups_toSubcircuit,
    lookups_packLimbs]

lemma lookups_iota (window : Var (Window Row) (F p)) (n : ℕ) :
    ((Iota.circuit.main window).operations n).lookups = [] := by
  simp [Iota.circuit, Iota.main, circuit_norm, lookups_forEach, lookups_toSubcircuit,
    lookups_packLimbs, lookups_conditionalEquality]

lemma length_roundControl (window : Var (Window Row) (F p)) (n : ℕ) :
    ((RoundControl.circuit.main window).operations n).constraints.length = 250 := by
  simp [RoundControl.circuit, RoundControl.main, circuit_norm, constraints_forEach,
    constraints_toSubcircuit, length_constraints_conditionalEquality]

lemma length_rhoPiChi (row : Var Row (F p)) (n : ℕ) :
    ((RhoPiChi.circuit.main row).operations n).constraints.length = 100 := by
  simp [RhoPiChi.circuit, RhoPiChi.main, circuit_norm, constraints_forEach,
    constraints_toSubcircuit, length_constraints_packLimbs]

lemma length_iota (window : Var (Window Row) (F p)) (n : ℕ) :
    ((Iota.circuit.main window).operations n).constraints.length = 172 := by
  simp [Iota.circuit, Iota.main, circuit_norm, constraints_forEach, constraints_toSubcircuit,
    length_constraints_packLimbs, length_constraints_conditionalEquality]

variable [Fact (2 ^ 16 < p)]

lemma lookups_theta (row : Var Row (F p)) (n : ℕ) :
    ((Theta.circuit.main row).operations n).lookups = [] := by
  simp [Theta.circuit, Theta.main, circuit_norm, lookups_forEach, lookups_toSubcircuit,
    lookups_packLimbs]

theorem admissible_theta {row : Var Row (F p)} (h : RowCells (Shaped w wv .plain a) row)
    (n : ℕ) : ∀ x ∈ ((Theta.circuit.main row).operations n).constraints,
      Admissible w wv (max (3 * a) (b + 2 * a)) x := by
  intro x hx
  simp only [Theta.circuit, Theta.main, circuit_norm, mem_constraints_forEach,
    constraints_toSubcircuit, mem_constraints_packLimbs, List.mem_append, List.mem_singleton,
    Fin.eta] at hx
  have hD (d : ℕ) (hd : d ≤ 3 * a) {y : Expression (F p)} (hy : Shaped w wv .plain d y) :
      Admissible w wv (max (3 * a) (b + 2 * a)) y :=
    (hy.mono (le_max_of_le_left hd)).admissible trivial
  rcases hx with ⟨x, ⟨z, rfl⟩ | ⟨z, rfl⟩⟩ | ⟨x, y, ⟨z, rfl⟩ | ⟨l, rfl⟩⟩ | ⟨x, z, rfl⟩
  · rw [Row.getElem_cLane _ _ _ z.isLt]
    exact hD _ (by omega) (shaped_boolCheck (h.cBit x _))
  · exact hD _ (by omega) (shaped_sub (h.cPrimeBit x z)
      (shaped_bitXor (shaped_bitXor (h.cBit x z) (h.cBit _ z)) (h.cBit _ _)))
  · rw [Row.getElem_aPrimeLane _ _ _ _ z.isLt]
    exact hD _ (by omega) (shaped_boolCheck (h.aPrimeBit y x _))
  · refine hD (3 * a) le_rfl (shaped_pack (fun z => ?_) (fun l => ?_) l)
    · simp only [Theta.inputBits, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (shaped_bitXor (h.aPrimeBit y x _)
        (shaped_bitXor (h.cBit x _) (h.cPrimeBit x _))).mono (by omega)
    · simp only [Row.aLane, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (h.aLimb y x _).mono (by omega)
  · exact hD _ le_rfl (shaped_parityCheck (h.aPrimeBit 0 x z) (h.aPrimeBit 1 x z)
      (h.aPrimeBit 2 x z) (h.aPrimeBit 3 x z) (h.aPrimeBit 4 x z) (h.cPrimeBit x z))

lemma lookups_main (window : Var (Window Row) (F p)) (n : ℕ) :
    ((main window).operations n).lookups = [] := by
  simp only [main, circuit_norm, List.append_eq_nil_iff, lookups_toSubcircuit]
  exact ⟨lookups_roundControl _ _, lookups_theta _ _, lookups_rhoPiChi _ _, lookups_iota _ _⟩

/-- The constraints of the row circuit are those of its four steps. -/
theorem admissible_main {window : Var (Window Row) (F p)} (h : WindowShaped w wv a b window)
    (n : ℕ) : ∀ x ∈ ((main window).operations n).constraints,
      Admissible w wv (max (3 * a) (b + 2 * a)) x := by
  intro x hx
  simp only [main, circuit_norm, List.mem_append] at hx
  rcases hx with hx | hx | hx | hx <;> rw [constraints_toSubcircuit] at hx
  · exact admissible_roundControl h _ x hx
  · exact admissible_theta h.current _ x hx
  · exact admissible_rhoPiChi h.current _ x hx
  · exact admissible_iota h _ x hx

lemma length_theta (row : Var Row (F p)) (n : ℕ) :
    ((Theta.circuit.main row).operations n).constraints.length = 2660 := by
  simp only [Theta.circuit, Theta.main, circuit_norm, constraints_forEach,
    constraints_toSubcircuit, length_constraints_packLimbs, List.length_append,
    List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def, List.length_ofFn,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The row circuit has Plonky3's `3182` constraints. -/
lemma length_main (window : Var (Window Row) (F p)) (n : ℕ) :
    ((main window).operations n).constraints.length = 3182 := by
  simp only [main, circuit_norm, List.length_append]
  rw [constraints_toSubcircuit, constraints_toSubcircuit, constraints_toSubcircuit,
    constraints_toSubcircuit, length_roundControl, length_theta, length_rhoPiChi, length_iota]

end Steps

section Variables
variable {F : Type} {R : TypeMap} [ProvableType R]

lemma toElements_varFromOffset_window :
    toElements (varFromOffset (F := F) (Window R) 0) =
      Vector.mapRange (size (Window R)) fun i => .var ⟨0 + i⟩ :=
  ProvableType.toElements_fromElements _

lemma varFromOffset_current :
    ∀ x ∈ (toElements (varFromOffset (F := F) (Window R) 0).current).toList,
    ∃ j < size R, x = .var ⟨j⟩ := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < size R := by simpa using hj
  refine ⟨j, hj', ?_⟩
  have h := congrArg (fun v : Vector (Expression F) (Window.layout R).rowWidth => v[j]'hj')
    (Window.layout_current (varFromOffset (F := F) (Window R) 0))
  simp only [Vector.getElem_toList]
  refine h.symm.trans ?_
  simp only [WindowLayout.current, WindowLayout.cell, Vector.getElem_ofFn,
    toElements_varFromOffset_window, Vector.getElem_mapRange, Nat.zero_add]

lemma varFromOffset_next : ∀ x ∈ (toElements (varFromOffset (F := F) (Window R) 0).next).toList,
    ∃ j < size R, x = .var ⟨size R + j⟩ := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < size R := by simpa using hj
  refine ⟨j, hj', ?_⟩
  have h := congrArg (fun v : Vector (Expression F) (Window.layout R).rowWidth => v[j]'hj')
    (Window.layout_next (varFromOffset (F := F) (Window R) 0))
  simp only [Vector.getElem_toList]
  refine h.symm.trans ?_
  simp only [WindowLayout.next, WindowLayout.cell, Vector.getElem_ofFn,
    toElements_varFromOffset_window, Vector.getElem_mapRange, Nat.zero_add]
  rfl

lemma varFromOffset_isFirstRow :
    (varFromOffset (F := F) (Window R) 0).isFirstRow = .var ⟨2 * size R⟩ := by
  rw [← Window.layout_isFirstRow]
  simp only [WindowLayout.isFirstRow, WindowLayout.cell, toElements_varFromOffset_window,
    Vector.getElem_mapRange, Nat.zero_add, Window.layout]

lemma varFromOffset_isLastRow :
    (varFromOffset (F := F) (Window R) 0).isLastRow = .var ⟨2 * size R + 1⟩ := by
  rw [← Window.layout_isLastRow]
  simp only [WindowLayout.isLastRow, WindowLayout.cell, toElements_varFromOffset_window,
    Vector.getElem_mapRange, Nat.zero_add, Window.layout]

lemma varFromOffset_isTransition :
    (varFromOffset (F := F) (Window R) 0).isTransition = .var ⟨2 * size R + 2⟩ := by
  rw [← Window.layout_isTransition]
  simp only [WindowLayout.isTransition, WindowLayout.cell, toElements_varFromOffset_window,
    Vector.getElem_mapRange, Nat.zero_add, Window.layout]

end Variables

/-! ### The component -/

section Component
variable {p : ℕ}

/-- The variables of a window, the input of the component's row operations. -/
abbrev vars : Window Row (Expression (F p)) := varFromOffset (Window Row) 0

/-- The weights of cells: `a` for the cells of the rows and the first- and last-row selectors,
`b` for the transition selector. -/
def cellWeight (a b : ℕ) (j : ℕ) : ℕ := if j = 2 * size Row + 2 then b else a

/-- The cells of the window of variables have their shapes. -/
theorem windowShaped_vars (a b : ℕ) :
    WindowShaped (size Row) (cellWeight a b) a b (vars (p := p)) := by
  have hcell (j : ℕ) (hj : j < 2 * size Row) :
      Shaped (size Row) (cellWeight a b) .plain a (.var ⟨j⟩ : Expression (F p)) :=
    (shaped_var hj).mono (by simp only [cellWeight]; split_ifs <;> omega)
  refine ⟨rowCells_of_toElements fun x hx => ?_, rowCells_of_toElements fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := varFromOffset_current x hx
    exact hcell j (by omega)
  · obtain ⟨j, hj, rfl⟩ := varFromOffset_next x hx
    exact hcell _ (by omega)
  · rw [varFromOffset_isFirstRow]
    exact (shaped_selector (by simp [selectorGate?])).mono (by simp [cellWeight])
  · rw [varFromOffset_isTransition]
    exact (shaped_selector (by simp [selectorGate?])).mono (by simp [cellWeight])

variable [Fact p.Prime] [Fact (2 ^ 16 < p)]

lemma rowOperations_component (height : UInt64) :
    (component (p := p) height).rowOperations = (main vars).operations (size (Window Row)) :=
  rfl

/-- Every constraint of the component is admissible. -/
theorem admissible_component (height : UInt64) (a b : ℕ) :
    ∀ x ∈ (component (p := p) height).rowOperations.constraints,
      Admissible (size Row) (cellWeight a b) (max (3 * a) (b + 2 * a)) x := by
  rw [rowOperations_component]
  exact admissible_main (windowShaped_vars a b) _

/-- The Keccak-f component has no fixed columns: its segment program computes all its cells. -/
theorem fixedColumns_component (height : UInt64) : fixedColumns (component (p := p) height) = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun j hj => ?_
  simp only [fixedColumns, component, WitnessGeneration.Generation.cells, Vector.toList_replicate,
    List.mem_map, List.mem_filter] at hj
  obtain ⟨⟨cell, _⟩, ⟨hmem, hfixed⟩, -⟩ := hj
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_replicate] at hmem
  split at hmem
  · cases hmem
    exact absurd hfixed Bool.false_ne_true
  · cases hmem

/-- **The Keccak-f component is bridgeable**: no legacy lookups, every constraint is a gate times
a body that reads no selector, and every expression reads cells of the row. -/
theorem bridgeable_component (height : UInt64) : bridgeable (component (p := p) height) = true := by
  have hwidth : 2 * size Row + 3 ≤ (component (p := p) height).width :=
    rowWidth_le_size (component := component (p := p) height) (layout := Window.layout Row) rfl
  have hwindow : (component (p := p) height).window.map (·.rowWidth) = some (size Row) := rfl
  have hinteractions : (component (p := p) height).rowOperations.interactions = [] :=
    interactions_main _ _
  have hadmissible := admissible_component (p := p) height 0 0
  simp only [bridgeable, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true,
    Option.isNone_iff_eq_none, hwindow]
  refine ⟨⟨⟨by rw [rowOperations_component]; exact lookups_main _ _,
    fun x hx => (hadmissible x hx).1⟩, ?_⟩, by simp [fixedColumns_component]⟩
  simp only [rowExpressions, hinteractions, List.flatMap_nil, List.append_nil,
    expressionsBadVariable]
  exact List.findSome?_eq_none_iff.mpr fun x hx => expressionBadVariable_eq_none _ x
    fun j hj => by have := (hadmissible x hx).2.1 j hj; omega

/-- A parity constraint of θ weighs `3` when the cells of the rows weigh `1`. -/
theorem exists_weight_eq (height : UInt64) :
    ∃ x ∈ (component (p := p) height).rowOperations.constraints,
      weight (cellWeight 1 0) x = 3 := by
  have hcells : RowCells (fun x => ∃ j < size Row, x = .var ⟨j⟩) (vars (p := p)).current :=
    rowCells_of_toElements varFromOffset_current
  refine ⟨parityCheck ((vars (p := p)).current.aPrimeBit 0 0 0)
    ((vars (p := p)).current.aPrimeBit 1 0 0) ((vars (p := p)).current.aPrimeBit 2 0 0)
    ((vars (p := p)).current.aPrimeBit 3 0 0) ((vars (p := p)).current.aPrimeBit 4 0 0)
    ((vars (p := p)).current.cPrimeBit 0 0), ?_, ?_⟩
  · rw [rowOperations_component]
    simp only [main, circuit_norm, List.mem_append]
    right; left
    rw [constraints_toSubcircuit]
    simp only [Theta.circuit, Theta.main, circuit_norm, mem_constraints_forEach,
      constraints_toSubcircuit, mem_constraints_packLimbs, List.mem_append, List.mem_singleton,
      Fin.eta]
    right; right
    exact ⟨0, 0, rfl⟩
  · obtain ⟨j0, hj0, h0⟩ := hcells.aPrimeBit 0 0 0
    obtain ⟨j1, hj1, h1⟩ := hcells.aPrimeBit 1 0 0
    obtain ⟨j2, hj2, h2⟩ := hcells.aPrimeBit 2 0 0
    obtain ⟨j3, hj3, h3⟩ := hcells.aPrimeBit 3 0 0
    obtain ⟨j4, hj4, h4⟩ := hcells.aPrimeBit 4 0 0
    obtain ⟨j5, hj5, h5⟩ := hcells.cPrimeBit 0 0
    have htwo : weight (cellWeight 1 0) (2 : Expression (F p)) = 0 := rfl
    have hfour : weight (cellWeight 1 0) (4 : Expression (F p)) = 0 := rfl
    rw [h0, h1, h2, h3, h4, h5]
    simp only [parityCheck, weight_mul, weight_sub, weight_add, weight_var, htwo, hfour,
      cellWeight]
    split_ifs <;> omega

end Component

end CleanCompStark.KeccakAir
