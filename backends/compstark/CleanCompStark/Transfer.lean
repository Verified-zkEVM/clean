module

public import CleanCompStark.Air
public import CompStark.Stark.Satisfied

/-!
# From a satisfied AIR to a Clean table

A trace satisfying a component's AIR (`toAir`) is a table of the component whose constraints hold
(`toTable`, `constraints_toTable`), under checks on the component (`bridgeable`) and its height
(`Fits`).

The lowering is correct row by row (`eval_constraint_iff`): a Clean constraint holds on a row read
off the trace (`toRow`) if and only if its lowered form vanishes on the trace's row with CompStark's
selectors. These are Plonky3's, nonzero exactly on the rows where the 0/1 selectors of the Clean
row are `1` (`selectors_eq_zero_iff`): `n` on the first row, `n ω` on the last, `ωⁱ - ω⁻¹` on
the row `i` of a transition.
-/

@[expose] public section

namespace CleanCompStark
open Air.Flat Air.Flat.WitnessGeneration Backends CompStark CompStark.Stark

section Expressions
variable {F : Type}

theorem cells_lt_of_badVariable (width : ℕ) :
    ∀ x : Expression F, expressionBadVariable width x = none → ∀ j ∈ expressionCells x, j < width
  | .var v, h, j, hj => by
    simp only [expressionCells, List.mem_singleton] at hj
    subst hj
    simp only [expressionBadVariable] at h
    split at h
    · assumption
    · cases h
  | .const _, _, j, hj => by simp [expressionCells] at hj
  | .add a b, h, j, hj | .mul a b, h, j, hj => by
    simp only [expressionBadVariable] at h
    cases ha : expressionBadVariable width a with
    | some _ => simp [ha] at h
    | none =>
      simp only [ha, Option.orElse_none] at h
      simp only [expressionCells, List.mem_append] at hj
      rcases hj with hj | hj
      · exact cells_lt_of_badVariable width a ha j hj
      · exact cells_lt_of_badVariable width b h j hj

theorem cells_subset_of_splitSelector {width : ℕ} {gate : Gate} {body : Expression F} :
    ∀ {x : Expression F}, splitSelector width x = some (gate, body) →
      ∀ j ∈ expressionCells body, j ∈ expressionCells x
  | .var _, h | .const _, h | .add _ _, h => by simp [splitSelector] at h
  | .mul left right, h => by
    simp only [splitSelector] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro j hj
      simp [expressionCells, hj]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro j hj
      simp [expressionCells, hj]
    · split at h
      · rename_i hsplit
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro j hj
        simp only [expressionCells, List.mem_append] at hj ⊢
        rcases hj with hj | hj
        · exact Or.inl (cells_subset_of_splitSelector hsplit j hj)
        · exact Or.inr hj
      · obtain ⟨⟨gate', right'⟩, hsplit, heq⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        intro j hj
        simp only [expressionCells, List.mem_append] at hj ⊢
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr (cells_subset_of_splitSelector hsplit j hj)

end Expressions

variable {F : Type} [FiniteField F] {K : Type} [BaseField K] (e : F ≃+* K)

/-! ### Side conditions -/

/-- The expressions a component's row reads: its constraints, and its interactions' multiplicities
and messages. -/
def rowExpressions (component : Component F) : List (Expression F) :=
  component.rowOperations.constraints ++
    component.rowOperations.interactions.flatMap fun i => i.mult :: i.msg.toList

/-- What a component's AIR needs to mean what its circuit means: the circuit has no legacy lookups,
every constraint is a gate times a body that reads no selector (`gateConstraint`), and every
expression reads cells of the row. -/
def bridgeable (component : Component F) : Bool :=
  component.rowOperations.lookups.isEmpty &&
    component.rowOperations.constraints.all
      (fun x => (gateConstraint (component.window.map (·.rowWidth)) x).isSome) &&
    (expressionsBadVariable component.width (rowExpressions component)).isNone

/-- A trace height of `2 ^ logN` that a component's AIR proves: the trace domain is a two-adic
subgroup of `K`, row indices fit in `u64`, and the fixed columns have this height. -/
structure Fits (component : Component F) (logN : ℕ) : Prop where
  twoAdic : logN ≤ twoAdicity K
  height_le : logN ≤ 64
  fixedHeight : ∀ fixed ∈ component.fixedColumns, fixed.height.toNat = 2 ^ logN

namespace Bridgeable
variable {component : Component F} (h : bridgeable component = true)
include h

theorem lookups_eq_nil : component.rowOperations.lookups = [] := by
  simp only [bridgeable, Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.1.1

theorem gated : ∀ x ∈ component.rowOperations.constraints,
    (gateConstraint (component.window.map (·.rowWidth)) x).isSome := by
  simp only [bridgeable, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2

theorem cells_lt : ∀ x ∈ rowExpressions component, ∀ j ∈ expressionCells x,
    j < component.width := by
  simp only [bridgeable, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  intro x hx
  exact cells_lt_of_badVariable _ x
    ((List.findSome?_eq_none_iff.mp h.2) x hx)

end Bridgeable

/-! ### Cells and expressions -/

/-- A selector cell of a two-row component's row. -/
def IsSelectorCell (component : Component F) (j : ℕ) : Prop :=
  ∃ layout ∈ component.window, 2 * layout.rowWidth ≤ j ∧ j < 2 * layout.rowWidth + 3

theorem rowWidth_le_size {component : Component F} {layout : WindowLayout component.Input}
    (_ : component.window = some layout) : 2 * layout.rowWidth + 3 ≤ component.width := by
  have h := layout.size_eq
  have := component.circuit.size_eq
  simp only [Component.width]
  omega

theorem fixedWidth_le_rowWidth {component : Component F} {layout : WindowLayout component.Input}
    (hw : component.window = some layout) : component.fixedWidth ≤ layout.rowWidth := by
  have := component.fixed_width_le_input
  simp only [hw] at this
  exact this

variable (logN : ℕ) (trace : Array K)

/-- The trace's row `i`, with Plonky3's selectors. -/
abbrev traceEnv (component : Component F) (publicValues : List K) (i : ℕ) : Expr.Env K K :=
  (toAir e component logN).traceRow logN trace publicValues i

/-- The trace's row `i`, with the selectors `0` and `1`. -/
abbrev rowEnv (component : Component F) (i : ℕ) : Expr.Env K K :=
  Lookup.generationRow (toAir e component logN) logN trace [] i

/-- Off the selector cells, a cell reads the same in both environments of a row. -/
theorem eval_cellExpr_congr (component : Component F) (publicValues : List K) (i j : ℕ)
    (hj : ¬ IsSelectorCell component j) :
    (cellExpr component j).eval (traceEnv e logN trace component publicValues i) =
      (cellExpr component j).eval (rowEnv e logN trace component i) := by
  unfold cellExpr
  cases hw : component.window with
  | none => dsimp only; split <;> rfl
  | some layout =>
    have hsel : ¬ (2 * layout.rowWidth ≤ j ∧ j < 2 * layout.rowWidth + 3) :=
      fun h => hj ⟨layout, hw, h⟩
    dsimp only
    split_ifs <;> first | rfl | (exfalso; omega)

/-- An expression without selector cells reads the same in both environments of a row. -/
theorem eval_toExpr_congr (component : Component F) (publicValues : List K) (i : ℕ) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, ¬ IsSelectorCell component j) →
      (toExpr e component x).eval (traceEnv e logN trace component publicValues i) =
        (toExpr e component x).eval (rowEnv e logN trace component i)
  | .var v, h => eval_cellExpr_congr e logN trace component publicValues i v.index
      (h v.index (by simp [expressionCells]))
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [toExpr, Expr.eval]
    rw [eval_toExpr_congr component publicValues i a fun j hj => h j (Or.inl hj),
      eval_toExpr_congr component publicValues i b fun j hj => h j (Or.inr hj)]

/-- A cell of a row read off the trace. -/
theorem getD_toRow (component : Component F) (i j : ℕ) (hj : j < component.width) :
    (toRow e component logN trace i)[j]?.getD 0 =
      e.symm ((cellExpr component j).eval (rowEnv e logN trace component i)) := by
  simp [toRow, hj]

/-- A Clean expression on a row read off the trace is its AIR expression on the trace's row. -/
theorem eval_toRow (component : Component F) (i : ℕ) (data : ProverData F) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, j < component.width) →
      Expression.eval (Environment.fromArray (toRow e component logN trace i) data) x =
        e.symm ((toExpr e component x).eval (rowEnv e logN trace component i))
  | .var v, h => getD_toRow e logN trace component i v.index (h v.index (by simp [expressionCells]))
  | .const c, _ => (e.symm_apply_apply c).symm
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [Expression.eval, toExpr, Expr.eval, map_add, map_mul]
    rw [eval_toRow component i data a fun j hj => h j (Or.inl hj),
      eval_toRow component i data b fun j hj => h j (Or.inr hj)]

/-! ### Selectors -/

/-- On the rows of the trace domain, each of Plonky3's selectors vanishes exactly where the
corresponding 0/1 selector does. -/
theorem selectors_eq_zero_iff (A : Air K) (publicValues : List K) {i : ℕ} (hi : i < 2 ^ logN)
    (hlog : logN ≤ twoAdicity K) :
    ((A.traceRow logN trace publicValues i).isFirstRow = 0 ↔
        (Lookup.generationRow A logN trace [] i).isFirstRow = 0) ∧
      ((A.traceRow logN trace publicValues i).isLastRow = 0 ↔
        (Lookup.generationRow A logN trace [] i).isLastRow = 0) ∧
      ((A.traceRow logN trace publicValues i).isTransition = 0 ↔
        (Lookup.generationRow A logN trace [] i).isTransition = 0) := by
  have hroot := BaseField.isPrimitiveRoot_twoAdicGen (F := K) logN hlog
  have hn : ((2 ^ logN : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_ne_zero _ BaseField.two_ne_zero
  have hω : twoAdicGen (F := K) logN ≠ 0 := hroot.ne_zero (by positivity)
  simp only [Air.traceRow, Lookup.generationRow]
  refine ⟨?_, ?_, ?_⟩
  · split_ifs
    · exact iff_of_false hn one_ne_zero
    · exact Iff.rfl
  · split_ifs
    · exact iff_of_false (mul_ne_zero hn hω) one_ne_zero
    · exact Iff.rfl
  · rw [sub_eq_zero]
    constructor
    · intro h
      have h1 : twoAdicGen (F := K) logN ^ (i + 1) = 1 := by
        rw [pow_succ, h, inv_mul_cancel₀ hω]
      have hdvd := (hroot.pow_eq_one_iff_dvd (i + 1)).mp h1
      have : i + 1 = 2 ^ logN := Nat.le_antisymm (by omega) (Nat.le_of_dvd (by omega) hdvd)
      simp [this]
    · intro h
      split_ifs at h with hlt
      · exact absurd h one_ne_zero
      · have : i + 1 = 2 ^ logN := by omega
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, this, hroot.pow_eq_one])

/-! ### Constraints -/

/-- A gate's selector cell reads its selector. -/
theorem cellExpr_selectorCell {component : Component F} {layout : WindowLayout component.Input}
    (hw : component.window = some layout) {gate : Gate} {cell : ℕ}
    (hcell : gate.selectorCell layout.rowWidth = some cell) :
    cellExpr (K := K) component cell = match gate with
      | .everyRow => .const 1
      | .firstRow => .isFirstRow
      | .lastRow => .isLastRow
      | .transition => .isTransition := by
  have h0 : ¬ 2 * layout.rowWidth < layout.rowWidth ∧ ¬ 2 * layout.rowWidth < 2 * layout.rowWidth :=
    by omega
  have h1 : ¬ 2 * layout.rowWidth + 1 < layout.rowWidth ∧
      ¬ 2 * layout.rowWidth + 1 < 2 * layout.rowWidth ∧
      ¬ 2 * layout.rowWidth + 1 = 2 * layout.rowWidth := by omega
  have h2 : ¬ 2 * layout.rowWidth + 2 < layout.rowWidth ∧
      ¬ 2 * layout.rowWidth + 2 < 2 * layout.rowWidth ∧
      ¬ 2 * layout.rowWidth + 2 = 2 * layout.rowWidth ∧
      ¬ 2 * layout.rowWidth + 2 = 2 * layout.rowWidth + 1 := by omega
  cases gate <;> simp only [Gate.selectorCell, Option.some.injEq, reduceCtorEq] at hcell <;>
    subst hcell <;> simp only [cellExpr, hw, h0, h1, h2, ↓reduceIte]

/-- A gate multiplies by its selector cell. -/
theorem eval_gateExpr {component : Component F} {layout : WindowLayout component.Input}
    (hw : component.window = some layout) {gate : Gate} {cell : ℕ}
    (hcell : gate.selectorCell layout.rowWidth = some cell) (body : Expr K) (env : Expr.Env K K) :
    (gateExpr gate body).eval env = (cellExpr component cell).eval env * body.eval env := by
  rw [cellExpr_selectorCell hw hcell]
  cases gate <;> simp only [Gate.selectorCell, reduceCtorEq] at hcell <;> rfl

/-- A selector cell vanishes on the same rows in both environments. -/
theorem selectorCell_eq_zero_iff {component : Component F} {layout : WindowLayout component.Input}
    (hw : component.window = some layout) {gate : Gate} {cell : ℕ}
    (hcell : gate.selectorCell layout.rowWidth = some cell) (publicValues : List K) {i : ℕ}
    (hi : i < 2 ^ logN) (hlog : logN ≤ twoAdicity K) :
    (cellExpr component cell).eval (traceEnv e logN trace component publicValues i) = 0 ↔
      (cellExpr component cell).eval (rowEnv e logN trace component i) = 0 := by
  have hsel := selectors_eq_zero_iff logN trace (toAir e component logN) publicValues hi hlog
  rw [cellExpr_selectorCell hw hcell]
  cases gate <;> simp only [Gate.selectorCell, reduceCtorEq] at hcell
  · exact hsel.1
  · exact hsel.2.1
  · exact hsel.2.2

/-- **Lowering is correct.** On row `i` of the trace domain, a constraint of a bridgeable
component holds on the row read off the trace if and only if its lowered form vanishes on the
trace's row with Plonky3's selectors. -/
theorem eval_constraint_iff {component : Component F} (hc : bridgeable component = true)
    (hlog : logN ≤ twoAdicity K) (publicValues : List K) {i : ℕ} (hi : i < 2 ^ logN)
    (data : ProverData F) {x : Expression F} (hx : x ∈ component.rowOperations.constraints)
    {g : GatedConstraint F} (hg : gateConstraint (component.window.map (·.rowWidth)) x = some g) :
    Expression.eval (Environment.fromArray (toRow e component logN trace i) data) x = 0 ↔
      (gateExpr g.gate (toExpr e component g.body)).eval
        (traceEnv e logN trace component publicValues i) = 0 := by
  have hcells := Bridgeable.cells_lt hc x (List.mem_append_left _ hx)
  -- an ungated constraint without selector cells
  have ungated : (∀ j ∈ expressionCells x, ¬ IsSelectorCell component j) → g = ⟨.everyRow, x⟩ →
      (Expression.eval (Environment.fromArray (toRow e component logN trace i) data) x = 0 ↔
        (gateExpr g.gate (toExpr e component g.body)).eval
          (traceEnv e logN trace component publicValues i) = 0) := by
    rintro hsel rfl
    rw [eval_toRow e logN trace component i data x hcells, gateExpr,
      eval_toExpr_congr e logN trace component publicValues i x hsel,
      map_eq_zero_iff _ e.symm.injective]
  cases hw : component.window with
  | none =>
    simp only [hw, Option.map_none, gateConstraint, Option.some.injEq] at hg
    exact ungated (fun j _ ⟨layout, hl, _⟩ => by simp [hw] at hl) hg.symm
  | some layout =>
    simp only [hw, Option.map_some, gateConstraint] at hg
    split at hg
    · rename_i hread
      simp only [Option.some.injEq] at hg
      refine ungated (fun j hj ⟨layout', hl, hj'⟩ => ?_) hg.symm
      rw [hw, Option.mem_def, Option.some.injEq] at hl
      subst hl
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true,
        decide_eq_true_eq, not_and, not_lt] at hread
      exact absurd (hread j hj hj'.1) (by omega)
    · obtain ⟨⟨gate, body⟩, hsplit, hg⟩ := Option.bind_eq_some_iff.mp hg
      split at hg
      · cases hg
      · rename_i hbody
        simp only [Option.some.injEq] at hg
        subst hg
        obtain ⟨cell, hcell, heval⟩ := eval_of_splitSelector
          (Environment.fromArray (toRow e component logN trace i) data) hsplit
        have hbodySel : ∀ j ∈ expressionCells body, ¬ IsSelectorCell component j := by
          intro j hj ⟨layout', hl, hj'⟩
          rw [hw, Option.mem_def, Option.some.injEq] at hl
          subst hl
          simp only [Bool.not_eq_true, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq,
            not_and, not_lt] at hbody
          exact absurd (hbody j hj hj'.1) (by omega)
        have hbodyCells : ∀ j ∈ expressionCells body, j < component.width :=
          fun j hj => hcells j (cells_subset_of_splitSelector hsplit j hj)
        have hcellLt : cell < component.width := by
          have := rowWidth_le_size hw
          cases gate <;> simp only [Gate.selectorCell, Option.some.injEq, reduceCtorEq] at hcell <;>
            omega
        have hget := getD_toRow e logN trace component i cell hcellLt
        have hbodyEval := eval_toRow e logN trace component i data body hbodyCells
        rw [heval]
        simp only [Environment.fromArray] at hbodyEval ⊢
        rw [hget, hbodyEval, ← map_mul,
          map_eq_zero_iff _ e.symm.injective, eval_gateExpr hw hcell,
          eval_toExpr_congr e logN trace component publicValues i body hbodySel, mul_eq_zero,
          mul_eq_zero, selectorCell_eq_zero_iff e logN trace hw hcell publicValues hi hlog]

/-! ### The table -/

section Table
variable (component : Component F)

theorem length_toRows : (toRows e component logN trace).length = 2 ^ logN := List.length_ofFn

theorem getElem_toRows (i : ℕ) (hi : i < (toRows e component logN trace).length) :
    (toRows e component logN trace)[i] = toRow e component logN trace i := List.getElem_ofFn _

theorem size_toRow (i : ℕ) : (toRow e component logN trace i).size = component.width :=
  Array.size_ofFn

theorem cellExpr_of_lt_fixedWidth {K' : Type} {j : ℕ} (hj : j < component.fixedWidth) :
    cellExpr (K := K') component j = .prepCur j := by
  unfold cellExpr
  cases hw : component.window with
  | none => simp only [hj, ↓reduceIte]
  | some layout =>
    have := fixedWidth_le_rowWidth hw
    simp only [show j < layout.rowWidth by omega, hj, ↓reduceIte]

theorem getD_fixedTrace {fixed : FixedColumns F} (hf : component.fixedColumns = some fixed)
    {i j : ℕ} (hi : i < 2 ^ logN) (hj : j < fixed.width) :
    (fixedTrace e component logN).getD (i * fixed.width + j) 0 =
      e ((fixed.values (UInt64.ofNat i))[j]?.getD 0) := by
  have hlt : i * fixed.width + j < 2 ^ logN * fixed.width := by
    have : (i + 1) * fixed.width ≤ 2 ^ logN * fixed.width := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    omega
  have hdiv : (i * fixed.width + j) / fixed.width = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * fixed.width + j) % fixed.width = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [fixedTrace, hf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hlt, ↓reduceDIte,
    Option.getD_some, hdiv, hmod]

/-- The rows read off a trace start with the fixed columns. -/
theorem fixedRowsMatch_toRows
    (hfixed : ∀ fixed ∈ component.fixedColumns, fixed.height.toNat = 2 ^ logN) :
    component.FixedRowsMatch (toRows e component logN trace) := by
  unfold Component.FixedRowsMatch
  cases hf : component.fixedColumns with
  | none => trivial
  | some fixed =>
    have hheight := hfixed fixed hf
    have hwidth : component.fixedWidth = fixed.width := by simp [Component.fixedWidth, hf]
    have hle : fixed.width ≤ component.width := by
      have := component.fixed_width_le_input
      have := component.circuit.size_eq
      cases hw : component.window with
      | none => simp only [hf, hw, Option.map_some, Option.getD_some, Option.map_none,
          Option.getD_none] at *; simp only [Component.width]; omega
      | some layout =>
        have := rowWidth_le_size hw
        simp only [hf, hw, Option.map_some, Option.getD_some] at *
        omega
    simp only [FixedColumns.RowsMatch]
    apply List.ext_getElem
    · simp [length_toRows, hheight]
    · intro i h1 h2
      simp only [List.length_map, length_toRows] at h1
      simp only [List.getElem_map, getElem_toRows, List.getElem_range, Function.comp_apply]
      have hsize : (fixed.values (UInt64.ofNat i)).size = fixed.width := by
        simp [FixedColumns.values]
      apply Array.ext
      · simp [size_toRow, hsize, hle]
      · intro j hj _
        simp only [Array.size_extract, size_toRow] at hj
        have hjw : j < fixed.width := by omega
        rw [Array.getElem_extract]
        simp only [Nat.zero_add, toRow, Array.getElem_ofFn]
        rw [cellExpr_of_lt_fixedWidth component (by omega)]
        simp only [Expr.eval, Lookup.generationRow, toAir, hwidth]
        rw [getD_fixedTrace e logN component hf h1 hjw, RingEquiv.symm_apply_apply,
          Array.getElem?_eq_getElem (by omega), Option.getD_some]

theorem cell_inputOf {layout : WindowLayout component.Input} (row : Array F) (j : ℕ)
    (h : j < 2 * layout.rowWidth + 3) :
    layout.cell (component.inputOf row) j h = row[j]?.getD 0 := by
  simp [WindowLayout.cell, Component.inputOf, ProvableType.toElements_fromElements, rowPrefix]

/-- The window cells of the rows read off a trace hold the next row's input and the 0/1
selectors. -/
theorem windowsMatch_toRows : component.WindowsMatch (toRows e component logN trace) := by
  unfold Component.WindowsMatch
  cases hw : component.window with
  | none => trivial
  | some layout =>
    have hsize := rowWidth_le_size hw
    intro i hi
    have hi' : i < 2 ^ logN := by rwa [length_toRows] at hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext j hj
      simp only [WindowLayout.next, WindowLayout.current, Vector.getElem_ofFn, cell_inputOf,
        getElem_toRows]
      rw [getD_toRow e logN trace component _ _ (by omega),
        getD_toRow e logN trace component _ _ (by omega), length_toRows]
      congr 1
      simp only [cellExpr, hw, show ¬ layout.rowWidth + j < layout.rowWidth by omega,
        show layout.rowWidth + j < 2 * layout.rowWidth by omega, hj,
        Nat.add_sub_cancel_left, ↓reduceIte]
      split <;> rfl
    · simp only [WindowLayout.isFirstRow, cell_inputOf, getElem_toRows]
      rw [getD_toRow e logN trace component _ _ (by omega),
        cellExpr_selectorCell (gate := .firstRow) hw rfl]
      simp only [Expr.eval, Lookup.generationRow]
      split <;> simp
    · simp only [WindowLayout.isLastRow, cell_inputOf, getElem_toRows, length_toRows]
      rw [getD_toRow e logN trace component _ _ (by omega),
        cellExpr_selectorCell (gate := .lastRow) hw rfl]
      simp only [Expr.eval, Lookup.generationRow]
      split <;> simp
    · simp only [WindowLayout.isTransition, cell_inputOf, getElem_toRows, length_toRows]
      rw [getD_toRow e logN trace component _ _ (by omega),
        cellExpr_selectorCell (gate := .transition) hw rfl]
      simp only [Expr.eval, Lookup.generationRow]
      split_ifs <;> first | omega | simp

/-- The table of a component read off a trace of `2 ^ logN` rows of its AIR, with prover data
`data`. -/
def toTable (fits : Fits (K := K) component logN) (data : ProverData F) : Table F where
  component
  table := toRows e component logN trace
  data
  uniform_width row hrow := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
    rw [getElem_toRows]
    exact size_toRow e logN trace component i
  length_le := by
    rw [length_toRows]
    calc 2 ^ logN ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) fits.height_le
      _ = UInt64.size := rfl
  fixed_rows_match := fixedRowsMatch_toRows e logN trace component fits.fixedHeight
  windows_match := windowsMatch_toRows e logN trace component

/-- If the trace's rows satisfy the component's AIR, the table's constraints hold. -/
theorem constraints_toTable {component : Component F} (hc : bridgeable component = true)
    (fits : Fits (K := K) component logN) (data : ProverData F) {publicValues : List K}
    (h : (toAir e component logN).ConstraintsVanish logN trace publicValues) :
    (toTable e logN trace component fits data).Constraints := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  have hi' : i < 2 ^ logN := by
    simpa only [toTable, length_toRows] using hi
  simp only [toTable, getElem_toRows, Table.environment]
  rw [Component.constraintsHold_iff]
  refine ⟨fun x hx => ?_, fun l hl => by simp [Bridgeable.lookups_eq_nil hc] at hl⟩
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp (Bridgeable.gated hc x hx)
  refine (eval_constraint_iff e logN trace hc fits.twoAdic publicValues hi' data hx hg).mpr ?_
  exact h _ (List.mem_map.mpr ⟨g, List.mem_filterMap.mpr ⟨x, hx, hg⟩, rfl⟩) i hi'

end Table

/-- **The transfer theorem for one component.** A trace satisfying a bridgeable component's AIR on
`2 ^ logN` rows is, read as Clean rows (`toRows`), a table of the component with consistent prover
data whose constraints hold. -/
theorem table_of_satisfied {component : Component F} (hc : bridgeable component = true)
    (fits : Fits (K := K) component logN) {publicValues : List K}
    (h : (toAir e component logN).Satisfied logN trace publicValues) :
    ∃ table : Table F, table.component = component ∧ table.table = toRows e component logN trace ∧
      table.DataConsistency ∧ table.Constraints := by
  let table := toTable e logN trace component fits (fun _ _ => #[])
  refine ⟨{ table with data := deriveProverData [table] }, rfl, rfl, ?_,
    constraints_toTable e logN trace hc fits _ h.vanish⟩
  simp [Table.DataConsistency, deriveProverData, Table.proverRows, table]

end CleanCompStark
