module

public import CleanCompStark.KeccakAir.Degree
public import CompStark.SoundnessError

/-!
# The Keccak-f AIR's numbers

The shape of the CompStark AIR of the Keccak-f component (`toAir`), which the STARK's validity
and the security calculator read: 2633 columns, 3182 constraints that read the current and the
next row, Plonky3's constraint degree 3 and so a quotient of two chunks, and degree profiles that
fit two chunks at every trace length.

A lowered constraint is a Clean constraint's body under CompStark's selector
(`mem_toAir_constraints`); its degree is a weight of the Clean constraint (`degree_lower`), and so
is the sum of its degree profile's entries (`degProfile_lower`); the weights of the component's
constraints are bounded by `weights_le`.
-/

@[expose] public section

namespace CleanCompStark.KeccakAir
open Air.Flat Air.Flat.WitnessGeneration Backends CompStark CompStark.Stark _root_.KeccakAir

/-! ### Lowered constraints of a two-row component -/

section Lowering
variable {F : Type} [FiniteField F] {K : Type}

theorem mem_toAir_constraints [BaseField K] (e : F ≃+* K) {component : Component F} {logN : ℕ}
    {y : Expr K} :
    y ∈ (toAir e component logN).constraints ↔
      ∃ x ∈ component.rowOperations.constraints, ∃ g,
        gateConstraint (component.window.map (·.rowWidth)) x = some g ∧
          y = gateExpr g.gate (toExpr e component g.body) := by
  simp only [toAir, gatedConstraints, List.mem_map, List.mem_filterMap]
  constructor
  · rintro ⟨g, ⟨x, hx, hg⟩, rfl⟩
    exact ⟨x, hx, g, hg, rfl⟩
  · rintro ⟨x, hx, g, hg, rfl⟩
    exact ⟨g, ⟨x, hx, hg⟩, rfl⟩

variable {component : Component F} {layout : WindowLayout component.Input}

/-- A cell of a window's rows is a column of the current or the next row, of the trace or the
preprocessed trace. -/
theorem cellExpr_of_lt (hw : component.window = some layout) {j : ℕ}
    (hj : j < 2 * layout.rowWidth) :
    ∃ c, cellExpr (K := K) component j = .cur c ∨ cellExpr (K := K) component j = .next c ∨
      cellExpr (K := K) component j = .prepCur c ∨ cellExpr (K := K) component j = .prepNext c := by
  unfold cellExpr
  rw [hw]
  dsimp only
  split_ifs <;> first
    | exact ⟨_, Or.inl rfl⟩ | exact ⟨_, Or.inr (Or.inl rfl)⟩
    | exact ⟨_, Or.inr (Or.inr (Or.inl rfl))⟩ | exact ⟨_, Or.inr (Or.inr (Or.inr rfl))⟩

variable [BaseField K] (e : F ≃+* K)

theorem degree_toExpr (hw : component.window = some layout) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, j < 2 * layout.rowWidth) →
      (toExpr e component x).degree = weight (fun _ => 1) x
  | .var v, h => by
    obtain ⟨c, hc | hc | hc | hc⟩ :=
      cellExpr_of_lt (K := K) hw (h v.index (by simp [expressionCells]))
    all_goals simp only [toExpr, hc, Expr.degree, weight]
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [toExpr, degree_addExpr, Expr.degree, weight,
      degree_toExpr hw a fun j hj => h j (Or.inl hj),
      degree_toExpr hw b fun j hj => h j (Or.inr hj)]

/-- A body reading the window's rows has the degree profile `(w, 0)`, `w` its weight with every
cell weighing `1`. -/
theorem degProfile_toExpr (hw : component.window = some layout) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, j < 2 * layout.rowWidth) →
      (toExpr e component x).degProfile = (weight (fun _ => 1) x, 0)
  | .var v, h => by
    obtain ⟨c, hc | hc | hc | hc⟩ :=
      cellExpr_of_lt (K := K) hw (h v.index (by simp [expressionCells]))
    all_goals simp only [toExpr, hc, Expr.degProfile, weight]
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [toExpr, degProfile_addExpr, Expr.degProfile, weight,
      degProfile_toExpr hw a fun j hj => h j (Or.inl hj),
      degProfile_toExpr hw b fun j hj => h j (Or.inr hj), Nat.max_self, Nat.add_zero]

/-- The weights of Plonky3's degree: `1` per cell, but `0` for the transition selector. -/
def degreeWeight (w : ℕ) (j : ℕ) : ℕ := if j = 2 * w + 2 then 0 else 1

theorem degree_lower (hw : component.window = some layout) {x : Expression F}
    {g : GatedConstraint F} (hcells : ∀ j ∈ expressionCells x, j < 2 * layout.rowWidth + 3)
    (hg : gateConstraint (some layout.rowWidth) x = some g) :
    (gateExpr g.gate (toExpr e component g.body)).degree =
      weight (degreeWeight layout.rowWidth) x := by
  obtain ⟨hbody, hweight⟩ := gateConstraint_weight hcells hg
  rw [hweight, weight_congr (degreeWeight layout.rowWidth) (fun _ => 1) g.body fun j hj => by
    have := hbody j hj
    simp only [degreeWeight]
    split_ifs <;> omega, ← degree_toExpr e hw g.body hbody]
  cases hgate : g.gate <;> simp [gateExpr, gateWeight, degreeWeight, Expr.degree]

/-- A lowered constraint's degree profile `(a, b)`: `a + b` is the Clean constraint's weight with
every cell weighing `1`, and `b ≤ 1`, the transition selector's share. -/
theorem degProfile_lower (hw : component.window = some layout) {x : Expression F}
    {g : GatedConstraint F} (hcells : ∀ j ∈ expressionCells x, j < 2 * layout.rowWidth + 3)
    (hg : gateConstraint (some layout.rowWidth) x = some g) :
    (gateExpr g.gate (toExpr e component g.body)).degProfile.1 +
        (gateExpr g.gate (toExpr e component g.body)).degProfile.2 = weight (fun _ => 1) x ∧
      (gateExpr g.gate (toExpr e component g.body)).degProfile.2 ≤ 1 := by
  obtain ⟨hbody, hweight⟩ := gateConstraint_weight hcells hg
  rw [hweight]
  have hprofile := degProfile_toExpr e hw g.body hbody
  cases g.gate <;>
    simp only [gateExpr, gateWeight, HMul.hMul, Mul.mul, Expr.degProfile, hprofile] <;> omega

theorem colsBelow_toExpr (hw : component.window = some layout) (logN : ℕ) :
    ∀ y : Expression F, (∀ j ∈ expressionCells y, j < 2 * layout.rowWidth) →
      (toExpr e component y).colsBelow (toAir e component logN).width
        (toAir e component logN).mainNextWidth (toAir e component logN).preprocessedWidth
        (toAir e component logN).preprocessedNextWidth
  | .var v, h => by
    have hj := h v.index (by simp [expressionCells])
    have hsize := rowWidth_le_size hw
    have hfixed := fixedWidth_le_rowWidth hw
    have hwidth : (toAir e component logN).width = component.width - component.fixedWidth -
        (layout.rowWidth + 3) := by
      simp only [toAir, traceWidth, Component.windowWidth, hw, Option.map_some, Option.getD_some,
        WindowLayout.windowWidth]
    have hnext : (toAir e component logN).mainNextWidth = (toAir e component logN).width := rfl
    have hprep : (toAir e component logN).preprocessedWidth = component.fixedWidth := rfl
    simp only [toExpr, cellExpr, hw]
    split_ifs with h1 h2 h2
    · simp only [Expr.colsBelow, hprep, decide_eq_true_eq]
      omega
    · simp only [Expr.colsBelow, hwidth, decide_eq_true_eq]
      omega
    · have hpos : 0 < component.fixedWidth := by omega
      simp only [Expr.colsBelow, Air.preprocessedNextWidth, Air.opensPreprocessedNext, hprep,
        hpos, decide_true, Bool.true_and, decide_eq_true_eq]
      exact h2
    · simp only [Expr.colsBelow, hnext, hwidth, decide_eq_true_eq]
      omega
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [toExpr, colsBelow_addExpr, Expr.colsBelow, Bool.and_eq_true]
    exact ⟨colsBelow_toExpr hw logN a fun j hj => h j (Or.inl hj),
      colsBelow_toExpr hw logN b fun j hj => h j (Or.inr hj)⟩

theorem colsBelow_lower (hw : component.window = some layout) (logN : ℕ) {x : Expression F}
    {g : GatedConstraint F} (hcells : ∀ j ∈ expressionCells x, j < 2 * layout.rowWidth + 3)
    (hg : gateConstraint (some layout.rowWidth) x = some g) :
    (gateExpr g.gate (toExpr e component g.body)).colsBelow (toAir e component logN).width
      (toAir e component logN).mainNextWidth (toAir e component logN).preprocessedWidth
      (toAir e component logN).preprocessedNextWidth := by
  obtain ⟨hbody, -⟩ := gateConstraint_weight hcells hg
  have := colsBelow_toExpr e hw logN g.body hbody
  cases g.gate <;> simp only [gateExpr, HMul.hMul, Mul.mul, Expr.colsBelow, Bool.true_and, this]

end Lowering

end CleanCompStark.KeccakAir
