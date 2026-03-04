/-
Predicates and lemmas for proving that circuit outputs consist of fresh, distinct variables.
Used primarily by `InductiveTable.outputFreshVars`.
-/
import Clean.Circuit.Provable

set_option linter.unusedSectionVars false

variable {F : Type} [Field F]

namespace Var

/-- All expression components are bare `.var v` with distinct indices in `[lower, upper)`. -/
def IsFreshVars {α : TypeMap} [ProvableType α] (v : Var α F) (lower upper : ℕ) : Prop :=
  let elems := toVars v
  (∀ i (hi : i < size α), ∃ w, elems[i] = .var w ∧ w.index ≥ lower ∧ w.index < upper) ∧
  (∀ i j (hi : i < size α) (hj : j < size α), i ≠ j →
    ∀ v w, elems[i] = .var v → elems[j] = .var w → v.index ≠ w.index)

/-- `varFromOffset α base` is always fresh in `[base, base + size α)`. -/
theorem isFreshVars_varFromOffset (α : TypeMap) [ProvableType α] (base : ℕ) :
    IsFreshVars (F := F) (varFromOffset α base) base (base + size α) := by
  simp only [IsFreshVars, toVars, varFromOffset, fromVars, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange]
  constructor
  · intro i hi
    exact ⟨⟨base + i⟩, rfl, by dsimp; omega, by dsimp; omega⟩
  · intro i j hi hj hij v w hv hw
    simp only [Expression.var.injEq] at hv hw
    subst hv; subst hw; dsimp; omega

/-- Weaken bounds of `IsFreshVars`. -/
theorem IsFreshVars.weaken {α : TypeMap} [ProvableType α] {v : Var α F} {l u l' u' : ℕ}
    (h : IsFreshVars v l u) (hl : l' ≤ l) (hu : u ≤ u') : IsFreshVars v l' u' :=
  ⟨fun i hi => let ⟨w, hw, hge, hlt⟩ := h.1 i hi; ⟨w, hw, by omega, by omega⟩, h.2⟩

/-- `IsFreshVars` for a `ProvableVector` when each component is `varFromOffset` at non-overlapping bases. -/
theorem isFreshVars_provableVector
    {α : TypeMap} [inst : NonEmptyProvableType α] {n : ℕ}
    (v : Vector (Var α F) n) (bases : Fin n → ℕ) (lower upper : ℕ)
    (h_eq : ∀ j : Fin n, v[j.val] = varFromOffset α (bases j))
    (h_lower : ∀ j, bases j ≥ lower)
    (h_upper : ∀ j, bases j + size α ≤ upper)
    (h_disjoint : ∀ i j : Fin n, i ≠ j →
       bases i + size α ≤ bases j ∨ bases j + size α ≤ bases i) :
    IsFreshVars (α := ProvableVector α n) v lower upper := by
  have h_size_pos : 0 < size α := inst.nonempty
  have h_pv_size : size (ProvableVector α n) = n * size α := by simp [size]
  constructor
  · intro i hi
    have h_i_bound : i < n * size α := by omega
    have hj : i / size α < n := by
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact h_i_bound
    simp only [toVars, ProvableVector.instance, toElements,
      Vector.getElem_flatten, Vector.getElem_map]
    have h_comp := h_eq ⟨i / size α, hj⟩
    simp only [h_comp, varFromOffset, fromVars, ProvableType.toElements_fromElements,
      Vector.getElem_mapRange]
    refine ⟨⟨bases ⟨i / size α, hj⟩ + i % size α⟩, rfl, ?_, ?_⟩
    · have := h_lower ⟨i / size α, hj⟩; dsimp; omega
    · have := h_upper ⟨i / size α, hj⟩; have := Nat.mod_lt i h_size_pos; dsimp; omega
  · intro i₁ i₂ hi₁ hi₂ hne v₁ v₂ hv₁ hv₂
    have h_i₁_bound : i₁ < n * size α := by omega
    have h_i₂_bound : i₂ < n * size α := by omega
    have hj₁ : i₁ / size α < n := by
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact h_i₁_bound
    have hj₂ : i₂ / size α < n := by
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact h_i₂_bound
    simp only [toVars, ProvableVector.instance, toElements,
      Vector.getElem_flatten, Vector.getElem_map] at hv₁ hv₂
    have h_comp₁ := h_eq ⟨i₁ / size α, hj₁⟩
    have h_comp₂ := h_eq ⟨i₂ / size α, hj₂⟩
    simp only [h_comp₁, varFromOffset, fromVars, ProvableType.toElements_fromElements,
      Vector.getElem_mapRange, Expression.var.injEq] at hv₁
    simp only [h_comp₂, varFromOffset, fromVars, ProvableType.toElements_fromElements,
      Vector.getElem_mapRange, Expression.var.injEq] at hv₂
    subst hv₁; subst hv₂
    show bases ⟨i₁ / size α, hj₁⟩ + i₁ % size α ≠ bases ⟨i₂ / size α, hj₂⟩ + i₂ % size α
    by_cases hj : i₁ / size α = i₂ / size α
    · have hbase_eq : bases ⟨i₁ / size α, hj₁⟩ = bases ⟨i₂ / size α, hj₂⟩ := by
        congr 1; exact Fin.ext hj
      have h₁ := Nat.div_add_mod i₁ (size α)
      have h₂ := Nat.div_add_mod i₂ (size α)
      have hprod : size α * (i₁ / size α) = size α * (i₂ / size α) := by rw [hj]
      omega
    · have hd := h_disjoint ⟨i₁ / size α, hj₁⟩ ⟨i₂ / size α, hj₂⟩
        (by intro h; apply hj; exact congrArg Fin.val h)
      have hk₁ := Nat.mod_lt i₁ h_size_pos
      have hk₂ := Nat.mod_lt i₂ h_size_pos
      omega

/-- Derive `outputFreshVars` from `IsFreshVars`. Since the shapes match exactly, this is trivial. -/
theorem outputFreshVars_of_isFreshVars
    {State : TypeMap} [ProvableType State]
    {output : Var State F} {lower upper : ℕ}
    (h : IsFreshVars output lower upper) :
    (∀ (i : ℕ) (hi : i < size State),
      ∃ (v : Variable F), (toVars output)[i] = .var v ∧ v.index ≥ lower ∧ v.index < upper) ∧
    (∀ (i j : ℕ) (hi : i < size State) (hj : j < size State), i ≠ j →
      ∀ (v w : Variable F), (toVars output)[i] = .var v → (toVars output)[j] = .var w →
        v.index ≠ w.index) :=
  h

/-- `Vector.getElem_append` variant for `Vector.append` (method syntax) which may not
    match the `++` pattern used by the standard lemma. -/
theorem getElem_append_vec {α : Type*} {n m i : ℕ} (xs : Vector α n) (ys : Vector α m)
    (hi : i < n + m) :
    (Vector.append xs ys)[i] = if h : i < n then xs[i] else ys[i - n] :=
  Vector.getElem_append hi

/-- Prove `IsFreshVars` when each element of `toVars v` equals `.var ⟨base + i⟩`. -/
theorem isFreshVars_of_elems_eq
    {S : TypeMap} [ProvableType S]
    {v : Var S F} {base lower upper : ℕ}
    (elems_eq : ∀ (i : ℕ) (hi : i < size S), (toVars v)[i] = .var ⟨base + i⟩)
    (h_lower : lower ≤ base)
    (h_upper : base + size S ≤ upper) :
    IsFreshVars v lower upper := by
  constructor
  · intro i hi
    refine ⟨⟨base + i⟩, elems_eq i hi, ?_, ?_⟩ <;> dsimp <;> omega
  · intro i j hi hj hij w₁ w₂ hw₁ hw₂
    have := (elems_eq i hi).symm.trans hw₁
    have := (elems_eq j hj).symm.trans hw₂
    simp only [Expression.var.injEq] at *
    subst_vars; dsimp; omega

end Var
