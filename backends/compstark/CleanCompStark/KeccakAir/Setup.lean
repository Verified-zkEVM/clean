module

public import CleanCompStark.KeccakAir.Lowered
public import CleanCompStark.KeccakAir
public import CompStark.SecurityCalculator

/-!
# The Keccak-f STARK

The CompStark AIR of the Keccak-f component on `2 ^ logN` rows has 2633 columns, 3182 constraints
of Plonky3's degree at most 3 that read the current and the next row (`colsInWidth`), a quotient of
two chunks (`logQuotientChunks_eq`) and CompStark's degree bound below `3 n` (`degreeFits`). With
FRI's parameters, it is a STARK (`setup`) whose numbers the security calculator reads:
`numConstraints_setup`, `identityDegree_setup`, `numOpened_setup`.
-/

@[expose] public section

namespace CleanCompStark.KeccakAir
open Air.Flat Air.Flat.WitnessGeneration Backends CompStark CompStark.Stark CompStark.Iop
  _root_.KeccakAir

/-! ### Largest values of lists -/

section Fold
variable {α : Type} (f : α → ℕ)

lemma foldl_max_le (k : ℕ) : ∀ (l : List α) (start : ℕ), start ≤ k → (∀ y ∈ l, f y ≤ k) →
    l.foldl (fun m c => max m (f c)) start ≤ k
  | [], _, hm, _ => hm
  | y :: l, _, hm, h => foldl_max_le k l _ (max_le hm (h y (List.mem_cons_self ..)))
      fun z hz => h z (List.mem_cons_of_mem _ hz)

lemma le_foldl_max : ∀ (l : List α) (m : ℕ), m ≤ l.foldl (fun m c => max m (f c)) m ∧
    ∀ y ∈ l, f y ≤ l.foldl (fun m c => max m (f c)) m
  | [], _ => ⟨le_rfl, fun _ h => nomatch h⟩
  | y :: l, m => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max m (f y))
    refine ⟨(le_max_left _ _).trans h1, fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact (le_max_right _ _).trans h1
    · exact h2 z hz

/-- The largest value of a list, from `0`, is `k` if every value is at most `k` and one is `k`. -/
lemma foldl_max_eq (l : List α) (k : ℕ) (hle : ∀ y ∈ l, f y ≤ k) (hex : ∃ y ∈ l, f y = k) :
    l.foldl (fun m c => max m (f c)) 0 = k := by
  obtain ⟨y, hy, rfl⟩ := hex
  exact le_antisymm (foldl_max_le f _ l 0 (Nat.zero_le _) hle) ((le_foldl_max f l 0).2 y hy)

lemma length_filterMap_of_isSome {β : Type} (g : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, (g x).isSome) → (l.filterMap g).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self ..))
    rw [List.filterMap_cons_some hy, List.length_cons, List.length_cons,
      length_filterMap_of_isSome g l fun z hz => h z (List.mem_cons_of_mem _ hz)]

end Fold

section Air
variable {p : ℕ} [Fact p.Prime] {K : Type} [BaseField K] (e : _root_.F p ≃+* K)
  (height : UInt64) (logN : ℕ)

/-- The weights of the component's constraints are the constraints of the cells' weights: `a`
for the cells of the rows and the first- and last-row selectors, `b` for the transition
selector. -/
theorem weights_vars (a b : ℕ) :
    (constraints (vars (p := p))).map
        (fun x => (⟨weight (fun j => if j = 2 * size Row + 2 then b else a) x⟩ : Deg)) =
      constraints (degWindow (vars (p := p)).current (vars (p := p)).next a b) := by
  rw [(isHom_weight _).map_constraints]
  have h := varWindow_vars (p := p)
  have hcell (j : ℕ) (hj : j < 2 * size Row) :
      (⟨weight (fun j => if j = 2 * size Row + 2 then b else a)
        (.var ⟨j⟩ : Expression (_root_.F p))⟩ : Deg) = ⟨a⟩ := by
    simp only [weight, Deg.mk.injEq]
    split_ifs <;> omega
  have h1 : 2 * size Row ≠ 2 * size Row + 2 := by omega
  have h2 : 2 * size Row + 1 ≠ 2 * size Row + 2 := by omega
  simp only [mapWindow, degWindow, h.isFirstRow, h.isLastRow, h.isTransition, weight, h1, h2,
    ↓reduceIte]
  have hrow (row : Row (Expression (_root_.F p)))
      (hrow : ∀ x ∈ (toElements row).toList, ∃ j < 2 * size Row, x = .var ⟨j⟩) :
      row.map (fun x => (⟨weight (fun j => if j = 2 * size Row + 2 then b else a) x⟩ : Deg)) =
        row.map fun _ => ⟨a⟩ := by
    refine Row.map_congr _ fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := hrow x hx
    exact hcell j hj
  rw [hrow _ fun x hx => (h.current x hx).imp fun j ⟨hj, hx⟩ => ⟨by omega, hx⟩,
    hrow _ fun x hx => (h.next x hx).imp' (size Row + ·) fun j ⟨hj, hx⟩ => ⟨by omega, hx⟩]

variable [Fact (2 ^ 16 < p)]

lemma window_component :
    (_root_.KeccakAir.component (p := p) height).window = some (Window.layout Row) := rfl

/-- A constraint of the AIR is a gated constraint of the component, read off the trace. -/
theorem lower_of_mem {y : Expr K}
    (hy : y ∈ (toAir e (_root_.KeccakAir.component (p := p) height) logN).constraints) :
    ∃ x ∈ constraints (vars (p := p)), ∃ g,
      gateConstraint (some (size Row)) x = some g ∧
        (∀ j ∈ expressionCells x, j < 2 * size Row + 3) ∧
        y = gateExpr g.gate (toExpr e (_root_.KeccakAir.component (p := p) height) g.body) := by
  obtain ⟨x, hx, g, hg, rfl⟩ := (mem_toAir_constraints e).mp hy
  rw [rowOperations_component, constraints_map_assert] at hx
  exact ⟨x, hx, g, hg, (constraints_varWindow varWindow_vars x hx).2, rfl⟩

theorem degree_le {y : Expr K}
    (hy : y ∈ (toAir e (_root_.KeccakAir.component (p := p) height) logN).constraints) :
    y.degree ≤ 3 := by
  obtain ⟨x, hx, g, hg, hcells, rfl⟩ := lower_of_mem e height logN hy
  rw [degree_lower e (window_component height) hcells hg]
  have hmem := List.mem_map_of_mem
    (f := fun x => (⟨weight (fun j => if j = 2 * size Row + 2 then 0 else 1) x⟩ : Deg)) hx
  rw [weights_vars] at hmem
  have := weights_le _ _ 1 0 _ hmem
  simp only at this
  have hw : degreeWeight (Window.layout Row).rowWidth =
      fun j => if j = 2 * size Row + 2 then 0 else 1 := rfl
  rw [hw]
  omega

theorem exists_degree_eq :
    ∃ y ∈ (toAir e (_root_.KeccakAir.component (p := p) height) logN).constraints,
      y.degree = 3 := by
  obtain ⟨d, hd, hval⟩ := exists_weight_eq (vars (p := p)).current (vars (p := p)).next 1 0
  rw [← weights_vars] at hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
  have hgate := constraints_varWindow varWindow_vars x hx
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hgate.1
  refine ⟨gateExpr g.gate (toExpr e (_root_.KeccakAir.component (p := p) height) g.body),
    (mem_toAir_constraints e).mpr ⟨x, ?_, g, hg, rfl⟩, ?_⟩
  · rw [rowOperations_component, constraints_map_assert]
    exact hx
  · rw [degree_lower e (window_component height) hgate.2 hg]
    exact hval

theorem degBound_le (n : ℕ) (hn : 2 ≤ n) (pd : ℕ → ℕ) {y : Expr K}
    (hy : y ∈ (toAir e (_root_.KeccakAir.component (p := p) height) logN).constraints) :
    y.degBound n pd ≤ 3 * (n - 1) := by
  obtain ⟨x, hx, g, hg, hcells, rfl⟩ := lower_of_mem e height logN hy
  rw [degBound_lower e (window_component height) n pd hcells hg]
  have hmem := List.mem_map_of_mem
    (f := fun x => (⟨weight (fun j => if j = 2 * size Row + 2 then 1 else n - 1) x⟩ : Deg)) hx
  rw [weights_vars] at hmem
  have := weights_le _ _ (n - 1) 1 _ hmem
  simp only at this
  have hw : boundWeight (Window.layout Row).rowWidth n =
      fun j => if j = 2 * size Row + 2 then 1 else n - 1 := rfl
  rw [hw]
  omega

local notation "A" => toAir e (_root_.KeccakAir.component (p := p) height) logN

theorem size_row : size Row = 2633 := rfl

theorem width_toAir : (A).width = size Row := by
  have hlocal : (_root_.KeccakAir.component (p := p) height).circuit.localLength
      (varFromOffset (Window Row) 0) = 0 := rfl
  have hwindow : size (Window Row) = 2 * size Row + 3 := (Window.layout Row).size_eq
  have hfixed : (_root_.KeccakAir.component (p := p) height).fixedWidth = 0 := rfl
  have hwidth : (_root_.KeccakAir.component (p := p) height).windowWidth = size Row + 3 := rfl
  show (_root_.KeccakAir.component (p := p) height).circuit.size - _ - _ = _
  rw [GeneralFormalCircuit.size_eq, hfixed, hwidth]
  change size (Window Row) + (_root_.KeccakAir.component (p := p) height).circuit.localLength
    (varFromOffset (Window Row) 0) - 0 - (size Row + 3) = size Row
  rw [hlocal]
  omega

theorem length_toAir : (A).constraints.length = 3182 := by
  have hwindow : (_root_.KeccakAir.component (p := p) height).window.map (·.rowWidth) =
      some (size Row) := rfl
  simp only [toAir, gatedConstraints, List.length_map, hwindow, rowOperations_component,
    constraints_map_assert]
  rw [length_filterMap_of_isSome _ _ fun x hx => (constraints_varWindow varWindow_vars x hx).1]
  exact length_constraints _

theorem maxDegree_toAir : (A).maxDegree = 3 :=
  foldl_max_eq _ _ 3 (fun _ hy => degree_le e height logN hy) (exists_degree_eq e height logN)

theorem logQuotientChunks_toAir : (A).logQuotientChunks logN = 1 := by
  have hperiodic : (A).periodic = [] := rfl
  unfold Air.logQuotientChunks Air.constraintDegree
  simp only [hperiodic, ↓reduceIte, maxDegree_toAir]
  rfl

theorem colsInWidth_toAir : (A).ColsInWidth := fun _ hy => by
  obtain ⟨x, -, g, hg, hcells, rfl⟩ := lower_of_mem e height logN hy
  exact colsBelow_lower e (window_component height) logN hcells hg

theorem degreeFits_toAir (hlogN : 1 ≤ logN) : (A).DegreeFits logN := by
  unfold Air.DegreeFits Air.DegreeFitsAt
  rw [logQuotientChunks_toAir]
  intro c hc
  have h2 : 2 ≤ 2 ^ logN := (Nat.pow_le_pow_right (by norm_num) hlogN : 2 ^ 1 ≤ 2 ^ logN)
  have := degBound_le e height logN (2 ^ logN) h2 ((A).periodicDegree (2 ^ logN)) hc
  rw [Nat.pow_succ]
  omega

theorem preprocessedSize_toAir : (A).preprocessed.size = 2 ^ logN * (A).preprocessedWidth := by
  simp only [toAir, fixedTrace, _root_.KeccakAir.component, Array.size_ofFn]
  rfl

end Air

/-! ### The STARK -/

section Stark
open KoalaBear

/-- FRI's parameters fit the Keccak-f AIR on `2 ^ logN` rows over KoalaBear: the extended domain
is two-adic, the quotient's two chunks fit the blowup, FRI folds at least once and queries, and
the Merkle cap fits. -/
def ParamsFit (params : Fri.Params) (logN : ℕ) : Prop :=
  1 ≤ params.logBlowup ∧ logN + params.logBlowup ≤ 24 ∧ 0 < params.maxLogArity ∧
    params.logFinalPolyLen < logN ∧ 0 < params.numQueries ∧
    params.capHeight ≤ logN + params.logBlowup - params.maxLogArity

instance (params : Fri.Params) (logN : ℕ) : Decidable (ParamsFit params logN) := by
  unfold ParamsFit; infer_instance

/-- The STARK of the Keccak-f component on `2 ^ logN` rows over KoalaBear's quartic extension, with
FRI's parameters `params`. -/
def setup (params : Fri.Params) (logN : ℕ) (h : ParamsFit params logN) :
    Iop.Setup KoalaBear.Fast.Ext4 where
  params
  air := toAir koalaBear (component logN) logN
  logN
  valid :=
    { colsInWidth := colsInWidth_toAir koalaBear _ logN
      preprocessedSize := preprocessedSize_toAir koalaBear _ logN
      periodicFits := rfl
      degreeFits := degreeFits_toAir koalaBear _ logN (Nat.lt_of_le_of_lt (Nat.zero_le _) h.2.2.2.1)
      twoAdic := by rw [KoalaBear.twoAdicity_eq]; exact h.2.1
      chunksFit := by rw [logQuotientChunks_toAir]; exact h.1
      folds := h.2.2.1
      finalPolyFits := Nat.le_of_lt h.2.2.2.1
      queries := h.2.2.2.2.1
      blowup := h.1 }
  folds := h.2.2.2.1
  capFits := h.2.2.2.2.2

variable (params : Fri.Params) (logN : ℕ) (h : ParamsFit params logN)

theorem numConstraints_setup : (setup params logN h).numConstraints = 3182 := by
  rw [Setup.numConstraints_nil]
  exact length_toAir koalaBear _ logN

theorem chunks_setup : (setup params logN h).chunks = 2 := by
  rw [Setup.chunks_nil]
  simp only [setup, logQuotientChunks_toAir]
  rfl

theorem width_setup : (setup params logN h).air.width = 2633 :=
  (width_toAir koalaBear _ logN).trans size_row

theorem numOpened_setup : (setup params logN h).numOpened = 5274 := by
  have hnext : (setup params logN h).air.mainNextWidth = (setup params logN h).air.width := rfl
  have hprep : (setup params logN h).air.preprocessedWidth = 0 := rfl
  have hprepNext : (setup params logN h).air.preprocessedNextWidth = 0 := rfl
  have hd : Challenge.d KoalaBear.Fast.Ext4 = 4 := rfl
  rw [Setup.numOpened_nil, chunks_setup, hnext, hprep, hprepNext, hd, width_setup]

theorem identityDegree_setup : (setup params logN h).identityDegree = 3 * 2 ^ logN := by
  rw [Setup.identityDegree_nil, chunks_setup]
  have hle := foldl_max_le (fun c : Expr KoalaBear.Fast.Field => c.degBound (2 ^ logN + 1)
    ((setup params logN h).air.periodicDegree (2 ^ logN))) (3 * 2 ^ logN)
    (setup params logN h).air.constraints 0 (Nat.zero_le _) fun c hc => by
      have := degBound_le koalaBear _ logN (2 ^ logN + 1)
        (by have := Nat.one_le_two_pow (n := logN); omega)
        ((setup params logN h).air.periodicDegree (2 ^ logN)) hc
      omega
  simp only [Setup.n] at hle ⊢
  rw [Nat.mul_comm]
  exact max_eq_right hle

end Stark

end CleanCompStark.KeccakAir
