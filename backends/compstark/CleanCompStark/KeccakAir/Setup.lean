module

public import CleanCompStark.KeccakAir.Lowered
public import CleanCompStark.KeccakAir
public import CompStark.Complete.Quotient
public import CompStark.Sound.Calculator

/-!
# The Keccak-f STARK

The CompStark AIR of the Keccak-f component on `2 ^ logN` rows has 2633 columns, 3182 constraints
of Plonky3's degree at most 3 that read the current and the next row (`colsInWidth_toAir`), a
quotient of two chunks (`logQuotientChunks_toAir`) and degree profiles that fit them at every trace
length (`profileFits_toAir`). With FRI's parameters, it is a STARK (`setup`) whose shape the
security calculator reads (`shape_setup`).
-/

@[expose] public section

namespace CleanCompStark.KeccakAir
open Air.Flat Air.Flat.WitnessGeneration Backends CompStark CompStark.Stark CompStark.Iop
  _root_.KeccakAir

/-! ### Largest values of lists -/

section Fold
variable {α : Type} (f : α → ℕ)

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
  exact le_antisymm (Sound.foldl_max_le f _ l 0 (Nat.zero_le _) hle) ((le_foldl_max f l 0).2 y hy)

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

variable [Fact (2 ^ 16 < p)]

lemma window_component :
    (_root_.KeccakAir.component (p := p) height).window = some (Window.layout Row) := rfl

lemma degreeWeight_eq : degreeWeight (Window.layout Row).rowWidth = cellWeight 1 0 := rfl

/-- A constraint of the AIR is a gated constraint of the component, read off the trace. -/
theorem lower_of_mem {y : Expr K}
    (hy : y ∈ (toAir e (_root_.KeccakAir.component (p := p) height) logN).constraints) :
    ∃ x ∈ (_root_.KeccakAir.component (p := p) height).rowOperations.constraints, ∃ g,
      gateConstraint (some (size Row)) x = some g ∧
        (∀ j ∈ expressionCells x, j < 2 * size Row + 3) ∧
        y = gateExpr g.gate (toExpr e (_root_.KeccakAir.component (p := p) height) g.body) := by
  obtain ⟨x, hx, g, hg, rfl⟩ := (mem_toAir_constraints e).mp hy
  exact ⟨x, hx, g, hg, (admissible_component height 0 0 x hx).2.1, rfl⟩

theorem degree_le {y : Expr K}
    (hy : y ∈ (toAir e (_root_.KeccakAir.component (p := p) height) logN).constraints) :
    y.degree ≤ 3 := by
  obtain ⟨x, hx, g, hg, hcells, rfl⟩ := lower_of_mem e height logN hy
  rw [degree_lower e (window_component height) hcells hg, degreeWeight_eq]
  have := (admissible_component height 1 0 x hx).2.2
  omega

theorem exists_degree_eq :
    ∃ y ∈ (toAir e (_root_.KeccakAir.component (p := p) height) logN).constraints,
      y.degree = 3 := by
  obtain ⟨x, hx, hweight⟩ := exists_weight_eq (p := p) height
  obtain ⟨hgate, hcells, -⟩ := admissible_component height 0 0 x hx
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hgate
  refine ⟨gateExpr g.gate (toExpr e (_root_.KeccakAir.component (p := p) height) g.body),
    (mem_toAir_constraints e).mpr ⟨x, hx, g, hg, rfl⟩, ?_⟩
  rw [degree_lower e (window_component height) hcells hg, degreeWeight_eq]
  exact hweight

/-- Every constraint's degree profile `(a, b)` has `a + b ≤ 3` and `b ≤ 1`: it fits two quotient
chunks. -/
theorem profileFits_toAir :
    (toAir e (_root_.KeccakAir.component (p := p) height) logN).ProfileFits 1 := fun y hy => by
  obtain ⟨x, hx, g, hg, hcells, rfl⟩ := lower_of_mem e height logN hy
  obtain ⟨hsum, htransition⟩ := degProfile_lower e (window_component height) hcells hg
  have := (admissible_component height 1 1 x hx).2.2
  have hw : cellWeight 1 1 = fun _ => 1 := funext fun _ => ite_self 1
  simp only [hw] at this
  simp only [pow_one]
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
  simp only [toAir, gatedConstraints, List.length_map, hwindow]
  rw [length_filterMap_of_isSome _ _ fun x hx => (admissible_component height 0 0 x hx).1,
    rowOperations_component]
  exact length_main _ _

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

theorem degreeFits_toAir : (A).DegreeFits logN := by
  unfold Air.DegreeFits
  rw [logQuotientChunks_toAir]
  exact Air.degreeFitsAt_of_profileFits _ _ _ (profileFits_toAir e height logN)

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
      degreeFits := degreeFits_toAir koalaBear _ logN
      twoAdic := by rw [KoalaBear.twoAdicity_eq]; exact h.2.1
      chunksFit := by rw [logQuotientChunks_toAir]; exact h.1
      folds := h.2.2.1
      finalPolyFits := Nat.le_of_lt h.2.2.2.1
      queries := h.2.2.2.2.1
      blowup := h.1 }
  folds := h.2.2.2.1
  capFits := h.2.2.2.2.2

variable (params : Fri.Params) (logN : ℕ) (h : ParamsFit params logN)

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

/-- The calculator's shape of the STARK: `3182` constraints, the identity degree `3 n`, `5274`
opened words, no lookups. -/
theorem shape_setup : (setup params logN h).shape = ⟨3182, 2 ^ logN * 3, 5274, false, logN⟩ := by
  rw [Sound.shape_eq_of_profileFits _ (by
      change (toAir koalaBear (component logN) logN).ProfileFits
        ((toAir koalaBear (component logN) logN).logQuotientChunks logN)
      rw [logQuotientChunks_toAir]
      exact profileFits_toAir koalaBear _ logN), chunks_setup, numOpened_setup]
  change Iop.Shape.mk (toAir koalaBear (component logN) logN).constraints.length _ _ _ _ = _
  rw [length_toAir]
  rfl

end Stark

end CleanCompStark.KeccakAir
