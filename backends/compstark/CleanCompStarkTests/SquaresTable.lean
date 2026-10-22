module

public import CleanCompStark
public import Clean.Examples.SquaresTable.Ensemble
public import CompStark.Plonky3.Prover
public import CompStark.BabyBear.Poseidon2
public import CompStark.BabyBear.Challenge

-- `#eval` and `#guard` run compiled code from these modules.
public meta import CleanCompStark
public meta import Clean.Examples.SquaresTable.Ensemble
public meta import CompStark.Plonky3.Prover
public meta import CompStark.BabyBear.Poseidon2
public meta import CompStark.BabyBear.Challenge

@[expose] public section

namespace CleanCompStarkTests.SquaresTable
open CleanCompStark CompStark CompStark.Stark Air.Flat

abbrev K : Type := _root_.BabyBear.Fast.Field
local notation "EF" => _root_.BabyBear.Fast.Ext4
abbrev p : ℕ := _root_.BabyBear.fieldSize

def component : Component (F p) := _root_.SquaresTable.component 8

theorem bridgeable_component : bridgeable component = true := by decide +kernel

/-! ### Proving and verifying a generated table -/

/-- The rows Clean generates for the public counter `7` and square `49`. -/
def rows : List (Array (F p)) :=
  match _root_.SquaresTable.generate (p := p) 8 (7, 49) with
  | .ok witness => (witness.tables.head?.map (·.table)).getD []
  | .error _ => []

def trace : Array K := toTrace babyBear component rows

def air : Air K := toAir babyBear component 3

/-- FRI with blowup `2`, folding by arity `2` to a constant, and `8` queries. -/
def params : Fri.Params := ⟨1, 0, 1, 8, 0, 0, 0, 0, 0⟩

#guard rows.length == 8 && air.width == 3 && trace.size == 8 * 3
#guard toRows babyBear component 3 trace == rows
#guard verify params air (setup params air 3) (prove EF params air 3 trace []) [] matches .ok ()

/-- The trace with the square of row `5` changed. -/
def tampered : Array K := trace.modify (5 * 3 + 1) (· + 1)

#guard verify params air (setup params air 3) (prove EF params air 3 tampered []) [] matches .error _

/-! ### Soundness -/

/-- The STARK of the squares table on `8` rows. -/
def setup : Iop.Setup EF where
  params := params
  air := air
  logN := 3
  valid :=
    { colsInWidth := by unfold Air.ColsInWidth; decide +kernel
      preprocessedSize := by decide +kernel
      periodicFits := rfl
      degreeFits := by unfold Air.DegreeFits Air.DegreeFitsAt; decide +kernel
      twoAdic := by decide
      chunksFit := by decide +kernel
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
  folds := by decide

/-- Every row of a squares table holds the square of its counter. -/
def SquaresHeld (rows : List (Array (F p))) : Prop :=
  ∀ row ∈ rows, row[1]?.getD 0 = row[0]?.getD 0 * row[0]?.getD 0

theorem tableSound (height : UInt64) :
    TableSound (_root_.SquaresTable.component (p := p) height) SquaresHeld := by
  rintro ⟨component', rows, data, uniform_width, length_le, fixed_rows_match, windows_match⟩
    hcomponent consistent constraints row hrow
  subst hcomponent
  have hguarantees : Table.Guarantees
      ⟨_, rows, data, uniform_width, length_le, fixed_rows_match, windows_match⟩ := by
    intro row _
    rw [Component.guarantees_iff]
    intro interaction hinteraction
    simp [circuit_norm, _root_.SquaresTable.component, _root_.SquaresTable.step] at hinteraction
    subst hinteraction
    simp [AbstractInteraction.Guarantees, circuit_norm]
  have hspec := (Table.weakSoundness consistent (fun _ _ => trivial) constraints hguarantees).1
    row hrow
  simp [circuit_norm, Component.Spec, _root_.SquaresTable.component, _root_.SquaresTable.step,
    Table.environment] at hspec
  simp only [valueFromOffset, explicit_provable_type, circuit_norm] at hspec
  set window : Window SquaresTable.Row (F p) :=
    fromElements (Vector.mapRange (size (Window SquaresTable.Row)) fun i ↦ row[i]?.getD 0)
  have hcurrent := Window.layout_current window
  have hcell : ∀ j (hj : j < 3), (toElements window.current)[j] = row[j]?.getD 0 := by
    intro j hj
    rw [← hcurrent]
    simp [WindowLayout.current, WindowLayout.cell, window, ProvableType.toElements_fromElements,
      Window.layout, Vector.getElem_mapRange]
  have hlist : (toElements window.current).toList =
      [window.current.index, window.current.square, window.current.last] := by
    rw [ProvableStruct.toList_toElements]
    rfl
  have hindex : window.current.index = row[0]?.getD 0 := by
    have h : (toElements window.current).toList[0]'(by simp [hlist]) = row[0]?.getD 0 := by
      rw [Vector.getElem_toList]
      exact hcell 0 (by norm_num)
    simpa only [hlist, List.getElem_cons_zero] using h
  have hsquare : window.current.square = row[1]?.getD 0 := by
    have h : (toElements window.current).toList[1]'(by simp [hlist]) = row[1]?.getD 0 := by
      rw [Vector.getElem_toList]
      exact hcell 1 (by norm_num)
    simpa only [hlist, List.getElem_cons_succ, List.getElem_cons_zero] using h
  rw [← hindex, ← hsquare]
  exact hspec.1

theorem fits : Fits (K := K) component 3 where
  twoAdic := by decide +kernel
  height_le := by norm_num
  fixedHeight := by rintro _ ⟨⟩; rfl

/-- **Knowledge soundness of the squares table's STARK.** Unless the rows of some trace within `δ'`
of the prover's committed trace each hold the square of their counter, the verifier accepts with
probability at most the knowledge error. -/
theorem knowledgeSoundness (prover : Iop.Prover setup) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - setup.rate) :
    (∀ trace ∈ Iop.closeTraces setup δ' prover.trace,
      ¬ SquaresHeld (toRows babyBear component 3 trace)) →
      Iop.acceptance [] prover ≤ Iop.knowledgeError setup δ δ' :=
  knowledgeSoundness_of_tableSound babyBear setup rfl bridgeable_component fits (tableSound 8) []
    prover δ δ' hδ'

/-- **Knowledge soundness of the squares table's STARK in the random-oracle model.** -/
theorem knowledgeSoundness_ro (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - setup.rate) (Q : ℕ)
    (prover : Iop.NIProver setup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Iop.run setup [] prover}[
      verdict = .ok () ∧ proof.degreeBits = setup.logN ∧
        ∀ trace ∈ Iop.closeTraces setup δ' (Iop.committedTrace setup log proof),
          ¬ SquaresHeld (toRows babyBear component 3 trace)] ≤
      (Q + setup.verifierQueries) * Iop.roundError setup δ δ' +
        Iop.hashError K (Q + setup.verifierQueries) :=
  knowledgeSoundness_ro_of_tableSound babyBear setup rfl bridgeable_component fits (tableSound 8)
    [] δ δ' hδ' Q prover hQ

/--
info: 'CleanCompStarkTests.SquaresTable.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms knowledgeSoundness

/--
info: 'CleanCompStarkTests.SquaresTable.knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms knowledgeSoundness_ro

end CleanCompStarkTests.SquaresTable
