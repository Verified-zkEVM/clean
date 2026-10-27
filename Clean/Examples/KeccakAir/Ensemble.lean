/-
Plonky3's Keccak-f AIR as a one-component ensemble, and what a satisfying table proves: the rows
computing the last round of a permutation output Keccak-f of their preimage.
-/
module

public import Clean.Examples.KeccakAir.Component
public import CompPoly.Fields.BabyBear.Basic
public import CompPoly.Fields.KoalaBear.Basic

@[expose] public section

namespace KeccakAir
open Air.Flat Specs.Keccak256

variable {p : ℕ}

lemma preimageState_eq {first last : Row (F p)} (h : last.preimage = first.preimage) :
    last.preimageState = first.preimageState := by
  simp only [Row.preimageState]
  congr 1
  funext y x l
  simp only [Row.preimageLimb, h]

variable [Fact p.Prime]

/-- The row stored in the first cells of a trace row. -/
def traceRow (cells : Array (F p)) : Row (F p) := fromElements (rowPrefix (size Row) cells)

/-- The window stored in a trace row: its own cells, the next row's and the selectors. -/
def windowOf (cells : Array (F p)) : Window Row (F p) :=
  fromElements (rowPrefix (size (Window Row)) cells)

lemma windowOf_current (cells : Array (F p)) : (windowOf cells).current = traceRow cells := by
  have hwindow := Window.toList_toElements (windowOf cells)
  rw [windowOf, ProvableType.toElements_fromElements] at hwindow
  have hcurrent : (toElements (windowOf cells).current).toList =
      (rowPrefix (size (Window Row)) cells).toList.take (size Row) := by
    rw [windowOf, hwindow, List.take_left' (by simp)]
  rw [traceRow, ← ProvableType.fromElements_toElements (windowOf cells).current]
  refine congrArg fromElements (Vector.toList_inj.mp ?_)
  rw [hcurrent]
  have hsize := (Window.layout Row).size_eq
  apply List.ext_getElem
  · simp only [List.length_take, Vector.length_toList]
    simp only [Window.layout] at hsize
    omega
  · intro j hj _
    simp only [List.getElem_take, rowPrefix, Vector.toList_mk, List.getElem_ofFn]

lemma rounds_24 (state : Vector ℕ 25) : rounds 24 state = keccakPermutation state := by
  simp only [rounds, keccakPermutation, ← Vector.foldl_toList]
  rw [List.take_of_length_le (by simp)]

lemma oneHot_injective {r s : Fin 24} (h : (oneHot r : Vector (F p) 24) = oneHot s) : r = s := by
  have := congrArg (·[r]) h
  by_contra hne
  simp only [oneHot_getElem, ↓reduceIte, show ¬(r = s) from hne] at this
  exact one_ne_zero this

variable [Fact (2 ^ 16 < p)]

/-- The number of permutations of a trace with `height` rows, the last one possibly cut off. -/
def permutations (height : UInt64) : ℕ := (height.toNat + 23) / 24

/-- The ensemble of the Keccak-f AIR with `height` rows. The prover's input is the input of every
permutation, as the 100 16-bit limbs of its lanes in the order of the `preimage` columns. -/
def ensemble (height : UInt64) : Ensemble (F p) unit where
  tables := [component height]
  unique_names := by simp
  channels := []
  ProverInput := fields (permutations height * 100)
  hintTables := [{ key := "keccak", width := 100, offset := 0, rows := permutations height }]

/-- Every window of a satisfied table of the Keccak-f component computes a round of its
preimage. -/
theorem windowSpec_of_table {height : UInt64} {table : Table (F p)}
    (hcomponent : table.component = component height) (consistent : table.DataConsistency)
    (satisfied : table.Constraints) :
    table.component.WindowsMatch table.table ∧
      ∀ i (hi : i < table.table.length), WindowSpec (windowOf table.table[i]) := by
  obtain ⟨component', rows, data, uniform_width, length_le, fixed_rows_match, windows_match⟩ :=
    table
  subst hcomponent
  refine ⟨windows_match, fun i hi => ?_⟩
  have spec := (Table.weakSoundness consistent (fun _ _ => trivial) satisfied ?_).left
    rows[i] (List.getElem_mem hi)
  · have hinput : (component height).inputOf rows[i] = windowOf rows[i] := rfl
    simp only [Component.Spec, Table.environment, Component.rowInput_fromArray, hinput] at spec
    exact spec
  · intro row _
    rw [Component.guarantees_iff]
    intro interaction hinteraction
    change interaction ∈ Operations.interactions ((main _).operations _) at hinteraction
    erw [interactions_main] at hinteraction
    simp at hinteraction

/-- In a satisfied table of the Keccak-f component, the rows computing the last round of a
permutation output Keccak-f of their preimage, whose limbs are 16-bit. -/
theorem table_soundness {height : UInt64} {table : Table (F p)}
    (hcomponent : table.component = component height) (consistent : table.DataConsistency)
    (satisfied : table.Constraints) :
    ∀ cells ∈ table.table, (traceRow cells).stepFlags[23] = 1 →
      (traceRow cells).PreimageNormalized ∧
        (traceRow cells).outputState = keccakPermutation (traceRow cells).preimageState := by
  intro cells hcells hlast
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcells
  obtain ⟨r, hr, hnormalized, -, houtput, -⟩ :=
    (windowSpec_of_table hcomponent consistent satisfied).2 i hi
  rw [windowOf_current] at hr hnormalized houtput
  have : r = 23 := by
    by_contra hne
    have h23 : (oneHot r : Vector (F p) 24)[(23 : ℕ)] = if (23 : Fin 24) = r then 1 else 0 :=
      oneHot_getElem r 23
    rw [hr, h23] at hlast
    simp only [show ¬((23 : Fin 24) = r) from fun h => hne h.symm, ↓reduceIte] at hlast
    exact zero_ne_one hlast
  subst this
  exact ⟨hnormalized, houtput.trans (rounds_24 _)⟩

lemma next_of_windowsMatch {height : UInt64} {rows : List (Array (F p))}
    (hmatch : (component (p := p) height).WindowsMatch rows) {j : ℕ} (hj : j + 1 < rows.length) :
    (windowOf rows[j]).next = traceRow rows[j + 1] ∧ (windowOf rows[j]).isTransition = 1 := by
  obtain ⟨hnext, -, -, htransition⟩ := hmatch j (by omega)
  have hinput (j : ℕ) (hj : j < rows.length) :
      (component (p := p) height).inputOf rows[j] = windowOf rows[j] := rfl
  simp only [hinput, Nat.mod_eq_of_lt hj] at hnext htransition
  have hnext := (Window.layout_next _).symm.trans (hnext.trans (Window.layout_current _))
  have htransition := (Window.layout_isTransition _).symm.trans htransition
  refine ⟨?_, by simpa [show j + 1 ≠ rows.length by omega] using htransition⟩
  rw [← windowOf_current]
  simpa only [ProvableType.fromElements_toElements] using congrArg fromElements hnext

/-- In a satisfied table of the Keccak-f component, a block of 24 rows that starts at round 0
computes Keccak-f of the preimage of its first row: its last row computes the last round, of the
same preimage, and outputs Keccak-f of it. -/
theorem table_block_soundness {height : UInt64} {table : Table (F p)}
    (hcomponent : table.component = component height) (consistent : table.DataConsistency)
    (satisfied : table.Constraints) :
    ∀ i (hi : i + 23 < table.table.length), (traceRow table.table[i]).stepFlags[0] = 1 →
      let first := traceRow table.table[i]
      let last := traceRow table.table[i + 23]
      last.stepFlags[23] = 1 ∧ last.preimage = first.preimage ∧ first.PreimageNormalized ∧
        last.outputState = keccakPermutation first.preimageState := by
  intro i hi hfirst
  obtain ⟨hmatch, hspec⟩ := windowSpec_of_table hcomponent consistent satisfied
  rw [hcomponent] at hmatch
  -- the rows of the block compute rounds 0, ..., 23 of the same preimage
  have hround (k : ℕ) (hk : k ≤ 23) :
      (traceRow table.table[i + k]).stepFlags = oneHot ⟨k, by omega⟩ ∧
        (traceRow table.table[i + k]).preimage = (traceRow table.table[i]).preimage := by
    induction k with
    | zero =>
      simp only [Nat.add_zero, and_true]
      obtain ⟨r, hr, -⟩ := hspec i (by omega)
      rw [windowOf_current] at hr
      have hr0 : r = 0 := by
        by_contra hne
        have h0 : (oneHot r : Vector (F p) 24)[(0 : ℕ)] = if (0 : Fin 24) = r then 1 else 0 :=
          oneHot_getElem r 0
        rw [hr, h0] at hfirst
        simp only [show ¬((0 : Fin 24) = r) from fun h => hne h.symm, ↓reduceIte] at hfirst
        exact zero_ne_one hfirst
      rw [hr, hr0]
      rfl
    | succ k ih =>
      simp only [← Nat.add_assoc]
      obtain ⟨hflags, hpreimage⟩ := ih (by omega)
      obtain ⟨r, hr, -, -, -, -, hnext⟩ := hspec (i + k) (by omega)
      rw [windowOf_current, hflags] at hr
      have hr : r = ⟨k, by omega⟩ := (oneHot_injective hr).symm
      obtain ⟨hnextRow, htransition⟩ := next_of_windowsMatch hmatch (j := i + k) (by omega)
      obtain ⟨hnextFlags, hsame⟩ := hnext htransition
      have hlast : r ≠ 23 := by
        rw [hr]
        intro h
        have := congrArg Fin.val h
        simp only at this
        omega
      obtain ⟨hnextPreimage, -⟩ := hsame hlast
      rw [hnextRow, windowOf_current, hpreimage] at hnextPreimage
      rw [hnextRow] at hnextFlags
      refine ⟨?_, hnextPreimage⟩
      rw [hnextFlags, hr]
      congr 1
      ext
      simp only [Fin.val_add, Fin.val_one]
      omega
  obtain ⟨hlastFlags, hlastPreimage⟩ := hround 23 le_rfl
  have hlastRound : (traceRow table.table[i + 23]).stepFlags[23] = 1 := by
    have h23 : (oneHot 23 : Vector (F p) 24)[(23 : ℕ)] = if (23 : Fin 24) = 23 then 1 else 0 :=
      oneHot_getElem 23 23
    rw [hlastFlags]
    simpa using h23
  obtain ⟨hnormalized, houtput⟩ := table_soundness hcomponent consistent satisfied _
    (List.getElem_mem (by omega)) hlastRound
  refine ⟨hlastRound, hlastPreimage, ?_, ?_⟩
  · intro y x l
    simpa only [Row.preimageLimb, hlastPreimage] using hnormalized y x l
  · rw [houtput, preimageState_eq hlastPreimage]

/-- The tables of a witness of the ensemble are tables of the Keccak-f component. -/
lemma component_of_mem {height : UInt64} (witness : EnsembleWitness (ensemble (p := p) height))
    {table : Table (F p)} (htable : table ∈ witness.tables) :
    table.component = component height := by
  have hmem : table.component ∈ witness.tables.map (·.component) := List.mem_map_of_mem htable
  rw [witness.tables_map_component] at hmem
  simpa [ensemble] using hmem

/-- In a witness of the ensemble that satisfies the constraints, the rows computing the last round
of a permutation output Keccak-f of their preimage, whose limbs are 16-bit. -/
theorem soundness {height : UInt64} (witness : EnsembleWitness (ensemble (p := p) height))
    (satisfied : witness.Constraints) :
    ∀ table ∈ witness.tables, ∀ cells ∈ table.table, (traceRow cells).stepFlags[23] = 1 →
      (traceRow cells).PreimageNormalized ∧
        (traceRow cells).outputState = keccakPermutation (traceRow cells).preimageState :=
  fun table htable => table_soundness (component_of_mem witness htable)
    (witness.dataConsistency_of_mem table htable) (satisfied table htable)

/-- In a witness of the ensemble that satisfies the constraints, a block of 24 rows that starts at
round 0 computes Keccak-f of the preimage of its first row. -/
theorem block_soundness {height : UInt64} (witness : EnsembleWitness (ensemble (p := p) height))
    (satisfied : witness.Constraints) :
    ∀ table ∈ witness.tables, ∀ i (hi : i + 23 < table.table.length),
      (traceRow table.table[i]).stepFlags[0] = 1 →
      let first := traceRow table.table[i]
      let last := traceRow table.table[i + 23]
      last.stepFlags[23] = 1 ∧ last.preimage = first.preimage ∧ first.PreimageNormalized ∧
        last.outputState = keccakPermutation first.preimageState :=
  fun table htable => table_block_soundness (component_of_mem witness htable)
    (witness.dataConsistency_of_mem table htable) (satisfied table htable)

end KeccakAir

/-! The field-size hypothesis holds for KoalaBear and BabyBear. -/

instance : Fact (2 ^ 16 < KoalaBear.fieldSize) := ⟨by norm_num [KoalaBear.fieldSize]⟩

instance : Fact (2 ^ 16 < BabyBear.fieldSize) := ⟨by norm_num [BabyBear.fieldSize]⟩

section
open Air.Flat KeccakAir

example {height : UInt64} (witness : EnsembleWitness (ensemble (p := KoalaBear.fieldSize) height))
    (satisfied : witness.Constraints) :=
  block_soundness witness satisfied

example {height : UInt64} (witness : EnsembleWitness (ensemble (p := BabyBear.fieldSize) height))
    (satisfied : witness.Constraints) :=
  block_soundness witness satisfied

end
