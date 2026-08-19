/-
Transition AIR tables: a component whose circuit is checked on each *adjacent pair* of rows.

Where a flat component is checked independently on each row, a transition component is checked on
each pair `(rows[i], rows[i+1])`. Next-row access is expressed by *widening the environment*
rather than by extending `Expression`: the circuit is evaluated against the concatenation
`curr ++ next`, so that

    cell `i`              is `curr[i]`
    cell `rowWidth + i`   is `next[i]`

Since `Environment.fromArray` already reads a flat `Array F` by index, "next" is just an index
offset. This requires no changes to `Expression`, `Environment`, `eval`, or `circuit_norm`.

There is no separate transition `Table` type. A transition trace is an ordinary `Air.Flat.Table`
whose component has `windowRows = 2`, so the generic `windows` / `windowEnv` machinery in
`FlatComponent.lean` already produces exactly the adjacent pairs. What lives here is only the
row-pair *spelling* of that machinery: `pairEnv`, `pairs`, and the lemmas relating them, kept so
that transition-specific reasoning reads in terms of `curr`/`next` rather than window indices.

Crucially, the next row is the circuit's **output**: the component's `Input` is the current row
and `main` witnesses the next row, so `circuit.size = 2 * rowWidth`. That is what makes the
next-row cells owned by the instantiation, and hence
- completeness provable (they are pinned by `UsesLocalWitnessesCompleteness`), and
- `Spec input output` the adjacent-row transition relation.
-/
import Clean.Air.FlatComponent

namespace Air.Flat
variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

namespace Transition

/--
The environment for the transition at a given position: the current row followed by the next row.

Cells `[0, rowWidth)` read `curr`, cells `[rowWidth, 2 * rowWidth)` read `next`.
-/
@[circuit_norm]
def pairEnv (curr next : Array F) (data : ProverData F) : Environment F :=
  Environment.fromArray (curr ++ next) data

end Transition

namespace Table
variable {table : Table F} {data : ProverData F} {channel : RawChannel F}

/-- A transition component spans two rows. -/
abbrev IsTransition (t : Table F) : Prop := t.component.windowRows = 2

/--
Adjacent row pairs, each tagged with the index of its *current* row.

For a transition table this is exactly `windows`: `windowRows = 2` means a window exists at `i`
precisely when `i + 2 ≤ length`, so the count is `length - 1`. A trace of 0 or 1 rows has no
adjacent pairs and is therefore entirely unconstrained, matching
`TableOperation.everyRowExceptLast` semantics.
-/
def pairs (t : Table F) : List (ℕ × Array F × Array F) :=
  t.windows.map fun i => (i, t.table[i]!, t.table[i + 1]!)

@[circuit_norm] lemma pairs_length (t : Table F) (h : t.IsTransition) :
    t.pairs.length = t.table.length - 1 := by
  simp only [pairs, List.length_map, Table.windows_length, h]
  omega

/-- A one-row trace has no adjacent pairs, hence no constraints and no interactions. -/
@[circuit_norm] lemma pairs_eq_nil_of_length_le_one (t : Table F) (h : t.IsTransition)
    (hlen : t.table.length ≤ 1) : t.pairs = [] := by
  rw [← List.length_eq_zero_iff, pairs_length t h]
  omega

/-- Membership in `pairs` exposes the index, and both rows, by indexing into `table`. -/
lemma mem_pairs_iff {t : Table F} (h : t.IsTransition) {i : ℕ} {curr next : Array F} :
    (i, curr, next) ∈ t.pairs ↔
      ∃ (hi : i + 1 < t.table.length), t.table[i] = curr ∧ t.table[i + 1] = next := by
  simp only [pairs, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl, rfl⟩
    rw [Table.mem_windows_iff, h] at hj
    have hlt : j + 1 < t.table.length := by omega
    refine ⟨hlt, ?_, ?_⟩
    · exact (getElem!_pos t.table j (by omega)).symm
    · exact (getElem!_pos t.table (j + 1) hlt).symm
  · rintro ⟨hi, rfl, rfl⟩
    refine ⟨i, ?_, rfl, ?_, ?_⟩
    · rw [Table.mem_windows_iff, h]; omega
    · exact getElem!_pos t.table i (by omega)
    · exact getElem!_pos t.table (i + 1) hi

/-- The current row of any pair is a row of the trace. -/
lemma curr_mem_table {t : Table F} (h : t.IsTransition) {i : ℕ} {curr next : Array F}
    (hp : (i, curr, next) ∈ t.pairs) : curr ∈ t.table := by
  rw [mem_pairs_iff h] at hp
  obtain ⟨hi, rfl, _⟩ := hp
  exact List.getElem_mem (by omega)

/-- The index of a pair addresses its current row in the trace. -/
lemma getElem_of_mem_pairs {t : Table F} (h : t.IsTransition) {i : ℕ} {curr next : Array F}
    (hp : (i, curr, next) ∈ t.pairs) :
    ∃ hi : i < t.table.length, t.table[i] = curr := by
  rw [mem_pairs_iff h] at hp
  obtain ⟨hi, hcurr, _⟩ := hp
  exact ⟨by omega, hcurr⟩

/-- For a transition table the window at `i` is the pair `(rows[i], rows[i+1])`. -/
lemma windowRow_eq_pair {t : Table F} (h : t.IsTransition) (i : ℕ) :
    t.windowRow i = t.table[i]! ++ t.table[i + 1]! := by
  simp [Table.windowRow, h, List.range_succ]

/-- A transition table's environments are exactly its pair environments. -/
lemma envs_eq_pairs (t : Table F) (h : t.IsTransition) (data : ProverData F) :
    RowEnvs.envs (F:=F) t data = t.pairs.map fun p => Transition.pairEnv p.2.1 p.2.2 data := by
  simp only [Table.envs_eq, pairs, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, Table.windowEnv, Transition.pairEnv, windowRow_eq_pair h]

/-- A pair of the trace is one of the environments the table is checked at. -/
lemma mem_envs_of_mem_pairs {t : Table F} (h : t.IsTransition)
    {p : ℕ × Array F × Array F} (hp : p ∈ t.pairs) {data : ProverData F} :
    Transition.pairEnv p.2.1 p.2.2 data ∈ RowEnvs.envs (F:=F) t data := by
  rw [envs_eq_pairs t h]
  exact List.mem_map_of_mem hp

/--
The current row's input cells are read identically from the row alone and from the row pair.

This is the pair-shaped spelling of `Table.valueFromOffset_windowEnv`; it holds because the input
occupies the low `size Input` indices and `size Input ≤ rowWidth` (`input_le_rowWidth`).
-/
lemma valueFromOffset_pairEnv {t : Table F} (h : t.IsTransition) {i : ℕ} {curr next : Array F}
    (hmem : (i, curr, next) ∈ t.pairs) (data : ProverData F) :
    valueFromOffset t.component.Input 0 (Transition.pairEnv curr next data) =
      valueFromOffset t.component.Input 0 (Environment.fromArray curr data) := by
  have hsize : curr.size = t.component.width :=
    t.uniform_width curr (curr_mem_table h hmem)
  have hinput : size t.component.Input ≤ curr.size := by
    rw [hsize]
    exact t.component.input_le_rowWidth
  simp only [valueFromOffset, Transition.pairEnv, Environment.fromArray]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange, zero_add]
  have hlt : j < curr.size := lt_of_lt_of_le (by simpa using hj) hinput
  rw [Array.getElem?_append_left hlt]

/-! ### Window access and the transition induction

The lemmas below are what turns `Table.Spec` -- the circuit's `Spec` at every *window* -- into
statements about *indexed rows*, which is the form an induction along the trace can consume.
Cell-level access first, then the typed reads, then the induction principle itself.
-/

/-- Cell `j` of the window at `i` is cell `j` of the current row. -/
lemma windowRow_getElem_left {t : Table F} (h : t.IsTransition) {i : ℕ} (hi : i ∈ t.windows)
    {j : ℕ} (hj : j < t.component.rowWidth) :
    (t.windowRow i)[j]! = (t.table[i]!)[j]! := by
  have hlen : i + 2 ≤ t.table.length := by rwa [mem_windows_iff, h] at hi
  have hj' : j < (t.table[i]!).size := by rw [t.row_size (by omega)]; exact hj
  rw [windowRow_eq_pair h, Array.getElem!_eq_getD, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left hj']

/-- Cell `rowWidth + j` of the window at `i` is cell `j` of the next row. -/
lemma windowRow_getElem_right {t : Table F} (h : t.IsTransition) {i : ℕ} (hi : i ∈ t.windows)
    (j : ℕ) :
    (t.windowRow i)[t.component.rowWidth + j]! = (t.table[i + 1]!)[j]! := by
  have hlen : i + 2 ≤ t.table.length := by rwa [mem_windows_iff, h] at hi
  have hsize : (t.table[i]!).size = t.component.rowWidth := t.row_size (by omega)
  rw [windowRow_eq_pair h, Array.getElem!_eq_getD, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_right (by omega), hsize, Nat.add_sub_cancel_left]

/--
Reading any type at offset `rowWidth` of the window at `i` is reading it at offset `0` of row
`i + 1`: the window's second row *is* the next row. This is the typed access that makes the
next-row-as-output layout consumable. No width bound on the read is needed -- out-of-range
cells are `0` on both sides.
-/
lemma valueFromOffset_windowEnv_next {t : Table F} (h : t.IsTransition) {i : ℕ}
    (hi : i ∈ t.windows) (data : ProverData F) (T : TypeMap) [ProvableType T] :
    valueFromOffset T t.component.rowWidth (t.windowEnv i data) =
      valueFromOffset T 0 (Environment.fromArray t.table[i + 1]! data) := by
  have hlen : i + 2 ≤ t.table.length := by rwa [mem_windows_iff, h] at hi
  have hsize : (t.table[i]!).size = t.component.rowWidth := t.row_size (by omega)
  simp only [valueFromOffset, windowEnv, Environment.fromArray, windowRow_eq_pair h]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange, zero_add]
  rw [Array.getElem?_append_right (by omega), hsize, Nat.add_sub_cancel_left]

/--
Adjacent windows overlap on a full row: the second row of the window at `i` is the first row
of the window at `i + 1`, so typed reads through both windows agree. `size T ≤ rowWidth`
confines the read to the shared row.
-/
lemma windowEnv_overlap {t : Table F} (h : t.IsTransition) {i : ℕ}
    (hi : i ∈ t.windows) (hi' : i + 1 ∈ t.windows) (data : ProverData F)
    (T : TypeMap) [ProvableType T] (hT : size T ≤ t.component.rowWidth) :
    valueFromOffset T t.component.rowWidth (t.windowEnv i data) =
      valueFromOffset T 0 (t.windowEnv (i + 1) data) := by
  rw [valueFromOffset_windowEnv_next h hi data, valueFromOffset_windowEnv_curr hi' data T hT]

/-- The typed input of the window at `i` is the input prefix of row `i`. This is the same read
a first-row boundary assertion performs (`Boundary.Assertion.RowSpec`). -/
lemma rowInput_windowEnv {t : Table F} {i : ℕ} (hi : i ∈ t.windows) (data : ProverData F) :
    t.component.rowInput (t.windowEnv i data) =
      valueFromOffset t.component.Input 0 (Environment.fromArray t.table[i]! data) :=
  valueFromOffset_windowEnv_curr hi data _ t.component.input_le_rowWidth

/--
The circuit's output at the window at `i` is the output prefix of row `i + 1` -- provided the
circuit's output variable is the canonical layout at offset `rowWidth`, i.e. the low cells of
the window's second row. That per-circuit fact (`houtput`) is definitional for a circuit that
witnesses the next row's cells in order and returns them, as `FibonacciTransition.fibStep` does.
-/
lemma rowOutput_windowEnv {t : Table F} (h : t.IsTransition) {i : ℕ} (hi : i ∈ t.windows)
    (data : ProverData F)
    (houtput : (t.component.circuit t.component.rowInputVar).output t.component.rowOffset =
      varFromOffset t.component.Output t.component.rowWidth) :
    t.component.rowOutput (t.windowEnv i data) =
      valueFromOffset t.component.Output 0 (Environment.fromArray t.table[i + 1]! data) := by
  show Eval.eval (t.windowEnv i data)
    ((t.component.circuit t.component.rowInputVar).output t.component.rowOffset) = _
  rw [houtput, eval_varFromOffset_valueFromOffset, valueFromOffset_windowEnv_next h hi data]

/--
The transition induction principle: a boundary pins row `0`, the windows step, and the
invariant follows for every row of the trace.

The step hypothesis receives the circuit's `Spec` as a relation between the *typed reads of two
adjacent indexed rows* -- all window plumbing is discharged here, once. The base case is what a
first-row boundary assertion supplies; the conclusion at the last index is what a last-row
boundary assertion consumes.
-/
theorem transition_induction {t : Table F} (h : t.IsTransition) {data : ProverData F}
    (hspec : t.Spec data)
    (houtput : (t.component.circuit t.component.rowInputVar).output t.component.rowOffset =
      varFromOffset t.component.Output t.component.rowWidth)
    {P : ℕ → Prop}
    (base : P 0)
    (step : ∀ i, i + 1 < t.table.length →
      t.component.circuit.Spec
        (valueFromOffset t.component.Input 0 (Environment.fromArray t.table[i]! data))
        (valueFromOffset t.component.Output 0 (Environment.fromArray t.table[i + 1]! data))
        data →
      P i → P (i + 1)) :
    ∀ i, i < t.table.length → P i := by
  intro i
  induction i with
  | zero => exact fun _ => base
  | succ n ih =>
    intro hlt
    have hwin : n ∈ t.windows := by rw [mem_windows_iff, h]; omega
    have hs := hspec _ (mem_envs_of_mem_windows hwin (data := data))
    rw [Table.component_eq] at hs
    unfold Component.Spec at hs
    rw [rowInput_windowEnv hwin data, rowOutput_windowEnv h hwin data houtput] at hs
    exact step n hlt hs (ih (by omega))

end Table

end Air.Flat
