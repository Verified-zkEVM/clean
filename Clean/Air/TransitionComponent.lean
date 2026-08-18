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
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  · rintro ⟨hi, rfl, rfl⟩
    refine ⟨i, ?_, rfl, ?_, ?_⟩
    · rw [Table.mem_windows_iff, h]; omega
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

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

end Table

end Air.Flat
