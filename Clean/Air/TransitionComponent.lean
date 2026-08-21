/-
Transition AIR tables: a component checked on each adjacent pair of rows `(rows[i], rows[i+1])`.

Next-row access widens the environment rather than extending `Expression`: the circuit is
evaluated against `curr ++ next`, so cell `rowWidth + i` is `next[i]`. A transition trace is an
ordinary `Table` whose component has `windowRows = 2`, so the generic `windows` / `windowEnv`
machinery already produces the adjacent pairs; what lives here is their two-row reading and the
induction along the trace it makes possible.

The next row is the circuit's **output**: `Input` is the current row and `main` witnesses the
next row, which makes `Spec input output` the transition relation and completeness provable.
-/
import Clean.Air.FlatComponent

namespace Air.Flat
variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

namespace Table
variable {table : Table F} {data : ProverData F} {channel : RawChannel F}

/-- A transition component spans two rows. -/
abbrev IsTransition (t : Table F) : Prop := t.component.windowRows = 2

/-- For a transition table the window at `i` is the pair `(rows[i], rows[i+1])`. -/
lemma windowRow_eq_pair {t : Table F} (h : t.IsTransition) (i : ℕ) :
    t.windowRow i = t.table[i]! ++ t.table[i + 1]! := by
  simp [Table.windowRow, h, List.range_succ]

/-! ### Window access and the transition induction

The lemmas below turn `Table.Spec` -- the circuit's `Spec` at every window -- into statements
about indexed rows, which is what an induction along the trace can consume.
-/

/-- Reading any type at offset `rowWidth` of the window at `i` is reading it at offset `0` of row
`i + 1`: the window's second row *is* the next row. -/
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

/-- The typed input of the window at `i` is the input prefix of row `i`. This is the same read
a first-row boundary assertion performs (`Boundary.Assertion.RowSpec`). -/
lemma rowInput_windowEnv {t : Table F} {i : ℕ} (hi : i ∈ t.windows) (data : ProverData F) :
    t.component.rowInput (t.windowEnv i data) =
      valueFromOffset t.component.Input 0 (Environment.fromArray t.table[i]! data) :=
  valueFromOffset_windowEnv_curr hi data _ t.component.input_le_rowWidth

/-- The circuit's output at the window at `i` is the output prefix of row `i + 1`, provided its
output variable sits at offset `rowWidth` (`houtput`, definitional for a circuit that witnesses
the next row's cells in order and returns them). -/
lemma rowOutput_windowEnv {t : Table F} (h : t.IsTransition) {i : ℕ} (hi : i ∈ t.windows)
    (data : ProverData F)
    (houtput : (t.component.circuit t.component.rowInputVar).output t.component.rowOffset =
      varFromOffset t.component.Output t.component.rowWidth) :
    t.component.rowOutput (t.windowEnv i data) =
      valueFromOffset t.component.Output 0 (Environment.fromArray t.table[i + 1]! data) := by
  show Eval.eval (t.windowEnv i data)
    ((t.component.circuit t.component.rowInputVar).output t.component.rowOffset) = _
  rw [houtput, eval_varFromOffset_valueFromOffset, valueFromOffset_windowEnv_next h hi data]

/-- The transition induction principle: a boundary pins row `0`, the windows step, and the
invariant follows for every row. The base case is what a first-row boundary assertion supplies,
the conclusion what a last-row assertion consumes. -/
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
    unfold Component.Spec at hs
    rw [rowInput_windowEnv hwin data, rowOutput_windowEnv h hwin data houtput] at hs
    exact step n hlt hs (ih (by omega))

end Table

end Air.Flat
