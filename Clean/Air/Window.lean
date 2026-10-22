module

public import Clean.Air.Circuit

@[expose] public section

/-!
# Two-row windows

A two-row component checks its circuit on a *window* of the trace: the current row, the input of
the next row, and three selectors that locate the row in the trace, with Plonky3's semantics. The
next row of the last row is the first row, so constraints that read the next row are usually gated
by `isTransition`.

The window is the circuit's input, of type `Window Row` for the row's own input `Row`. Its cells
beyond the row's own input are virtual: a trace stores them in every row, and the table's
`WindowsMatch` fact ties them to the next row and to the row's position, while a proving backend
reads them from the next row and from its selectors instead of committing them.
-/

namespace Air.Flat
variable {F : Type}

/-- The input of a two-row component's circuit. -/
structure Window (Row : TypeMap) (F : Type) where
  /-- The row's own input. -/
  current : Row F
  /-- The own input of the next row. The next row of the last row is the first row. -/
  next : Row F
  /-- 1 on the first row, 0 on every other row. -/
  isFirstRow : F
  /-- 1 on the last row, 0 on every other row. -/
  isLastRow : F
  /-- 1 on every row but the last, where it is 0. -/
  isTransition : F
deriving ProvableStruct

/-- Where the window cells of a two-row component's circuit input are: its first `rowWidth` cells
are the row's own input, the next `rowWidth` cells are the next row's own input, and the last three
cells are the selectors `isFirstRow`, `isLastRow` and `isTransition`. -/
structure WindowLayout (Input : TypeMap) [ProvableType Input] where
  rowWidth : ℕ
  size_eq : size Input = 2 * rowWidth + 3

/-- The layout of `Window Row`. -/
def Window.layout (Row : TypeMap) [ProvableType Row] : WindowLayout (Window Row) where
  rowWidth := size Row
  size_eq := by simp only [size, ProvableStruct.combinedSize, ProvableStruct.combinedSize']; omega

namespace WindowLayout
variable {Input : TypeMap} [ProvableType Input]

/-- The number of cells of a circuit input that a backend doesn't commit: the next row's input and
the selectors. -/
def windowWidth (layout : WindowLayout Input) : ℕ := layout.rowWidth + 3

/-- Cell `j` of a circuit input. -/
def cell (layout : WindowLayout Input) (input : Input F) (j : ℕ)
    (h : j < 2 * layout.rowWidth + 3) : F :=
  (toElements input)[j]'(layout.size_eq ▸ h)

/-- The row's own input. -/
def current (layout : WindowLayout Input) (input : Input F) : Vector F layout.rowWidth :=
  .ofFn fun j => layout.cell input j.val (by omega)

/-- The next row's own input. -/
def next (layout : WindowLayout Input) (input : Input F) : Vector F layout.rowWidth :=
  .ofFn fun j => layout.cell input (layout.rowWidth + j.val) (by omega)

def isFirstRow (layout : WindowLayout Input) (input : Input F) : F :=
  layout.cell input (2 * layout.rowWidth) (by omega)

def isLastRow (layout : WindowLayout Input) (input : Input F) : F :=
  layout.cell input (2 * layout.rowWidth + 1) (by omega)

def isTransition (layout : WindowLayout Input) (input : Input F) : F :=
  layout.cell input (2 * layout.rowWidth + 2) (by omega)

/-- The selectors of row `i` of a trace with `height` rows. -/
def SelectorsAt [Zero F] [One F] (layout : WindowLayout Input) (input : Input F)
    (i height : ℕ) : Prop :=
  layout.isFirstRow input = (if i = 0 then 1 else 0) ∧
    layout.isLastRow input = (if i + 1 = height then 1 else 0) ∧
    layout.isTransition input = (if i + 1 = height then 0 else 1)

end WindowLayout

namespace Window
variable {Row : TypeMap} [ProvableType Row]

lemma toList_toElements (window : Window Row F) :
    (toElements window).toList = (toElements window.current).toList ++
      ((toElements window.next).toList ++
        [window.isFirstRow, window.isLastRow, window.isTransition]) := by
  rw [ProvableStruct.toList_toElements]
  rfl

lemma getElem_toElements (window : Window Row F) (j : ℕ) (h : j < size (Window Row)) :
    (toElements window)[j] = ((toElements window.current).toList ++
      ((toElements window.next).toList ++
        [window.isFirstRow, window.isLastRow, window.isTransition]))[j]'(by
          rw [← toList_toElements]; simpa using h) := by
  simp only [← toList_toElements, Vector.getElem_toList]

@[simp] lemma layout_current (window : Window Row F) :
    (Window.layout Row).current window = toElements window.current := by
  ext j hj
  simp only [WindowLayout.current, WindowLayout.cell, Vector.getElem_ofFn, getElem_toElements]
  rw [List.getElem_append_left (by simpa [Window.layout] using hj)]
  rfl

@[simp] lemma layout_next (window : Window Row F) :
    (Window.layout Row).next window = toElements window.next := by
  ext j hj
  simp only [WindowLayout.next, WindowLayout.cell, Vector.getElem_ofFn, getElem_toElements]
  rw [List.getElem_append_right (by simp [Window.layout]),
    List.getElem_append_left (by simpa [Window.layout] using hj)]
  simp only [Window.layout, Vector.length_toList, Nat.add_sub_cancel_left]
  rfl

@[simp] lemma layout_isFirstRow (window : Window Row F) :
    (Window.layout Row).isFirstRow window = window.isFirstRow := by
  simp only [WindowLayout.isFirstRow, WindowLayout.cell, getElem_toElements]
  rw [List.getElem_append_right (by simp [Window.layout]; omega),
    List.getElem_append_right (by simp [Window.layout]; omega)]
  simp only [Window.layout, Vector.length_toList]
  simp [show ∀ n : ℕ, 2 * n - n - n = 0 by omega]

@[simp] lemma layout_isLastRow (window : Window Row F) :
    (Window.layout Row).isLastRow window = window.isLastRow := by
  simp only [WindowLayout.isLastRow, WindowLayout.cell, getElem_toElements]
  rw [List.getElem_append_right (by simp [Window.layout]; omega),
    List.getElem_append_right (by simp [Window.layout]; omega)]
  simp only [Window.layout, Vector.length_toList]
  simp [show ∀ n m : ℕ, 2 * n + m - n - n = m by omega]

@[simp] lemma layout_isTransition (window : Window Row F) :
    (Window.layout Row).isTransition window = window.isTransition := by
  simp only [WindowLayout.isTransition, WindowLayout.cell, getElem_toElements]
  rw [List.getElem_append_right (by simp [Window.layout]; omega),
    List.getElem_append_right (by simp [Window.layout]; omega)]
  simp only [Window.layout, Vector.length_toList]
  simp [show ∀ n m : ℕ, 2 * n + m - n - n = m by omega]

end Window
end Air.Flat
