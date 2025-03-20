import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.SubCircuit
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Table.SimpTable

/--
  A row is StructuredElement that contains field elements.
-/
@[reducible]
def Row (F : Type) (S : Type → Type) [ProvableType S] := S F

variable {F : Type} {S : Type → Type} [ProvableType S]

@[table_norm, table_assignment_norm]
def Row.get (row : Row F S) (i : Fin (size S)) : F :=
  let elems := to_elements row
  elems.get i

@[table_norm]
def Row.fill (element: F) : Row F S :=
  let elems := .fill (size S) element
  from_elements elems

@[table_norm]
def Row.findIdx? (row : Row F S) (prop: F → Bool) : Option (Fin (size S)) :=
  let elems := to_elements row
  elems.findIdx? prop

/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (F : Type) (S : Type → Type) [ProvableType S] :=
  /-- An empty trace -/
  | empty : Trace F S
  /-- Add a row to the end of the trace -/
  | cons (rest: Trace F S) (row: Row F S) : Trace F S

@[inherit_doc] notation:67 "<+>" => Trace.empty
@[inherit_doc] infixl:67 " +> " => Trace.cons

namespace Trace
/--
  The length of a trace is the number of rows it contains.
-/
@[table_norm, table_assignment_norm]
def len : Trace F S → ℕ
  | <+> => 0
  | rest +> _ => rest.len + 1

/--
  Get the row at a specific index in the trace, starting from the bottom of the trace
-/
@[table_assignment_norm]
def getLeFromBottom :
    (trace : Trace F S) → (row : Fin trace.len) → (col : Fin (size S)) → F
  | _ +> currRow, ⟨0, _⟩, j => currRow.get j
  | rest +> _, ⟨i + 1, h⟩, j => getLeFromBottom rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

end Trace


/--
  A trace of length N is a trace with exactly N rows.
-/
def TraceOfLength (F : Type) (S : Type → Type) [ProvableType S] (N : ℕ) : Type :=
  { env : Trace F S // env.len = N }

namespace TraceOfLength

/--
  Get the row at a specific index in the trace, starting from the top
-/
@[table_assignment_norm]
def get {M : ℕ} :
    (env : TraceOfLength F S M) → (i : Fin M) → (j : Fin (size S)) → F
  | ⟨env, h⟩, i, j => env.getLeFromBottom ⟨
      M - 1 - i,
      by rw [h]; apply Nat.sub_one_sub_lt_of_lt; exact i.is_lt
    ⟩ j

/--
  Apply a proposition to every row in the trace
-/
@[table_norm]
def forAllRowsOfTrace {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → Prop) : Prop :=
  inner trace.val prop
  where
  @[table_norm]
  inner : Trace F S → (Row F S → Prop) → Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

/--
  Apply a proposition to every row in the trace except the last one
-/
@[table_norm]
def forAllRowsOfTraceExceptLast {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace F S → (Row F S → Prop) → Prop
    | <+>, _ => true
    | <+> +> _, _ => true
    | rest +> curr +> _, prop => prop curr ∧ inner (rest +> curr) prop

/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
@[table_norm]
def forAllRowsOfTraceWithIndex {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → ℕ → Prop) : Prop :=
  inner trace.val prop
  where
  @[table_norm]
  inner : Trace F S → (Row F S → ℕ → Prop) → Prop
    | <+>, _ => true
    | rest +> row, prop => (prop row rest.len) ∧ inner rest prop

end TraceOfLength
variable {W: ℕ} {α: Type}

/--
  A cell offset is an offset in a table that points to a specific cell in a row.
  It is used to define a relative position in the trace.
  `W` is the size of the "vertical window", which means that we can reference at most
  `W` rows above the current row.
  To make sure that the vertical offset is bounded, it is represented as a `Fin W`.
-/
structure CellOffset (W: ℕ+) (S : Type → Type) [ProvableType S]  where
  rowOffset: Fin W
  column: Fin (size S)
deriving Repr

namespace CellOffset

/--
  Current row offset
-/
@[table_assignment_norm]
def curr {W : ℕ+} (j : Fin (size S)) :  CellOffset W S := ⟨0, j⟩

/--
  Next row offset
-/
@[table_assignment_norm]
def next {W : ℕ+} (j : Fin (size S)) :  CellOffset W S := ⟨1, j⟩

end CellOffset

inductive Cell (W: ℕ+) (S : Type → Type) [ProvableType S] :=
  | input : CellOffset W S → Cell W S
  | aux : ℕ → Cell W S

/--
Mapping between cell offsets in the table and variable indices.

The mapping must maintain the invariant that each variable is assigned to at most one cell.
On the other hand, a cell can be assigned zero, one or more variables.

`CellAssignment` keeps track of the mapping in both directions, and requires that these remain consistent.
-/
structure CellAssignment (W: ℕ+) (S : Type → Type) [ProvableType S] where
  offset : ℕ -- number of variables
  aux_length : ℕ -- number of auxiliary cells (i.e. those not part of the input/output layout)

  /-- every variable is assigned to exactly one cell in the trace -/
  vars : Vector (Cell W S) offset

  -- /-- every cell (input / aux) is assigned a _list_ of variables (that could be empty) -/
  -- input_to_vars : Matrix (List (Fin offset)) W (size S)
  -- aux_to_vars : Vector (List (Fin offset)) aux_length

  -- -- the mappings vars -> cells and cells -> vars are inverses of each other
  -- input_cell_consistent : ∀ (var : Fin offset) (i : Fin W) (j : Fin (size S)),
  --   vars.get var = .input ⟨ i, j ⟩ ↔ var ∈ input_to_vars.get i j

  -- aux_cell_consistent : ∀ (var : Fin offset) (i : Fin aux_length),
  --   vars.get var = .aux i ↔ var ∈ aux_to_vars.get i

variable {W: ℕ+}

namespace CellAssignment
@[table_assignment_norm]
def get (assignment: CellAssignment W S) (var: Fin assignment.offset) : Cell W S :=
  assignment.vars.get var

@[table_assignment_norm, reducible]
def empty (W: ℕ+) : CellAssignment W S where
  offset := 0
  aux_length := 0
  vars := .nil
  -- input_to_vars := .fill W (size S) []
  -- aux_to_vars := .nil
  -- input_cell_consistent := fun var => absurd var.is_lt var.val.not_lt_zero
  -- aux_cell_consistent := fun var => absurd var.is_lt var.val.not_lt_zero

-- @[table_norm]
-- def increase_aux_capacity (assignment: CellAssignment W S) : CellAssignment W S where
  -- offset := assignment.offset
  -- aux_length := assignment.aux_length + 1
  -- vars := assignment.vars
  -- .map fun
  --   | .input off => .input off
  --   | .aux i => .aux i.castSucc
  -- input_to_vars := assignment.input_to_vars
  -- aux_to_vars := assignment.aux_to_vars.push []
  -- input_cell_consistent := by
  --   intro var i j
  --   rw [Vector.get_map, ← assignment.input_cell_consistent var i j]
  --   split <;> simp_all
  -- aux_cell_consistent := by
  --   intro var i
  --   rw [Vector.get_map]
  --   by_cases hi : i.val < assignment.aux_length
  --   -- induction hypothesis case
  --   have ih := assignment.aux_cell_consistent var ⟨ i, hi ⟩
  --   have : (assignment.aux_to_vars.push []).get i = assignment.aux_to_vars.get ⟨ i, hi ⟩ := by
  --     simp [Vector.push, hi, List.getElem_append]
  --   rw [this, ← ih]; clear this
  --   split
  --   · simp_all
  --   next _ i' heq => rw [heq]; simp [Fin.ext_iff]
  --   -- contradictory case
  --   have i_eq : i.val = assignment.aux_length := by linarith [i.is_lt]
  --   simp [i_eq]
  --   split; simp
  --   next _ i' _ =>
  --     rw [Cell.aux.injEq, Fin.ext_iff, i_eq]
  --     have : ↑i'.castSucc < assignment.aux_length := i'.is_lt
  --     linarith

@[table_assignment_norm]
def push_var_aux (assignment: CellAssignment W S) : CellAssignment W S :=
  -- let assignment' := increase_aux_capacity assignment
  -- the new variable index
  -- let fin_offset : Fin (assignment.offset + 1) := ⟨ assignment.offset, by linarith ⟩
  -- let fin_aux_length : Fin (assignment.aux_length + 1) := Fin.last assignment.aux_length
  -- let input_to_vars := assignment.input_to_vars.map (fun l => l.map Fin.castSucc)
  -- let aux_to_vars := assignment'.aux_to_vars.map (fun l => l.map Fin.castSucc)
  {
    offset := assignment.offset + 1
    aux_length := assignment.aux_length + 1
    vars := assignment.vars.push (.aux assignment.aux_length)
    -- input_to_vars := input_to_vars
    -- aux_to_vars := aux_to_vars.set fin_aux_length [fin_offset]

    -- input_cell_consistent := by
    --   intro var i j
    --   by_cases h_var : var.val < assignment'.offset
    --   -- induction hypothesis case
    --   have ih := assignment'.input_cell_consistent ⟨ var, h_var ⟩ i j
    --   have h_len : assignment'.vars.val.length = assignment'.offset := by simp
    --   have : (assignment'.vars.push (.aux fin_aux_length)).get var = assignment'.vars.get ⟨ var, h_var ⟩ := by
    --     simp [Vector.push]
    --     exact List.getElem_append var.val (by linarith)
    --   rw [this, ih]; clear this
    --   simp [input_to_vars]
    --   constructor
    --   · intro h_mem; use ⟨ var, h_var ⟩; use h_mem; simp
    --   · rintro ⟨ var', ⟨ h_mem, h_cast ⟩ ⟩
    --     have : var' = ⟨var, h_var⟩ := by simp [←h_cast]
    --     rw [←this]
    --     exact h_mem
    --   -- new variable case
    --   have : var.val < assignment'.offset + 1 := var.is_lt
    --   have var_eq : var.val = assignment'.offset := by linarith
    --   have : (assignment'.vars.push (.aux fin_aux_length)).get var = .aux fin_aux_length := by
    --     simp [var_eq]
    --   rw [this]; clear this
    --   simp [input_to_vars]
    --   rintro var' h_mem h_cast
    --   rw [Fin.ext_iff, var_eq] at h_cast
    --   have : ↑var'.castSucc < assignment'.offset := var'.is_lt
    --   linarith

    -- aux_cell_consistent := by
    --   intro var i
    --   by_cases h_var : var.val < assignment'.offset
    --   -- induction hypothesis case
    --   have ih := assignment'.aux_cell_consistent ⟨ var, h_var ⟩ i
    --   have : (assignment'.vars.push (.aux fin_aux_length)).get var = assignment'.vars.get ⟨ var, h_var ⟩ := by
    --     simp [Vector.push]
    --     have h_len : assignment'.vars.val.length = assignment'.offset := by simp
    --     exact List.getElem_append var.val (by linarith)
    --   rw [this, ih]; clear this
    --   suffices h : var ∈ aux_to_vars.get i ↔ var ∈ (aux_to_vars.set fin_aux_length [fin_offset]).get i by
    --     rw [←h]
    --     simp [aux_to_vars]
    --     constructor
    --     · intro h_mem; use ⟨ var, h_var ⟩; use h_mem; simp
    --     · rintro ⟨ var', ⟨ h_mem, h_cast ⟩ ⟩
    --       have : var' = ⟨var, h_var⟩ := by simp [←h_cast]
    --       rw [←this]
    --       exact h_mem
    --   sorry
    --   -- new variable case
    --   have : var.val < assignment'.offset + 1 := var.is_lt
    --   have var_eq : var.val = assignment'.offset := by linarith
    --   have : (assignment'.vars.push (.aux fin_aux_length)).get var = .aux fin_aux_length := by
    --     simp [var_eq]
    --   rw [this]; clear this
    --   rw [Cell.aux.injEq]
    --   constructor
    --   · rintro rfl; simp; ext; simp [var_eq]; rfl
    --   intro h_mem
    --   by_contra h_ne
    --   rw [Fin.ext_iff] at h_ne
    --   replace h_ne : ¬ i.val = assignment.aux_length := by
    --     rintro h_eq; rw [h_eq] at h_ne; simp [fin_aux_length] at h_ne
    --   have : i.val < assignment.aux_length + 1 := i.is_lt
    --   have : i.val ≤ assignment.aux_length := Nat.le_of_lt_succ this
    --   have : i.val < assignment.aux_to_vars.val.length := by rw [assignment.aux_to_vars.prop]; exact Nat.lt_of_le_of_ne this h_ne
    --   simp [fin_aux_length, Vector.set, aux_to_vars, assignment', increase_aux_capacity] at h_mem
    --   -- TODO need more lemmas
    --   sorry
  }

@[table_assignment_norm]
def push_vars_aux (assignment: CellAssignment W S) : ℕ → CellAssignment W S
  | 0 => assignment
  | n + 1 => (assignment.push_vars_aux n).push_var_aux

lemma push_vars_aux_offset (assignment: CellAssignment W S) (n : ℕ) :
  (assignment.push_vars_aux n).offset = assignment.offset + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [push_vars_aux]
    simp_arith [push_var_aux, ih]

@[table_assignment_norm]
def push_var_input (assignment: CellAssignment W S) (row: Fin W) (col: Fin (size S)) : CellAssignment W S :=
  let cell := Cell.input ⟨ row, col ⟩
  -- let fin_offset : Fin (assignment.offset + 1) := ⟨ assignment.offset, by linarith ⟩
  -- let input_to_vars' := assignment.input_to_vars.map (fun l => l.map Fin.castSucc)
  -- let input_to_vars := input_to_vars'.set row col <| input_to_vars'.get row col ++ [fin_offset]
  -- let aux_to_vars := assignment.aux_to_vars.map (fun l => l.map Fin.castSucc)
  {
    offset := assignment.offset + 1
    aux_length := assignment.aux_length
    vars := assignment.vars.push cell
    -- input_to_vars := input_to_vars
    -- aux_to_vars := aux_to_vars

    -- input_cell_consistent := by
    --   intro var i j
    --   by_cases h_var : var.val < assignment.offset
    --   -- induction hypothesis case
    --   have ih := assignment.input_cell_consistent ⟨ var, h_var ⟩ i j
    --   have h_len : assignment.vars.val.length = assignment.offset := by simp
    --   have : (assignment.vars.push cell).get var = assignment.vars.get ⟨ var, h_var ⟩ := by
    --     simp [Vector.push]
    --     exact List.getElem_append var.val (by linarith)
    --   rw [this, ih]; clear this

    --   suffices h : var ∈ input_to_vars'.get i j ↔ var ∈ input_to_vars.get i j by
    --     rw [←h]
    --     simp [input_to_vars']
    --     constructor
    --     · intro h_mem; use ⟨ var, h_var ⟩; use h_mem; simp
    --     · rintro ⟨ var', ⟨ h_mem, h_cast ⟩ ⟩
    --       have : var' = ⟨var, h_var⟩ := by simp [←h_cast]
    --       rw [←this]
    --       exact h_mem
    --   simp only [input_to_vars]
    --   -- TODO
    --   sorry
    --   -- new variable case
    --   have var_eq : var.val = assignment.offset := by linarith [var.is_lt]
    --   have : (assignment.vars.push cell).get var = .input ⟨ row, col ⟩ := by
    --     simp [var_eq]
    --   rw [this]; clear this
    --   simp [input_to_vars]
    --   constructor
    --   · rintro ⟨ rfl, rfl ⟩
    --     simp; right; ext; simp [var_eq]
    --   sorry

    -- aux_cell_consistent := by
    --   intro var i
    --   by_cases h_var : var.val < assignment.offset
    --   -- induction hypothesis case
    --   have ih := assignment.aux_cell_consistent ⟨ var, h_var ⟩ i
    --   have h_len : assignment.vars.val.length = assignment.offset := by simp
    --   have : (assignment.vars.push cell).get var = assignment.vars.get ⟨ var, h_var ⟩ := by
    --     simp [Vector.push]
    --     exact List.getElem_append var.val (by linarith)
    --   rw [this, ih]; clear this
    --   simp [aux_to_vars]
    --   constructor
    --   · intro h_mem; use ⟨ var, h_var ⟩; use h_mem; simp
    --   · rintro ⟨ var', ⟨ h_mem, h_cast ⟩ ⟩
    --     have : var' = ⟨var, h_var⟩ := by simp [←h_cast]
    --     rw [←this]
    --     exact h_mem
    --   -- new variable case
    --   have var_eq : var.val = assignment.offset := by linarith [var.is_lt]
    --   have : (assignment.vars.push cell).get var = .input ⟨ row, col ⟩ := by
    --     simp [var_eq]
    --   rw [this]; clear this
    --   simp [aux_to_vars]
    --   intro var' h_mem
    --   by_contra h_cast
    --   have : var'.val = var.val := by simp [←h_cast]
    --   have : var.val < assignment.offset := this ▸ var'.is_lt
    --   linarith
  }

def push_var_input_offset (assignment: CellAssignment W S) (row: Fin W) (col: Fin (size S)) :
  (assignment.push_var_input row col).offset = assignment.offset + 1 := by
  simp [push_var_input, Vector.push]

def foldRange (n : ℕ) (f : α → Fin n → α) (init : α) : α :=
  List.finRange n |>.foldl f init

def foldRange_succ (n : ℕ) (f : α → Fin (n + 1) → α) (init : α) :
  foldRange (n + 1) f init = f (foldRange n (fun acc i => f acc i.castSucc) init) (.last n) := by
  simp [foldRange, List.finRange_succ, List.foldl_concat, List.foldl_map]

@[table_assignment_norm]
def push_row (assignment: CellAssignment W S) (row: Fin W) : CellAssignment W S :=
  (List.finRange (size S)).foldl (fun assignment col => push_var_input assignment row col) assignment

lemma push_row_offset (assignment: CellAssignment W S) (row: Fin W) :
  (assignment.push_row row).offset = assignment.offset + size S := by
  -- generalize goal to enable induction
  suffices ∀ n : ℕ, (hs : n ≤ size S) →
    (foldRange n (fun assignment col ↦ assignment.push_var_input row ⟨col, by linarith [col.is_lt]⟩) assignment).offset = assignment.offset + n
    by apply this; rfl
  intro n
  induction n with
  | zero => simp [foldRange]
  | succ n ih =>
    intro hs
    specialize ih (by linarith)
    rw [foldRange_succ, push_var_input_offset]
    simp only [Fin.coe_castSucc]
    rw [ih]
    ac_rfl

-- def push_var_default_input (assignment: CellAssignment W S) (lt: assignment.offset < W * (size S)) : CellAssignment W S :=
--   let index := assignment.offset
--   have nonempty : size S > 0 := by
--       by_contra h'
--       have eq_zero : size S = 0 := by linarith
--       simp [eq_zero] at lt
--   let row : Fin W := ⟨ index / size S, (Nat.div_lt_iff_lt_mul nonempty).mpr lt⟩
--   let col : Fin (size S) := ⟨ index % size S, Nat.mod_lt index nonempty ⟩
--   push_var_input assignment row col

-- def get_vars (assignment: CellAssignment W S) (cell: Cell W S assignment.aux_length) : List (Fin assignment.offset) :=
--   match cell with
--   | .input ⟨ row, col ⟩ => assignment.input_to_vars.get row col
--   | .aux i => assignment.aux_to_vars.get i

@[table_assignment_norm]
def set_var_input (assignment: CellAssignment W S) (row: Fin W) (col: Fin (size S)) (var: ℕ) : CellAssignment W S :=
  -- let current_cell := assignment.vars.get var
  -- change assignment of variable
  let vars := assignment.vars.set? var (.input ⟨ row, col ⟩)
  -- remove variable from existing cell
  -- let input_to_vars := match current_cell with
  --   | .input ⟨ i, j ⟩ => assignment.input_to_vars.update i j (.filter (· = var))
  --   | .aux _ => assignment.input_to_vars
  -- let aux_to_vars := match current_cell with
  --   | .input _ => assignment.aux_to_vars
  --   | .aux i => assignment.aux_to_vars.update i (.filter (· = var))
  -- -- add variable to new cell
  -- let input_to_vars := input_to_vars.update row col (fun l => l ++ [var])
  {
    -- offset := assignment.offset
    aux_length := assignment.aux_length
    vars := vars
    -- input_to_vars := input_to_vars
    -- aux_to_vars := aux_to_vars
    -- input_cell_consistent := by sorry
    -- aux_cell_consistent := by sorry
  }

@[table_assignment_norm]
def default_from_offset (W: ℕ+) (offset : ℕ) : CellAssignment W S := push_vars_aux (.empty W) offset

lemma default_from_offset_offset (n : ℕ) : (default_from_offset (S:=S) W n).offset = n := by
  simp [default_from_offset, push_vars_aux_offset]

-- TODO: operations that modify a cell assignment while maintaining the invariants:
-- - add a new variable
-- - add a row of variables
-- - assign a variable from an aux cell to an input cell
-- - assign a variable from an input cell to a different input cell
end CellAssignment

/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  offset, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  circuit : OperationsList F
  assignment : CellAssignment W S
  -- /-- invariant: the `circuit` and the `assignment` have the same number of variables -/
  offset_consistent : circuit.offset = assignment.offset

variable [Field F]  {α : Type}

namespace TableContext
/--
  An empty context has offset zero, and all variables are assigned by default to the first cell
-/
@[reducible, table_norm, table_assignment_norm]
def empty : TableContext W S F where
  circuit := .from_offset 0
  assignment := .empty W
  offset_consistent := rfl

@[reducible, table_norm, table_assignment_norm]
def offset (table : TableContext W S F) : ℕ := table.circuit.offset

@[reducible, table_assignment_norm]
def aux_length (table : TableContext W S F) : ℕ := table.assignment.aux_length

@[table_norm, table_assignment_norm]
def from_offset (n : ℕ) : TableContext W S F where
  circuit := .from_offset n
  assignment := .default_from_offset W n
  offset_consistent := by rw [CellAssignment.default_from_offset_offset]

structure TableContextOfCircuit (W: ℕ+) (S : Type → Type) (F : Type) [ProvableType S] [Field F] (ops: OperationsList F) where
  ctx: TableContext W S F
  circuit_consistent : ctx.circuit = ops

def from_circuit (W: ℕ+) (S : Type → Type) (F : Type) [ProvableType S] [Field F]
  (ops: OperationsList F) : TableContext W S F :=
  (from_circuit_with_consistency ops).ctx
where
/--
`circuit_consistent` is needed within the function definition itself,
for adding subcircuits to the result of a recursive call
-/
@[table_assignment_norm]
from_circuit_with_consistency : (ops : OperationsList F) → TableContextOfCircuit W S F ops
  | ⟨_, .empty n⟩ => ⟨.from_offset n, rfl⟩
  | ⟨n + _, .witness ops m c⟩ =>
    let ⟨prev, h⟩ := from_circuit_with_consistency ops
    let assignment := prev.assignment.push_vars_aux m
    ⟨{ prev with
      circuit := prev.circuit.witness m c
      assignment
      offset_consistent := by
        simp only [assignment]
        rw [prev.assignment.push_vars_aux_offset m, prev.offset_consistent]
    }, by simp [h]⟩
  | ⟨n, .assert ops e⟩ =>
    let ⟨prev, h⟩ := from_circuit_with_consistency ops
    ⟨{ prev with circuit := prev.circuit.assert e }, by simp [h]⟩
  | ⟨n, .lookup ops l⟩ =>
    let ⟨prev, h⟩ := from_circuit_with_consistency ops
    ⟨{ prev with circuit := prev.circuit.lookup l }, by simp [h]⟩
  | ⟨n + _, .subcircuit ops s⟩ =>
    let ⟨prev, h⟩ := from_circuit_with_consistency ops
    let subcircuit : SubCircuit F prev.circuit.offset := cast (by rw [h]) s
    let assignment := prev.assignment.push_vars_aux subcircuit.witness_length
    ⟨{ prev with
      circuit := prev.circuit.subcircuit subcircuit
      assignment
      offset_consistent := by
        simp only [assignment]
        rw [prev.assignment.push_vars_aux_offset _, ← prev.offset_consistent]
    }, by
      simp [h, subcircuit]
      constructor <;> {
        congr
        repeat rw [h]
        apply cast_heq
      }
    ⟩

end TableContext

-- TODO why is simp not able to use this?
@[table_norm, table_assignment_norm]
theorem from_circuit_circuit : ∀ ops, (TableContext.from_circuit W S F ops).circuit = ops := by
  intro ops
  simp only [TableContext.from_circuit]
  rw [TableContext.TableContextOfCircuit.circuit_consistent]

@[table_assignment_norm]
theorem from_circuit_offset : ∀ ops, (TableContext.from_circuit W S F ops).assignment.offset = ops.offset := by
  intro ops
  rw [← TableContext.offset_consistent, from_circuit_circuit]

@[reducible, table_norm, table_assignment_norm]
def TableConstraint (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] :=
  StateM (TableContext W S F)

@[table_norm, table_assignment_norm]
instance : MonadLift (Circuit F) (TableConstraint W S F) where
  monadLift circuit ctx :=
    let res := circuit ctx.circuit
    (res.fst, .from_circuit W S F res.snd)

namespace TableConstraint
@[reducible, table_norm]
def final_offset (table : TableConstraint W S F α) : ℕ :=
  table .empty |>.snd.circuit.offset

@[table_norm]
def operations (table : TableConstraint W S F α) : Operations F table.final_offset :=
  table .empty |>.snd.circuit.withLength

@[table_assignment_norm]
def assignment (table : TableConstraint W S F α) : CellAssignment W S :=
  table .empty |>.snd.assignment

-- construct an env by taking the result of the assignment function for input/output cells,
-- and allowing arbitrary values for aux cells and invalid variables
def window_env (table : TableConstraint W S F Unit)
  (window: TraceOfLength F S W) (aux_env : Environment F) : Environment F :=
  let ctx := table .empty |>.snd
  .mk fun i =>
    if hi : i < ctx.assignment.offset then
      match ctx.assignment.vars.get ⟨i, hi⟩ with
      | .input ⟨i, j⟩ => window.get i j
      | .aux k => aux_env.get k
    else aux_env.get (i + ctx.assignment.aux_length)

/--
  A table constraint holds on a window of rows if the constraints hold on a suitable environment.
  In particular, we construct the environment by taking directly the result of the assignment function
  so that every variable evaluate to the trace cell value which is assigned to
-/
@[table_norm]
def constraints_hold_on_window (table : TableConstraint W S F Unit)
  (window: TraceOfLength F S W) (aux_env : Environment F) : Prop :=
  let env := window_env table window aux_env

  -- then we fold over allocated sub-circuits
  -- lifting directly to the soundness of the sub-circuit
  Circuit.constraints_hold.soundness env table.operations

@[table_norm]
def output {α: Type} {W: ℕ+} (table : TableConstraint W S F α) : α :=
  table .empty |>.fst

/--
  Get a fresh variable for each cell in a given row
-/
@[table_norm, table_assignment_norm]
def get_row {W: ℕ+} (row : Fin W) : TableConstraint W S F (Var S F) :=
  modifyGet fun ctx =>
    let vars := Vector.init (fun i => ⟨ctx.offset + i⟩)
    let exprs := vars.map Expression.var
    let ctx' : TableContext W S F := {
      circuit := ctx.circuit.witness (size S) (fun eval => exprs.map eval),
      assignment := ctx.assignment.push_row row,
      offset_consistent := by
        show ctx.circuit.offset + size S = _
        rw [CellAssignment.push_row_offset, ctx.offset_consistent]
    }
    (from_vars exprs, ctx')

/--
  Get a fresh variable for each cell in the current row
-/
@[table_norm, table_assignment_norm]
def get_curr_row {W: ℕ+} : TableConstraint W S F (Var S F) := get_row 0

/--
  Get a fresh variable for each cell in the next row
-/
@[table_norm, table_assignment_norm]
def get_next_row {W: ℕ+} : TableConstraint W S F (Var S F) := get_row 1

@[table_assignment_norm]
def assign_var {W: ℕ+} (off : CellOffset W S) (v : Variable F) : TableConstraint W S F Unit :=
  modify fun ctx =>
    -- a valid variable is assigned directly
    -- if h : v.index < ctx.offset then
    let assignment := ctx.assignment.set_var_input off.rowOffset off.column v.index
    { ctx with assignment }
    -- for invalid variables, we create a new valid variable and add a constraint that they are equal
    -- (this branch should in practice never be taken)
    -- else
    --   let new_var : Variable F := ⟨ ctx.offset ⟩
    --   let circuit := ctx.circuit
    --     |>.witness 1 (fun eval => vec [eval v])
    --     |>.assert (v - new_var)
    --   let assignment := ctx.assignment.push_var_input off.rowOffset off.column
    --   { circuit, assignment,
    --     offset_consistent := by
    --       show ctx.circuit.offset + 1 = _
    --       rw [CellAssignment.push_var_input_offset, ctx.offset_consistent]
    --   }

@[table_norm, table_assignment_norm]
theorem assign_var_circuit : ∀ ctx (off : CellOffset W S) (v : Variable F),
  (assign_var off v ctx).snd.circuit = ctx.circuit := by intros; rfl

@[table_norm, table_assignment_norm]
def assign {W: ℕ+} (off : CellOffset W S) (x : Expression F): TableConstraint W S F Unit := do
  -- TODO we would like to match on var vs other expressions here.
  -- `| .var v => assign_var off v`
  -- however, that makes the circuit almost impossible to resolve in proofs, since the expression kind
  -- can be buried deep within subcircuits that created the expression.
  let new_var ← witness_var x.eval
  assert_zero (x - var new_var) -- there could be an optimization pass that reduces redundant vars
  assign_var off new_var

@[table_norm, table_assignment_norm]
def assign_next_row {W: ℕ+} (next : Var S F) : TableConstraint W S F Unit :=
  let vars := to_vars next
  for i in List.finRange (size S) do
    assign (.next i) (vars.get i)

attribute [table_norm] size
attribute [table_norm, table_assignment_norm] to_elements
attribute [table_norm] from_elements
attribute [table_norm] to_vars
attribute [table_norm] from_vars

attribute [table_norm] Circuit.constraints_hold.soundness

attribute [table_norm, table_assignment_norm] liftM
attribute [table_norm, table_assignment_norm] monadLift
attribute [table_norm, table_assignment_norm] bind
attribute [table_norm, table_assignment_norm] StateT.bind
attribute [table_norm, table_assignment_norm] modify
attribute [table_norm, table_assignment_norm] modifyGet
attribute [table_norm, table_assignment_norm] MonadStateOf.modifyGet
attribute [table_norm, table_assignment_norm] StateT.modifyGet
end TableConstraint

export TableConstraint (get_curr_row get_next_row assign assign_next_row)

@[reducible]
def SingleRowConstraint (S : Type → Type) (F : Type) [Field F] [ProvableType S] := TableConstraint 1 S F Unit

@[reducible]
def TwoRowsConstraint (S : Type → Type) (F : Type) [Field F] [ProvableType S] := TableConstraint 2 S F Unit

inductive TableOperation (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | Boundary: ℕ → SingleRowConstraint S F → TableOperation S F

  /--
    An `EveryRow` constraint is a constraint that is applied to every row.
    It can only reference cells on the same row
  -/
  | EveryRow: SingleRowConstraint S F → TableOperation S F

  /--
    An `EveryRowExceptLast` constraint is a constraint that is applied to every row except the last.
    It can reference cells from the current row, or the next row.

    Note that this will not apply any constraints to a trace of length one.
  -/
  | EveryRowExceptLast: TwoRowsConstraint S F → TableOperation S F


/--
  The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
@[table_norm]
def table_constraints_hold {N : ℕ} (constraints : List (TableOperation S F))
  (trace: TraceOfLength F S N) (env: ℕ → ℕ → Environment F) : Prop :=
  let constraints_and_envs := constraints.mapIdx (fun i cs => (cs, env i))
  foldl constraints_and_envs trace.val constraints_and_envs
  where
  /--
    The foldl function applies the constraints to the trace inductively on the trace

    We want to write something like:
    ```
    for row in trace:
      for constraint in constraints:
        apply constraint to row
    ```
    in this exact order, so that the row-inductive structure is at the top-level.

    We do double induction: first on the trace, then on the constraints: we apply every constraint to the current row, and
    then recurse on the rest of the trace.
    `cs` is the list of constraints that we have to apply and it is never changed during the induction
    `cs_iterator` is walked inductively for every row.
    Once the `cs_iterator` is empty, we start again on the rest of the trace with the initial constraints `cs`
  -/
  @[table_norm]
  foldl (cs : List (TableOperation S F × (ℕ → (Environment F)))) :
    Trace F S → (cs_iterator: List (TableOperation S F × (ℕ → (Environment F)))) → Prop
    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (⟨.EveryRowExceptLast constraint, env⟩)::rest =>
        let others := foldl cs (trace +> curr +> next) rest
        let window : TraceOfLength F S 2 := ⟨<+> +> curr +> next, rfl ⟩
        constraint.constraints_hold_on_window window (env (trace.len + 1)) ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (⟨.Boundary idx constraint, env⟩)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        if trace.len = idx then constraint.constraints_hold_on_window window (env trace.len) ∧ others else others

    -- if the trace has at least one row and the constraint is a "every row" constraint, we apply the constraint
    | trace +> row, (⟨.EveryRow constraint, env⟩)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        constraint.constraints_hold_on_window window (env trace.len) ∧ others

    -- if the trace has not enough rows for the "every row except last" constraint, we skip the constraint
    | trace, (⟨.EveryRowExceptLast _, _⟩)::rest =>
        foldl cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl cs trace cs

    -- if the trace is empty, we are done
    | <+>, _ => True


structure FormalTable (F : Type) [Field F] (S : Type → Type) [ProvableType S] where
  -- list of constraints that are applied over the table
  constraints : List (TableOperation S F)

  -- optional assumption on the table length
  assumption : ℕ → Prop := fun _ => True

  -- specification for the table
  spec {N : ℕ} : TraceOfLength F S N → Prop

  -- the soundness states that if the assumptions hold, then
  -- the constraints hold implies that the spec holds
  soundness :
    ∀ (N : ℕ) (trace: TraceOfLength F S N) (env: ℕ → ℕ → Environment F),
    assumption N →
    table_constraints_hold constraints trace env →
    spec trace
