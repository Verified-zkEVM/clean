import Clean.Table.Basic

variable {F : Type} {S : Type → Type} {W : ℕ+} [ProvableType S] [Field F]

/--
  Build an index map for auxiliary cells from vars of `CellAssignment` to the cells in a trace row.
  The rule is that the auxiliary cells are appended to the end of the row in order.
  For example: [input<0>, aux<0>, input<1>, input<2>, aux<1>] => {1: 3, 4: 4}
-/
def buildAuxMap (as : CellAssignment W S) : Std.HashMap ℕ ℕ := Id.run do
  let (_, _, map) :=
    as.vars.foldl
      fun (idx, offset, m) cell =>
        match cell with
        | .aux _ => (idx + 1, offset + 1, m.insert idx offset)
        | _ => (idx + 1, offset, m)
      (0, size S, Std.HashMap.emptyWithCapacity)

  map

/--
  Given a trace row, compute the next row in the trace, which includes the auxiliary values.
  The computation logic is obtained from the `TableConstraint` witness generators, each of which
  represents a witness variable corresponding to the `vars` in the `CellAssignment`.

  Mapping for auxiliary columns:
  - The auxiliary cells' mapping from the `CellAssignment` to the aux columns in the trace row
  is done using the `buildAuxMap` function.
  - The generated witnesses are assigned to the corresponding aux columns in next trace row.

  Mapping for input columns:
  - According to `CellAssignment` for input cells, the input columns are assigned to
  the corresponding columns in the trace row.
-/
def generateNextRow (tc : TableConstraint W S F Unit) (cur_row : Array F) : Array F :=
  let ctx := (tc .empty).2

  let assignment := ctx.assignment
  let generators := ctx.circuit.witnessGenerators

  let aux_map := buildAuxMap assignment
  let next_row := Array.replicate cur_row.size 0

  -- evaluate the witness generators
  let (_, next_row) := generators.foldl (fun (idx, next_row) compute =>
      -- env is defined inside the fold so it sees the latest next_row,
      -- allowing later witnesses to depend on earlier aux values.
      let env i :=
        if h : i < assignment.offset then
          match assignment.vars[i] with
          | .input ⟨r, c⟩ =>
              if r = 0 then cur_row[c]! else next_row[c]!
          | .aux _ =>
            next_row[aux_map[i]!]!
        else panic! s!"Invalid variable index {i} in environment"

      let wit := compute ⟨ env, fun _ _ => #[] ⟩

      -- insert the witness value to the next row
      let next_row := if h : idx < assignment.offset then
        let var := assignment.vars[idx]

        match var with
          | .input ⟨r, c⟩ => if r = 1 then next_row.set! c wit else next_row
          | .aux _ => next_row.set! aux_map[idx]! wit
      else panic! s!"Invalid variable index {idx} in environment"

      (idx + 1, next_row)
    )
    (0, next_row)

  next_row

/--
  Generates a trace of length n, starting from the given row.

  Returns an array of rows where each subsequent row is generated using the
  table constraint's witness generators.
-/
def witnesses
    (tc : TableConstraint W S F Unit) (init_row : Row F S) (n : ℕ) : Array (Array F) := Id.run do

  -- append auxiliary columns to the current row
  let aux_cols := Array.replicate tc.finalAssignment.numAux 0
  let cur_row := (toElements init_row).toArray ++ aux_cols

  let mut trace := #[cur_row]
  let mut current := cur_row

  for _ in [: n-1] do
    let next := generateNextRow tc current
    trace := trace.push next
    current := next
  trace

/--
  Like `generateNextRow` but accepts `ProverData F` to pass to witness generators
  (instead of `fun _ _ => #[]`).
-/
def generateNextRowWithData (tc : TableConstraint W S F Unit) (cur_row : Array F)
    (data : ProverData F) : Array F :=
  let ctx := (tc .empty).2
  let assignment := ctx.assignment
  let generators := ctx.circuit.witnessGenerators
  let aux_map := buildAuxMap assignment
  let next_row := Array.replicate cur_row.size 0

  let (_, next_row) := generators.foldl (fun (idx, next_row) compute =>
      -- env is defined inside the fold so it sees the latest next_row,
      -- allowing later witnesses to depend on earlier aux values.
      let env i :=
        if h : i < assignment.offset then
          match assignment.vars[i] with
          | .input ⟨r, c⟩ =>
              if r = 0 then cur_row[c]! else next_row[c]!
          | .aux _ =>
            next_row[aux_map[i]!]!
        else panic! s!"Invalid variable index {i} in environment"

      let wit := compute ⟨ env, data ⟩

      let next_row := if h : idx < assignment.offset then
        let var := assignment.vars[idx]
        match var with
          | .input ⟨r, c⟩ => if r = 1 then next_row.set! c wit else next_row
          | .aux _ => next_row.set! aux_map[idx]! wit
      else panic! s!"Invalid variable index {idx} in environment"

      (idx + 1, next_row)
    )
    (0, next_row)

  next_row

/--
  Like `witnesses` but accepts `ProverData F` and threads it through witness generation.
  Use this when witness generators need access to prover data (e.g., memory tables).
-/
def witnessesWithData
    (tc : TableConstraint W S F Unit) (init_row : Row F S) (n : ℕ)
    (data : ProverData F) : Array (Array F) := Id.run do

  let aux_cols := Array.replicate tc.finalAssignment.numAux 0
  let cur_row := (toElements init_row).toArray ++ aux_cols

  let mut trace := #[cur_row]
  let mut current := cur_row

  for _ in [: n-1] do
    let next := generateNextRowWithData tc current data
    trace := trace.push next
    current := next
  trace
