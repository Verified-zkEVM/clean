module

public import Clean.Backends.Plonky3.Codegen
public import Clean.Backends.Plonky3.Program

@[expose] public section

/-!
# Correctness of the witness IR to Rust translation

The Rust model computes exactly the witness IR's values: `program_run` states that running a translated witness program produces the witness IR's output vector, for fields of order at most `2^64`. `witnessBlock_run` and `rowProgram_run` specialize it to component witness blocks and to row programs.
-/

namespace Backends.Plonky3.Codegen

open Rust

variable {F : Type} [FiniteField F]

/-- The prover environment seen by the witness IR when the Rust function reads `env`. -/
def proverEnvironment (env : Env F) : ProverEnvironment F where
  get index := env.row[index]?.getD 0
  data := env.data
  hint := env.hint

/-- The witness IR context matching a Rust frame. `.idx` is the loop variable inside loops and the row index outside. -/
def context (env : Env F) (frame : Frame F) (inLoop : Bool) : Witgen.Ctx F where
  env := proverEnvironment env
  locals := frame.locals
  idx := if inLoop then frame.loopVar else env.rowIndex.toNat

lemma expression_eval (env : Env F) (frame : Frame F) (e : Expression F) :
    (expression e).eval env frame = e.eval (proverEnvironment env).toEnvironment := by
  induction e with
  | var cell => rfl
  | const value => rfl
  | add left right ihLeft ihRight =>
      simp only [expression, FieldExpr.eval, Expression.eval, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp only [expression, FieldExpr.eval, Expression.eval, ihLeft, ihRight]

lemma evalList_eq_getD (ctx : Witgen.Ctx F) :
    ∀ (index : ℕ) (values : List (Witgen.FExpr F)),
      Witgen.FExpr.evalList ctx index values = (values.map (·.eval ctx))[index]?.getD 0
  | _, [] => by simp [Witgen.FExpr.evalList]
  | 0, value :: values => by simp [Witgen.FExpr.evalList]
  | index + 1, value :: values => by
      simp [Witgen.FExpr.evalList, evalList_eq_getD ctx index values]

omit [FiniteField F] in
lemma constants?_eq_some {values : List (Witgen.FExpr F)} {constants : List F}
    (h : constants? values = some constants) : values = constants.map .const := by
  induction values generalizing constants with
  | nil => simp [constants?] at h; simp [← h]
  | cons value values ih =>
      cases value <;> simp [constants?] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      simp [ih hrest]

lemma tableGet_eq (table : String → (n : ℕ) → Array (Vector F n)) (key : String) (width : ℕ)
    (row : UInt64) (column : Fin width) :
    tableGet table key width row column.val =
      ((table key width)[row.toNat]?.getD default)[column.val]'column.isLt := by
  simp only [tableGet]
  cases (table key width)[row.toNat]? with
  | none => simp [default]
  | some values => simp

omit [FiniteField F] in
/-- Bit `bit` of a value below `2^64`, computed on its `u64` representation. -/
lemma testBit_eq_u64 {value bit : ℕ} (hvalue : value < UInt64.size) (hbit : bit < 64) :
    value.testBit bit = decide ((UInt64.ofNat value >>> bit.toUInt64) &&& 1 = 1) := by
  have hbits : ((UInt64.ofNat value >>> bit.toUInt64) &&& 1).toNat = (value >>> bit) % 2 := by
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_ofNat_of_lt' hvalue,
      Nat.mod_eq_of_lt hbit, Nat.and_one_is_mod]
  have hiff : ((UInt64.ofNat value >>> bit.toUInt64) &&& 1 = 1) ↔ (value >>> bit) % 2 = 1 := by
    rw [← UInt64.toNat_inj, hbits]
    simp
  simp only [hiff, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (value >>> bit) with h | h <;> simp [h]

omit [FiniteField F] in
lemma shiftRight_eq_zero {value bit : ℕ} (hvalue : value < UInt64.size) (hbit : 64 ≤ bit) :
    value >>> bit = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  calc value < 2 ^ 64 := hvalue
    _ ≤ 2 ^ bit := Nat.pow_le_pow_right (by norm_num) hbit

omit [FiniteField F] in
lemma testBit_eq_false {value bit : ℕ} (hvalue : value < UInt64.size) (hbit : 64 ≤ bit) :
    value.testBit bit = false := by
  simp [Nat.testBit, shiftRight_eq_zero hvalue hbit]

omit [FiniteField F] in
/-- Bit `index` of a value below `2^64`, as computed by `loopBit`. -/
lemma loopBit_toNat {value index : ℕ} (hvalue : value < UInt64.size) :
    (if index < 64 then (UInt64.ofNat value >>> UInt64.ofNat index) &&& 1 else 0).toNat =
      value >>> index % 2 := by
  split
  · rename_i hindex
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_ofNat_of_lt' hvalue,
      Nat.and_one_is_mod, Nat.mod_eq_of_lt hindex]
  · rename_i hindex
    simp [shiftRight_eq_zero (bit := index) hvalue (by omega)]

lemma val_lt_u64 (hsize : FiniteField.size (F := F) ≤ UInt64.size) (x : F) :
    FiniteField.val x < UInt64.size :=
  Nat.lt_of_lt_of_le (FiniteField.val_lt x) hsize

mutual

theorem fieldExpr_eval (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F) (frame : Frame F) (inLoop : Bool) :
    (e : Witgen.FExpr F) →
      (fieldExpr inLoop e).eval env frame = e.eval (context env frame inLoop)
  | .expr e => expression_eval env frame e
  | .const value => rfl
  | .localVar index => rfl
  | .add left right => by
      simp only [fieldExpr, FieldExpr.eval, Witgen.FExpr.eval,
        fieldExpr_eval hsize env frame inLoop left, fieldExpr_eval hsize env frame inLoop right]
  | .mul left right => by
      simp only [fieldExpr, FieldExpr.eval, Witgen.FExpr.eval,
        fieldExpr_eval hsize env frame inLoop left, fieldExpr_eval hsize env frame inLoop right]
  | .inv value => by
      simp only [fieldExpr, FieldExpr.eval, Witgen.FExpr.eval, fieldExpr_eval hsize env frame inLoop value]
  | .ofU64 value => by
      simp only [fieldExpr, FieldExpr.eval, Witgen.FExpr.eval, u64Expr_eval hsize env frame inLoop value]
  | .ite condition thenValue elseValue => by
      simp only [fieldExpr, FieldExpr.eval, Witgen.FExpr.eval,
        boolExpr_eval hsize env frame inLoop condition, fieldExpr_eval hsize env frame inLoop thenValue,
        fieldExpr_eval hsize env frame inLoop elseValue]
  | .listGet values index => by
      simp only [fieldExpr]
      split
      · rename_i constants hconstants
        rw [constants?_eq_some hconstants]
        simp [FieldExpr.eval, Witgen.FExpr.eval, u64Expr_eval hsize env frame inLoop index,
          evalList_eq_getD, Function.comp_def]
      · simp only [FieldExpr.eval, Witgen.FExpr.eval, u64Expr_eval hsize env frame inLoop index,
          fieldExprList_eval hsize env frame inLoop values, evalList_eq_getD]
  | .dataGet key width row column => by
      simp only [fieldExpr, FieldExpr.eval, Witgen.FExpr.eval, u64Expr_eval hsize env frame inLoop row]
      exact tableGet_eq _ key width _ column
  | .hintGet key width row column => by
      simp only [fieldExpr, FieldExpr.eval, Witgen.FExpr.eval, u64Expr_eval hsize env frame inLoop row]
      exact tableGet_eq _ key width _ column

theorem fieldExprList_eval (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F) (frame : Frame F) (inLoop : Bool) :
    (values : List (Witgen.FExpr F)) →
      FieldExpr.evalList env frame (fieldExprList inLoop values) =
        values.map (·.eval (context env frame inLoop))
  | [] => rfl
  | value :: values => by
      simp only [fieldExprList, FieldExpr.evalList, List.map_cons,
        fieldExpr_eval hsize env frame inLoop value, fieldExprList_eval hsize env frame inLoop values]

theorem u64Expr_eval (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F) (frame : Frame F) (inLoop : Bool) :
    (e : Witgen.U64Expr F) →
      (u64Expr inLoop e).eval env frame = e.eval (context env frame inLoop)
  | .const value => rfl
  | .val value => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval, fieldExpr_eval hsize env frame inLoop value]
  | .idx => by
      cases inLoop <;> simp [u64Expr, U64Expr.eval, Witgen.U64Expr.eval, context]
  | .localVar index => rfl
  | .add left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .mul left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .div left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .mod left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .land left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .lor left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .lxor left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .shiftL left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .shiftR left right => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .ite condition thenValue elseValue => by
      simp only [u64Expr, U64Expr.eval, Witgen.U64Expr.eval,
        boolExpr_eval hsize env frame inLoop condition, u64Expr_eval hsize env frame inLoop thenValue,
        u64Expr_eval hsize env frame inLoop elseValue]

theorem boolExpr_eval (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F) (frame : Frame F) (inLoop : Bool) :
    (e : Witgen.BExpr F) →
      (boolExpr inLoop e).eval env frame = e.eval (context env frame inLoop)
  | .true => rfl
  | .false => rfl
  | .feq left right => by
      simp only [boolExpr, BoolExpr.eval, Witgen.BExpr.eval,
        fieldExpr_eval hsize env frame inLoop left, fieldExpr_eval hsize env frame inLoop right]
  | .neq left right => by
      simp only [boolExpr, BoolExpr.eval, Witgen.BExpr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .lt left right => by
      simp only [boolExpr, BoolExpr.eval, Witgen.BExpr.eval,
        u64Expr_eval hsize env frame inLoop left, u64Expr_eval hsize env frame inLoop right]
  | .flt left right => by
      simp only [boolExpr, BoolExpr.eval, U64Expr.eval, Witgen.BExpr.eval,
        fieldExpr_eval hsize env frame inLoop left, fieldExpr_eval hsize env frame inLoop right]
      have hleft := val_lt_u64 hsize (Witgen.FExpr.eval (context env frame inLoop) left)
      have hright := val_lt_u64 hsize (Witgen.FExpr.eval (context env frame inLoop) right)
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hleft,
        UInt64.toNat_ofNat_of_lt' hright]
  | .bit value bit => by
      simp only [boolExpr, Witgen.BExpr.eval]
      split
      · simp only [BoolExpr.eval, U64Expr.eval, fieldExpr_eval hsize env frame inLoop value]
        rw [testBit_eq_u64 (val_lt_u64 hsize _) ‹_›]
      · rw [testBit_eq_false (val_lt_u64 hsize _) (by omega)]
        rfl
  | .not condition => by
      simp only [boolExpr, BoolExpr.eval, Witgen.BExpr.eval, boolExpr_eval hsize env frame inLoop condition]
  | .and left right => by
      simp only [boolExpr, BoolExpr.eval, Witgen.BExpr.eval,
        boolExpr_eval hsize env frame inLoop left, boolExpr_eval hsize env frame inLoop right]

end

omit [FiniteField F] in
lemma toArray_mapRange {α : Type} (count : ℕ) (create : ℕ → α) :
    (Vector.mapRange count create).toArray = (List.range count).toArray.map create := by
  ext index hleft hright
  · simp
  · simp [Vector.getElem_mapRange]

lemma context_outside_loop (env : Env F) (locals : Array (F ⊕ UInt64)) (loopVar : ℕ) :
    context env ⟨locals, loopVar⟩ false = context env ⟨locals, 0⟩ false := rfl

theorem steps_run (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F)
    (stepList : List (Witgen.Step F)) (locals : Array (F ⊕ UInt64)) (output : Array F) :
    (steps stepList).foldl (Stmt.run env) ⟨locals, output⟩ =
      ⟨Witgen.evalSteps (proverEnvironment env) stepList locals env.rowIndex.toNat, output⟩ := by
  induction stepList generalizing locals with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | letF value =>
          simp only [steps, List.foldl_cons, Stmt.run, Witgen.evalSteps,
            fieldExpr_eval hsize env ⟨locals, 0⟩ false value]
          exact ih _
      | letU value =>
          simp only [steps, List.foldl_cons, Stmt.run, Witgen.evalSteps,
            u64Expr_eval hsize env ⟨locals, 0⟩ false value]
          exact ih _

theorem pushes_run (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F)
    (locals : Array (F ⊕ UInt64)) :
    (values : List (Witgen.FExpr F)) → (out : Array F) →
      (values.map fun value => Stmt.push (fieldExpr false value)).foldl (Stmt.run env)
          ⟨locals, out⟩ =
        ⟨locals, out ++ (values.map (·.eval (context env ⟨locals, 0⟩ false))).toArray⟩
  | [], out => by simp
  | value :: values, out => by
      simp only [List.map_cons, List.foldl_cons, Stmt.run, fieldExpr_eval hsize env,
        pushes_run hsize env locals values]
      simp

theorem output_run (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F)
    (locals : Array (F ⊕ UInt64)) :
    {n : ℕ} → (vector : Witgen.VExpr F n) → (out : Array F) →
      (Codegen.output vector).foldl (Stmt.run env) ⟨locals, out⟩ =
        ⟨locals, out ++ (vector.eval (context env ⟨locals, 0⟩ false)).toArray⟩
  | _, .lit values, out => by
      simp only [Codegen.output, pushes_run hsize env locals, Witgen.VExpr.eval]
      congr 2
      apply Array.ext'
      simp [Vector.toList]
  | _, .mapRange count body, out => by
      simp only [Codegen.output, List.foldl_cons, List.foldl_nil, Stmt.run, Witgen.VExpr.eval,
        toArray_mapRange]
      simp only [fieldExpr_eval hsize env]
      rfl
  | count, .envRange offset, out => by
      simp only [Codegen.output, List.foldl_cons, List.foldl_nil, Stmt.run, Witgen.VExpr.eval,
        toArray_mapRange]
      rfl
  | count, .bitsOf value, out => by
      simp only [Codegen.output, List.foldl_cons, List.foldl_nil, Stmt.run, Witgen.VExpr.eval,
        toArray_mapRange]
      simp only [FieldExpr.eval, U64Expr.eval, fieldExpr_eval hsize env, context_outside_loop,
        loopBit_toNat (val_lt_u64 hsize _)]
  | _, .append left right, out => by
      simp only [Codegen.output, List.foldl_append, output_run hsize env locals left,
        output_run hsize env locals right, Witgen.VExpr.eval, Vector.toArray_append,
        Array.append_assoc]

/-- Running a translated witness program yields the witness IR's output vector. -/
theorem program_run (hsize : FiniteField.size (F := F) ≤ UInt64.size) (env : Env F) {n : ℕ}
    (programSteps : List (Witgen.Step F)) (programOutput : Witgen.VExpr F n) :
    (run env (program programSteps programOutput)).output =
      (programOutput.eval {
        env := proverEnvironment env
        locals := Witgen.evalSteps (proverEnvironment env) programSteps #[] env.rowIndex.toNat
        idx := env.rowIndex.toNat }).toArray := by
  simp only [run, program, List.foldl_append]
  rw [steps_run hsize env programSteps #[] #[], output_run hsize env _ programOutput #[]]
  simp only [Array.empty_append]
  rfl

/-- The Rust function of a component witness block, run on the row built so far, computes the block's witness values. -/
theorem witnessBlock_run (hsize : FiniteField.size (F := F) ≤ UInt64.size) (block : WitnessBlock F)
    (row : Array F) (data : ProverData F) (hint : ProverHint F) :
    (run ⟨row, 0, data, hint⟩ (program block.steps block.output)).output =
      (block.eval { get index := row[index]?.getD 0, data, hint } 0).toArray :=
  program_run hsize ⟨row, 0, data, hint⟩ block.steps block.output

/-- The Rust function of a row program computes its values at `row`. -/
theorem rowProgram_run (hsize : FiniteField.size (F := F) ≤ UInt64.size)
    (rowProgram : Witgen.RowProgram F) (row : UInt64) (hint : ProverHint F) :
    (run ⟨#[], row, fun _ _ => #[], hint⟩ (program rowProgram.steps rowProgram.output)).output =
      (rowProgram.eval row hint).toArray := by
  rw [program_run hsize]
  have henv : proverEnvironment ⟨#[], row, fun _ _ => #[], hint⟩ =
      { get := fun _ => 0, data := fun _ _ => #[], hint } := by
    simp [proverEnvironment]
  simp only [henv]
  rfl

end Backends.Plonky3.Codegen
