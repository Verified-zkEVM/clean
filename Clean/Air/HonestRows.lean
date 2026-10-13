module

public import Clean.Air.WitnessGeneration

@[expose] public section

/-!
# Honest rows

A component row whose cells are computed by the component's witness programs is honest: the
environment of its cells, together with the prover data and hint the programs read, uses the
circuit's local witnesses. Circuit completeness then applies to it.

Witness programs read the environment through earlier cells only, which `witgenReadsBelow` checks
syntactically. Reading the same cells, prover-data cells and hint, they compute the same values
(`fexpr_eval_congr` and its siblings).
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

/-! ### Evaluation reads only what it reads -/

/-- A prover-data cell, zero when absent. -/
def dataCell (data : ProverData F) (key : String) (width row column : ℕ) : F :=
  ((data key width)[row]?.bind fun values => values[column]?).getD 0

/-- Two environments agree on the cells a witness program may read: below `n`, at every row of
the prover-data columns in `reads`, and on the hint. -/
structure ReadsAgree (n : ℕ) (reads : List DataRead) (env env' : ProverEnvironment F) : Prop where
  get : ∀ index < n, env.get index = env'.get index
  data : ∀ read ∈ reads, ∀ row,
    dataCell env.data read.key read.width row read.column =
      dataCell env'.data read.key read.width row read.column
  hint : env.hint = env'.hint

namespace ReadsAgree

variable {n : ℕ} {reads reads' : List DataRead} {env env' : ProverEnvironment F}

lemma mono (h : ReadsAgree n reads env env') (hsub : ∀ read ∈ reads', read ∈ reads) :
    ReadsAgree n reads' env env' :=
  ⟨h.get, fun read hread => h.data read (hsub read hread), h.hint⟩

end ReadsAgree

lemma expression_eval_congr_below {n : ℕ} {env env' : Environment F}
    (hget : ∀ index < n, env.get index = env'.get index) :
    (e : Expression F) → expressionReadsBelow n e = true → e.eval env = e.eval env'
  | .var cell, h => by
      simp only [expressionReadsBelow, decide_eq_true_eq] at h
      exact hget _ h
  | .const _, _ => rfl
  | .add left right, h => by
      simp only [expressionReadsBelow, Bool.and_eq_true] at h
      simp only [Expression.eval, expression_eval_congr_below hget left h.1,
        expression_eval_congr_below hget right h.2]
  | .mul left right, h => by
      simp only [expressionReadsBelow, Bool.and_eq_true] at h
      simp only [Expression.eval, expression_eval_congr_below hget left h.1,
        expression_eval_congr_below hget right h.2]

lemma dataGet_eq_dataCell (data : ProverData F) (key : String) (width row : ℕ) (column : Fin width) :
    ((data key width)[row]?.getD default)[column.val]'column.isLt =
      dataCell data key width row column.val := by
  simp only [dataCell]
  cases (data key width)[row]? with
  | none => simp [default]
  | some values => simp

section Congruence

variable {n : ℕ} {env env' : ProverEnvironment F} (locals : Array (F ⊕ UInt64)) (idx : ℕ)

mutual

theorem fexpr_eval_congr : (e : Witgen.FExpr F) → fexprReadsBelow n e = true →
    ReadsAgree n (fexprDataReads e) env env' →
      e.eval { env, locals, idx } = e.eval { env := env', locals, idx }
  | .expr e, hbelow, hagree => expression_eval_congr_below hagree.get e hbelow
  | .const _, _, _ => rfl
  | .localVar _, _, _ => rfl
  | .add left right, hbelow, hagree => by
      simp only [fexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.FExpr.eval,
        fexpr_eval_congr left hbelow.1 (hagree.mono fun _ h => by simp [fexprDataReads, h]),
        fexpr_eval_congr right hbelow.2 (hagree.mono fun _ h => by simp [fexprDataReads, h])]
  | .mul left right, hbelow, hagree => by
      simp only [fexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.FExpr.eval,
        fexpr_eval_congr left hbelow.1 (hagree.mono fun _ h => by simp [fexprDataReads, h]),
        fexpr_eval_congr right hbelow.2 (hagree.mono fun _ h => by simp [fexprDataReads, h])]
  | .inv value, hbelow, hagree => by
      simp only [fexprReadsBelow] at hbelow
      simp only [Witgen.FExpr.eval,
        fexpr_eval_congr value hbelow (hagree.mono fun _ h => by simp [fexprDataReads, h])]
  | .ofU64 value, hbelow, hagree => by
      simp only [fexprReadsBelow] at hbelow
      simp only [Witgen.FExpr.eval,
        u64expr_eval_congr value hbelow (hagree.mono fun _ h => by simp [fexprDataReads, h])]
  | .ite condition thenValue elseValue, hbelow, hagree => by
      simp only [fexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.FExpr.eval,
        bexpr_eval_congr condition hbelow.1.1 (hagree.mono fun _ h => by simp [fexprDataReads, h]),
        fexpr_eval_congr thenValue hbelow.1.2 (hagree.mono fun _ h => by simp [fexprDataReads, h]),
        fexpr_eval_congr elseValue hbelow.2 (hagree.mono fun _ h => by simp [fexprDataReads, h])]
  | .listGet values index, hbelow, hagree => by
      simp only [fexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.FExpr.eval,
        u64expr_eval_congr index hbelow.2 (hagree.mono fun _ h => by simp [fexprDataReads, h])]
      exact fexprList_evalList_congr _ values hbelow.1
        (hagree.mono fun _ h => by simp [fexprDataReads, h])
  | .dataGet key width row column, hbelow, hagree => by
      simp only [fexprReadsBelow] at hbelow
      have hrow := u64expr_eval_congr row hbelow
        (hagree.mono fun _ h => by simp [fexprDataReads, h])
      simp only [Witgen.FExpr.eval, dataGet_eq_dataCell, hrow]
      exact hagree.data ⟨key, width, column.val, false⟩ (by simp [fexprDataReads]) _
  | .hintGet key width row column, hbelow, hagree => by
      simp only [fexprReadsBelow] at hbelow
      have hrow := u64expr_eval_congr row hbelow
        (hagree.mono fun _ h => by simp [fexprDataReads, h])
      simp only [Witgen.FExpr.eval, hrow, hagree.hint]

theorem fexprList_evalList_congr : (index : ℕ) → (values : List (Witgen.FExpr F)) →
    fexprListReadsBelow n values = true → ReadsAgree n (fexprListDataReads values) env env' →
      Witgen.FExpr.evalList { env, locals, idx } index values =
        Witgen.FExpr.evalList { env := env', locals, idx } index values
  | _, [], _, _ => rfl
  | 0, value :: values, hbelow, hagree => by
      simp only [fexprListReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.FExpr.evalList]
      exact fexpr_eval_congr value hbelow.1
        (hagree.mono fun _ h => by simp [fexprListDataReads, h])
  | index + 1, value :: values, hbelow, hagree => by
      simp only [fexprListReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.FExpr.evalList]
      exact fexprList_evalList_congr index values hbelow.2
        (hagree.mono fun _ h => by simp [fexprListDataReads, h])

theorem u64expr_eval_congr : (e : Witgen.U64Expr F) → u64exprReadsBelow n e = true →
    ReadsAgree n (u64exprDataReads e) env env' →
      e.eval { env, locals, idx } = e.eval { env := env', locals, idx }
  | .const _, _, _ => rfl
  | .idx, _, _ => rfl
  | .localVar _, _, _ => rfl
  | .val value, hbelow, hagree => by
      simp only [u64exprReadsBelow] at hbelow
      simp only [Witgen.U64Expr.eval,
        fexpr_eval_congr value hbelow (hagree.mono fun _ h => by simp [u64exprDataReads, h])]
  | .add left right, hbelow, hagree | .mul left right, hbelow, hagree |
    .div left right, hbelow, hagree | .mod left right, hbelow, hagree |
    .land left right, hbelow, hagree | .lor left right, hbelow, hagree |
    .lxor left right, hbelow, hagree | .shiftL left right, hbelow, hagree |
    .shiftR left right, hbelow, hagree => by
      simp only [u64exprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.U64Expr.eval,
        u64expr_eval_congr left hbelow.1 (hagree.mono fun _ h => by simp [u64exprDataReads, h]),
        u64expr_eval_congr right hbelow.2 (hagree.mono fun _ h => by simp [u64exprDataReads, h])]
  | .ite condition thenValue elseValue, hbelow, hagree => by
      simp only [u64exprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.U64Expr.eval,
        bexpr_eval_congr condition hbelow.1.1 (hagree.mono fun _ h => by simp [u64exprDataReads, h]),
        u64expr_eval_congr thenValue hbelow.1.2
          (hagree.mono fun _ h => by simp [u64exprDataReads, h]),
        u64expr_eval_congr elseValue hbelow.2
          (hagree.mono fun _ h => by simp [u64exprDataReads, h])]

theorem bexpr_eval_congr : (e : Witgen.BExpr F) → bexprReadsBelow n e = true →
    ReadsAgree n (bexprDataReads e) env env' →
      e.eval { env, locals, idx } = e.eval { env := env', locals, idx }
  | .true, _, _ => rfl
  | .false, _, _ => rfl
  | .feq left right, hbelow, hagree | .flt left right, hbelow, hagree => by
      simp only [bexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.BExpr.eval,
        fexpr_eval_congr left hbelow.1 (hagree.mono fun _ h => by simp [bexprDataReads, h]),
        fexpr_eval_congr right hbelow.2 (hagree.mono fun _ h => by simp [bexprDataReads, h])]
  | .neq left right, hbelow, hagree | .lt left right, hbelow, hagree => by
      simp only [bexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.BExpr.eval,
        u64expr_eval_congr left hbelow.1 (hagree.mono fun _ h => by simp [bexprDataReads, h]),
        u64expr_eval_congr right hbelow.2 (hagree.mono fun _ h => by simp [bexprDataReads, h])]
  | .bit value _, hbelow, hagree => by
      simp only [bexprReadsBelow] at hbelow
      simp only [Witgen.BExpr.eval,
        fexpr_eval_congr value hbelow (hagree.mono fun _ h => by simp [bexprDataReads, h])]
  | .not condition, hbelow, hagree => by
      simp only [bexprReadsBelow] at hbelow
      simp only [Witgen.BExpr.eval,
        bexpr_eval_congr condition hbelow (hagree.mono fun _ h => by simp [bexprDataReads, h])]
  | .and left right, hbelow, hagree => by
      simp only [bexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.BExpr.eval,
        bexpr_eval_congr left hbelow.1 (hagree.mono fun _ h => by simp [bexprDataReads, h]),
        bexpr_eval_congr right hbelow.2 (hagree.mono fun _ h => by simp [bexprDataReads, h])]

end

end Congruence

section ProgramCongruence

variable {n : ℕ} {env env' : ProverEnvironment F}

theorem vexpr_eval_congr (locals : Array (F ⊕ UInt64)) (idx : ℕ) : {m : ℕ} → (v : Witgen.VExpr F m) →
    vexprReadsBelow n v = true → ReadsAgree n (vexprDataReads v) env env' →
      v.eval { env, locals, idx } = v.eval { env := env', locals, idx }
  | _, .lit values, hbelow, hagree => by
      simp only [vexprReadsBelow, List.all_eq_true] at hbelow
      simp only [Witgen.VExpr.eval]
      apply Vector.map_congr_left
      intro value hvalue
      have hmem : value ∈ values.toList := by simpa using hvalue
      exact fexpr_eval_congr locals idx value (hbelow value hmem)
        (hagree.mono fun read h => by
          simp only [vexprDataReads, List.mem_flatMap]
          exact ⟨value, hmem, h⟩)
  | _, .mapRange _ body, hbelow, hagree => by
      simp only [vexprReadsBelow] at hbelow
      simp only [Witgen.VExpr.eval]
      congr 1
      funext index
      exact fexpr_eval_congr locals index body hbelow (hagree.mono fun _ h => by simpa [vexprDataReads])
  | m, .envRange offset, hbelow, hagree => by
      simp only [vexprReadsBelow, decide_eq_true_eq] at hbelow
      ext index hindex
      simp only [Witgen.VExpr.eval, Vector.getElem_mapRange]
      exact hagree.get _ (by omega)
  | _, .bitsOf value, hbelow, hagree => by
      simp only [vexprReadsBelow] at hbelow
      simp only [Witgen.VExpr.eval,
        fexpr_eval_congr locals idx value hbelow (hagree.mono fun _ h => by simpa [vexprDataReads])]
  | _, .append left right, hbelow, hagree => by
      simp only [vexprReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.VExpr.eval,
        vexpr_eval_congr locals idx left hbelow.1 (hagree.mono fun _ h => by simp [vexprDataReads, h]),
        vexpr_eval_congr locals idx right hbelow.2 (hagree.mono fun _ h => by simp [vexprDataReads, h])]

theorem evalSteps_congr (idx : ℕ) : (steps : List (Witgen.Step F)) → (locals : Array (F ⊕ UInt64)) →
    steps.all (stepReadsBelow n) = true → ReadsAgree n (steps.flatMap stepDataReads) env env' →
      Witgen.evalSteps env steps locals idx = Witgen.evalSteps env' steps locals idx
  | [], _, _, _ => rfl
  | step :: steps, locals, hbelow, hagree => by
      simp only [List.all_cons, Bool.and_eq_true] at hbelow
      have hrest := hagree.mono fun read h => by
        simp only [List.flatMap_cons, List.mem_append]
        exact .inr h
      cases step with
      | letF value =>
          simp only [Witgen.evalSteps]
          rw [fexpr_eval_congr locals idx value hbelow.1 (hagree.mono fun _ h => by
            simp [stepDataReads, h])]
          exact evalSteps_congr idx steps _ hbelow.2 hrest
      | letU value =>
          simp only [Witgen.evalSteps]
          rw [u64expr_eval_congr locals idx value hbelow.1 (hagree.mono fun _ h => by
            simp [stepDataReads, h])]
          exact evalSteps_congr idx steps _ hbelow.2 hrest
      | read key width row column proposal =>
          simp only [stepReadsBelow, Bool.and_eq_true] at hbelow
          have hrow := u64expr_eval_congr locals idx row hbelow.1.1 (hagree.mono fun _ h => by
            simp [stepDataReads, h])
          have hcell : (Witgen.FExpr.dataGet key width row column).eval { env, locals, idx } =
              (Witgen.FExpr.dataGet key width row column).eval { env := env', locals, idx } := by
            simp only [Witgen.FExpr.eval, dataGet_eq_dataCell, hrow]
            exact hagree.data ⟨key, width, column.val, true⟩ (by simp [stepDataReads]) _
          simp only [Witgen.evalSteps]
          rw [hcell]
          exact evalSteps_congr idx steps _ hbelow.2 hrest

/-- A witness program reading only below `n` computes the same values in environments that agree
on what it reads. -/
theorem witgen_eval_congr {m : ℕ} (code : Witgen.WitgenIR F m) (hbelow : witgenReadsBelow n code = true)
    (hagree : ReadsAgree n (witnessDataReads code) env env') : code.eval env = code.eval env' := by
  cases code with
  | native => simp [witgenReadsBelow] at hbelow
  | ir steps output =>
      simp only [witgenReadsBelow, Bool.and_eq_true] at hbelow
      simp only [Witgen.WitgenIR.eval]
      rw [evalSteps_congr 0 steps #[] hbelow.1 (hagree.mono fun _ h => by
        simp [witnessDataReads, h])]
      exact vexpr_eval_congr _ 0 output hbelow.2 (hagree.mono fun _ h => by
        simp [witnessDataReads, h])

end ProgramCongruence

/-! ### Honest witness values -/

/-- The prover environment of a row's cells, the prover data and the hint. -/
def rowEnvironment (values : Array F) (data : ProverData F) (hint : ProverHint F) :
    ProverEnvironment F where
  get index := values[index]?.getD 0
  data
  hint

/-- One witness operation, computed from the row built so far, the prover data and the hint. -/
def honestStep (data : ProverData F) (hint : ProverHint F) (acc : Array F) :
    FlatOperation F → Array F
  | .witness _ code => acc ++ (code.eval (rowEnvironment acc data hint)).toArray
  | .assert _ | .lookup _ | .interact _ => acc

/-- A row's cells, computed from its input by the witness operations in order. -/
def honestWitgen (data : ProverData F) (hint : ProverHint F) (ops : List (FlatOperation F))
    (input : Array F) : Array F :=
  ops.foldl (honestStep data hint) input

lemma honestWitgen_size (data : ProverData F) (hint : ProverHint F) :
    (ops : List (FlatOperation F)) → (input : Array F) →
      (honestWitgen data hint ops input).size = input.size + FlatOperation.localLength ops
  | [], _ => rfl
  | .witness m code :: ops, input => by
      simp only [honestWitgen, List.foldl_cons, honestStep]
      rw [← honestWitgen, honestWitgen_size data hint ops, FlatOperation.localLength]
      simp only [Array.size_append, Vector.size_toArray]
      omega
  | .assert _ :: ops, input | .lookup _ :: ops, input | .interact _ :: ops, input => by
      simp only [honestWitgen, List.foldl_cons, honestStep]
      rw [← honestWitgen, honestWitgen_size data hint ops, FlatOperation.localLength]

lemma honestWitgen_getElem? (data : ProverData F) (hint : ProverHint F) :
    (ops : List (FlatOperation F)) → (input : Array F) → (index : ℕ) → index < input.size →
      (honestWitgen data hint ops input)[index]? = input[index]?
  | [], _, _, _ => rfl
  | .witness m code :: ops, input, index, hindex => by
      simp only [honestWitgen, List.foldl_cons, honestStep]
      rw [← honestWitgen, honestWitgen_getElem? data hint ops _ index (by simp; omega),
        Array.getElem?_append_left hindex]
  | .assert _ :: ops, input, index, hindex | .lookup _ :: ops, input, index, hindex |
    .interact _ :: ops, input, index, hindex => by
      simp only [honestWitgen, List.foldl_cons, honestStep]
      rw [← honestWitgen, honestWitgen_getElem? data hint ops _ index hindex]

/-- The cells computed by honest witness generation use the local witnesses of the operations. -/
theorem honestWitgen_usesLocalWitnesses (data : ProverData F) (hint : ProverHint F) :
    (ops : List (FlatOperation F)) → (input : Array F) → flatReadsBelow input.size ops = true →
      (rowEnvironment (honestWitgen data hint ops input) data hint).UsesLocalWitnessesFlat
        input.size ops
  | [], _, _ => trivial
  | .witness m code :: ops, input, hbelow => by
      simp only [flatReadsBelow, Bool.and_eq_true] at hbelow
      set values := honestWitgen data hint (.witness m code :: ops) input
      have hstep : values = honestWitgen data hint ops
          (input ++ (code.eval (rowEnvironment input data hint)).toArray) := rfl
      have hsize : (input ++ (code.eval (rowEnvironment input data hint)).toArray).size =
          m + input.size := by simp; omega
      have heval : code.eval (rowEnvironment values data hint) =
          code.eval (rowEnvironment input data hint) := by
        apply witgen_eval_congr code hbelow.1
        refine ⟨fun index hindex => ?_, fun _ _ _ => rfl, rfl⟩
        simp only [rowEnvironment, hstep]
        rw [honestWitgen_getElem? data hint ops _ index (by simp; omega),
          Array.getElem?_append_left hindex]
      constructor
      · intro index
        rw [heval]
        simp only [rowEnvironment]
        rw [hstep, honestWitgen_getElem? data hint ops _ _ (by simp),
          Array.getElem?_append_right (by omega)]
        simp [rowEnvironment]
      · have := honestWitgen_usesLocalWitnesses data hint ops _ (hsize ▸ hbelow.2)
        rw [hsize] at this
        exact this
  | .assert _ :: ops, input, hbelow | .lookup _ :: ops, input, hbelow |
    .interact _ :: ops, input, hbelow => by
      simp only [flatReadsBelow] at hbelow
      exact ⟨trivial, honestWitgen_usesLocalWitnesses data hint ops input hbelow⟩

/-! ### The generator computes honest rows -/

/-- The generator's view of the prover-data cells read by `reads` agrees with `data`: its data
snapshot does, and read steps find the cells defined in its rows. -/
def ViewAgrees (states : List (ComponentState F)) (snapshot data : ProverData F)
    (reads : List DataRead) : Prop :=
  ∀ read ∈ reads, ∀ row,
    dataCell snapshot read.key read.width row read.column =
      dataCell data read.key read.width row read.column ∧
    readCell states [] read.key read.width row read.column =
      some (dataCell data read.key read.width row read.column)

lemma ViewAgrees.mono {states : List (ComponentState F)} {snapshot data : ProverData F}
    {reads reads' : List DataRead} (h : ViewAgrees states snapshot data reads)
    (hsub : ∀ read ∈ reads', read ∈ reads) : ViewAgrees states snapshot data reads' :=
  fun read hread => h read (hsub read hread)

lemma runSteps_eq_evalSteps (states : List (ComponentState F)) {n : ℕ}
    {env env' : ProverEnvironment F} (hget : ∀ index < n, env.get index = env'.get index)
    (hhint : env.hint = env'.hint) :
    (steps : List (Witgen.Step F)) → (locals : Array (F ⊕ UInt64)) →
      steps.all (stepReadsBelow n) = true →
      ViewAgrees states env.data env'.data (steps.flatMap stepDataReads) →
      runSteps states env steps locals [] = (Witgen.evalSteps env' steps locals 0, [])
  | [], _, _, _ => rfl
  | step :: steps, locals, hbelow, hview => by
      simp only [List.all_cons, Bool.and_eq_true] at hbelow
      have hrest := hview.mono fun read h => by
        simp only [List.flatMap_cons, List.mem_append]
        exact .inr h
      have hagree (reads : List DataRead) (hsub : ∀ read ∈ reads, read ∈ stepDataReads step) :
          ReadsAgree n reads env env' :=
        ⟨hget, fun read hread row => (hview read (by simp [hsub read hread]) row).1, hhint⟩
      cases step with
      | letF value =>
          simp only [runSteps, Witgen.evalSteps]
          rw [fexpr_eval_congr locals 0 value hbelow.1 (hagree _ fun _ h => by simpa [stepDataReads])]
          exact runSteps_eq_evalSteps states hget hhint steps _ hbelow.2 hrest
      | letU value =>
          simp only [runSteps, Witgen.evalSteps]
          rw [u64expr_eval_congr locals 0 value hbelow.1 (hagree _ fun _ h => by simpa [stepDataReads])]
          exact runSteps_eq_evalSteps states hget hhint steps _ hbelow.2 hrest
      | read key width row column proposal =>
          simp only [stepReadsBelow, Bool.and_eq_true] at hbelow
          have hrow := u64expr_eval_congr locals 0 row hbelow.1.1 (hagree _ fun _ h => by
            simp [stepDataReads, h])
          have hcell := (hview ⟨key, width, column.val, true⟩ (by simp [stepDataReads])
            (Witgen.U64Expr.eval { env, locals } row).toNat).2
          simp only [runSteps, Witgen.evalSteps, hcell]
          rw [show (Witgen.FExpr.dataGet key width row column).eval { env := env', locals, idx := 0 } =
              dataCell env'.data key width (Witgen.U64Expr.eval { env, locals } row).toNat column.val by
            simp only [Witgen.FExpr.eval, dataGet_eq_dataCell]
            rw [← hrow]]
          exact runSteps_eq_evalSteps states hget hhint steps _ hbelow.2 hrest

/-- Every witness operation of `ops` is a structured program, whose reads agree. -/
def ViewAgreesOps (states : List (ComponentState F)) (snapshot data : ProverData F)
    (ops : List (FlatOperation F)) : Prop :=
  ∀ op ∈ ops, ∀ m (code : Witgen.WitgenIR F m), op = .witness m code →
    ViewAgrees states snapshot data (witnessDataReads code)

/-- The generator computes a row as honest witness generation over prover data its view agrees
with, and defines no cell. -/
theorem witgen_eq_honestWitgen (states : List (ComponentState F)) (snapshot data : ProverData F)
    (hint : ProverHint F) :
    (ops : List (FlatOperation F)) → (input : Array F) →
      flatReadsBelow input.size ops = true → ViewAgreesOps states snapshot data ops →
      witgen states snapshot hint ops input [] = (honestWitgen data hint ops input, [])
  | [], _, _, _ => rfl
  | .witness m code :: ops, input, hbelow, hview => by
      simp only [flatReadsBelow, Bool.and_eq_true] at hbelow
      have hcode := hview _ (by simp) m code rfl
      have hrest : ViewAgreesOps states snapshot data ops := fun op hop =>
        hview op (List.mem_cons_of_mem _ hop)
      cases code with
      | native => simp [witgenReadsBelow] at hbelow
      | ir steps output =>
          simp only [witgenReadsBelow, Bool.and_eq_true] at hbelow
          set environment : ProverEnvironment F :=
            { get index := input[index]?.getD 0, data := snapshot, hint }
          have hsteps := runSteps_eq_evalSteps states (n := input.size) (env := environment)
            (env' := rowEnvironment input data hint) (fun _ _ => rfl) rfl steps #[] hbelow.1.1
            (hcode.mono fun _ h => by simp [witnessDataReads, h])
          have houtput := vexpr_eval_congr (n := input.size) (env := environment)
            (env' := rowEnvironment input data hint)
            (Witgen.evalSteps (rowEnvironment input data hint) steps #[] 0) 0 output hbelow.1.2
            ⟨fun _ _ => rfl, fun read hread row =>
              (hcode read (by simp [witnessDataReads, hread]) row).1, rfl⟩
          have hfirst : witgenStep states snapshot hint (input, []) (.witness m (.ir steps output)) =
              (honestStep data hint input (.witness m (.ir steps output)), []) := by
            simp only [witgenStep, honestStep]
            rw [hsteps]
            simp only [Witgen.WitgenIR.eval]
            exact congrArg (fun values => (input ++ values.toArray, ([] : List (Definition F))))
              houtput
          simp only [witgen, List.foldl_cons, hfirst]
          have hsize : (honestStep data hint input (.witness m (.ir steps output))).size =
              m + input.size := by simp [honestStep]; omega
          have := witgen_eq_honestWitgen states snapshot data hint ops _
            (hsize ▸ hbelow.2) hrest
          exact this
  | .assert _ :: ops, input, hbelow, hview | .lookup _ :: ops, input, hbelow, hview |
    .interact _ :: ops, input, hbelow, hview => by
      simp only [flatReadsBelow] at hbelow
      exact witgen_eq_honestWitgen states snapshot data hint ops input hbelow
        fun op hop => hview op (List.mem_cons_of_mem _ hop)

/-! ### Honest component rows -/

/-- The cells of a row of `component` with `input`, computed by its witness programs from the prover
data and the hint. -/
def honestRow (component : Component F) (data : ProverData F) (hint : ProverHint F)
    (input : Array F) : Array F :=
  honestWitgen data hint component.rowOperations.toFlat input

/-- The input of an honest row is the input it was computed from. -/
lemma inputRow_honestRow (component : Component F) (data : ProverData F) (hint : ProverHint F)
    (input : Array F) (hsize : input.size = component.rowOffset) :
    inputRow component.Input (honestRow component data hint input) =
      inputRow component.Input input := by
  ext index hindex
  simp only [inputRow, Vector.getElem_mk, List.getElem_toArray, List.getElem_ofFn]
  rw [honestRow, honestWitgen_getElem? data hint _ input index
    (by rw [hsize]; exact hindex)]

/-- An honest row whose input satisfies the circuit's prover assumptions satisfies the component's
constraints, and its interactions their guarantees and prover guarantees. -/
theorem honestRow_complete (component : Component F) (data : ProverData F) (hint : ProverHint F)
    (input : Array F) (hsize : input.size = component.rowOffset)
    (hbelow : flatReadsBelow component.rowOffset component.rowOperations.toFlat = true)
    (hassumptions : component.circuit.ProverAssumptions
      (fromElements (inputRow component.Input input)) data hint) :
    let env := rowEnvironment (honestRow component data hint input) data hint
    component.operations.ConstraintsHold env.toEnvironment ∧
      component.rowOperations.FullGuarantees env.toEnvironment ∧
      component.rowOperations.FullProverGuarantees env.toEnvironment := by
  intro env
  have hlocal : env.UsesLocalWitnesses (size component.Input) component.rowOperations := by
    rw [ProverEnvironment.usesLocalWitnesses_iff_flat]
    have := honestWitgen_usesLocalWitnesses data hint component.rowOperations.toFlat input
      (by rw [hsize]; exact hbelow)
    rw [hsize] at this
    exact this
  have hinput : Eval.eval env (varFromOffset component.Input 0 : component.Input (Expression F)) =
      fromElements (inputRow component.Input input) := by
    rw [ProvableType.eval_varFromOffset_prover, ← inputRow_honestRow component data hint input hsize]
    congr 1
    ext index hindex
    simp [env, rowEnvironment, inputRow, Vector.getElem_mapRange]
  have h := component.circuit.original_full_completeness (size component.Input) env
    (varFromOffset component.Input 0) hlocal (by rw [hinput]; exact hassumptions)
  refine ⟨?_, h.2.1, h.2.2⟩
  obtain ⟨hconstraints, hlookups⟩ := h.1
  refine ⟨fun e he => hconstraints e ?_, fun l hl => hlookups l ?_⟩
  · have he' : e ∈ component.rowOperations.constraints := by
      rw [← Component.constraints_eq]; exact he
    exact he'
  · have hl' : l ∈ component.rowOperations.lookups := by
      rw [← Component.lookups_eq]; exact hl
    exact hl'

end Air.Flat.WitnessGeneration
