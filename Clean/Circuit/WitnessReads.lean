module

public import Clean.Circuit.WitnessIR
public import Clean.Circuit.WitnessIRSugar

@[expose] public section

/-!
# Syntactic read support for structured witness IR

Total, computable read collectors over all structured `WitgenIROver` constructors (`FExprOver`,
`U64ExprOver`, `BExprOver`, `VExprOver`, `StepOver`, and `MOver` builders). The collectors retain
every variable atom that could be read, including both branches of conditionals and every element
of a dynamically indexed expression list, so the congruence theorems apply unconditionally across
all inputs and exceptional arithmetic values.

Native closures (`.native`) have no syntactic read set and return `none`.
-/

namespace Witgen

variable {F Env V : Type}

mutual

/-- All variable atoms syntactically read by a field-sorted witness expression. -/
def fieldReads : FExprOver F V → List V
  | .expr cell => [cell]
  | .const _ | .localVar _ => []
  | .add left right | .mul left right => fieldReads left ++ fieldReads right
  | .inv value => fieldReads value
  | .ofU64 value => u64Reads value
  | .ite condition yes no => boolReads condition ++ fieldReads yes ++ fieldReads no
  | .listGet values index => fieldListReads values ++ u64Reads index
  | .dataGet _ _ row _ | .hintGet _ _ row _ => u64Reads row

/-- All variable atoms syntactically read by a list of field-sorted witness expressions. -/
def fieldListReads : List (FExprOver F V) → List V
  | [] => []
  | value :: rest => fieldReads value ++ fieldListReads rest

/-- All variable atoms syntactically read by a u64-sorted witness expression. -/
def u64Reads : U64ExprOver F V → List V
  | .const _ | .idx | .localVar _ => []
  | .val value => fieldReads value
  | .add left right | .mul left right | .div left right | .mod left right
  | .land left right | .lor left right | .lxor left right
  | .shiftL left right | .shiftR left right => u64Reads left ++ u64Reads right
  | .ite condition yes no => boolReads condition ++ u64Reads yes ++ u64Reads no

/-- All variable atoms syntactically read by a witness condition. -/
def boolReads : BExprOver F V → List V
  | .true | .false => []
  | .feq left right | .flt left right => fieldReads left ++ fieldReads right
  | .neq left right | .lt left right => u64Reads left ++ u64Reads right
  | .bit value _ => fieldReads value
  | .not value => boolReads value
  | .and left right => boolReads left ++ boolReads right

end

/-- All variable atoms syntactically read by a vector-shaped witness output. -/
def vectorReads : {n : ℕ} → VExprOver F V n → List V
  | _, .lit values => fieldListReads values.toList
  | _, .mapRange _ body => fieldReads body
  | _, .envRange _ => []
  | _, .bitsOf value => fieldReads value
  | _, .append left right => vectorReads left ++ vectorReads right

/-- All variable atoms syntactically read by a single `let`-step. -/
def stepReads : StepOver F V → List V
  | .letF expression => fieldReads expression
  | .letU expression => u64Reads expression

/-- All variable atoms syntactically read by a sequence of `let`-steps. -/
def stepsReads : List (StepOver F V) → List V
  | [] => []
  | step :: rest => stepReads step ++ stepsReads rest

/-- Syntactic read support of a witness program, or `none` for `.native` closures. -/
def programReads {n : ℕ} : WitgenIROver F Env V n → Option (List V)
  | .native _ => none
  | .ir steps out => some (stepsReads steps ++ vectorReads out)

/-- Check that a read-support result is structured (`some`) and every read satisfies `allowed`. -/
def readsAccepted (allowed : V → Bool) : Option (List V) → Bool
  | none => false
  | some cells => cells.all allowed

theorem readsAccepted_some (allowed : V → Bool) (cells : List V) :
    readsAccepted allowed (some cells) = cells.all allowed := rfl

theorem readsAccepted_none (allowed : V → Bool) :
    readsAccepted allowed none = false := rfl

section ContextAgreement

variable [WitgenEnv F Env V]

/-- Agreement of two evaluation contexts on immutable environment state (`get`, `data`, `hint`),
local variables, loop index, and every variable atom in `reads`. -/
structure ContextAgreement (reads : List V) (left right : CtxOver F Env) : Prop where
  cellValues : ∀ cell ∈ reads,
    WitgenEnv.readVar (F := F) left.env cell = WitgenEnv.readVar right.env cell
  indexed : WitgenEnv.get (F := F) (V := V) left.env = WitgenEnv.get (V := V) right.env
  data : WitgenEnv.data (F := F) (V := V) left.env = WitgenEnv.data (V := V) right.env
  hints : WitgenEnv.hint (F := F) (V := V) left.env = WitgenEnv.hint (V := V) right.env
  locals : left.locals = right.locals
  index : left.idx = right.idx

theorem ContextAgreement.mono {reads smaller : List V} {left right : CtxOver F Env}
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V) reads left right)
    (hsubset : smaller ⊆ reads) :
    ContextAgreement (F := F) (Env := Env) (V := V) smaller left right :=
  { agreement with cellValues := fun cell hcell => agreement.cellValues cell (hsubset hcell) }

theorem ContextAgreement.left {first second : List V} {left right : CtxOver F Env}
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V) (first ++ second) left right) :
    ContextAgreement (F := F) (Env := Env) (V := V) first left right :=
  agreement.mono (List.subset_append_left _ _)

theorem ContextAgreement.right {first second : List V} {left right : CtxOver F Env}
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V) (first ++ second) left right) :
    ContextAgreement (F := F) (Env := Env) (V := V) second left right :=
  agreement.mono (List.subset_append_right _ _)

theorem ContextAgreement.with_locals {reads : List V} {left right : CtxOver F Env}
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V) reads left right)
    (locals : Array (F ⊕ UInt64)) :
    ContextAgreement (F := F) (Env := Env) (V := V) reads
      { left with locals } { right with locals } :=
  { agreement with locals := rfl }

theorem ContextAgreement.with_idx {reads : List V} {left right : CtxOver F Env}
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V) reads left right)
    (idx : ℕ) :
    ContextAgreement (F := F) (Env := Env) (V := V) reads
      { left with idx } { right with idx } :=
  { agreement with index := rfl }

end ContextAgreement

section Semantics

variable [FiniteField F] [WitgenEnv F Env V]

mutual

theorem fieldReads_eval (expression : FExprOver F V) (left right : CtxOver F Env)
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (fieldReads expression) left right) :
    expression.eval left = expression.eval right := by
  cases expression with
  | expr cell =>
    exact agreement.cellValues cell List.mem_cons_self
  | const _ => rfl
  | localVar i =>
    simp only [FExprOver.eval, agreement.locals]
  | add x y =>
    exact congrArg₂ (· + ·)
      (fieldReads_eval x left right agreement.left)
      (fieldReads_eval y left right agreement.right)
  | mul x y =>
    exact congrArg₂ (· * ·)
      (fieldReads_eval x left right agreement.left)
      (fieldReads_eval y left right agreement.right)
  | inv x =>
    exact congrArg Inv.inv (fieldReads_eval x left right agreement)
  | ofU64 x =>
    exact congrArg (fun v : UInt64 => FiniteField.fromNat (F := F) v.toNat)
      (u64Reads_eval x left right agreement)
  | ite c t e =>
    have hc := boolReads_eval c left right agreement.left.left
    have ht := fieldReads_eval t left right agreement.left.right
    have he := fieldReads_eval e left right agreement.right
    simp only [FExprOver.eval, hc, ht, he]
  | listGet xs i =>
    have hi := u64Reads_eval i left right agreement.right
    simp only [FExprOver.eval, hi]
    exact fieldListReads_eval xs (i.eval right).toNat left right agreement.left
  | dataGet key n row col =>
    have hrow := u64Reads_eval row left right agreement
    simp only [FExprOver.eval, hrow, agreement.data]
  | hintGet key n row col =>
    have hrow := u64Reads_eval row left right agreement
    simp only [FExprOver.eval, hrow, agreement.hints]

theorem fieldListReads_eval (expressions : List (FExprOver F V)) (index : ℕ)
    (left right : CtxOver F Env)
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (fieldListReads expressions) left right) :
    FExprOver.evalList left index expressions = FExprOver.evalList right index expressions := by
  cases expressions with
  | nil => rfl
  | cons head tail =>
    cases index with
    | zero =>
      exact fieldReads_eval head left right agreement.left
    | succ next =>
      exact fieldListReads_eval tail next left right agreement.right

theorem u64Reads_eval (expression : U64ExprOver F V) (left right : CtxOver F Env)
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (u64Reads expression) left right) :
    expression.eval left = expression.eval right := by
  cases expression with
  | const _ => rfl
  | val x =>
    exact congrArg (fun v => UInt64.ofNat (FiniteField.val v))
      (fieldReads_eval x left right agreement)
  | idx =>
    simp only [U64ExprOver.eval, agreement.index]
  | localVar i =>
    simp only [U64ExprOver.eval, agreement.locals]
  | add x y | mul x y | div x y | mod x y
  | land x y | lor x y | lxor x y | shiftL x y | shiftR x y =>
    have hx := u64Reads_eval x left right agreement.left
    have hy := u64Reads_eval y left right agreement.right
    simp only [U64ExprOver.eval, hx, hy]
  | ite c t e =>
    have hc := boolReads_eval c left right agreement.left.left
    have ht := u64Reads_eval t left right agreement.left.right
    have he := u64Reads_eval e left right agreement.right
    simp only [U64ExprOver.eval, hc, ht, he]

theorem boolReads_eval (expression : BExprOver F V) (left right : CtxOver F Env)
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (boolReads expression) left right) :
    expression.eval left = expression.eval right := by
  cases expression with
  | true | false => rfl
  | feq x y | flt x y =>
    have hx := fieldReads_eval x left right agreement.left
    have hy := fieldReads_eval y left right agreement.right
    simp only [BExprOver.eval, hx, hy]
  | neq x y | lt x y =>
    have hx := u64Reads_eval x left right agreement.left
    have hy := u64Reads_eval y left right agreement.right
    simp only [BExprOver.eval, hx, hy]
  | bit x i =>
    have hx := fieldReads_eval x left right agreement
    simp only [BExprOver.eval, hx]
  | not b =>
    exact congrArg (·.not) (boolReads_eval b left right agreement)
  | and x y =>
    have hx := boolReads_eval x left right agreement.left
    have hy := boolReads_eval y left right agreement.right
    simp only [BExprOver.eval, hx, hy]

end

omit [FiniteField F] in
theorem fieldReads_subset_fieldListReads {expressions : List (FExprOver F V)}
    {expression : FExprOver F V} (hmem : expression ∈ expressions) :
    fieldReads expression ⊆ fieldListReads expressions := by
  induction expressions with
  | nil => cases hmem
  | cons head tail ih =>
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact List.subset_append_left _ _
    · exact List.Subset.trans (ih htail) (List.subset_append_right _ _)

theorem vectorReads_eval {n : ℕ} (output : VExprOver F V n) (left right : CtxOver F Env)
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (vectorReads output) left right) :
    output.eval left = output.eval right := by
  induction output with
  | lit values =>
    apply Vector.ext
    intro i hi
    simp only [VExprOver.eval, Vector.getElem_map]
    have hmem : values[i] ∈ values.toList := by
      have hi' : i < values.toList.length := by simpa using hi
      rw [← Vector.getElem_toList (h := hi')]
      exact List.getElem_mem hi'
    exact fieldReads_eval values[i] left right
      (agreement.mono (fieldReads_subset_fieldListReads hmem))
  | mapRange len body =>
    apply Vector.ext
    intro i hi
    simp only [VExprOver.eval, Vector.getElem_mapRange]
    exact fieldReads_eval body { left with idx := i } { right with idx := i }
      (agreement.with_idx i)
  | envRange offset =>
    apply Vector.ext
    intro i hi
    simp only [VExprOver.eval, Vector.getElem_mapRange]
    exact congrFun agreement.indexed (offset + i)
  | bitsOf x =>
    have hx := fieldReads_eval x left right agreement
    simp only [VExprOver.eval, hx]
  | append a b iha ihb =>
    simp only [VExprOver.eval]
    rw [iha agreement.left, ihb agreement.right]

theorem stepsReads_eval (steps : List (StepOver F V)) (left right : CtxOver F Env)
    (agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (stepsReads steps) left right) :
    evalSteps left.env steps left.locals left.idx =
      evalSteps right.env steps right.locals right.idx := by
  induction steps generalizing left right with
  | nil => exact agreement.locals
  | cons step rest ih =>
    cases step with
    | letF expression =>
      simp only [evalSteps]
      have hval := fieldReads_eval expression left right agreement.left
      rw [hval, agreement.locals, agreement.index]
      exact ih
        { left with
          locals := right.locals.push (.inl (expression.eval right))
          idx := right.idx }
        { right with
          locals := right.locals.push (.inl (expression.eval right))
          idx := right.idx }
        ((agreement.right.with_locals
          (right.locals.push (.inl (expression.eval right)))).with_idx right.idx)
    | letU expression =>
      simp only [evalSteps]
      have hval := u64Reads_eval expression left right agreement.left
      rw [hval, agreement.locals, agreement.index]
      exact ih
        { left with
          locals := right.locals.push (.inr (expression.eval right))
          idx := right.idx }
        { right with
          locals := right.locals.push (.inr (expression.eval right))
          idx := right.idx }
        ((agreement.right.with_locals
          (right.locals.push (.inr (expression.eval right)))).with_idx right.idx)

/-- Structured witness programs depend only on their syntactically collected variable reads and
immutable environment state (`get`, `data`, `hint`). -/
theorem programReads_eval {n : ℕ} (program : WitgenIROver F Env V n) (reads : List V)
    (hreads : programReads program = some reads) (left right : Env)
    (hcells : ∀ cell ∈ reads,
      WitgenEnv.readVar (F := F) left cell = WitgenEnv.readVar right cell)
    (hget : WitgenEnv.get (F := F) (V := V) left = WitgenEnv.get (V := V) right)
    (hdata : WitgenEnv.data (F := F) (V := V) left = WitgenEnv.data (V := V) right)
    (hhint : WitgenEnv.hint (F := F) (V := V) left = WitgenEnv.hint (V := V) right) :
    program.eval left = program.eval right := by
  cases program with
  | native _ => cases hreads
  | ir steps out =>
    simp only [programReads, Option.some.injEq] at hreads
    subst reads
    let agreement : ContextAgreement (F := F) (Env := Env) (V := V)
        (stepsReads steps ++ vectorReads out) { env := left } { env := right } :=
      { cellValues := hcells
        indexed := hget
        data := hdata
        hints := hhint
        locals := rfl
        index := rfl }
    have hsteps := stepsReads_eval steps { env := left } { env := right } agreement.left
    simp only [WitgenIROver.eval]
    rw [hsteps]
    exact vectorReads_eval out _ _ (agreement.right.with_locals (evalSteps right steps))

/-- If `readsAccepted allowed (programReads program) = true`, the program depends only on
variable atoms satisfying `allowed` and immutable environment state. -/
theorem readsAccepted_programReads_eval {n : ℕ} (allowed : V → Bool)
    (program : WitgenIROver F Env V n)
    (haccepted : readsAccepted allowed (programReads program) = true)
    (left right : Env)
    (hcells : ∀ cell, allowed cell = true →
      WitgenEnv.readVar (F := F) left cell = WitgenEnv.readVar right cell)
    (hget : WitgenEnv.get (F := F) (V := V) left = WitgenEnv.get (V := V) right)
    (hdata : WitgenEnv.data (F := F) (V := V) left = WitgenEnv.data (V := V) right)
    (hhint : WitgenEnv.hint (F := F) (V := V) left = WitgenEnv.hint (V := V) right) :
    program.eval left = program.eval right := by
  cases hreads : programReads program with
  | none =>
    simp [readsAccepted, hreads] at haccepted
  | some reads =>
    simp only [readsAccepted, hreads, List.all_eq_true] at haccepted
    exact programReads_eval program reads hreads left right
      (fun cell hcell => hcells cell (haccepted cell hcell)) hget hdata hhint

/-! ## Builders -/

/-- Complete variable support of a structured value-yielding builder. -/
def valueBuilderReads {value : TypeMap} [ProvableType value]
    (program : MOver F V (value (FExprOver F V))) : List V :=
  stepsReads (program #[]).2.toList ++ fieldListReads (toElements (program #[]).1).toList

/-- Complete variable support of a u64-yielding builder. -/
def u64BuilderReads (program : MOver F V (U64ExprOver F V)) : List V :=
  stepsReads (program #[]).2.toList ++ u64Reads (program #[]).1

/-- Complete variable support of a Boolean-yielding builder. -/
def boolBuilderReads (program : MOver F V (BExprOver F V)) : List V :=
  stepsReads (program #[]).2.toList ++ boolReads (program #[]).1

theorem valueBuilderReads_eval {value : TypeMap} [ProvableType value]
    (program : MOver F V (value (FExprOver F V))) (left right : Env)
    (hcells : ∀ cell ∈ valueBuilderReads program,
      WitgenEnv.readVar (F := F) left cell = WitgenEnv.readVar right cell)
    (hget : WitgenEnv.get (F := F) (V := V) left = WitgenEnv.get (V := V) right)
    (hdata : WitgenEnv.data (F := F) (V := V) left = WitgenEnv.data (V := V) right)
    (hhint : WitgenEnv.hint (F := F) (V := V) left = WitgenEnv.hint (V := V) right) :
    program.eval left = program.eval right := by
  have hvalues : (program.toIRLiteral (Env := Env)).eval left =
      (program.toIRLiteral (Env := Env)).eval right :=
    programReads_eval (program.toIRLiteral (Env := Env)) (valueBuilderReads program)
      rfl left right hcells hget hdata hhint
  rw [MOver.eval_toIRLiteral, MOver.eval_toIRLiteral] at hvalues
  simpa only [ProvableType.fromElements_toElements] using
    congrArg (fromElements (M := value)) hvalues

theorem u64BuilderReads_eval (program : MOver F V (U64ExprOver F V)) (left right : Env)
    (hcells : ∀ cell ∈ u64BuilderReads program,
      WitgenEnv.readVar (F := F) left cell = WitgenEnv.readVar right cell)
    (hget : WitgenEnv.get (F := F) (V := V) left = WitgenEnv.get (V := V) right)
    (hdata : WitgenEnv.data (F := F) (V := V) left = WitgenEnv.data (V := V) right)
    (hhint : WitgenEnv.hint (F := F) (V := V) left = WitgenEnv.hint (V := V) right) :
    program.evalU64 left = program.evalU64 right := by
  let agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (u64BuilderReads program) { env := left } { env := right } :=
    { cellValues := hcells
      indexed := hget
      data := hdata
      hints := hhint
      locals := rfl
      index := rfl }
  have hsteps := stepsReads_eval (program #[]).2.toList { env := left } { env := right }
    agreement.left
  simp only [MOver.evalU64]
  rw [hsteps]
  exact u64Reads_eval (program #[]).1 _ _
    (agreement.right.with_locals (evalSteps right (program #[]).2.toList))

theorem boolBuilderReads_eval (program : MOver F V (BExprOver F V)) (left right : Env)
    (hcells : ∀ cell ∈ boolBuilderReads program,
      WitgenEnv.readVar (F := F) left cell = WitgenEnv.readVar right cell)
    (hget : WitgenEnv.get (F := F) (V := V) left = WitgenEnv.get (V := V) right)
    (hdata : WitgenEnv.data (F := F) (V := V) left = WitgenEnv.data (V := V) right)
    (hhint : WitgenEnv.hint (F := F) (V := V) left = WitgenEnv.hint (V := V) right) :
    program.evalBool left = program.evalBool right := by
  let agreement : ContextAgreement (F := F) (Env := Env) (V := V)
      (boolBuilderReads program) { env := left } { env := right } :=
    { cellValues := hcells
      indexed := hget
      data := hdata
      hints := hhint
      locals := rfl
      index := rfl }
  have hsteps := stepsReads_eval (program #[]).2.toList { env := left } { env := right }
    agreement.left
  simp only [MOver.evalBool]
  rw [hsteps]
  exact boolReads_eval (program #[]).1 _ _
    (agreement.right.with_locals (evalSteps right (program #[]).2.toList))

end Semantics

end Witgen
