import Clean.Circuit.WitnessIRSugar

/-!
# Read support of structured witness expressions and programs

The collectors retain every variable read, including both branches of a conditional and every
candidate in a dynamically indexed expression list, so the evaluation theorems apply to all
inputs and exceptional arithmetic values. Local steps, vector outputs, loop indices, and the
builder monad preserve the expression-level guarantee. A native witness closure is never
accepted by these theorems; it needs its own dependency certificate
(`Clean.Halo2.WitnessSupport`).
-/

namespace Witgen

mutual

/-- All cell atoms used by a field-sorted witness expression. -/
def fieldWitnessReads {F V : Type} : FExprOver F V → List V
  | .expr cell => [cell]
  | .envGet index => natWitnessReads index
  | .const _ | .localVar _ => []
  | .add left right | .mul left right => fieldWitnessReads left ++ fieldWitnessReads right
  | .inv value => fieldWitnessReads value
  | .ofNat value => natWitnessReads value
  | .ite condition yes no =>
      boolWitnessReads condition ++ fieldWitnessReads yes ++ fieldWitnessReads no
  | .listGet values index => listWitnessReads values ++ natWitnessReads index
  | .dataGet _ _ row _ | .hintGet _ _ row _ => natWitnessReads row

/-- All cell atoms used by a dynamically indexed list of witness expressions. -/
def listWitnessReads {F V : Type} : List (FExprOver F V) → List V
  | [] => []
  | value :: rest => fieldWitnessReads value ++ listWitnessReads rest

/-- All cell atoms used by a Nat-sorted witness expression. -/
def natWitnessReads {F V : Type} : NExprOver F V → List V
  | .const _ | .idx | .localVar _ => []
  | .val value => fieldWitnessReads value
  | .add left right | .mul left right | .div left right | .mod left right
  | .land left right | .lor left right | .lxor left right
  | .shiftL left right | .shiftR left right => natWitnessReads left ++ natWitnessReads right
  | .ite condition yes no => boolWitnessReads condition ++ natWitnessReads yes ++ natWitnessReads no

/-- All cell atoms used by a witness condition. -/
def boolWitnessReads {F V : Type} : BExprOver F V → List V
  | .true | .false => []
  | .feq left right => fieldWitnessReads left ++ fieldWitnessReads right
  | .neq left right | .lt left right => natWitnessReads left ++ natWitnessReads right
  | .not value => boolWitnessReads value
  | .and left right => boolWitnessReads left ++ boolWitnessReads right

end

/-- Equal immutable context data and equal values for the declared variable reads. -/
structure WitnessContextAgreement {F Env V : Type} [WitgenEnv F Env V]
    (reads : List V) (left right : CtxOver F Env) : Prop where
  cellValues : ∀ cell ∈ reads,
    WitgenEnv.readVar (F := F) left.env cell = WitgenEnv.readVar right.env cell
  indexed : WitgenEnv.get (F := F) (V := V) left.env = WitgenEnv.get (V := V) right.env
  data : WitgenEnv.data (F := F) (V := V) left.env = WitgenEnv.data (V := V) right.env
  hints : WitgenEnv.hint (F := F) (V := V) left.env = WitgenEnv.hint (V := V) right.env
  locals : left.locals = right.locals
  index : left.idx = right.idx

/-- A context agreement also covers any subset of its declared reads. -/
theorem WitnessContextAgreement.mono {F Env V : Type} [WitgenEnv F Env V]
    {reads smaller : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement reads left right) (hsubset : smaller ⊆ reads) :
    WitnessContextAgreement smaller left right :=
  { agreement with cellValues := fun cell hcell => agreement.cellValues cell (hsubset hcell) }

/-- Context agreement for concatenated read lists restricts to the left fragment. -/
theorem WitnessContextAgreement.left {F Env V : Type} [WitgenEnv F Env V]
    {first second : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement (first ++ second) left right) :
    WitnessContextAgreement first left right :=
  agreement.mono (List.subset_append_left _ _)

/-- Context agreement for concatenated read lists restricts to the right fragment. -/
theorem WitnessContextAgreement.right {F Env V : Type} [WitgenEnv F Env V]
    {first second : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement (first ++ second) left right) :
    WitnessContextAgreement second left right :=
  agreement.mono (List.subset_append_right _ _)

/-- Replacing both local stores by the same values preserves context agreement. -/
theorem WitnessContextAgreement.withLocals {F Env V : Type} [WitgenEnv F Env V]
    {reads : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement reads left right) (locals : Array (F ⊕ ℕ)) :
    WitnessContextAgreement reads { left with locals } { right with locals } :=
  { agreement with locals := rfl }

/-- Giving both vector loops the same iteration index preserves context agreement. -/
theorem WitnessContextAgreement.withIndex {F Env V : Type} [WitgenEnv F Env V]
    {reads : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement reads left right) (index : ℕ) :
    WitnessContextAgreement reads { left with idx := index } { right with idx := index } :=
  { agreement with index := rfl }

/-- A list's complete support contains the support of every expression it can select. -/
theorem WitnessContextAgreement.list_member {F Env V : Type} [WitgenEnv F Env V]
    {expressions : List (FExprOver F V)} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement (listWitnessReads expressions) left right)
    {expression : FExprOver F V} (hmem : expression ∈ expressions) :
    WitnessContextAgreement (fieldWitnessReads expression) left right := by
  induction expressions with
  | nil => cases hmem
  | cons first rest ih =>
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact agreement.left
    · exact ih agreement.right hrest

variable {F Env V : Type} [FiniteField F] [WitgenEnv F Env V]

-- Separate constructor lemmas keep each part of the mutual induction small. The
-- public theorems apply Lean's mutual recursors to these checked proof constants.
private abbrev FieldReadAgreement (left right : CtxOver F Env) (e : FExprOver F V) : Prop :=
  WitnessContextAgreement (fieldWitnessReads e) left right → e.eval left = e.eval right

private abbrev NatReadAgreement (left right : CtxOver F Env) (e : NExprOver F V) : Prop :=
  WitnessContextAgreement (natWitnessReads e) left right → e.eval left = e.eval right

private abbrev BoolReadAgreement (left right : CtxOver F Env) (e : BExprOver F V) : Prop :=
  WitnessContextAgreement (boolWitnessReads e) left right → e.eval left = e.eval right

private abbrev ListReadAgreement (left right : CtxOver F Env) (es : List (FExprOver F V)) :
    Prop :=
  ∀ index, WitnessContextAgreement (listWitnessReads es) left right →
    FExprOver.evalList left index es = FExprOver.evalList right index es

variable {left right : CtxOver F Env}

/-- A cell atom is covered directly by context agreement, supplying the leaf case of read
support. -/
private theorem fieldRead_expr (cell : V) :
    FieldReadAgreement (V := V) left right (FExprOver.expr cell) := by
  intro agreement
  exact agreement.cellValues cell (List.mem_singleton_self _)

/-- An indexed environment read uses its certified index and the shared indexed provider. -/
private theorem fieldRead_envGet (index : NExprOver F V)
    (hindex : NatReadAgreement (V := V) left right index) :
    FieldReadAgreement (V := V) left right (FExprOver.envGet index) := by
  intro agreement
  simp only [FExprOver.eval, agreement.indexed, hindex agreement]

/-- A field constant reads no context, closing the constant branch of the mutual induction. -/
private theorem fieldRead_const (value : F) :
    FieldReadAgreement (V := V) left right (FExprOver.const value) := by
  intro _
  rfl

/-- Local field reads use the immutable locals shared by the two contexts. -/
private theorem fieldRead_localVar (index : ℕ) :
    FieldReadAgreement (V := V) left right (FExprOver.localVar index) := by
  intro agreement
  simp only [FExprOver.eval, agreement.locals]

/-- The field arithmetic case composes its operand certificates over the concatenated read
list. -/
private theorem fieldRead_add (a b : FExprOver F V)
    (ha : FieldReadAgreement (V := V) left right a)
    (hb : FieldReadAgreement (V := V) left right b) :
    FieldReadAgreement (V := V) left right (FExprOver.add a b) := by
  intro agreement
  exact congrArg₂ (· + ·) (ha agreement.left) (hb agreement.right)

/-- The field arithmetic case composes its operand certificates over the concatenated read
list. -/
private theorem fieldRead_mul (a b : FExprOver F V)
    (ha : FieldReadAgreement (V := V) left right a)
    (hb : FieldReadAgreement (V := V) left right b) :
    FieldReadAgreement (V := V) left right (FExprOver.mul a b) := by
  intro agreement
  exact congrArg₂ (· * ·) (ha agreement.left) (hb agreement.right)

/-- Inversion preserves evaluation equality, including zero, using the operand read
certificate. -/
private theorem fieldRead_inv (value : FExprOver F V)
    (hvalue : FieldReadAgreement (V := V) left right value) :
    FieldReadAgreement (V := V) left right (FExprOver.inv value) := by
  intro agreement
  exact congrArg Inv.inv (hvalue agreement)

/-- Nat-to-field conversion transfers the Nat operand certificate to the field evaluator. -/
private theorem fieldRead_ofNat (value : NExprOver F V)
    (hvalue : NatReadAgreement (V := V) left right value) :
    FieldReadAgreement (V := V) left right (FExprOver.ofNat value) := by
  intro agreement
  exact congrArg FiniteField.fromNat (hvalue agreement)

/-- Field selection retains both branch certificates and the condition certificate,
independently of which branch runs. -/
private theorem fieldRead_ite (condition : BExprOver F V) (yes no : FExprOver F V)
    (hc : BoolReadAgreement (V := V) left right condition)
    (hy : FieldReadAgreement (V := V) left right yes)
    (hn : FieldReadAgreement (V := V) left right no) :
    FieldReadAgreement (V := V) left right (FExprOver.ite condition yes no) := by
  intro agreement
  simp only [FExprOver.eval, hc agreement.left.left, hy agreement.left.right, hn agreement.right]

/-- Dynamic list selection combines the certified index with all candidate reads, including
out-of-range selection. -/
private theorem fieldRead_listGet (values : List (FExprOver F V)) (index : NExprOver F V)
    (hvalues : ListReadAgreement (V := V) left right values)
    (hindex : NatReadAgreement (V := V) left right index) :
    FieldReadAgreement (V := V) left right (FExprOver.listGet values index) := by
  intro agreement
  simp only [FExprOver.eval, hindex agreement.right]
  exact hvalues _ agreement.left

/-- The selected row is certified while context agreement supplies equality of the
immutable data provider. -/
private theorem fieldRead_dataGet (key : String) (width : ℕ) (row : NExprOver F V)
    (column : Fin width) (hrow : NatReadAgreement (V := V) left right row) :
    FieldReadAgreement (V := V) left right (FExprOver.dataGet key width row column) := by
  intro agreement
  simp only [FExprOver.eval, agreement.data, hrow agreement]

/-- The selected row is certified while context agreement supplies equality of the
immutable hint provider. -/
private theorem fieldRead_hintGet (key : String) (width : ℕ) (row : NExprOver F V)
    (column : Fin width) (hrow : NatReadAgreement (V := V) left right row) :
    FieldReadAgreement (V := V) left right (FExprOver.hintGet key width row column) := by
  intro agreement
  simp only [FExprOver.eval, agreement.hints, hrow agreement]

/-- A Nat constant closes its read-support case without inspecting the context. -/
private theorem natRead_const (value : ℕ) :
    NatReadAgreement (V := V) left right (NExprOver.const value) := by
  intro _
  rfl

/-- Field-to-Nat conversion transfers the field operand certificate to the Nat evaluator. -/
private theorem natRead_val (value : FExprOver F V)
    (hvalue : FieldReadAgreement (V := V) left right value) :
    NatReadAgreement (V := V) left right (NExprOver.val value) := by
  intro agreement
  exact congrArg FiniteField.val (hvalue agreement)

/-- The loop index agrees because it is immutable context data. -/
private theorem natRead_idx :
    NatReadAgreement (V := V) left right (NExprOver.idx) := by
  intro agreement
  exact agreement.index

/-- Local Nat reads use the immutable locals shared by the two contexts. -/
private theorem natRead_localVar (index : ℕ) :
    NatReadAgreement (V := V) left right (NExprOver.localVar index) := by
  intro agreement
  simp only [NExprOver.eval, agreement.locals]

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_add (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.add a b) := by
  intro agreement
  exact congrArg₂ Nat.add (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_mul (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.mul a b) := by
  intro agreement
  exact congrArg₂ Nat.mul (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_div (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.div a b) := by
  intro agreement
  exact congrArg₂ Nat.div (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_mod (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.mod a b) := by
  intro agreement
  exact congrArg₂ Nat.mod (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_land (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.land a b) := by
  intro agreement
  exact congrArg₂ Nat.land (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_lor (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.lor a b) := by
  intro agreement
  exact congrArg₂ Nat.lor (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_lxor (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.lxor a b) := by
  intro agreement
  exact congrArg₂ Nat.xor (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_shiftL (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.shiftL a b) := by
  intro agreement
  exact congrArg₂ Nat.shiftLeft (ha agreement.left) (hb agreement.right)

/-- A Nat operation composes its operand certificates; its total arithmetic does not need any input
restriction. -/
private theorem natRead_shiftR (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    NatReadAgreement (V := V) left right (NExprOver.shiftR a b) := by
  intro agreement
  exact congrArg₂ Nat.shiftRight (ha agreement.left) (hb agreement.right)

/-- Nat selection retains both branch certificates and the condition certificate,
independently of which branch runs. -/
private theorem natRead_ite (condition : BExprOver F V) (yes no : NExprOver F V)
    (hc : BoolReadAgreement (V := V) left right condition)
    (hy : NatReadAgreement (V := V) left right yes)
    (hn : NatReadAgreement (V := V) left right no) :
    NatReadAgreement (V := V) left right (NExprOver.ite condition yes no) := by
  intro agreement
  simp only [NExprOver.eval, hc agreement.left.left, hy agreement.left.right, hn agreement.right]

/-- A constant branch condition closes its read-support case without inspecting the
context. -/
private theorem boolRead_true :
    BoolReadAgreement (V := V) left right (BExprOver.true) := by
  intro _
  rfl

/-- A constant branch condition closes its read-support case without inspecting the
context. -/
private theorem boolRead_false :
    BoolReadAgreement (V := V) left right (BExprOver.false) := by
  intro _
  rfl

/-- A comparison obtains both operand values from their certificates before deciding the
branch condition. -/
private theorem boolRead_feq (a b : FExprOver F V)
    (ha : FieldReadAgreement (V := V) left right a)
    (hb : FieldReadAgreement (V := V) left right b) :
    BoolReadAgreement (V := V) left right (BExprOver.feq a b) := by
  intro agreement
  exact congrArg₂ (fun x y : F => decide (x = y))
    (ha agreement.left) (hb agreement.right)

/-- A comparison obtains both operand values from their certificates before deciding the
branch condition. -/
private theorem boolRead_neq (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    BoolReadAgreement (V := V) left right (BExprOver.neq a b) := by
  intro agreement
  exact congrArg₂ (fun x y : ℕ => decide (x = y))
    (ha agreement.left) (hb agreement.right)

/-- A comparison obtains both operand values from their certificates before deciding the
branch condition. -/
private theorem boolRead_lt (a b : NExprOver F V)
    (ha : NatReadAgreement (V := V) left right a) (hb : NatReadAgreement (V := V) left right b) :
    BoolReadAgreement (V := V) left right (BExprOver.lt a b) := by
  intro agreement
  exact congrArg₂ (fun x y : ℕ => decide (x < y))
    (ha agreement.left) (hb agreement.right)

/-- Negation reuses the operand certificate without introducing another read. -/
private theorem boolRead_not (value : BExprOver F V)
    (hvalue : BoolReadAgreement (V := V) left right value) :
    BoolReadAgreement (V := V) left right (BExprOver.not value) := by
  intro agreement
  exact congrArg Bool.not (hvalue agreement)

/-- Conjunction retains both condition certificates and their concatenated read support. -/
private theorem boolRead_and (a b : BExprOver F V)
    (ha : BoolReadAgreement (V := V) left right a)
    (hb : BoolReadAgreement (V := V) left right b) :
    BoolReadAgreement (V := V) left right (BExprOver.and a b) := by
  intro agreement
  exact congrArg₂ Bool.and (ha agreement.left) (hb agreement.right)

/-- Every selection from an empty candidate list returns the same default value. -/
private theorem listRead_nil :
    ListReadAgreement (V := V) left right ([]) := by
  intro index _
  rfl

/-- List selection uses the head certificate at zero and the tail certificate otherwise,
covering out-of-range indices. -/
private theorem listRead_cons (value : FExprOver F V) (rest : List (FExprOver F V))
    (hvalue : FieldReadAgreement (V := V) left right value)
    (hrest : ListReadAgreement (V := V) left right rest) :
    ListReadAgreement (V := V) left right (value :: rest) := by
  intro index agreement
  cases index with
  | zero => exact hvalue agreement.left
  | succ index => exact hrest index agreement.right

/-- The field evaluator depends only on the collected reads and context data. -/
theorem fieldWitnessReads_eval (expression : FExprOver F V) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (fieldWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  exact FExprOver.rec
    (motive_1 := FieldReadAgreement (V := V) left right)
    (motive_2 := NatReadAgreement (V := V) left right)
    (motive_3 := BoolReadAgreement (V := V) left right)
    (motive_4 := ListReadAgreement (V := V) left right)
    fieldRead_expr fieldRead_envGet fieldRead_const fieldRead_localVar
    fieldRead_add fieldRead_mul fieldRead_inv fieldRead_ofNat
    fieldRead_ite fieldRead_listGet fieldRead_dataGet fieldRead_hintGet
    natRead_const natRead_val natRead_idx natRead_localVar
    natRead_add natRead_mul natRead_div natRead_mod
    natRead_land natRead_lor natRead_lxor natRead_shiftL
    natRead_shiftR natRead_ite boolRead_true boolRead_false
    boolRead_feq boolRead_neq boolRead_lt boolRead_not
    boolRead_and listRead_nil listRead_cons
    expression agreement

/-- Nat arithmetic and bit operations depend only on the collected reads and context data. -/
theorem natWitnessReads_eval (expression : NExprOver F V) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (natWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  exact NExprOver.rec
    (motive_1 := FieldReadAgreement (V := V) left right)
    (motive_2 := NatReadAgreement (V := V) left right)
    (motive_3 := BoolReadAgreement (V := V) left right)
    (motive_4 := ListReadAgreement (V := V) left right)
    fieldRead_expr fieldRead_envGet fieldRead_const fieldRead_localVar
    fieldRead_add fieldRead_mul fieldRead_inv fieldRead_ofNat
    fieldRead_ite fieldRead_listGet fieldRead_dataGet fieldRead_hintGet
    natRead_const natRead_val natRead_idx natRead_localVar
    natRead_add natRead_mul natRead_div natRead_mod
    natRead_land natRead_lor natRead_lxor natRead_shiftL
    natRead_shiftR natRead_ite boolRead_true boolRead_false
    boolRead_feq boolRead_neq boolRead_lt boolRead_not
    boolRead_and listRead_nil listRead_cons
    expression agreement

/-- Branch conditions depend only on the collected reads and context data. -/
theorem boolWitnessReads_eval (expression : BExprOver F V) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (boolWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  exact BExprOver.rec
    (motive_1 := FieldReadAgreement (V := V) left right)
    (motive_2 := NatReadAgreement (V := V) left right)
    (motive_3 := BoolReadAgreement (V := V) left right)
    (motive_4 := ListReadAgreement (V := V) left right)
    fieldRead_expr fieldRead_envGet fieldRead_const fieldRead_localVar
    fieldRead_add fieldRead_mul fieldRead_inv fieldRead_ofNat
    fieldRead_ite fieldRead_listGet fieldRead_dataGet fieldRead_hintGet
    natRead_const natRead_val natRead_idx natRead_localVar
    natRead_add natRead_mul natRead_div natRead_mod
    natRead_land natRead_lor natRead_lxor natRead_shiftL
    natRead_shiftR natRead_ite boolRead_true boolRead_false
    boolRead_feq boolRead_neq boolRead_lt boolRead_not
    boolRead_and listRead_nil listRead_cons
    expression agreement

/-- Dynamic indexing introduces no undeclared read even when the index is out of bounds. -/
theorem listWitnessReads_eval (expressions : List (FExprOver F V)) (index : ℕ)
    (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (listWitnessReads expressions) left right) :
    FExprOver.evalList left index expressions = FExprOver.evalList right index expressions := by
  exact FExprOver.rec_1
    (motive_1 := FieldReadAgreement (V := V) left right)
    (motive_2 := NatReadAgreement (V := V) left right)
    (motive_3 := BoolReadAgreement (V := V) left right)
    (motive_4 := ListReadAgreement (V := V) left right)
    fieldRead_expr fieldRead_envGet fieldRead_const fieldRead_localVar
    fieldRead_add fieldRead_mul fieldRead_inv fieldRead_ofNat
    fieldRead_ite fieldRead_listGet fieldRead_dataGet fieldRead_hintGet
    natRead_const natRead_val natRead_idx natRead_localVar
    natRead_add natRead_mul natRead_div natRead_mod
    natRead_land natRead_lor natRead_lxor natRead_shiftL
    natRead_shiftR natRead_ite boolRead_true boolRead_false
    boolRead_feq boolRead_neq boolRead_lt boolRead_not
    boolRead_and listRead_nil listRead_cons
    expressions index agreement

/-! ## Structured programs -/

/-- All cell atoms in a vector-shaped witness output. -/
def vectorWitnessReads {F V : Type} : {width : ℕ} → VExprOver F V width → List V
  | _, .lit expressions => listWitnessReads expressions.toList
  | _, .mapRange _ body => fieldWitnessReads body
  | _, .append left right => vectorWitnessReads left ++ vectorWitnessReads right

/-- All cell atoms read by the local steps of a structured witness program. -/
def stepsWitnessReads {F V : Type} : List (StepOver F V) → List V
  | [] => []
  | .letF expression :: rest => fieldWitnessReads expression ++ stepsWitnessReads rest
  | .letN expression :: rest => natWitnessReads expression ++ stepsWitnessReads rest

/-- Vector evaluation introduces no variable reads beyond its collected support. -/
theorem vectorWitnessReads_eval {width : ℕ} (expression : VExprOver F V width)
    (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (vectorWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  induction expression with
  | lit expressions =>
    ext index hindex
    simp only [VExprOver.eval, Vector.getElem_map]
    apply fieldWitnessReads_eval
    apply agreement.list_member
    exact List.getElem_mem (l := expressions.toList) (n := index) (by simpa using hindex)
  | mapRange width body =>
    ext index hindex
    simp only [VExprOver.eval, Vector.getElem_mapRange]
    exact fieldWitnessReads_eval body _ _ (agreement.withIndex index)
  | append first second ihfirst ihsecond =>
    simp only [VExprOver.eval, ihfirst agreement.left, ihsecond agreement.right]

/-- Sequential local evaluation depends only on the collected reads and initial local values. -/
theorem stepsWitnessReads_eval (steps : List (StepOver F V)) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (stepsWitnessReads steps) left right) :
    evalSteps left.env steps left.locals = evalSteps right.env steps right.locals := by
  induction steps generalizing left right with
  | nil => exact agreement.locals
  | cons step rest ih =>
    cases step with
    | letF expression =>
      simp only [evalSteps]
      have hvalue := fieldWitnessReads_eval expression
        { env := left.env, locals := left.locals } { env := right.env, locals := right.locals }
        (agreement.left.withIndex 0)
      rw [hvalue, agreement.locals]
      exact ih _ _ (agreement.right.withLocals
        (right.locals.push (.inl (expression.eval { env := right.env, locals := right.locals }))))
    | letN expression =>
      simp only [evalSteps]
      have hvalue := natWitnessReads_eval expression
        { env := left.env, locals := left.locals } { env := right.env, locals := right.locals }
        (agreement.left.withIndex 0)
      rw [hvalue, agreement.locals]
      exact ih _ _ (agreement.right.withLocals
        (right.locals.push (.inr (expression.eval { env := right.env, locals := right.locals }))))

/-- The straight-line IR evaluator depends only on the complete declared variable support. -/
theorem structuredWitnessReads_eval {width : ℕ} (steps : List (StepOver F V))
    (output : VExprOver F V width) (left right : Env)
    (agreement : WitnessContextAgreement (stepsWitnessReads steps ++ vectorWitnessReads output)
      ({ env := left } : CtxOver F Env) { env := right }) :
    (WitgenIROver.ir steps output).eval left = (WitgenIROver.ir steps output).eval right := by
  have hsteps := stepsWitnessReads_eval steps _ _ agreement.left
  simp only [WitgenIROver.eval]
  rw [hsteps]
  exact vectorWitnessReads_eval output _ _ (agreement.right.withLocals (evalSteps right steps))

/-! ## Builders -/

/-- Complete variable support of a structured field-valued or record-valued builder. -/
def valueBuilderReads {F V : Type} {value : TypeMap} [ProvableType value]
    (program : MOver F V (value (FExprOver F V))) : List V :=
  stepsWitnessReads (program #[]).2.toList ++ listWitnessReads (toElements (program #[]).1).toList

/-- Complete variable support of a Nat-valued builder, including its local steps. -/
def natBuilderReads {F V : Type} (program : MOver F V (NExprOver F V)) : List V :=
  stepsWitnessReads (program #[]).2.toList ++ natWitnessReads (program #[]).1

/-- Complete variable support of a Boolean-valued builder, including its local steps. -/
def boolBuilderReads {F V : Type} (program : MOver F V (BExprOver F V)) : List V :=
  stepsWitnessReads (program #[]).2.toList ++ boolWitnessReads (program #[]).1

/-- The value-builder evaluator depends only on its declared variable support. -/
theorem valueBuilderReads_eval {value : TypeMap} [ProvableType value]
    (program : MOver F V (value (FExprOver F V))) (left right : Env)
    (agreement : WitnessContextAgreement (valueBuilderReads program)
      ({ env := left } : CtxOver F Env) { env := right }) :
    program.eval left = program.eval right := by
  have hvalues : (program.toIRLiteral (Env := Env)).eval left =
      (program.toIRLiteral (Env := Env)).eval right :=
    structuredWitnessReads_eval (program #[]).2.toList (.lit (toElements (program #[]).1))
      left right agreement
  rw [MOver.eval_toIRLiteral, MOver.eval_toIRLiteral] at hvalues
  simpa only [ProvableType.fromElements_toElements] using
    congrArg (fromElements (M := value)) hvalues

/-- The Nat-builder evaluator depends only on its declared variable support. -/
theorem natBuilderReads_eval (program : MOver F V (NExprOver F V)) (left right : Env)
    (agreement : WitnessContextAgreement (natBuilderReads program)
      ({ env := left } : CtxOver F Env) { env := right }) :
    program.evalNat left = program.evalNat right := by
  have hsteps := stepsWitnessReads_eval (program #[]).2.toList _ _ agreement.left
  simp only [MOver.evalNat]
  rw [hsteps]
  exact natWitnessReads_eval (program #[]).1 _ _
    (agreement.right.withLocals (evalSteps right (program #[]).2.toList))

/-- The Boolean-builder evaluator depends only on its declared variable support. -/
theorem boolBuilderReads_eval (program : MOver F V (BExprOver F V)) (left right : Env)
    (agreement : WitnessContextAgreement (boolBuilderReads program)
      ({ env := left } : CtxOver F Env) { env := right }) :
    program.evalBool left = program.evalBool right := by
  have hsteps := stepsWitnessReads_eval (program #[]).2.toList _ _ agreement.left
  simp only [MOver.evalBool]
  rw [hsteps]
  exact boolWitnessReads_eval (program #[]).1 _ _
    (agreement.right.withLocals (evalSteps right (program #[]).2.toList))

end Witgen
