module

public import Clean.Circuit.WitnessReads
public import Clean.Halo2.WitnessSupportAttr
public import Clean.Halo2.Basic

@[expose] public section

/-!
# Semantic read support for witness programs

Native callbacks are ordinary functions, so their dependencies cannot be inferred by the
structured IR collector (`Clean.Circuit.WitnessReads`). `WitnessFunctionSupport reads compute`
certifies the function itself: equal immutable context data, equal non-advice (fixed/instance)
cells, and equal listed cell values imply equal results. It composes through arbitrary
deterministic arithmetic on those results. The rules tagged `witness_support` cover the program
shapes Clean itself produces; a downstream project tags the rules for its own callbacks.
-/

namespace Halo2

open Witgen

section
variable {F : Type} [FiniteField F]

/-- Declared cell values and the immutable placement, usable-row bound, and public/fixed
environment agree. -/
structure WitnessFunctionAgreement
    (reads : List (AssignedCell F)) (left right : Placed ProverEnvironment F) : Prop extends
    ContextAgreement (F := F) (Env := Placed ProverEnvironment F) (V := AssignedCell F)
      reads ({ env := left } : CtxOver F (Placed ProverEnvironment F)) { env := right } where
  place : left.place = right.place
  usableRows : left.env.usableRows = right.env.usableRows
  nonAdvice : ∀ column row, column.kind ≠ .advice →
    left.env.get column row = right.env.get column row

/-- Restrict declared reads while retaining all immutable values. -/
theorem WitnessFunctionAgreement.mono
    {reads smaller : List (AssignedCell F)} {left right : Placed ProverEnvironment F}
    (agreement : WitnessFunctionAgreement reads left right) (hsubset : smaller ⊆ reads) :
    WitnessFunctionAgreement smaller left right :=
  ⟨agreement.toContextAgreement.mono hsubset, agreement.place, agreement.usableRows,
    agreement.nonAdvice⟩

/-- Restrict a concatenated support to its first component. -/
theorem WitnessFunctionAgreement.left
    {first second : List (AssignedCell F)} {left right : Placed ProverEnvironment F}
    (agreement : WitnessFunctionAgreement (first ++ second) left right) :
    WitnessFunctionAgreement first left right :=
  agreement.mono (List.subset_append_left _ _)

/-- Restrict a concatenated support to its second component. -/
theorem WitnessFunctionAgreement.right
    {first second : List (AssignedCell F)} {left right : Placed ProverEnvironment F}
    (agreement : WitnessFunctionAgreement (first ++ second) left right) :
    WitnessFunctionAgreement second left right :=
  agreement.mono (List.subset_append_right _ _)

/-- The declared cell reads and immutable context determine the callback's result. -/
def WitnessFunctionSupport {Value : Type}
    (reads : List (AssignedCell F)) (compute : Placed ProverEnvironment F → Value) : Prop :=
  ∀ left right, WitnessFunctionAgreement reads left right → compute left = compute right

/-- Enlarging the declared read set preserves a semantic support certificate. -/
theorem WitnessFunctionSupport.mono {Value : Type}
    {reads larger : List (AssignedCell F)} {compute : Placed ProverEnvironment F → Value}
    (support : WitnessFunctionSupport reads compute) (hincluded : reads ⊆ larger) :
    WitnessFunctionSupport larger compute :=
  fun left right agreement => support left right (agreement.mono hincluded)

/-- A deterministic function of supported data introduces no additional environment read. -/
theorem WitnessFunctionSupport.map {Value Result : Type}
    {reads : List (AssignedCell F)} {compute : Placed ProverEnvironment F → Value}
    (support : WitnessFunctionSupport reads compute) (f : Value → Result) :
    WitnessFunctionSupport reads (fun env => f (compute env)) :=
  fun left right agreement => congrArg f (support left right agreement)

/-- Pair two supported computations using the concatenation of their read sets. -/
theorem WitnessFunctionSupport.pair {Left Right : Type}
    {leftReads rightReads : List (AssignedCell F)}
    {leftCompute : Placed ProverEnvironment F → Left}
    {rightCompute : Placed ProverEnvironment F → Right}
    (leftSupport : WitnessFunctionSupport leftReads leftCompute)
    (rightSupport : WitnessFunctionSupport rightReads rightCompute) :
    WitnessFunctionSupport (leftReads ++ rightReads)
      (fun env => (leftCompute env, rightCompute env)) :=
  fun left right agreement => Prod.ext
    (leftSupport left right agreement.left) (rightSupport left right agreement.right)

/-- Opens a read obligation with the read set left to unification: the registration tactic
applies this, closes the support by the tagged rules, and keeps the remaining property. -/
theorem exists_witnessFunctionSupport_of {Value : Type}
    {compute : Placed ProverEnvironment F → Value} {property : List (AssignedCell F) → Prop}
    (reads : List (AssignedCell F)) (support : WitnessFunctionSupport reads compute)
    (hproperty : property reads) :
    ∃ reads, WitnessFunctionSupport reads compute ∧ property reads :=
  ⟨reads, support, hproperty⟩

/-- The function that a single-output witness program computes. Read obligations and the
support rules are stated over it, not over the evaluation itself. A definition keeps the
program syntactic under keygen normalization, so rule search matches the program by shape. -/
def programFunction (program : WitgenIR F 1) (env : Placed ProverEnvironment F) : F :=
  (program.eval env)[0]

/-! ## Rules for Clean's own program shapes -/

/-- Reading one assigned cell has exactly that cell as a sufficient support. -/
@[witness_support]
theorem witnessFunctionSupport_readCell (cell : AssignedCell F) :
    WitnessFunctionSupport [cell] (fun env => readCell env cell) :=
  fun _ _ agreement => agreement.cellValues cell (List.mem_singleton_self _)

/-- Absolute instance reads depend only on immutable public input, with no advice
dependency. -/
@[witness_support]
theorem witnessFunctionSupport_instanceGet (column : Column .instance) (row : ℕ) :
    WitnessFunctionSupport (F := F) [] (programFunction (instanceGet column row)) := by
  intro left right agreement
  dsimp only [programFunction]
  rw [eval_instanceGet, eval_instanceGet]
  exact agreement.nonAdvice column.toAny (row : ℤ)
    (by change ColumnKind.instance ≠ ColumnKind.advice; decide)

/-- A field-expression program reads only the cells in its syntax. -/
@[witness_support]
theorem witnessFunctionSupport_ofFExpr (expression : FExpr F) :
    WitnessFunctionSupport (fieldReads expression)
      (programFunction (WitgenIROver.ofFExpr expression)) := by
  intro left right agreement
  dsimp only [programFunction]
  rw [eval_ofFExpr_zero, eval_ofFExpr_zero]
  exact fieldReads_eval expression { env := left } { env := right } agreement.toContextAgreement

/-- A structured program reads the cells of its local steps and its output. -/
@[witness_support]
theorem witnessFunctionSupport_structured (steps : List (StepOver F (AssignedCell F)))
    (output : VExprOver F (AssignedCell F) 1) :
    WitnessFunctionSupport (stepsReads steps ++ vectorReads output)
      (programFunction (WitgenIROver.ir steps output)) :=
  fun left right agreement => congrArg (fun values : Vector F 1 => values[0])
    (programReads_eval (.ir steps output) (stepsReads steps ++ vectorReads output) rfl left right
      agreement.cellValues agreement.indexed agreement.data agreement.hints)

/-- The scalar program emitted by a builder reads exactly the builder's support. -/
@[witness_support]
theorem witnessFunctionSupport_scalarBuilder (program : MOver F (AssignedCell F) (FExpr F)) :
    WitnessFunctionSupport (valueBuilderReads (value := field) program)
      (programFunction (program.toIRScalar (Env := Placed ProverEnvironment F))) := by
  intro left right agreement
  dsimp only [programFunction]
  simp only [MOver.eval_toIRScalar]
  exact valueBuilderReads_eval (value := field) program left right
    agreement.cellValues agreement.indexed agreement.data agreement.hints

/-- Structured field or record builders supply a support for native callers. -/
@[witness_support]
theorem witnessFunctionSupport_valueBuilder {value : TypeMap} [ProvableType value]
    (program : MOver F (AssignedCell F) (value (FExpr F))) :
    WitnessFunctionSupport (valueBuilderReads program) (fun env => program.eval env) :=
  fun left right agreement => valueBuilderReads_eval program left right
    agreement.cellValues agreement.indexed agreement.data agreement.hints

/-- Native callers of a structured u64 builder inherit all its collected reads. -/
@[witness_support]
theorem witnessFunctionSupport_u64Builder (program : MOver F (AssignedCell F) (U64Expr F)) :
    WitnessFunctionSupport (u64BuilderReads program) (fun env => program.evalU64 env) :=
  fun left right agreement => u64BuilderReads_eval program left right
    agreement.cellValues agreement.indexed agreement.data agreement.hints

/-- Native callers of a structured Boolean builder inherit all its collected reads. -/
@[witness_support]
theorem witnessFunctionSupport_boolBuilder (program : MOver F (AssignedCell F) (BExpr F)) :
    WitnessFunctionSupport (boolBuilderReads program) (fun env => program.evalBool env) :=
  fun left right agreement => boolBuilderReads_eval program left right
    agreement.cellValues agreement.indexed agreement.data agreement.hints

/-- The one-element native wrapper of a supported function has that function's support. -/
@[witness_support]
theorem witnessFunctionSupport_nativeScalar {reads : List (AssignedCell F)}
    {compute : Placed ProverEnvironment F → F} (support : WitnessFunctionSupport reads compute) :
    WitnessFunctionSupport reads (programFunction (.native (fun input => #v[compute input]))) :=
  support

/-- The native wrapper of a supported Boolean function, as a field bit, has its support. -/
@[witness_support]
theorem witnessFunctionSupport_nativeBoolean {reads : List (AssignedCell F)}
    {compute : Placed ProverEnvironment F → Bool}
    (support : WitnessFunctionSupport reads compute) :
    WitnessFunctionSupport reads
      (programFunction (.native (fun input => #v[if compute input then (1 : F) else 0]))) :=
  support.map (fun value => if value then (1 : F) else 0)

/-- A constant native program does not read any cell. -/
@[witness_support]
theorem witnessFunctionSupport_nativeConstant (value : F) :
    WitnessFunctionSupport (F := F) [] (programFunction (.native (fun _ => #v[value]))) :=
  fun _ _ _ => rfl

/-- A fixed value does not need any cell read. Last among the rules, since it matches any
program whose evaluation unfolds to a constant. -/
@[witness_support]
theorem witnessFunctionSupport_const {Value : Type} (value : Value) :
    WitnessFunctionSupport (F := F) [] (fun _ => value) := fun _ _ _ => rfl

/-! ## Supported parameters -/

/-- A witness program with a certified read set. -/
structure SupportedProgram (F : Type) [FiniteField F] where
  /-- The program. -/
  program : WitgenIR F 1
  /-- The cells that the program may read. -/
  reads : List (AssignedCell F)
  /-- The certificate that the program reads only those cells. -/
  support : WitnessFunctionSupport reads (programFunction program)

/-- A native function with a certified read set. -/
structure SupportedFunction (F : Type) [FiniteField F] (Value : Type) where
  /-- The function. -/
  compute : Placed ProverEnvironment F → Value
  /-- The cells that the function may read. -/
  reads : List (AssignedCell F)
  /-- The certificate that the function reads only those cells. -/
  support : WitnessFunctionSupport reads compute

/-- A function of the assignment with a certified read set: the form of a parameter that a
witness program lifts to the prover environment and that `extract` applies to the assignment
itself, so the certificate is about the lift. -/
structure SupportedEnvironmentFunction (F : Type) [FiniteField F] (Value : Type) where
  /-- The function. -/
  compute : Placed Environment F → Value
  /-- The cells that the function may read. -/
  reads : List (AssignedCell F)
  /-- The certificate that the lift of the function reads only those cells. -/
  support : WitnessFunctionSupport reads (fun env => compute env.toEnvironment)

attribute [witness_support] SupportedProgram.support SupportedFunction.support
  SupportedEnvironmentFunction.support

/-- Close a `WitnessFunctionSupport` goal from the rules tagged `witness_support`; a read set
left as a natural hole is assigned by unification. -/
macro "solve_witness_support" : tactic =>
  `(tactic| solve_by_elim
      (maxDepth := 16) (transparency := .reducible) (symm := false) (exfalso := false)
      using $(Lean.mkIdent `witness_support))

/-- `supported% p` bundles the program or function `p` with the read set that the tagged rules
find for it. The expected type chooses between `SupportedProgram`, `SupportedFunction`, and
`SupportedEnvironmentFunction`. -/
macro "supported% " p:term:max : term => `(⟨$p, _, by solve_witness_support⟩)

end

/-! ## Explicit equation lemmas for `Witgen.*Reads`

Stating these one constructor at a time avoids triggering Lean's mutual-recursion splitter
generator during `attribute [keygen_norm]` registration. -/

section ReadEquations

variable {F : Type}

theorem fieldReads_expr {V : Type} (v : V) :
    Witgen.fieldReads (F := F) (.expr v) = [v] := rfl
theorem fieldReads_const {V : Type} (c : F) :
    Witgen.fieldReads (F := F) (V := V) (.const c) = [] := rfl
theorem fieldReads_localVar {V : Type} (i : ℕ) :
    Witgen.fieldReads (F := F) (V := V) (.localVar i) = [] := rfl
theorem fieldReads_add {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.fieldReads (.add l r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem fieldReads_hAdd {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.fieldReads (l + r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem fieldReads_mul {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.fieldReads (.mul l r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem fieldReads_hMul {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.fieldReads (l * r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem fieldReads_inv {V : Type} (e : Witgen.FExprOver F V) :
    Witgen.fieldReads (.inv e) = Witgen.fieldReads e := rfl
theorem fieldReads_hInv {V : Type} (e : Witgen.FExprOver F V) :
    Witgen.fieldReads (e⁻¹) = Witgen.fieldReads e := rfl
theorem fieldReads_neg [Field F] {V : Type} (e : Witgen.FExprOver F V) :
    Witgen.fieldReads (-e) = Witgen.fieldReads e := rfl
theorem fieldReads_sub [Field F] {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.fieldReads (l - r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem fieldReads_ofNat {V : Type} {n : ℕ} [OfNat F n] :
    Witgen.fieldReads (no_index (OfNat.ofNat n) : Witgen.FExprOver F V) = [] := rfl
theorem fieldReads_ofU64 {V : Type} (e : Witgen.U64ExprOver F V) :
    Witgen.fieldReads (.ofU64 e) = Witgen.u64Reads e := rfl
theorem fieldReads_ite {V : Type} (c : Witgen.BExprOver F V) (y n : Witgen.FExprOver F V) :
    Witgen.fieldReads (.ite c y n) =
      Witgen.boolReads c ++ Witgen.fieldReads y ++ Witgen.fieldReads n := rfl
theorem fieldReads_listGet {V : Type} (vs : List (Witgen.FExprOver F V))
    (i : Witgen.U64ExprOver F V) :
    Witgen.fieldReads (.listGet vs i) = Witgen.fieldListReads vs ++ Witgen.u64Reads i := rfl
theorem fieldReads_dataGet {V : Type} (d : String) (c : ℕ) (r : Witgen.U64ExprOver F V)
    (o : Fin c) :
    Witgen.fieldReads (.dataGet d c r o) = Witgen.u64Reads r := rfl
theorem fieldReads_hintGet {V : Type} (h : String) (c : ℕ) (r : Witgen.U64ExprOver F V)
    (o : Fin c) :
    Witgen.fieldReads (.hintGet h c r o) = Witgen.u64Reads r := rfl

theorem fieldListReads_nil {V : Type} :
    Witgen.fieldListReads (F := F) (V := V) [] = [] := rfl
theorem fieldListReads_cons {V : Type} (e : Witgen.FExprOver F V)
    (rest : List (Witgen.FExprOver F V)) :
    Witgen.fieldListReads (e :: rest) = Witgen.fieldReads e ++ Witgen.fieldListReads rest := rfl

theorem u64Reads_const {V : Type} (n : UInt64) :
    Witgen.u64Reads (F := F) (V := V) (.const n) = [] := rfl
theorem u64Reads_ofNat {V : Type} {n : ℕ} :
    Witgen.u64Reads (F := F) (V := V) (no_index (OfNat.ofNat n)) = [] := rfl
theorem u64Reads_idx {V : Type} :
    Witgen.u64Reads (F := F) (V := V) .idx = [] := rfl
theorem u64Reads_localVar {V : Type} (i : ℕ) :
    Witgen.u64Reads (F := F) (V := V) (.localVar i) = [] := rfl
theorem u64Reads_val {V : Type} (e : Witgen.FExprOver F V) :
    Witgen.u64Reads (.val e) = Witgen.fieldReads e := rfl
theorem u64Reads_add {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.add l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_hAdd {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (l + r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_mul {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.mul l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_hMul {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (l * r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_div {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.div l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_mod {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.mod l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_land {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.land l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_lor {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.lor l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_lxor {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.lxor l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_shiftL {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.shiftL l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_shiftR {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.shiftR l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem u64Reads_ite {V : Type} (c : Witgen.BExprOver F V) (y n : Witgen.U64ExprOver F V) :
    Witgen.u64Reads (.ite c y n) =
      Witgen.boolReads c ++ Witgen.u64Reads y ++ Witgen.u64Reads n := rfl

theorem boolReads_true {V : Type} :
    Witgen.boolReads (F := F) (V := V) .true = [] := rfl
theorem boolReads_false {V : Type} :
    Witgen.boolReads (F := F) (V := V) .false = [] := rfl
theorem boolReads_feq {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.boolReads (.feq l r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem boolReads_eqCondFF {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.boolReads (l =? r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem boolReads_eqCondFC {V : Type} (l : Witgen.FExprOver F V) (r : F) :
    Witgen.boolReads (l =? r) = Witgen.fieldReads l := by
  simp [Witgen.EqCond.eqCond, boolReads_feq, fieldReads_const]
theorem boolReads_eqCondFN {V : Type} [NatCast F] (l : Witgen.FExprOver F V) (r : ℕ) :
    Witgen.boolReads (l =? r) = Witgen.fieldReads l := by
  simp [Witgen.EqCond.eqCond, boolReads_feq, fieldReads_const]
theorem boolReads_flt {V : Type} (l r : Witgen.FExprOver F V) :
    Witgen.boolReads (.flt l r) = Witgen.fieldReads l ++ Witgen.fieldReads r := rfl
theorem boolReads_neq {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.boolReads (.neq l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem boolReads_lt {V : Type} (l r : Witgen.U64ExprOver F V) :
    Witgen.boolReads (.lt l r) = Witgen.u64Reads l ++ Witgen.u64Reads r := rfl
theorem boolReads_bit {V : Type} (e : Witgen.FExprOver F V) (k : ℕ) :
    Witgen.boolReads (.bit e k) = Witgen.fieldReads e := rfl
theorem boolReads_not {V : Type} (e : Witgen.BExprOver F V) :
    Witgen.boolReads (.not e) = Witgen.boolReads e := rfl
theorem boolReads_and {V : Type} (l r : Witgen.BExprOver F V) :
    Witgen.boolReads (.and l r) = Witgen.boolReads l ++ Witgen.boolReads r := rfl
theorem boolReads_hAnd {V : Type} (l r : Witgen.BExprOver F V) :
    Witgen.boolReads (l &&& r) = Witgen.boolReads l ++ Witgen.boolReads r := rfl

theorem vectorReads_lit {V : Type} {n : ℕ} (vs : Vector (Witgen.FExprOver F V) n) :
    Witgen.vectorReads (.lit vs) = Witgen.fieldListReads vs.toList := rfl
theorem vectorReads_mapRange {V : Type} (n : ℕ) (b : Witgen.FExprOver F V) :
    Witgen.vectorReads (.mapRange n b) = Witgen.fieldReads b := rfl
theorem vectorReads_envRange {V : Type} {m : ℕ} (n : ℕ) :
    Witgen.vectorReads (F := F) (V := V) (n := m) (.envRange n) = [] := rfl
theorem vectorReads_bitsOf {V : Type} {m : ℕ} (e : Witgen.FExprOver F V) :
    Witgen.vectorReads (n := m) (.bitsOf e) = Witgen.fieldReads e := rfl
theorem vectorReads_append {V : Type} {m n : ℕ}
    (l : Witgen.VExprOver F V m) (r : Witgen.VExprOver F V n) :
    Witgen.vectorReads (.append l r) = Witgen.vectorReads l ++ Witgen.vectorReads r := rfl

theorem stepReads_letF {V : Type} (e : Witgen.FExprOver F V) :
    Witgen.stepReads (.letF e) = Witgen.fieldReads e := rfl
theorem stepReads_letU {V : Type} (e : Witgen.U64ExprOver F V) :
    Witgen.stepReads (.letU e) = Witgen.u64Reads e := rfl

theorem stepsReads_nil {V : Type} :
    Witgen.stepsReads (F := F) (V := V) [] = [] := rfl
theorem stepsReads_cons {V : Type} (s : Witgen.StepOver F V) (rest : List (Witgen.StepOver F V)) :
    Witgen.stepsReads (s :: rest) = Witgen.stepReads s ++ Witgen.stepsReads rest := rfl

end ReadEquations

end Halo2
