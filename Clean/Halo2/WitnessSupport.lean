import Clean.Circuit.WitnessReads
import Clean.Halo2.WitnessSupportAttr
import Clean.Halo2.Basic

/-!
# Semantic read support for witness programs

Native callbacks are ordinary functions, so their dependencies cannot be inferred by the
structured IR collector. `WitnessFunctionSupport reads compute` certifies the function
itself: equal immutable context data and equal listed cell values imply equal results. It
composes through arbitrary deterministic arithmetic on those results. The rules tagged
`witness_support` cover the program shapes Clean itself produces; a downstream project tags
the rules for its own callbacks.
-/

namespace Halo2

open Witgen

variable {F : Type} [FiniteField F]

/-- Declared cell values and the immutable public/fixed environment agree. -/
structure WitnessFunctionAgreement
    (reads : List (AssignedCell F)) (left right : Placed ProverEnvironment F) : Prop extends
    WitnessContextAgreement reads
      ({ env := left } : CtxOver F (Placed ProverEnvironment F)) { env := right } where
  nonAdvice : ∀ column row, column.kind ≠ .advice →
    left.env.get column row = right.env.get column row

/-- Structured IR uses the context part of native-function agreement. -/
instance witnessFunctionAgreementCoe
    {reads : List (AssignedCell F)} {left right : Placed ProverEnvironment F} :
    Coe (WitnessFunctionAgreement reads left right)
      (WitnessContextAgreement reads
        ({ env := left } : CtxOver F (Placed ProverEnvironment F)) { env := right }) :=
  ⟨WitnessFunctionAgreement.toWitnessContextAgreement⟩

/-- Restrict declared reads while retaining all immutable values. -/
theorem WitnessFunctionAgreement.mono
    {reads smaller : List (AssignedCell F)} {left right : Placed ProverEnvironment F}
    (agreement : WitnessFunctionAgreement reads left right) (hsubset : smaller ⊆ reads) :
    WitnessFunctionAgreement smaller left right :=
  ⟨agreement.toWitnessContextAgreement.mono hsubset, agreement.nonAdvice⟩

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
program syntactic under the keygen normalization, whose `simp!` calls evaluate a native
program applied to an environment, so the rule search matches the program by its shape. -/
def programFunction (program : WitgenIR F 1) (env : Placed ProverEnvironment F) : F :=
  (program.eval env)[0]

/-! ## The rules for Clean's own program shapes -/

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
    WitnessFunctionSupport (fieldWitnessReads expression)
      (programFunction (WitgenIROver.ofFExpr expression)) := by
  intro left right agreement
  dsimp only [programFunction]
  rw [eval_ofFExpr_zero, eval_ofFExpr_zero]
  exact fieldWitnessReads_eval expression { env := left } { env := right } agreement

/-- A structured program reads the cells of its local steps and its output. -/
@[witness_support]
theorem witnessFunctionSupport_structured (steps : List (StepOver F (AssignedCell F)))
    (output : VExprOver F (AssignedCell F) 1) :
    WitnessFunctionSupport (stepsWitnessReads steps ++ vectorWitnessReads output)
      (programFunction (WitgenIROver.ir steps output)) :=
  fun left right agreement => congrArg (fun values : Vector F 1 => values[0])
    (structuredWitnessReads_eval steps output left right agreement.toWitnessContextAgreement)

/-- The scalar program emitted by a builder reads exactly the builder's support. -/
@[witness_support]
theorem witnessFunctionSupport_scalarBuilder (program : MOver F (AssignedCell F) (FExpr F)) :
    WitnessFunctionSupport (valueBuilderReads (value := field) program)
      (programFunction (program.toIRScalar (Env := Placed ProverEnvironment F))) := by
  intro left right agreement
  dsimp only [programFunction]
  simp only [MOver.eval_toIRScalar]
  exact valueBuilderReads_eval (value := field) program left right agreement

/-- Structured field or record builders supply a support for native callers. -/
@[witness_support]
theorem witnessFunctionSupport_valueBuilder {value : TypeMap} [ProvableType value]
    (program : MOver F (AssignedCell F) (value (FExpr F))) :
    WitnessFunctionSupport (valueBuilderReads program) (fun env => program.eval env) :=
  fun left right agreement => valueBuilderReads_eval program left right agreement

/-- Native callers of a structured Nat builder inherit all its collected reads. -/
@[witness_support]
theorem witnessFunctionSupport_natBuilder (program : MOver F (AssignedCell F) (NExpr F)) :
    WitnessFunctionSupport (natBuilderReads program) (fun env => program.evalNat env) :=
  fun left right agreement => natBuilderReads_eval program left right agreement

/-- Native callers of a structured Boolean builder inherit all its collected reads. -/
@[witness_support]
theorem witnessFunctionSupport_boolBuilder (program : MOver F (AssignedCell F) (BExpr F)) :
    WitnessFunctionSupport (boolBuilderReads program) (fun env => program.evalBool env) :=
  fun left right agreement => boolBuilderReads_eval program left right agreement

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

/-! ## Supported parameters

A gadget that takes a witness program or a native function as a parameter cannot discharge
its read obligation for an arbitrary value of that parameter. So it takes the parameter in one
of the two forms below, which carry a certified read set. Its contract then declares the
parameter's reads, and the registration tactic closes the obligation from the certificate,
since the `support` fields are themselves rules. -/

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
left as a natural hole is assigned by unification. Rules match at reducible transparency, so
a closure with a rule of its own is found by that rule and every other rule fails fast; a
program written as a definition around the IR is unfolded by the keygen normalization
before the search. The label is quoted without macro scopes, since a hygienic name would not
be the attribute's. -/
macro "solve_witness_support" : tactic =>
  `(tactic| solve_by_elim
      (config := { maxDepth := 16, transparency := .reducible, symm := false, exfalso := false })
      using $(Lean.mkIdent `witness_support))

/-- `supported% p` bundles the program or function `p` with the read set that the tagged rules
find for it. The expected type chooses between `SupportedProgram` and `SupportedFunction`. -/
macro "supported% " p:term:max : term => `(⟨$p, _, by solve_witness_support⟩)

end Halo2
