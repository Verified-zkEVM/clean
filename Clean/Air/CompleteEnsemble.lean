module

public import Clean.Air.FlatEnsemble

/-! # Sound and complete flat ensembles

`CompleteEnsemble` adds completeness to `FormalEnsemble` without changing the existing bundle.
`EnsembleCompiler` records a proof-independent partial witness constructor: successful
compilation implies semantic validity, and every semantically valid input succeeds.
The semantic domain is independent of compiler success and circuit witnesses. -/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The complete raw AIR obligation for one witness at a specified public input. -/
def EnsembleWitness.Valid {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (publicInput : PublicIO F) : Prop :=
  witness.publicInput = publicInput ∧ witness.Constraints ∧ witness.BalancedChannels

/-- A valid witness proves exactly Clean's raw ensemble statement. -/
theorem EnsembleWitness.Valid.statement {ens : Ensemble F PublicIO}
    {witness : EnsembleWitness ens} {publicInput : PublicIO F}
    (valid : witness.Valid publicInput) : ens.Statement publicInput :=
  ⟨witness, valid⟩

/-- A formal ensemble with both directions of its semantic contract. -/
structure CompleteEnsemble (F : Type) [FiniteField F] [DecidableEq F]
    (PublicIO : TypeMap) [ProvableType PublicIO] extends FormalEnsemble F PublicIO where
  completeness : ensemble.Completeness Assumptions Spec

/-- The public statement of a complete ensemble is its semantic specification. -/
theorem CompleteEnsemble.statement_iff (c : CompleteEnsemble F PublicIO)
    (publicInput : PublicIO F) (assumptions : c.Assumptions publicInput) :
    c.ensemble.Statement publicInput ↔ c.Spec publicInput :=
  ⟨c.soundness publicInput assumptions, c.completeness publicInput assumptions⟩

/-- A witness compiler for an independently defined execution relation.

`compile` consumes data, not a proof of validity. Soundness checks both the supplied execution and
the resulting AIR witness; completeness establishes success for every valid execution. The field
contains a Lean function, so executable implementations must separately avoid noncomputable code.
-/
structure EnsembleCompiler (ens : Ensemble F PublicIO) (Execution : Type)
    (Executes : PublicIO F → Execution → Prop) where
  compile : PublicIO F → Execution → Option (EnsembleWitness ens)
  sound : ∀ publicInput execution witness, compile publicInput execution = some witness →
    Executes publicInput execution ∧ witness.Valid publicInput
  complete : ∀ publicInput execution, Executes publicInput execution →
    ∃ witness, compile publicInput execution = some witness

/-- Successful compilation characterizes the semantic domain, independently of any choice of
proof of execution validity. -/
theorem EnsembleCompiler.succeeds_iff {ens : Ensemble F PublicIO} {Execution : Type}
    {Executes : PublicIO F → Execution → Prop} (c : EnsembleCompiler ens Execution Executes)
    (publicInput : PublicIO F) (execution : Execution) :
    (∃ witness, c.compile publicInput execution = some witness) ↔ Executes publicInput execution := by
  constructor
  · rintro ⟨witness, compiled⟩
    exact (c.sound publicInput execution witness compiled).1
  · exact c.complete publicInput execution

/-- Constructive witness compilation supplies the existential direction of AIR correctness. -/
theorem EnsembleCompiler.completeness {ens : Ensemble F PublicIO} {Execution : Type}
    {Executes : PublicIO F → Execution → Prop} (c : EnsembleCompiler ens Execution Executes) :
    ens.Completeness (fun _ => True) (fun publicInput => ∃ execution, Executes publicInput execution) := by
  rintro publicInput _ ⟨execution, valid⟩
  obtain ⟨witness, compiled⟩ := c.complete publicInput execution valid
  exact (c.sound publicInput execution witness compiled).2.statement

/-- Combine a proved raw-AIR soundness theorem with a complete witness compiler. -/
def EnsembleCompiler.toCompleteEnsemble {ens : Ensemble F PublicIO} {Execution : Type}
    {Executes : PublicIO F → Execution → Prop} (c : EnsembleCompiler ens Execution Executes)
    (soundness : ens.Soundness (fun _ => True)
      (fun publicInput => ∃ execution, Executes publicInput execution)) :
    CompleteEnsemble F PublicIO where
  ensemble := ens
  Spec publicInput := ∃ execution, Executes publicInput execution
  soundness := soundness
  completeness := c.completeness

end Air.Flat
