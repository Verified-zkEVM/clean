module

public import Clean.Air.CompleteEnsemble

/-! # Realization of an independent semantic trace relation

The semantic trace relation is supplied independently of the circuit representation.
Boundaries can authenticate full snapshots or openings. The semantic domain specifies
admissible executions independently of circuit rows and compiler success.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable {State Event Opening : Type}

/-- Data presented to a witness compiler, including explicit authentication openings. -/
structure ExecutionData (State Event Opening : Type) where
  initial : State
  events : List Event
  final : State
  opening : Opening

/-- An implementation-independent interpretation of execution and boundary data. -/
def ExecutionData.Valid
    (trace : State → List Event → State → Prop)
    (boundary : PublicIO F → State → State → Opening → Prop)
    (admissible : PublicIO F → State → List Event → State → Prop)
    (publicInput : PublicIO F) (execution : ExecutionData State Event Opening) : Prop :=
  boundary publicInput execution.initial execution.final execution.opening ∧
    trace execution.initial execution.events execution.final ∧
    admissible publicInput execution.initial execution.events execution.final

/-- Raw AIR acceptance is realized by the specified traces, with constructive completeness. -/
structure TraceRealizes (ens : Ensemble F PublicIO)
    (trace : State → List Event → State → Prop)
    (boundary : PublicIO F → State → State → Opening → Prop)
    (admissible : PublicIO F → State → List Event → State → Prop) where
  sound : ens.Soundness (fun _ => True)
    (fun publicInput => ∃ execution, ExecutionData.Valid trace boundary admissible publicInput execution)
  compiler : EnsembleCompiler ens (ExecutionData State Event Opening)
    (ExecutionData.Valid trace boundary admissible)

namespace TraceRealizes

variable {ens : Ensemble F PublicIO}
variable {trace : State → List Event → State → Prop}
variable {boundary : PublicIO F → State → State → Opening → Prop}
variable {admissible : PublicIO F → State → List Event → State → Prop}

/-- The public statement refers only to the independent trace and authenticated endpoints. -/
theorem statement_iff (realizes : TraceRealizes ens trace boundary admissible) (publicInput : PublicIO F) :
    ens.Statement publicInput ↔ ∃ initial events final,
      (∃ opening, boundary publicInput initial final opening) ∧
        trace initial events final ∧ admissible publicInput initial events final := by
  have characterized : ens.Statement publicInput ↔ ∃ execution,
      ExecutionData.Valid trace boundary admissible publicInput execution :=
    (realizes.compiler.toCompleteEnsemble realizes.sound).statement_iff publicInput trivial
  rw [characterized]
  constructor
  · rintro ⟨⟨initial, events, final, opening⟩, authenticated, executed, admitted⟩
    exact ⟨initial, events, final, ⟨opening, authenticated⟩, executed, admitted⟩
  · rintro ⟨initial, events, final, ⟨opening, authenticated⟩, executed, admitted⟩
    exact ⟨⟨initial, events, final, opening⟩, authenticated, executed, admitted⟩

end TraceRealizes

/-- Complete explicit snapshots are a functional specialization of relational authentication. -/
def snapshotBoundary (decode : PublicIO F → State × State)
    (publicInput : PublicIO F) (initial final : State) (_ : Unit) : Prop :=
  initial = (decode publicInput).1 ∧ final = (decode publicInput).2

theorem TraceRealizes.snapshot_statement_iff {ens : Ensemble F PublicIO}
    {trace : State → List Event → State → Prop} {decode : PublicIO F → State × State}
    {admissible : PublicIO F → State → List Event → State → Prop}
    (realizes : TraceRealizes ens trace (snapshotBoundary decode) admissible) (publicInput : PublicIO F) :
    ens.Statement publicInput ↔ ∃ events,
      trace (decode publicInput).1 events (decode publicInput).2 ∧
        admissible publicInput (decode publicInput).1 events (decode publicInput).2 := by
  rw [realizes.statement_iff]
  simp [snapshotBoundary]

/-- Join authenticated executions only at an actual shared state. A commitment boundary
must establish this equality separately; digest equality is not a premise of this rule. -/
theorem trace_join (trace : State → List Event → State → Prop)
    (append : ∀ initial middle final left right,
      trace initial left middle → trace middle right final → trace initial (left ++ right) final)
    {initial leftEnd rightStart final : State} {left right : List Event}
    (leftTrace : trace initial left leftEnd) (rightTrace : trace rightStart right final)
    (cut : leftEnd = rightStart) : trace initial (left ++ right) final := by
  subst rightStart
  exact append initial leftEnd final left right leftTrace rightTrace

end Air.Flat
