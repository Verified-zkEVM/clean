module

public import Clean.Air.Realizes
public import Clean.Air.LedgerView

/-! Constructive realization, empty shards, and physical occurrence regressions. -/

@[expose] public section

namespace ResourceRealizationTests

open Air.Flat

variable {F : Type} [FiniteField F] [DecidableEq F]

private def ensemble (F : Type) [FiniteField F] : Ensemble F field := .empty F field

private def witness (publicInput : F) : EnsembleWitness (ensemble F) where
  tables := []
  data _ _ := #[]
  publicInput := publicInput
  same_length := rfl
  same_circuits := by intro i hi; exact (Nat.not_lt_zero i hi).elim
  same_data := by simp

private theorem witness_valid (publicInput : F) : (witness publicInput).Valid publicInput := by
  refine ⟨rfl, ?_, ?_⟩
  · intro table member
    have same : table = (witness publicInput).verifierTable := by
      exact List.mem_singleton.mp member
    rw [same]
    exact EnsembleWitness.verifierTable_constraints_of_verifier_empty rfl
  · intro channel member
    exact (List.not_mem_nil member).elim

private def trace (initial : F) (events : List Unit) (final : F) : Prop :=
  events = [] ∧ initial = final

private def boundary := snapshotBoundary (F := F) (PublicIO := field) (fun publicInput => (publicInput, publicInput))
private def admissible (_ : F) (_ : F) (_ : List Unit) (_ : F) : Prop := True

private instance (publicInput : F) (data : ExecutionData F Unit Unit) :
    Decidable (ExecutionData.Valid trace boundary admissible publicInput data) := by
  unfold ExecutionData.Valid trace boundary snapshotBoundary admissible
  infer_instance

/-- The compiler checks data against a semantic domain and rejects invalid candidates. -/
private def compiler : EnsembleCompiler (ensemble F) (ExecutionData F Unit Unit)
    (ExecutionData.Valid trace boundary admissible) where
  compile publicInput data :=
    if ExecutionData.Valid trace boundary admissible publicInput data
    then some (witness publicInput) else none
  sound publicInput data result compiled := by
    split_ifs at compiled with valid
    · have same := Option.some.inj compiled
      exact ⟨valid, same ▸ witness_valid publicInput⟩
  complete publicInput data valid := by
    exact ⟨witness publicInput, if_pos valid⟩

private def realization : TraceRealizes (ensemble F) trace boundary admissible where
  sound publicInput _ _ :=
    ⟨⟨publicInput, [], publicInput, ()⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩
  compiler := compiler

/-- Empty shards keep the complete state and admit the identity execution. -/
example (publicInput : F) : (ensemble F).Statement publicInput ↔ ∃ events,
    trace publicInput events publicInput ∧ admissible publicInput publicInput events publicInput :=
  realization.snapshot_statement_iff publicInput

/-- Invalid input is rejected by executable checks, without a proof argument. -/
example (publicInput : F) : compiler.compile publicInput ⟨publicInput, [()], publicInput, ()⟩ = none := by
  simp [compiler, ExecutionData.Valid, trace]

private def duplicated : Table F where
  component := ⟨GeneralFormalCircuit.empty F field⟩
  width := 1
  table := [#[0], #[0]]
  data _ _ := #[]
  uniform_width := by simp

/-- Equal table contents retain separate physical table and row identities. -/
example : ((LedgerView.readOccurrences [duplicated (F := F), duplicated]).map
    (fun occurrence => (occurrence.tableIndex, occurrence.rowIndex))) =
    [(0, 0), (0, 1), (1, 0), (1, 1)] := rfl

end ResourceRealizationTests
