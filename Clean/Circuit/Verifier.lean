import Clean.Circuit.Theorems

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

namespace Verifier

/-- Operations emitted by a public verifier program. New verifier-only primitives belong here. -/
inductive Operation (F : Type) [FiniteField F] where
  /-- Append an interaction whose non-assumed side holds unconditionally. -/
  | interact (interaction : AbstractInteraction F)
      (otherSide : ∀ env, if interaction.assumeGuarantees then
        interaction.Requirements env else interaction.Guarantees env)

namespace Operation

@[circuit_norm]
def interaction : Operation F → AbstractInteraction F
  | .interact interaction _ => interaction

@[circuit_norm]
def guaranteeChannel : Operation F → Option (RawChannel F)
  | .interact interaction _ =>
      if interaction.assumeGuarantees then some interaction.channel else none

@[circuit_norm]
def requirementChannel : Operation F → Option (RawChannel F)
  | .interact interaction _ =>
      if interaction.assumeGuarantees then none else some interaction.channel

end Operation

abbrev Operations (F : Type) [FiniteField F] := List (Operation F)

namespace Operations

@[circuit_norm]
def interactions (operations : Operations F) : List (AbstractInteraction F) :=
  operations.map Operation.interaction

@[circuit_norm]
def circuitOperations (operations : Operations F) : _root_.Operations F :=
  operations.interactions.map _root_.Operation.interact

@[circuit_norm]
def channelsWithGuarantees (operations : Operations F) : List (RawChannel F) :=
  operations.filterMap Operation.guaranteeChannel

@[circuit_norm]
def channelsWithRequirements (operations : Operations F) : List (RawChannel F) :=
  operations.filterMap Operation.requirementChannel

@[circuit_norm]
lemma circuitOperations_interactions (operations : Operations F) :
    (_root_.Operations.interactions (circuitOperations operations)) = interactions operations := by
  induction operations with
  | nil => rfl
  | cons operation operations ih =>
      change Operation.interaction operation ::
        (_root_.Operations.interactions (circuitOperations operations)) =
          Operation.interaction operation :: interactions operations
      rw [ih]

lemma inChannelsOrGuaranteesFull (operations : Operations F) (env : Environment F) :
    operations.circuitOperations.InChannelsOrGuaranteesFull
      operations.channelsWithGuarantees env := by
  rw [_root_.Operations.InChannelsOrGuaranteesFull, circuitOperations_interactions]
  intro interaction h_interaction
  simp only [interactions, List.mem_map] at h_interaction
  obtain ⟨operation, h_operation, rfl⟩ := h_interaction
  obtain ⟨interaction, otherSide⟩ := operation
  by_cases assumes : interaction.assumeGuarantees
  · left
    rw [channelsWithGuarantees, List.mem_filterMap]
    refine ⟨.interact interaction otherSide, h_operation, ?_⟩
    simp only [Operation.guaranteeChannel, Operation.interaction, assumes, if_true]
  · right
    change interaction.Guarantees env
    have assumes_false : interaction.assumeGuarantees = false :=
      Bool.eq_false_of_not_eq_true assumes
    simpa only [assumes_false, Bool.false_eq_true, if_false] using otherSide env

lemma inChannelsOrRequirementsFull (operations : Operations F) (env : Environment F) :
    operations.circuitOperations.InChannelsOrRequirementsFull
      operations.channelsWithRequirements env := by
  rw [_root_.Operations.InChannelsOrRequirementsFull, circuitOperations_interactions]
  intro interaction h_interaction
  simp only [interactions, List.mem_map] at h_interaction
  obtain ⟨operation, h_operation, rfl⟩ := h_interaction
  obtain ⟨interaction, otherSide⟩ := operation
  by_cases assumes : interaction.assumeGuarantees
  · right
    change interaction.Requirements env
    simpa only [assumes, if_true] using otherSide env
  · left
    rw [channelsWithRequirements, List.mem_filterMap]
    refine ⟨.interact interaction otherSide, h_operation, ?_⟩
    have assumes_false : interaction.assumeGuarantees = false :=
      Bool.eq_false_of_not_eq_true assumes
    simp only [Operation.requirementChannel, Operation.interaction, assumes_false,
      Bool.false_eq_true, if_false]

end Operations

end Verifier

/--
An append-only verifier program. Like `Circuit`, its monad instance accumulates operations by
appending the continuation's operations to those already emitted.
-/
@[implicit_reducible]
def Verifier (F : Type) [FiniteField F] (α : Type) := α × Verifier.Operations F

namespace Verifier

def bind {α β : Type} (program : Verifier F α) (next : α → Verifier F β) : Verifier F β :=
  let (value, operations) := program
  let (result, moreOperations) := next value
  (result, operations ++ moreOperations)

instance : Monad (Verifier F) where
  pure value := (value, [])
  bind := bind
  map f program := (f program.1, program.2)

@[circuit_norm]
lemma bind_def {α β : Type} (program : Verifier F α) (next : α → Verifier F β) :
    program >>= next =
      let (value, operations) := program
      let (result, moreOperations) := next value
      (result, operations ++ moreOperations) := rfl

@[circuit_norm]
lemma pure_def {α : Type} (value : α) :
    (pure value : Verifier F α) = (value, []) := rfl

@[reducible, circuit_norm]
def operations {α : Type} (program : Verifier F α) : Operations F := program.2

@[reducible, circuit_norm]
def circuitOperations {α : Type} (program : Verifier F α) : _root_.Operations F :=
  program.operations.circuitOperations

@[circuit_norm]
def addOperation (operation : Operation F) : Verifier F Unit :=
  ((), [operation])

@[circuit_norm]
def emit {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (mult : Expression F) (message : Message (Expression F)) : Verifier F Unit :=
  addOperation (.interact (channel.emitted mult message).toRaw (by
    intro env
    change (channel.emitted mult message).toRaw.Guarantees env
    intro assumes
    exact Bool.noConfusion assumes))

@[circuit_norm]
def pull {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (message : Message (Expression F)) : Verifier F Unit :=
  addOperation (.interact (channel.pulled message).toRaw (by
    intro env
    change (channel.pulled message).toRaw.Requirements env
    rw [ChannelInteraction.toRaw_requirements]
    change Expression.eval env (-1 : Expression F) ≠ -1 →
      Expression.eval env (-1 : Expression F) ≠ 0 → _
    simp [Expression.eval]))

@[circuit_norm]
def push {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (message : Message (Expression F)) : Verifier F Unit :=
  emit channel 1 message

/-- A verifier program parameterized by the proof's public input variables. -/
structure Program (F : Type) [FiniteField F]
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  main : Var PublicIO F → Verifier F Unit
  Spec : PublicIO F → ProverData F → Prop := fun _ _ => True
  soundness : ∀ env,
    ((main (varFromOffset PublicIO 0)).operations.circuitOperations).FullGuarantees env →
      Spec (eval env (varFromOffset (F := F) PublicIO 0)) env.data := by simp

namespace Program

@[circuit_norm]
abbrev operations (program : Program F PublicIO) : Operations F :=
  (program.main (varFromOffset PublicIO 0)).operations

@[circuit_norm]
abbrev circuitOperations (program : Program F PublicIO) : _root_.Operations F :=
  program.operations.circuitOperations

@[circuit_norm]
abbrev interactions (program : Program F PublicIO) : List (AbstractInteraction F) :=
  program.operations.interactions

@[circuit_norm]
abbrev channelsWithGuarantees (program : Program F PublicIO) : List (RawChannel F) :=
  program.operations.channelsWithGuarantees

@[circuit_norm]
abbrev channelsWithRequirements (program : Program F PublicIO) : List (RawChannel F) :=
  program.operations.channelsWithRequirements

def empty (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] :
    Program F PublicIO where
  main _ := pure ()

@[circuit_norm]
lemma empty_operations : (empty F PublicIO).operations = [] := rfl

@[circuit_norm]
lemma empty_channelsWithGuarantees : (empty F PublicIO).channelsWithGuarantees = [] := rfl

@[circuit_norm]
lemma empty_channelsWithRequirements : (empty F PublicIO).channelsWithRequirements = [] := rfl

end Program
end Verifier
