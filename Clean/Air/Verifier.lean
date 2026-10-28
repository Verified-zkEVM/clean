module

public import Clean.Circuit.Theorems

@[expose] public section

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

namespace Verifier

/-- Operations of a verifier program. -/
inductive Operation (F : Type) [FiniteField F] where
  /-- Append an interaction. The verifier doesn't list the channel of a pull as one with
  requirements, so the requirements of a pull must hold unconditionally. -/
  | interact (interaction : AbstractInteraction F)
      (requirements : interaction.direction = .pull → ∀ env, interaction.Requirements env)

namespace Operation

@[circuit_norm]
def interaction : Operation F → AbstractInteraction F
  | .interact interaction _ => interaction

@[circuit_norm]
def guaranteeChannel : Operation F → Option (RawChannel F)
  | .interact interaction _ =>
      if interaction.direction = .pull then some interaction.channel else none

@[circuit_norm]
def requirementChannel : Operation F → Option (RawChannel F)
  | .interact interaction _ =>
      if interaction.direction = .pull then none else some interaction.channel

end Operation

abbrev Operations (F : Type) [FiniteField F] := List (Operation F)

namespace Operations

@[circuit_norm]
def interactions (operations : Operations F) : List (AbstractInteraction F) :=
  operations.map Operation.interaction

@[circuit_norm]
def circuitOperations (operations : Operations F) : _root_.Operations F :=
  operations.interactions.map _root_.Operation.interact

attribute [circuit_norm] List.filterMap_nil List.filterMap_cons

@[circuit_norm]
def channelsWithGuarantees (operations : Operations F) : List (RawChannel F) :=
  operations.filterMap Operation.guaranteeChannel

@[circuit_norm]
def channelsWithRequirements (operations : Operations F) : List (RawChannel F) :=
  operations.filterMap Operation.requirementChannel

/-- Every interaction is on a channel with guarantees or with requirements. -/
lemma channel_mem_of_mem_interactions {operations : Operations F}
    {interaction : AbstractInteraction F} : interaction ∈ operations.interactions →
      interaction.channel ∈ operations.channelsWithGuarantees ++
        operations.channelsWithRequirements := by
  simp only [interactions, List.mem_map, List.mem_append, channelsWithGuarantees,
    channelsWithRequirements, List.mem_filterMap]
  rintro ⟨⟨interaction, requirements⟩, h_mem, rfl⟩
  by_cases h : interaction.direction = .pull
  · exact .inl ⟨_, h_mem, by simp [Operation.guaranteeChannel, Operation.interaction, h]⟩
  · exact .inr ⟨_, h_mem, by simp [Operation.requirementChannel, Operation.interaction, h]⟩

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

lemma circuitOperations_inChannelsOrGuaranteesFull (operations : Operations F)
    (env : Environment F) :
    operations.circuitOperations.InChannelsOrGuaranteesFull
      operations.channelsWithGuarantees env := by
  rw [_root_.Operations.InChannelsOrGuaranteesFull, circuitOperations_interactions]
  intro interaction h_interaction
  simp only [interactions, List.mem_map] at h_interaction
  obtain ⟨operation, h_operation, rfl⟩ := h_interaction
  obtain ⟨interaction, requirements⟩ := operation
  by_cases assumes : interaction.direction = .pull
  · left
    rw [channelsWithGuarantees, List.mem_filterMap]
    refine ⟨.interact interaction requirements, h_operation, ?_⟩
    simp only [Operation.guaranteeChannel, Operation.interaction, assumes, ite_true]
  · right
    exact fun h => absurd h assumes

lemma circuitOperations_inChannelsOrRequirementsFull (operations : Operations F)
    (env : Environment F) :
    operations.circuitOperations.InChannelsOrRequirementsFull
      operations.channelsWithRequirements env := by
  rw [_root_.Operations.InChannelsOrRequirementsFull, circuitOperations_interactions]
  intro interaction h_interaction
  simp only [interactions, List.mem_map] at h_interaction
  obtain ⟨operation, h_operation, rfl⟩ := h_interaction
  obtain ⟨interaction, requirements⟩ := operation
  by_cases assumes : interaction.direction = .pull
  · right
    exact requirements assumes env
  · left
    rw [channelsWithRequirements, List.mem_filterMap]
    refine ⟨.interact interaction requirements, h_operation, ?_⟩
    simp only [Operation.requirementChannel, Operation.interaction, assumes, ite_false]

end Operations

end Verifier

/--
An append-only verifier program. Like `Circuit`, its monad instance accumulates operations by
appending the continuation's operations to those already emitted.
-/
@[implicit_reducible]
def Verifier.M (F : Type) [FiniteField F] (α : Type) := α × Verifier.Operations F

namespace Verifier

def bind {α β : Type} (program : M F α) (next : α → M F β) : M F β :=
  let (value, operations) := program
  let (result, moreOperations) := next value
  (result, operations ++ moreOperations)

instance : Monad (M F) where
  pure value := (value, [])
  bind := bind
  map f program := (f program.1, program.2)

@[circuit_norm]
lemma bind_def {α β : Type} (program : M F α) (next : α → M F β) :
    program >>= next =
      let (value, operations) := program
      let (result, moreOperations) := next value
      (result, operations ++ moreOperations) := rfl

@[circuit_norm]
lemma pure_def {α : Type} (value : α) :
    (pure value : M F α) = (value, []) := rfl

@[reducible, circuit_norm]
def M.operations {α : Type} (program : M F α) : Operations F := program.2

@[reducible, circuit_norm]
def M.circuitOperations {α : Type} (program : M F α) : _root_.Operations F :=
  program.operations.circuitOperations

@[circuit_norm]
def addOperation (operation : Operation F) : M F Unit :=
  ((), [operation])

@[circuit_norm]
def pull {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (message : Message (Expression F)) : M F Unit :=
  addOperation (.interact (channel.pulled message).toRaw (fun _ env => by
    rw [ChannelInteraction.toRaw_requirements]
    simp [ChannelInteraction.Requirements, Channel.pulled, pulled, Expression.eval]))

@[circuit_norm]
def push {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (message : Message (Expression F)) : M F Unit :=
  addOperation (.interact (channel.pushed message).toRaw (Interaction.Direction.noConfusion ·))

/-- A verifier program parameterized by the proof's public input variables. -/
structure Program (F : Type) [FiniteField F]
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  main : Var PublicIO F → M F Unit
  Spec : PublicIO F → ProverData F → Prop
  soundness : ∀ env,
    ((main (varFromOffset PublicIO 0)).operations.circuitOperations).FullGuarantees env →
      Spec (eval env (varFromOffset (F := F) PublicIO 0)) env.data

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

/-- The channels the program interacts with. -/
@[circuit_norm]
abbrev channels (program : Program F PublicIO) : List (RawChannel F) :=
  program.channelsWithGuarantees ++ program.channelsWithRequirements

def empty (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] :
    Program F PublicIO where
  main _ := pure ()
  Spec _ _ := True
  soundness _ _ := trivial

@[circuit_norm]
lemma empty_main (input : Var PublicIO F) : (empty F PublicIO).main input = pure () := rfl

end Program
end Verifier
