module

public import Clean.Air.StagedChannels
public import Clean.Air.WitnessGeneration

@[expose] public section

/-!
# One bus, pulled and pushed by the same table

A table that both pulls from a channel and pushes to it is not a cycle when what it reads and
what it writes are disjoint classes of messages. A bus shared by several operations is where this
happens: the table that answers one operation does so by using the answers to others, and all of
it travels under one channel name.

The bus here carries `(tag, a, b)`. At `tag = 0` the channel guarantees `b = a * a`, at `tag = 1`
it guarantees `b = a⁴`. Every interaction is a plain push or pull: multiplicity is what
`Clean/Examples/CountedSquares` is about, and it is orthogonal to the ordering question here. A squaring chip provides the squares. A fourth-power chip pulls a square
and pushes a fourth power, on the same bus: its push owes `b = a⁴`, and it pays for it with the
guarantee it got from its pull, plus one constraint of its own.

Ordering whole channels cannot express that — `powers` would have to come before itself. Ordering
*stages*, a channel together with a class of its messages, can: the squares are finished before
the fourth powers, and `Ensemble.tableSoundness_of_stagedRequirementsOn` runs the induction over
those two classes.
-/

namespace SameBus

open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- A message of the bus: an operation tag, an argument and a result. -/
structure PowerMsg (F : Type) where
  /-- `0` for a square, `1` for a fourth power -/
  tag : F
  a : F
  b : F
deriving ProvableStruct

/-- The bus. What it guarantees depends on the tag, which is what makes the two classes of
messages different obligations rather than the same one twice. -/
def powers : Channel (F p) PowerMsg where
  name := "powers"
  Guarantees m _ :=
    (m.tag = 0 → m.b = m.a * m.a) ∧ (m.tag = 1 → m.b = (m.a * m.a) * (m.a * m.a))

/-- The fourth-power messages of the bus, read off the raw message. -/
def isFourth (msg : Array (F p)) : Bool :=
  if h : msg.size = size PowerMsg then
    decide ((fromElements (⟨msg, h⟩ : Vector (F p) (size PowerMsg)) : PowerMsg (F p)).tag = 1)
  else false

lemma isFourth_toElements (m : PowerMsg (F p)) :
    isFourth (toElements m).toArray = decide (m.tag = 1) := by
  simp [isFourth, ProvableType.fromElements_toElements]

/-! ## The three chips -/

structure SquareInput (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- Provides the squares: constrains `b = a * a` and pushes it at `tag = 0`. Its own constraint
pays for the guarantee, so it pulls nothing and receives nothing. -/
def squareProvider : GeneralFormalCircuit (F p) SquareInput unit where
  name := "square-provider"
  main input := do
    input.b === input.a * input.a
    powers.push { tag := 0, a := input.a, b := input.b }

  channelsWithRequirements := [powers.toRaw]
  Spec _ _ _ := True
  ProverAssumptions input _ _ := input.b = input.a * input.a

  soundness := by
    circuit_proof_start [powers]
    simp_all
  completeness := by
    circuit_proof_start [powers]
    simp_all

structure FourthInput (F : Type) where
  x : F
  /-- the square of `x`, read off the bus -/
  y : F
  z : F
deriving ProvableStruct

/-- Pulls a square and pushes a fourth power, on the same bus. Its push owes `b = a⁴`, and one
constraint is not enough to pay for it: `z = y * y` says nothing about `x` until the bus says
`y = x * x`. That is the obligation the finishing order discharges. -/
def fourthChip : GeneralFormalCircuit (F p) FourthInput unit where
  name := "fourth-chip"
  main input := do
    powers.pull { tag := 0, a := input.x, b := input.y }
    input.z === input.y * input.y
    powers.push { tag := 1, a := input.x, b := input.z }

  channelsWithRequirements := [powers.toRaw]
  Spec _ _ _ := True
  ProverAssumptions input _ _ := input.y = input.x * input.x ∧ input.z = input.y * input.y

  soundness := by
    circuit_proof_start [powers]
    simp_all
  completeness := by
    circuit_proof_start [powers]
    simp_all

structure ConsumerInput (F : Type) where
  x : F
  z : F
deriving ProvableStruct

/-- Reads a fourth power off the bus. -/
def fourthConsumer : GeneralFormalCircuit (F p) ConsumerInput unit where
  name := "fourth-consumer"
  main input := do
    powers.pull { tag := 1, a := input.x, b := input.z }

  Spec input _ _ := input.z = (input.x * input.x) * (input.x * input.x)
  ProverAssumptions input _ _ := input.z = (input.x * input.x) * (input.x * input.x)

  soundness := by
    circuit_proof_start [powers]
    simp_all
  completeness := by
    circuit_proof_start [powers]
    simp_all

/-! ## The ensemble and its two stages -/

abbrev squareProviderComponent : Component (F p) where
  circuit := squareProvider
  generation := .demand {
    channel := powers
    trigger := .pull
    input m := pure { a := .witness m.a, b := .witness m.b }
  }

abbrev fourthChipComponent : Component (F p) where
  circuit := fourthChip
  generation := .demand {
    channel := powers
    trigger := .pull
    input m := pure { x := .witness m.a, y := .witness 0, z := .witness m.b }
  }

abbrev fourthConsumerComponent : Component (F p) where
  circuit := fourthConsumer
  generation := .demand {
    channel := powers
    trigger := .push
    input m := pure { x := .witness m.a, z := .witness m.b }
  }

/-- The three chips and the one bus they share. -/
def ensemble : Ensemble (F p) unit where
  tables := [squareProviderComponent, fourthChipComponent, fourthConsumerComponent]
  unique_names := by
    simp [squareProviderComponent, fourthChipComponent, fourthConsumerComponent,
      squareProvider, fourthChip, fourthConsumer]
  channels := [powers.toRaw]
  unique_channel_names := by simp [circuit_norm, powers]
  tables_channels := by
    intro table h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [circuit_norm, squareProvider, fourthChip, fourthConsumer]
  verifier_channels := by simp [circuit_norm]

/-- The two classes of the bus, newest first: the fourth powers, then the squares. One channel,
finished in two steps. -/
def stages : List (Stage (F p)) :=
  [{ channel := powers.toRaw, cls := isFourth },
   { channel := powers.toRaw, cls := fun m => !isFourth m }]

/-- Every interaction the chip makes on the bus is either its pull, at `tag = 0`, or its push, at
`tag = 1`. Nothing else travels, which is what lets the two classes split its obligations. -/
lemma chip_shape {table : Table (F p)} (h_comp : table.component = fourthChipComponent)
    {i : Interaction (F p)} (h_i : i ∈ table.interactionsWith powers.toRaw) :
    (i.direction = .pull ∧ isFourth i.msg = false) ∨
      (i.direction = .push ∧ isFourth i.msg = true) := by
  cases table
  simp only at h_comp
  subst h_comp
  simp [Table.interactionsWith, List.mem_flatMap, Operations.interactionValuesWith_eq_map,
    Component.interactionsWith_eq, Component.rowOperations, fourthChipComponent, fourthChip,
    powers, circuit_norm] at h_i
  obtain ⟨a, -, h⟩ := h_i
  rcases h with rfl | rfl
  · left; simp [AbstractInteraction.eval, isFourth_toElements, circuit_norm]
  · right; simp [AbstractInteraction.eval, isFourth_toElements, circuit_norm]

/-- On the squares the chip owes only what any plain pull owes, a multiplicity of `0` or `1`, and
it pulls exactly once. Its push is a fourth power, so this class excludes it. -/
theorem chip_requirementsAfterOn_square {earlier : List (Stage (F p))} :
    (fourthChipComponent (p := p)).RequirementsAfterOn
      { channel := powers.toRaw, cls := fun m => !isFourth m } earlier := by
  apply Component.requirementsAfterOn_of_rowOperations
  rintro table - - - - row hrow i h_i h_chan h_cls
  simp [circuit_norm, fourthChipComponent, fourthChip, powers] at h_i ⊢
  rcases h_i with rfl | h_i | rfl
  · simp [circuit_norm]
  · simp [circuit_norm, Gadgets.Equality.circuit,
      Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions] at h_i
  · simp [AbstractInteraction.eval, isFourth_toElements, circuit_norm] at h_cls

/-- The chip's push at `tag = 1` owes `b = a⁴`, and the guarantee it was handed at `tag = 0` is
what pays for it: the bus said `y = x * x`, the chip's own constraint says `z = y * y`. Its only
pull lies in the earlier class, so its soundness closes the rest. -/
theorem chip_requirementsAfterOn_fourth :
    (fourthChipComponent (p := p)).RequirementsAfterOn
      { channel := powers.toRaw, cls := isFourth }
      [{ channel := powers.toRaw, cls := fun m => !isFourth m }] := by
  apply Component.requirementsAfterOn_of_covered
  intro table h_comp c h_c i h_i h_pull
  have hc : c = powers.toRaw := by
    simpa [circuit_norm, fourthChipComponent, fourthChip] using h_c
  subst hc
  rcases chip_shape h_comp h_i with ⟨-, h_cls⟩ | ⟨h_push, -⟩
  · exact ⟨{ channel := powers.toRaw, cls := fun m => !isFourth m }, by simp, rfl, by simp [h_cls]⟩
  · rw [h_push] at h_pull; exact absurd h_pull (by decide)

theorem tableSoundness :
    (ensemble (p := p)).TableSoundness Balance.logUp := by
  apply Ensemble.tableSoundness_of_stagedRequirementsOn stages
    (verifier_covered := by simp [ensemble, circuit_norm, Verifier.Program.empty])
    (verifier_staged := Ensemble.verifierStagedRequirementsOn_of_verifier_empty rfl _)
  · intro s hs
    simp only [stages, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp [ensemble]
  · -- the bus is the only channel with guarantees, and the two classes cover every message
    intro table h_comp c h_c i h_i h_pull
    have hc : c = powers.toRaw := by
      simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at h_comp
      rcases h_comp with h | h | h <;> rw [h] at h_c <;>
        simp_all [circuit_norm, squareProvider, fourthChip, fourthConsumer]
    subst hc
    by_cases h : isFourth i.msg
    · exact ⟨{ channel := powers.toRaw, cls := isFourth }, by simp [stages], rfl, h⟩
    · exact ⟨{ channel := powers.toRaw, cls := fun m => !isFourth m }, by simp [stages], rfl,
        by simp [h]⟩
  · intro s hs
    show s.channel.ConsistentUpTo (Balance.logUp (F := F p)).pullBound
    simp only [stages, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> infer_instance
  · intro component h
    simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    -- the square provider receives no guarantee, so it owes nothing anywhere
    · exact Component.stagedRequirementsOn_of_no_guarantees
        (by simp [circuit_norm, squareProvider]) _
    -- the chip: the fourth powers after the squares, and a plain pull on the squares
    · exact ⟨chip_requirementsAfterOn_fourth, chip_requirementsAfterOn_square, trivial⟩
    -- the consumer declares no requirements at all
    · refine ⟨?_, ?_, trivial⟩ <;>
        exact Component.requirementsAfterOn_of_not_mem _ (by simp [circuit_norm, fourthConsumer])

end SameBus
