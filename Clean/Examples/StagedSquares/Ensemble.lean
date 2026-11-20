module

public import Clean.Examples.CountedSquares.Ensemble
public import Clean.Air.OrderedChannel
public import Clean.Air.StagedChannels

@[expose] public section

/-!
# A count bounded on another channel

`Clean/Examples/CountedSquares` pulls a square with multiplicity `1` or `2`, and the consumer
discharges the pull's requirement `count = 0 ∨ CountUpTo 2 count` with a constraint of its own,
`(count - 1) * (count - 2) = 0`. That only scales while the bound is small enough to write as a
polynomial: a chip counting to `255` range-checks its multiplicity instead, on a second channel.

Here the range check is that second channel. `counts` carries a multiplicity that counts up to
`countBound`, a chip provides it, and the consumer pulls from it rather than constraining its
count. The consumer's requirement on `squares` then follows from its *guarantee* on `counts`,
which `OrderedChannel` cannot express: it orders tables, and nothing about the order of these
three tables says where the bound comes from. `Ensemble.tableSoundness_of_stagedRequirements`
orders the channels instead, `counts` finished before `squares`.

The ensemble is assembled directly rather than through `SoundEnsemble`, which the staged argument
does not compose with. It generates, and `WitnessGenerationTest.lean` pins what it generates.
-/

namespace StagedSquares

open Air.Flat CountedSquares

variable {p : ℕ} [Fact p.Prime]

/-- A multiplicity that counts up to `countBound`. Pulling it is the range check. -/
def counts : Channel (F p) field where
  name := "counts"
  Guarantees c _ := CountUpTo countBound c

structure RangeInput (F : Type) where
  /-- the multiplicity being range-checked -/
  c : F
  /-- how many pulls this row answers -/
  mult : F
deriving ProvableStruct

/-- The range chip: constrains its value to `1` or `2` and pushes it as often as it is pulled. Its
constraint is what pays for the guarantee, exactly as the squaring chip's constraint pays for
`y = x * x`.

The multiplicity is pushed as it stands. The squaring chip of `CountedSquares` emits `mult + 1`
because it is `preallocated`: its rows exist before any demand and their multiplicity cells start
at `0`, so the `+ 1` is what seeds a run. This chip is `demand`, so a row is created only by a pull
it has to answer and is born with that pull counted; a `+ 1` here would push once more than anyone
pulls, and the channel would not balance. -/
def rangeProvider : GeneralFormalCircuit (F p) RangeInput unit where
  name := "counts-provider"
  main input := do
    assertZero ((input.c - 1) * (input.c - 2))
    counts.emit input.mult input.c

  channelsWithRequirements := [counts.toRaw]
  Spec _ _ _ := True
  ProverAssumptions input _ _ := input.c = 1 ∨ input.c = 2

  soundness := by
    circuit_proof_start [counts]
    simp_all [countUpTo_of_sub_one_mul_sub_two_eq_zero]
  completeness := by
    circuit_proof_start [counts]
    rcases h_assumptions with h | h <;> simp [h]

/-- A row that needs `y = x * x` `count` times, and says nothing about `count` itself: the bound
comes from the pull on `counts`. The pull on `squares` therefore owes a requirement this circuit
cannot pay on its own, which is the point of the example. -/
def stagedConsumer : GeneralFormalCircuit (F p) ConsumerInput unit where
  name := "staged-squares-consumer"
  main input := do
    counts.pull input.count
    squares.pullUpTo countBound input.count (input.x, input.y)

  channelsWithRequirements := [squares.counted countBound]
  Spec input _ _ := input.y = input.x * input.x
  ProverAssumptions input _ _ :=
    (input.count = 1 ∨ input.count = 2) ∧ input.y = input.x * input.x

  soundness := by
    circuit_proof_start [squares, counts]
    simp_all
  completeness := by
    circuit_proof_start [squares, counts]
    obtain ⟨h_count, h_square⟩ := h_assumptions
    refine ⟨?_, fun _ => h_square⟩
    rcases h_count with h | h <;> simp [h] <;>
      exact countUpTo_of_sub_one_mul_sub_two_eq_zero (by ring)

/-- One row per pulled count that nothing has pushed. The padding row answers nothing — multiplicity
`0`, no push — and `c := 1` is there to satisfy the chip's own constraint, which `0` would not. -/
abbrev rangeProviderComponent : Component (F p) where
  circuit := rangeProvider
  generation := .demand {
    channel := counts
    trigger := .pull
    input c := pure { c, mult := .multiplicity }
    padding := { c := 1, mult := 0 }
  }

/-- One row per pushed square that nothing has pulled, as in `CountedSquares`, but pulling its
count from `counts` instead of constraining it. -/
abbrev stagedConsumerComponent : Component (F p) where
  circuit := stagedConsumer
  generation := .demand {
    channel := squares
    trigger := .push
    input | (x, y) => pure { x, y, count := .witness 2 }
  }

/-- The claim the module docstring makes, machine-checked: the hierarchy of `OrderedChannel.lean`
cannot take this consumer, which both pulls from `squares` and owes requirements on it. -/
example : ¬ OrderedChannelRefl (squares.counted countBound : RawChannel (F p))
    (stagedConsumerComponent (p := p)) := by
  simp [circuit_norm, stagedConsumer]

/-- The three chips and the two channels they share. Assembled directly: the staged argument is
stated for a whole ensemble, so there is no `SoundEnsemble` to build up. -/
def ensemble : Ensemble (F p) unit where
  tables := [rangeProviderComponent, providerComponent, stagedConsumerComponent]
  unique_names := by
    simp [rangeProviderComponent, providerComponent, stagedConsumerComponent, rangeProvider,
      provider, stagedConsumer]
  channels := [squares.counted countBound, counts.toRaw]
  unique_channel_names := by simp [circuit_norm, squares, counts]
  tables_channels := by
    intro table h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [circuit_norm, rangeProvider, provider, stagedConsumer]
  verifier_channels := by simp [circuit_norm]

/-- `counts` finished before `squares`: the consumer's requirement on the second uses its
guarantee on the first. -/
def finished : List (RawChannel (F p)) := [squares.counted countBound, counts.toRaw]

/-- The heart of the example: the consumer owes `count = 0 ∨ CountUpTo countBound count` on its
counted pull, and pays for it with the guarantee it got from `counts`, not with a constraint. -/
theorem consumer_requirementsAfter {earlier : List (RawChannel (F p))}
    (h_earlier : counts.toRaw ∈ earlier) :
    (stagedConsumerComponent (p := p)).RequirementsAfter (squares.counted countBound) earlier := by
  rintro table h_comp - constraints guarantees row hrow
  have g := guarantees _ h_earlier row hrow
  cases table
  simp only at h_comp
  subst h_comp
  simp only [Component.channelGuarantees_iff, Component.channelRequirements_iff] at g ⊢
  simp [circuit_norm, Component.rowOperations, stagedConsumerComponent, stagedConsumer,
    counts, squares] at g ⊢
  exact .inr g.1

/-- Every channel a table has guarantees on is finished. -/
theorem guarantees_subset_finished : ∀ component ∈ (ensemble (p := p)).tables,
    component.circuit.channelsWithGuarantees ⊆ finished := by
  intro component h
  simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;>
    simp [circuit_norm, finished, rangeProvider, provider, stagedConsumer, counts, squares]

/-- Each component's requirements on `squares` follow from its guarantees on `counts`, and its
requirements on `counts` hold unconditionally. -/
theorem stagedRequirements :
    ∀ component ∈ (ensemble (p := p)).tables, component.StagedRequirements finished := by
  intro component h
  simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  -- the two providers pull nothing, so they receive no guarantee and owe unconditionally
  · exact Component.stagedRequirements_of_forall fun _ _ _ =>
      Component.requirementsAfter_of_guarantees_subset (by simp [circuit_norm, rangeProvider])
  · exact Component.stagedRequirements_of_forall fun _ _ _ =>
      Component.requirementsAfter_of_guarantees_subset (by simp [circuit_norm, provider])
  -- the consumer: `squares` after `counts`, and nothing owed on `counts` itself
  · refine ⟨consumer_requirementsAfter (by simp), ?_, trivial⟩
    apply Component.requirementsAfter_of_not_mem
    simp only [circuit_norm, stagedConsumer, List.mem_cons, List.not_mem_nil, or_false]
    intro h
    have := congrArg RawChannel.name h
    simp [counts, squares, Channel.toRaw, Channel.counted] at this

/-- Every finished channel is consistent under `Balance.logUpUpTo countBound`. -/
theorem finished_consistent :
    ∀ c ∈ (finished : List (RawChannel (F p))),
      c.ConsistentUpTo (Balance.logUpUpTo (F := F p) countBound).pullBound := by
  intro c hc
  simp only [finished, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> infer_instance

/-- Every table of the ensemble is sound, from the finishing order `counts`, then `squares`. The
consumer constrains nothing about its count; what makes its pull legal is a guarantee it was
handed on another channel, and the order is what says that guarantee was already earned. -/
theorem tableSoundness :
    (ensemble (p := p)).TableSoundness (Balance.logUpUpTo countBound) :=
  Ensemble.tableSoundness_of_stagedRequirements finished (List.Subset.refl _)
    guarantees_subset_finished
    (by simp [ensemble, circuit_norm, Verifier.Program.empty])
    finished_consistent stagedRequirements
    (Ensemble.verifierStagedRequirementsOn_of_verifier_empty rfl _)

end StagedSquares
