module

public import Clean.Air.CountedChannel
public import Clean.Air.OrderedChannel
public import Clean.Air.WitnessGeneration

@[expose] public section

/-!
# A fact pulled with multiplicity

A row that needs the same fact twice can pull it twice, or pull it once with multiplicity `2`. The
second costs one interaction instead of two, and is what `Channel.counted` is for.

The fact here is `y = x * x`. The squaring chip enforces it with a constraint and pushes the pair;
a consumer that needs the same square once or twice pulls it once with that multiplicity.
`squares.counted 2` hands its guarantee to a pull of multiplicity `1` or `2`, and asks such a pull
to say which. That obligation is what the consumer discharges by constraining its count, and it is
what makes the channel sound: `Channel.counted_not_consistent` shows that a row free to claim any
multiplicity would break it.

The ensemble also generates. Four provider rows exist before any demand, and a multiplicity cell
starts at `0`, so the `+ 1` of the provider's emit turns each of them into one push. Those four
pushes are the demand the consumer answers, with two rows pulling at multiplicity `2`. The `+ 1` is
there to seed the run and nothing else: a VM seeds its channels from the verifier instead, as in
`Clean/Examples/FemtoCairo/FlatAir.lean`. `Clean/Examples/CountedSquaresWitnessGenerationTest.lean`
runs it and pins the result.

A row's multiplicity is counted by `Tally.signedCount`, which reads it as a natural number, so a
counted pull is tallied as the number it claims; that part needs no change for counted channels.

Constraining the count arithmetically only scales for a small bound. A circuit counting to `510`
would range-check its multiplicity on another channel instead, which needs the finishing order of
`Ensemble.tableSoundness_of_stagedOn` rather than the single finished channel here.
-/

namespace CountedSquares

open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- Pulls may count up to `2`. -/
abbrev N : ℕ := 2

/-- Pairs `(x, y)` with `y = x * x`. -/
def squares : Channel (F p) (ProvablePair field field) where
  name := "squares"
  Guarantees | (x, y), _ => y = x * x

/-- A count of `1` or `2` is a count up to `2`: the step from a field constraint to the channel's
`CountUpTo`, and the only arithmetic the example needs. -/
lemma countUpTo_of_one_or_two {c : F p} (h : (c - 1) * (c - 2) = 0) : CountUpTo N c := by
  rcases mul_eq_zero.mp h with h | h <;> rw [sub_eq_zero] at h
  · exact ⟨1, le_rfl, by norm_num, by simp [h]⟩
  · exact ⟨2, by norm_num, le_rfl, by simp [h]⟩

structure ProviderInput (F : Type) where
  x : F
  y : F
  /-- how many pulls this row answers -/
  mult : F
deriving ProvableStruct

/-- The squaring chip: constrains `y = x * x` and pushes the pair, once on top of every pull it
answers. It owes the guarantee on every active push, and its own constraint is what pays for it, so
the chip assumes nothing.

The `+ 1` is the seed of generation, where a multiplicity cell starts at `0`. It is field
arithmetic and not a count, so it promises nothing about a row in general: a row whose `mult` is
`-1` pushes nothing. Soundness is indifferent to that, since pushing is what owes the guarantee. -/
def provider : GeneralFormalCircuit (F p) ProviderInput unit where
  name := "squares-provider"
  main input := do
    input.y === input.x * input.x
    squares.emitUpTo N (input.mult + 1) (input.x, input.y)

  channelsWithRequirements := [squares.counted N]
  Spec _ _ _ := True
  ProverAssumptions input _ _ := input.y = input.x * input.x

  soundness := by
    circuit_proof_start [squares]
    simp_all
  completeness := by
    circuit_proof_start [squares]
    simp_all

structure ConsumerInput (F : Type) where
  x : F
  y : F
  /-- how many times this row needs the fact: `1` or `2` -/
  count : F
deriving ProvableStruct

/-- A row that needs `y = x * x` once or twice, and pulls it once with that multiplicity.

The constraint on `count` is not bookkeeping: it is what discharges the pull's requirement
`count = 0 ∨ CountUpTo 2 count`. -/
def consumer : GeneralFormalCircuit (F p) ConsumerInput unit where
  name := "squares-consumer"
  main input := do
    assertZero ((input.count - 1) * (input.count - 2))
    squares.pullUpTo N input.count (input.x, input.y)

  Spec input _ _ := input.y = input.x * input.x
  ProverAssumptions input _ _ :=
    (input.count = 1 ∨ input.count = 2) ∧ input.y = input.x * input.x

  requirementsChannelsLawful := by
    simp only [circuit_norm, seval]
    intro input env h
    exact .inr (countUpTo_of_one_or_two h)

  soundness := by
    circuit_proof_start [squares]
    obtain ⟨h_count, h_guarantee⟩ := h_holds
    have h_in := countUpTo_of_one_or_two h_count
    exact ⟨h_guarantee h_in, .inr h_in⟩
  completeness := by
    circuit_proof_start [squares]
    obtain ⟨h_count, h_square⟩ := h_assumptions
    refine ⟨?_, fun _ => h_square⟩
    rcases h_count with h | h <;> simp [h]

/-- Four provider rows, all about the square `4 = 2 * 2`, which exist before there is any demand:
that is what lets a run start. The multiplicity counts the pulls a row answers, and the circuit's
`+ 1` turns the initial `0` of each row into one push.

`x` and `y` are witness cells rather than fixed columns on purpose: a fixed column is a value the
verifier knows, and the verifier knowing `y` would make `y = x * x` true of the table without the
push carrying it. -/
abbrev providerComponent : Component (F p) where
  circuit := provider
  generation := .preallocated {
    trigger := .pull
    channel := squares
    height := 4
    input _ := pure { x := .witness 2, y := .witness 4, mult := .multiplicity }
    rowOf _ := 0
  }

/-- One consumer row per pushed square that nothing has pulled, each needing it twice. Two rows
answer the provider's four pushes. Their `x` and `y` come from the message, so what makes
`y = x * x` true of a consumer row is the channel and the provider's constraint, nothing local. -/
abbrev consumerComponent : Component (F p) where
  circuit := consumer
  generation := .demand {
    channel := squares
    trigger := .push
    input | (x, y) => pure { x, y, count := .witness 2 }
  }

/-- The ensemble: the counted channel, the chip that serves it, the channel finished, and the chip
that reads it. `markFinished` is where the counted channel has to be `ConsistentUpTo` the balance
check's `pullBound`, which is why `Balance.logUpUpTo` must be reducible. -/
def soundEnsemble : SoundEnsemble (F p) unit (Balance.logUpUpTo N) :=
  SoundEnsemble.empty (F p) unit (Balance.logUpUpTo N)
  |>.addChannel (squares.counted N)
  |>.addTable providerComponent
      (by simp [circuit_norm, provider])
      (by simp [circuit_norm, provider])
      (by simp [circuit_norm, provider])
  |>.markFinished (squares.counted N)
  |>.addTable consumerComponent
      (by simp [circuit_norm, consumer])
      (by simp [circuit_norm, consumer])
      (by simp [circuit_norm, consumer, provider])

/-- The point of the example: every table of the ensemble is sound under `Balance.logUpUpTo 2`. For
the consumer that reads `y = x * x` out of a pull of multiplicity `2`, this is what says the fact it
read was really pushed by the squaring chip.

The balance check's `fits` is where the bound of `LogUpBalanced.matchedUpTo` is paid: a witness only
satisfies `Ensemble.Statement` when the interaction count times `2` stays below the characteristic.
-/
theorem tableSoundness :
    (soundEnsemble (p := p)).ensemble.TableSoundness (Balance.logUpUpTo N) :=
  Ensemble.tableSoundness_of_soundChannels
    ⟨_, (soundEnsemble (p := p)).finished_subset, (soundEnsemble (p := p)).soundChannels⟩

end CountedSquares
