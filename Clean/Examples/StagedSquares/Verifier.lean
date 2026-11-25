module

public import Clean.Examples.StagedSquares.Ensemble

@[expose] public section

/-!
# A count bounded on another channel, with a verifier

The tables of `Clean/Examples/StagedSquares/Ensemble.lean`, with a verifier. The staged argument
treats the verifier's interactions on a stage like a table's: its pulls get their guarantees from
the stage, and its pushes owe requirements that may use its guarantees on earlier stages.

The first verifier pulls its public input from `counts`, so its spec, that the input counts up to
`countBound`, is the guarantee of that pull. The second also pushes the input to `seenCounts`,
which a table reads; the table's spec rests on that push, whose requirement the verifier pays with
its guarantee on the earlier `counts` stage.
-/

namespace StagedSquares.Verifier

open Air.Flat CountedSquares StagedSquares

variable {p : ℕ} [Fact p.Prime]

/-! ## A verifier that pulls -/

/-- Pulls the public input from `counts`. -/
def countVerifier : Verifier.Program (F p) field where
  main c := Verifier.pull counts c
  Spec c _ := CountUpTo countBound c
  soundness := by simp_all [circuit_norm, counts]

/-- `StagedSquares.ensemble` with `countVerifier`. -/
def ensembleWithVerifier : Ensemble (F p) field where
  tables := (ensemble (p := p)).tables
  unique_names := (ensemble (p := p)).unique_names
  channels := (ensemble (p := p)).channels
  unique_channel_names := (ensemble (p := p)).unique_channel_names
  tables_channels := (ensemble (p := p)).tables_channels
  verifier := countVerifier
  verifier_channels := by simp [ensemble, circuit_norm, countVerifier, counts]

/-- The tables and the verifier's spec are sound under `Balance.logUpUpTo countBound`. -/
theorem tableSoundness_withVerifier :
    (ensembleWithVerifier (p := p)).TableSoundness (Balance.logUpUpTo countBound) :=
  Ensemble.tableSoundness_of_stagedRequirements (ens := ensembleWithVerifier) finished
    (List.Subset.refl _) guarantees_subset_finished
    (by simp [ensembleWithVerifier, circuit_norm, countVerifier, finished, counts])
    finished_consistent stagedRequirements
    (Ensemble.verifierStagedRequirementsOn_of_not_mem
      (by simp [ensembleWithVerifier, circuit_norm, countVerifier, counts]))

/-! ## A verifier that pushes -/

/-- Values known to count up to `countBound`. -/
def seenCounts : Channel (F p) field where
  name := "seen-counts"
  Guarantees c _ := CountUpTo countBound c

lemma seenCounts_ne_squares :
    (seenCounts (p := p)).toRaw ≠ squares.counted countBound := fun h => by
  have := congrArg RawChannel.name h
  simp [seenCounts, squares, circuit_norm] at this

lemma seenCounts_ne_counts : (seenCounts (p := p)).toRaw ≠ counts.toRaw := fun h => by
  have := congrArg RawChannel.name h
  simp [seenCounts, counts, circuit_norm] at this

/-- Pulls the public input from `counts`, then pushes it to `seenCounts`. -/
def forwardingVerifier : Verifier.Program (F p) field where
  main c := do
    Verifier.pull counts c
    Verifier.push seenCounts c
  Spec c _ := CountUpTo countBound c
  soundness := by simp_all [circuit_norm, counts]

/-- Pulls a value from `seenCounts`, and so knows it counts up to `countBound`. -/
def seenReader : GeneralFormalCircuit (F p) field unit where
  name := "seen-reader"
  main c := seenCounts.pull c
  Spec c _ _ := CountUpTo countBound c
  ProverAssumptions c _ _ := CountUpTo countBound c
  soundness := by
    circuit_proof_start [seenCounts]
    simp_all
  completeness := by
    circuit_proof_start [seenCounts]
    exact h_assumptions

/-- One row per value pushed to `seenCounts` that nothing has pulled. -/
abbrev seenReaderComponent : Component (F p) where
  circuit := seenReader
  generation := .demand {
    trigger := .push
    channel := seenCounts
    input c := pure c
  }

/-- `StagedSquares.ensemble` with `seenReaderComponent`, `forwardingVerifier`, and the channel
between them. -/
def ensembleWithForwardingVerifier : Ensemble (F p) field where
  tables := seenReaderComponent :: (ensemble (p := p)).tables
  unique_names := by
    simp [ensemble, circuit_norm, seenReader, rangeProvider, provider, stagedConsumer]
  channels := seenCounts.toRaw :: (ensemble (p := p)).channels
  unique_channel_names := by simp [ensemble, circuit_norm, squares, counts, seenCounts]
  tables_channels := by
    intro table h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp [circuit_norm, seenReader]
    · exact List.Subset.trans ((ensemble (p := p)).tables_channels table h)
        (List.subset_cons_self _ _)
  verifier := forwardingVerifier
  verifier_channels := by simp [ensemble, circuit_norm, forwardingVerifier, counts, seenCounts]

/-- The stages: `seenCounts` after `squares` after `counts`, each a whole channel. -/
abbrev stages : List (Stage (F p)) :=
  Stage.ofChannel seenCounts.toRaw :: finished.map Stage.ofChannel

/-- Sound under `Balance.logUpUpTo countBound`. The reader's spec comes from the verifier's push to
`seenCounts`, which is paid for by the verifier's pull from `counts`, finished earlier. -/
theorem tableSoundness_withForwardingVerifier :
    (ensembleWithForwardingVerifier (p := p)).TableSoundness (Balance.logUpUpTo countBound) := by
  apply Ensemble.tableSoundness_of_stagedRequirementsOn (ens := ensembleWithForwardingVerifier)
    stages
  · simp [ensembleWithForwardingVerifier, ensemble, finished, circuit_norm]
  · intro table h c h_c _ _ _
    simp only [ensembleWithForwardingVerifier, List.mem_cons] at h
    rcases h with h | h
    · rw [h] at h_c
      simp [circuit_norm, seenReader] at h_c
      subst h_c
      exact ⟨Stage.ofChannel seenCounts.toRaw, List.mem_cons_self, rfl, rfl⟩
    · exact ⟨Stage.ofChannel c, List.mem_cons_of_mem _
        (List.mem_map_of_mem (guarantees_subset_finished _ h h_c)), rfl, rfl⟩
  · intro c h_c _ _ _ _
    simp [ensembleWithForwardingVerifier, circuit_norm, forwardingVerifier, counts] at h_c
    subst h_c
    exact ⟨Stage.ofChannel counts.toRaw, List.mem_cons_of_mem _
      (List.mem_map_of_mem (by simp [finished])), rfl, rfl⟩
  · simp only [stages, finished, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, circuit_norm]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro component h
    simp only [ensembleWithForwardingVerifier, List.mem_cons] at h
    rcases h with rfl | h
    · -- the reader owes nothing anywhere: its one pull has multiplicity `1`
      simp only [stages, finished, List.map_cons, List.map_nil, circuit_norm]
      refine ⟨?_, ?_, ?_⟩ <;> exact Component.requirementsAfterOn_of_not_mem _
        (by simp [circuit_norm, seenReader])
    refine ⟨Component.requirementsAfterOn_of_not_mem _ ?_,
      Component.stagedRequirementsOn_of_stagedRequirements (stagedRequirements component h)⟩
    simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · simp [circuit_norm, rangeProvider, seenCounts_ne_counts]
    · simp [circuit_norm, provider, seenCounts_ne_squares]
    · simp [circuit_norm, stagedConsumer, seenCounts_ne_squares]
  · refine ⟨?_, Ensemble.verifierStagedRequirementsOn_of_not_mem ?_⟩
    · intro data h_earlier i h_i _
      have h_counts := h_earlier (Stage.ofChannel counts.toRaw) (by simp [finished])
      simp [Ensemble.VerifierGuaranteesOn, ensembleWithForwardingVerifier, circuit_norm,
        forwardingVerifier, counts, seenCounts, Operations.interactionValuesWith_eq_map]
        at h_counts h_i ⊢
      subst h_i
      rw [AbstractInteraction.eval_guarantees, ChannelInteraction.toRaw_guarantees] at h_counts
      rw [AbstractInteraction.eval_requirements, ChannelInteraction.toRaw_requirements]
      simp_all [circuit_norm, ChannelInteraction.Guarantees, ChannelInteraction.Requirements,
        Stage.ofChannel]
    · simp [ensembleWithForwardingVerifier, circuit_norm, forwardingVerifier, finished,
        Ne.symm seenCounts_ne_squares, Ne.symm seenCounts_ne_counts]

end StagedSquares.Verifier
