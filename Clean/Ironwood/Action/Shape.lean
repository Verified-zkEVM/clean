import Clean.Ironwood.Action.Shape.SelectorPacking
import Clean.Ironwood.Action.TopLevel

/-!
# The fully reduced Orchard Action circuit shape

The public record below is the finite shape used by verifier types.  Its proof is
assembled from the reduced configure and synthesis summaries; it does not use a
captured verifying-key fixture.
-/

namespace Zcash.Circuits.Action

open Halo2

/-- The literal circuit-owned shape of one Orchard Action. -/
def actionShape : CircuitShape where
  k := 11
  numAdviceColumns := 10
  numLookups := 3
  numPermutationSets := 3
  numPermutationColumns := 15
  numQuotientPieces := 8
  numInstanceColumns := 1
  numInstanceQueries := 1
  numAdviceQueries := 25
  numFixedQueries := 29

theorem actionConstraintSystem_numLookups_eq :
    (TopLevelCompilation.constraintSystem actionFormalCircuit).lookups.length = 3 := by
  unfold actionFormalCircuit TopLevelCompilation.constraintSystem
  simp only [Circuit.circuit]
  configure_norm

theorem actionConstraintSystem_numPermutationColumns_eq :
    (TopLevelCompilation.constraintSystem
      actionFormalCircuit).permutationColumns.length = 15 := by
  simpa only [actionFormalCircuit, TopLevelCompilation.constraintSystem,
    Circuit.circuit] using
      Circuit.configure_permutationColumns_length
        Specs.Sinsemilla.orchardGenerators

theorem actionConstraintSystem_chunkLen_eq :
    (TopLevelCompilation.constraintSystem actionFormalCircuit).chunkLen = 7 := by
  rw [ConstraintSystem.chunkLen, TopLevelCompilation.constraintSystem_csDegree]
  have hDegree : TopLevelCompilation.constraintDegree actionFormalCircuit = 9 := by
    simpa only [← actionCircuit_formalCircuit_eq,
      TopLevelCircuit.constraintDegree] using actionCircuit_constraintDegree_eq
  rw [hDegree]

theorem actionInstanceQueryCount_eq :
    (PinnedConstraintSystem.derive
      (TopLevelCompilation.constraintSystem actionFormalCircuit)
      (TopLevelCompilation.selectorMap actionFormalCircuit
        PublicInputs.layout)).instanceQueryLayout.length = 1 := by
  unfold TopLevelCompilation.constraintSystem actionFormalCircuit
  simp only [Circuit.circuit, PinnedConstraintSystem.derive, projectCS]
  rw [queryWalkInit_inst_toList, List.length_map]
  configure_norm

theorem actionAdviceQueryCount_eq :
    (PinnedConstraintSystem.derive
      (TopLevelCompilation.constraintSystem actionFormalCircuit)
      (TopLevelCompilation.selectorMap actionFormalCircuit
        PublicInputs.layout)).adviceQueryLayout.length = 25 := by
  unfold TopLevelCompilation.constraintSystem actionFormalCircuit
  simp only [Circuit.circuit, PinnedConstraintSystem.derive, projectCS]
  rw [queryWalkInit_advice_toList, List.length_map]
  exact Circuit.configure_adviceQueries_length
    Specs.Sinsemilla.orchardGenerators

theorem actionSelectorMap_newFixedCols_eq :
    (TopLevelCompilation.selectorMap actionFormalCircuit
      PublicInputs.layout).newFixedCols = 15 := by
  unfold TopLevelCompilation.selectorMap TopLevelCompilation.selectorMapAt
  rw [deriveSelCompressMap_newFixedCols_eq_selectorColumnCountWith _ _ _
    (by
      intro activation hactivation
      rw [actionDomainExponent_eq]
      exact actionSelectorActivation_row_lt_domain activation hactivation)]
  have hSelectorCount :
      (TopLevelCompilation.constraintSystem actionFormalCircuit).numSelectors = 56 := by
    simpa only [← actionCircuit_formalCircuit_eq,
      TopLevelCircuit.selectorCount, TopLevelCircuit.constraintSystem] using
        actionCircuit_selectorCount_eq
  have hDegree : TopLevelCompilation.constraintDegree actionFormalCircuit = 9 := by
    simpa only [← actionCircuit_formalCircuit_eq,
      TopLevelCircuit.constraintDegree] using actionCircuit_constraintDegree_eq
  rw [hSelectorCount, actionSelectorMaxDegrees_eq,
    TopLevelCompilation.constraintSystem_csDegree, hDegree,
    actionSelectorActivations_eq_reduced, actionSelectorColumnCount_eq]

/-- Every field of the canonical compiler shape agrees with the published Action
literals. -/
theorem actionShape_eq_compiled :
    actionShape =
      TopLevelCompilation.circuitShape actionFormalCircuit PublicInputs.layout := by
  apply CircuitShape.ext
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionDomainExponent_eq.symm
  · simpa only [actionShape, TopLevelCompilation.circuitShape,
      ← actionCircuit_formalCircuit_eq, TopLevelCircuit.constraintSystem] using
        actionCircuit_numAdviceColumns_eq.symm
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionConstraintSystem_numLookups_eq.symm
  · simp only [TopLevelCompilation.circuitShape,
      actionShape,
      actionConstraintSystem_numPermutationColumns_eq,
      actionConstraintSystem_chunkLen_eq]
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionConstraintSystem_numPermutationColumns_eq.symm
  · simp only [TopLevelCompilation.circuitShape,
      actionShape,
      TopLevelCompilation.constraintSystem_csDegree]
    have hDegree : TopLevelCompilation.constraintDegree actionFormalCircuit = 9 := by
      simpa only [← actionCircuit_formalCircuit_eq,
        TopLevelCircuit.constraintDegree] using actionCircuit_constraintDegree_eq
    rw [hDegree]
  · simpa only [actionShape, TopLevelCompilation.circuitShape,
      ← actionCircuit_formalCircuit_eq, TopLevelCircuit.constraintSystem] using
        actionCircuit_numInstanceColumns_eq.symm
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionInstanceQueryCount_eq.symm
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionAdviceQueryCount_eq.symm
  · simp only [actionShape, TopLevelCompilation.circuitShape]
    rw [TopLevelCompilation.fixedQueryCount_eq actionFormalCircuit
      PublicInputs.layout (by
        simpa only [actionFormalCircuit] using actionQueryRequirements)]
    rw [show (TopLevelCompilation.constraintSystem
        actionFormalCircuit).fixedQueries.length = 14 by
      simpa only [actionFormalCircuit, TopLevelCompilation.constraintSystem,
        Circuit.circuit] using
          Circuit.configure_fixedQueries_length
            Specs.Sinsemilla.orchardGenerators]
    rw [actionSelectorMap_newFixedCols_eq]

/-- The deployed Action circuit opts into its fully reduced compiler shape. -/
instance : TopLevelShape actionCircuit where
  shape := actionShape
  shape_eq := by
    rw [Internal.actionCircuit_eq_impl]
    exact actionShape_eq_compiled

/-- The Action circuit publishes its fully reduced circuit shape. -/
@[simp] theorem actionCircuit_shape_eq :
    actionCircuit.shape = actionShape :=
  actionCircuit.shape_eq_published

/-- Action's closed configure run equality-enables fifteen distinct columns. -/
theorem actionCircuit_permutationColumnCount_eq :
    actionCircuit.permutationColumnCount = 15 := by
  rw [TopLevelCircuit.permutationColumnCount, actionCircuit_shape_eq]
  rfl

end Zcash.Circuits.Action
