import Clean.Ironwood.Action.SelectorPacking

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

theorem actionConstraintSystem_numAdviceColumns_eq :
    (TopLevelCompilation.constraintSystem actionFormalCircuit).numAdviceColumns = 10 := by
  simpa only [actionFormalCircuit, TopLevelCompilation.constraintSystem,
    Circuit.circuit] using
      Circuit.configure_finalCounts_numAdviceColumns
        Specs.Sinsemilla.orchardGenerators

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

theorem actionConstraintSystem_numInstanceColumns_eq :
    (TopLevelCompilation.constraintSystem actionFormalCircuit).numInstanceColumns = 1 := by
  simpa only [actionFormalCircuit, TopLevelCompilation.constraintSystem,
    Circuit.circuit] using
      Circuit.configure_finalCounts_numInstanceColumns
        Specs.Sinsemilla.orchardGenerators

theorem actionConstraintSystem_chunkLen_eq :
    (TopLevelCompilation.constraintSystem actionFormalCircuit).chunkLen = 7 := by
  rw [ConstraintSystem.chunkLen,
    TopLevelCompilation.constraintSystem_csDegree,
    actionConstraintDegree_eq]

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
  unfold TopLevelCompilation.selectorMap
  rw [deriveSelCompressMap_newFixedCols_eq_selectorColumnCountWith _ _ _
    (by
      intro activation hactivation
      rw [actionDomainExponent_eq]
      exact actionSelectorActivation_row_lt_domain activation hactivation)]
  rw [actionNumSelectors_eq, actionSelectorMaxDegrees_eq,
    TopLevelCompilation.constraintSystem_csDegree, actionConstraintDegree_eq,
    actionSelectorActivations_eq_reduced, actionSelectorColumnCount_eq]

/-- Every field of the canonical compiler shape agrees with the published Action
literals. -/
theorem actionShape_eq_compiled :
    actionShape =
      TopLevelCompilation.circuitShape actionFormalCircuit PublicInputs.layout := by
  apply CircuitShape.ext
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionDomainExponent_eq.symm
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionConstraintSystem_numAdviceColumns_eq.symm
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
      TopLevelCompilation.constraintSystem_csDegree,
      actionConstraintDegree_eq]
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionConstraintSystem_numInstanceColumns_eq.symm
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionInstanceQueryCount_eq.symm
  · simpa only [actionShape, TopLevelCompilation.circuitShape] using
      actionAdviceQueryCount_eq.symm
  · simp only [actionShape, TopLevelCompilation.circuitShape]
    rw [TopLevelCompilation.fixedQueryCount_eq actionFormalCircuit
      PublicInputs.layout actionQueryRequirements]
    rw [show (TopLevelCompilation.constraintSystem
        actionFormalCircuit).fixedQueries.length = 14 by
      simpa only [actionFormalCircuit, TopLevelCompilation.constraintSystem,
        Circuit.circuit] using
          Circuit.configure_fixedQueries_length
            Specs.Sinsemilla.orchardGenerators]
    rw [actionSelectorMap_newFixedCols_eq]

end Zcash.Circuits.Action
