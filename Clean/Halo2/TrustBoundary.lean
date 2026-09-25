import Clean.Halo2.WitnessSupport

/-!
# Trust boundary of the witness-read support layer

Each entry pins the axiom footprint of one declaration in `Clean/Circuit/WitnessReads.lean` or
`Clean/Halo2/WitnessSupport.lean`, so that a `sorry` or a `native_decide` entering the layer
fails the build instead of passing unnoticed. The read collectors are computed without any
axiom, and nothing uses more than `propext`, `Classical.choice`, and `Quot.sound`. A pin is
`#guard_msgs` on `#print axioms`, which fixes the exact list rather than a budget: a proof that
starts to use choice changes its entry, and the change is reviewed with it.
-/

-- Read collectors for the witness IR.

/-- info: 'Witgen.fieldWitnessReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.fieldWitnessReads

/-- info: 'Witgen.listWitnessReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.listWitnessReads

/-- info: 'Witgen.natWitnessReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.natWitnessReads

/-- info: 'Witgen.boolWitnessReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.boolWitnessReads

/-- info: 'Witgen.vectorWitnessReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.vectorWitnessReads

/-- info: 'Witgen.stepsWitnessReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.stepsWitnessReads

/-- info: 'Witgen.valueBuilderReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.valueBuilderReads

/-- info: 'Witgen.natBuilderReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.natBuilderReads

/-- info: 'Witgen.boolBuilderReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.boolBuilderReads

-- Agreement of two contexts on the collected reads.

/-- info: 'Witgen.WitnessContextAgreement' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.WitnessContextAgreement

/-- info: 'Witgen.WitnessContextAgreement.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.WitnessContextAgreement.mono

/-- info: 'Witgen.WitnessContextAgreement.left' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.WitnessContextAgreement.left

/-- info: 'Witgen.WitnessContextAgreement.right' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.WitnessContextAgreement.right

/-- info: 'Witgen.WitnessContextAgreement.withLocals' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.WitnessContextAgreement.withLocals

/-- info: 'Witgen.WitnessContextAgreement.withIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms Witgen.WitnessContextAgreement.withIndex

/-- info: 'Witgen.WitnessContextAgreement.list_member' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Witgen.WitnessContextAgreement.list_member

-- Evaluation depends only on the collected reads.

/-- info: 'Witgen.fieldWitnessReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.fieldWitnessReads_eval

/-- info: 'Witgen.natWitnessReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.natWitnessReads_eval

/-- info: 'Witgen.boolWitnessReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.boolWitnessReads_eval

/-- info: 'Witgen.listWitnessReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.listWitnessReads_eval

/-- info: 'Witgen.vectorWitnessReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.vectorWitnessReads_eval

/-- info: 'Witgen.stepsWitnessReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.stepsWitnessReads_eval

/-- info: 'Witgen.structuredWitnessReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.structuredWitnessReads_eval

/-- info: 'Witgen.valueBuilderReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.valueBuilderReads_eval

/-- info: 'Witgen.natBuilderReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.natBuilderReads_eval

/-- info: 'Witgen.boolBuilderReads_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.boolBuilderReads_eval

-- Agreement of two prover environments for a native function.

/-- info: 'Halo2.WitnessFunctionAgreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionAgreement

/-- info: 'Halo2.witnessFunctionAgreementCoe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionAgreementCoe

/-- info: 'Halo2.WitnessFunctionAgreement.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionAgreement.mono

/-- info: 'Halo2.WitnessFunctionAgreement.left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionAgreement.left

/-- info: 'Halo2.WitnessFunctionAgreement.right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionAgreement.right

-- Support of a native function, and its combinators.

/-- info: 'Halo2.WitnessFunctionSupport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionSupport

/-- info: 'Halo2.WitnessFunctionSupport.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionSupport.mono

/-- info: 'Halo2.WitnessFunctionSupport.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionSupport.map

/-- info: 'Halo2.WitnessFunctionSupport.pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.WitnessFunctionSupport.pair

/-- info: 'Halo2.exists_witnessFunctionSupport_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.exists_witnessFunctionSupport_of

-- The function of a single-output program.

/-- info: 'Halo2.programFunction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.programFunction

-- The support rules for Clean's own program shapes.

/-- info: 'Halo2.witnessFunctionSupport_readCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_readCell

/-- info: 'Halo2.witnessFunctionSupport_instanceGet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_instanceGet

/-- info: 'Halo2.witnessFunctionSupport_ofFExpr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_ofFExpr

/-- info: 'Halo2.witnessFunctionSupport_structured' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_structured

/-- info: 'Halo2.witnessFunctionSupport_scalarBuilder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_scalarBuilder

/-- info: 'Halo2.witnessFunctionSupport_valueBuilder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_valueBuilder

/-- info: 'Halo2.witnessFunctionSupport_natBuilder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_natBuilder

/-- info: 'Halo2.witnessFunctionSupport_boolBuilder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_boolBuilder

/-- info: 'Halo2.witnessFunctionSupport_nativeScalar' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_nativeScalar

/-- info: 'Halo2.witnessFunctionSupport_nativeBoolean' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_nativeBoolean

/-- info: 'Halo2.witnessFunctionSupport_nativeConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_nativeConstant

/-- info: 'Halo2.witnessFunctionSupport_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.witnessFunctionSupport_const

-- Supported parameters.

/-- info: 'Halo2.SupportedProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.SupportedProgram

/-- info: 'Halo2.SupportedFunction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.SupportedFunction

/-- info: 'Halo2.SupportedEnvironmentFunction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halo2.SupportedEnvironmentFunction
