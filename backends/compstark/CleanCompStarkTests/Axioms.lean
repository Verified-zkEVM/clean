module

public import CleanCompStark

/-! # The headline theorems use only the standard axioms -/

/--
info: 'CleanCompStark.table_of_satisfied' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.table_of_satisfied

/--
info: 'CleanCompStark.statement_of_satisfied' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.statement_of_satisfied

/--
info: 'CleanCompStark.knowledgeSoundness_ro_of_tableSound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.knowledgeSoundness_ro_of_tableSound

/--
info: 'CleanCompStark.batchKnowledgeSoundness_ro_of_witnessSound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.batchKnowledgeSoundness_ro_of_witnessSound

/--
info: 'CleanCompStark.batchKnowledgeSoundness_of_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.batchKnowledgeSoundness_of_soundness

/--
info: 'CleanCompStark.KeccakAir.knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.KeccakAir.knowledgeSoundness

/--
info: 'CleanCompStark.KeccakAir.knowledgeSoundness_ro' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.KeccakAir.knowledgeSoundness_ro

/--
info: 'CleanCompStark.KeccakAir.bridgeable_component' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.KeccakAir.bridgeable_component

/--
info: 'CleanCompStark.KeccakShowcase.keccak_soundness_ro' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.KeccakShowcase.keccak_soundness_ro

/--
info: 'CleanCompStark.KeccakShowcase.keccak_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.KeccakShowcase.keccak_soundness

/--
info: 'CleanCompStark.KeccakShowcase.keccak_soundness_ro_example' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CleanCompStark.KeccakShowcase.keccak_soundness_ro_example
