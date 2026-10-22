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
