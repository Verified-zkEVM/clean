module

public import Clean.Examples.OpcodeVm.Ensemble
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.OpcodeVm.Ensemble
public meta import Clean.Utils.Primes

@[expose] public section

namespace OpcodeVm.WitnessGenerationTest

open Air.Flat.WitnessGeneration

/-- The prover's private input: the memory records that the accesses of the run read. -/
def proverInput :
    (memory (p := pBabybear) exampleProgram exampleProgram_height).ProverInput (F pBabybear) :=
  (memory exampleProgram exampleProgram_height).proverInput (accesses exampleProgram 2)

def result (final : F pBabybear) : Except String (List ℕ × Bool × Bool) :=
  let ensemble :=
    (formalEnsemble exampleProgram exampleProgram_length exampleProgram_height).ensemble
  match generate ensemble 1000 { initial := 2, final } proverInput
    with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.tables.map (·.length), constraintsHold witness, channelsBalanced witness)

/--
Each state goes to the table of the opcode at its `pc`: five rows in the `add` table, padded to
eight, and three in each of the `mul`, `load` and `store` tables, padded to four. The memory table
has eight rows, the range table of times thirty-two, and the program table sixteen.
-/
example : result (run exampleProgram (2, 0)).1 = .ok ([8, 4, 4, 4, 8, 32, 16], true, true) := by
  native_decide

/-- A wrong final accumulator leaves the final state unanswered. -/
example :
    result ((run exampleProgram (2, 0)).1 + 1) =
      .error "unhandled channel imbalance on: state, state" := by
  native_decide

end OpcodeVm.WitnessGenerationTest
