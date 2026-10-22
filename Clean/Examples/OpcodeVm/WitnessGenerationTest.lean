module

public import Clean.Examples.OpcodeVm.Ensemble
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.OpcodeVm.Ensemble
public meta import Clean.Utils.Primes

@[expose] public section

namespace OpcodeVm.WitnessGenerationTest

open Air.Flat.WitnessGeneration

def result (final : F pBabybear) : Except String (List ℕ × Bool × Bool) :=
  match generate (ensemble exampleProgram).ensemble 1000 (2, final) () with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.tables.map (·.length), constraintsHold witness, channelsBalanced witness)

/--
Each state goes to the table of the opcode at its `pc`: six rows in the `add` table, padded to
eight, and four in the `mul` table. The program table has sixteen rows.
-/
example : result (run exampleProgram 2) = .ok ([8, 4, 16], true, true) := by native_decide

/-- A wrong final accumulator leaves the final state unanswered. -/
example :
    result (run exampleProgram 2 + 1) = .error "unhandled channel imbalance on: state, state" := by
  native_decide

end OpcodeVm.WitnessGenerationTest
