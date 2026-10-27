module

public import Clean.Examples.BinaryFibonacci.Ensemble

-- `native_decide` runs compiled code from this module.
public meta import Clean.Examples.BinaryFibonacci.Ensemble

@[expose] public section

namespace BinaryFibonacci.WitnessGenerationTest

open Air.Flat.WitnessGeneration

def steps : ℕ := 100

def final : State BF64 :=
  let (x, y) := fibonacci steps
  { counter := g ^ steps, x, y }

def result : Except String (List ℕ × Bool × Bool) :=
  match generate final 1000 with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.tables.map (·.length), constraintsHold witness,
        balanceHolds .multiset 2 witness)

/-- The verifier's push creates 100 steps, padded to 128 rows, whose interactions pass the multiset
balance check. -/
example : result = .ok ([128], true, true) := by native_decide

end BinaryFibonacci.WitnessGenerationTest
