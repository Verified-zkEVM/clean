module

public import Clean.Examples.CountedSquares

-- `native_decide` runs compiled code from this module.
public meta import Clean.Examples.CountedSquares

@[expose] public section

namespace CountedSquares.WitnessGenerationTest

open Air.Flat Air.Flat.WitnessGeneration

/-- A field small enough to run in, and large enough for the bound: the run makes `6` interactions
on the channel, and `Balance.logUpUpTo 2` asks for `6 * 2 < 101`. -/
abbrev p : ℕ := 101

instance : Fact (Nat.Prime p) := ⟨by decide⟩

/-- The heights of the generated tables, and whether the witness satisfies the constraints, the
balance check and its interaction bound. -/
def result : Except String (List ℕ × Bool × Bool × Bool) :=
  match generate (soundEnsemble (p := p)).ensemble 100 () () with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.heights, constraintsHold witness, channelsBalanced witness,
        (soundEnsemble (p := p)).ensemble.interactionsFit (Balance.logUpUpTo N) witness.heights)

/-- The four provider rows seed the channel with one push each, and two consumer rows answer them
at multiplicity `2`. `heights` lists the tables in the ensemble's order, which `addTable` builds by
prepending, so the consumer added last comes first. -/
example : result = .ok ([2, 4], true, true, true) := by native_decide

end CountedSquares.WitnessGenerationTest
