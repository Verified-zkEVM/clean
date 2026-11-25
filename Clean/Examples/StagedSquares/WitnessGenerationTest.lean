module

public import Clean.Examples.StagedSquares.Ensemble
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.StagedSquares.Ensemble
public meta import Clean.Utils.Primes

@[expose] public section

namespace StagedSquares.WitnessGenerationTest

open Air.Flat Air.Flat.WitnessGeneration CountedSquares

/-- Small enough to run in, and large enough for the bound: the run below makes `8` interactions on
`squares`, and `Balance.logUpUpTo 2` asks for `8 * 2 < p1009`. -/
abbrev p : ℕ := p1009

/-- The heights of the generated tables, and whether the witness satisfies the constraints, the
balance check and its interaction bound. -/
def result : Except String (List ℕ × Bool × Bool × Bool) :=
  match generate (ensemble (p := p)) 100 () () with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.heights, constraintsHold witness, channelsBalanced witness,
        (ensemble (p := p)).interactionsFit (Balance.logUpUpTo countBound) witness.heights)

/-- Four provider rows seed `squares` with one push each, two consumer rows answer them at
multiplicity `2`, and each consumer row pulls its count once, so one range row answers both at
multiplicity `2`. `heights` lists the tables in the ensemble's order.

This is what the example claims and could not claim before: the count a consumer pulls is a
message on a channel like any other, so a run has to balance it like any other. An earlier version
of the range chip emitted `mult + 1`, as the preallocated squaring chip does, and generation
stopped with `unhandled channel imbalance on: counts`. -/
example : result = .ok ([1, 4, 2], true, true, true) := by native_decide

end StagedSquares.WitnessGenerationTest
