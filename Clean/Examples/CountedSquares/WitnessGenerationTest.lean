module

public import Clean.Examples.CountedSquares.Ensemble
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.CountedSquares.Ensemble
public meta import Clean.Utils.Primes

@[expose] public section

namespace CountedSquares.WitnessGenerationTest

open Air.Flat Air.Flat.WitnessGeneration

/-- Small enough to run in, and large enough for the bound: the runs below make `6` and `8`
interactions on the channel, and `Balance.logUpUpTo 2` asks for `8 * 2 < p1009`. -/
abbrev p : ℕ := p1009

/-- The heights of the generated tables, and whether the witness satisfies the constraints, the
balance check and its interaction bound. -/
def result : Except String (List ℕ × Bool × Bool × Bool) :=
  match generate (soundEnsemble (p := p)).ensemble 100 () () with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.heights, constraintsHold witness, channelsBalanced witness,
        (soundEnsemble (p := p)).ensemble.interactionsFit (Balance.logUpUpTo countBound)
          witness.heights)

/-- The four provider rows seed the channel with one push each, and two consumer rows answer them
at multiplicity `2`. `heights` lists the tables in the ensemble's order, which `addTable` builds by
prepending, so the consumer added last comes first. -/
example : result = .ok ([2, 4], true, true, true) := by native_decide

/-! ## The padding row

`result` never pads, because its consumer table has two rows. The scenarios below exercise
`ComponentState.pad` and the rebalancing that follows it, from a balanced state whose consumer
holds three rows.
-/

/-- Three consumer rows, each pulling the square twice, and four provider rows emitting six pushes
between them: the circuit's `+ 1` on the multiplicities `[2, 0, 0, 0]`. Six pulls against six
pushes balance, and `ComponentState.targetHeight` asks a three-row demand table for four. -/
def unpadded : Array (ComponentState (F p)) := Id.run do
  let data := ProverData.empty (F p)
  let hint := ProverHint.empty (F p)
  let mut consumer := ComponentState.initial (consumerComponent (p := p)) none
  for _ in List.range 3 do
    consumer := consumer.pushRow (completeRow consumer #[2, 4, 2] data hint)
  let mut provider := ComponentState.initial (providerComponent (p := p)) (some 2)
  for i in List.range 4 do
    provider := provider.pushRow
      (completeRow provider #[2, 4, if i = 0 then 2 else 0] data hint)
  return #[consumer, provider]

/-- The tail of `generateValid`, so that these states meet the same `constraintsHold` and
`channelsBalanced` as `result` rather than a restatement of them. -/
def witnessOf (states : List (ComponentState (F p))) :
    Except GenerationError (EnsembleWitness (soundEnsemble (p := p)).ensemble) := do
  let assembled ← assembleTables (soundEnsemble (p := p)).ensemble.tables states
  have hunique : (assembled.tables.map fun table => table.component.circuit.name).Nodup := by
    simpa [← assembled.map_component, Function.comp_def]
      using (soundEnsemble (p := p)).ensemble.unique_names
  let publicInput : unit (F p) := ()
  return {
    tables := withDerivedData assembled.tables hunique (toElements publicInput).toArray
    publicInput
    same_length := by simp [withDerivedData, assembled.same_length]
    same_circuits := by simp [withDerivedData, assembled.same_circuits]
    same_data := withDerivedData_data assembled.tables hunique _
  }

/-- The heights and the three checks of `result`, and the multiplicity of the provider row that
answers the message: `providerComponent` maps every message to row `0` with `rowOf _ := 0`, so
that cell is where an extra pull has to show up. -/
def resultOf (states : Array (ComponentState (F p))) :
    Except String (List ℕ × Bool × Bool × Bool × Option (F p)) :=
  let answering : Option (F p) :=
    (states.toList[1]?).bind fun provider =>
      (provider.rows.toList[0]?).bind (·.values.toList[2]?)
  match witnessOf states.toList with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.heights, constraintsHold witness, channelsBalanced witness,
        (soundEnsemble (p := p)).ensemble.interactionsFit (Balance.logUpUpTo countBound)
          witness.heights,
        answering)

/-- Before padding: three consumer rows, balanced against the provider's six pushes. -/
example : resultOf unpadded = .ok ([3, 4], true, true, true, some 2) := by native_decide

def padded : Except String (List ℕ × Bool × Bool × Bool × Option (F p)) :=
  match padAndBalance (ProverData.empty (F p)) (ProverHint.empty (F p)) 100 100 unpadded with
  | .error error => .error (toString error)
  | .ok states => resultOf states

/-- After padding: the consumer reaches four rows, and the padding row's pull is answered rather
than left dangling, so the constraints, the balance and the interaction bound all still hold. The
provider's multiplicity rises from `2` to `3`, which is the extra push that covers it. -/
example : padded = .ok ([4, 4], true, true, true, some 3) := by native_decide

end CountedSquares.WitnessGenerationTest
