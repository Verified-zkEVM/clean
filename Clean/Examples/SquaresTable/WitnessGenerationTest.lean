module

public import Clean.Examples.SquaresTable.Ensemble
public import Clean.Backends.Program
public import Clean.Utils.Primes

-- `#guard` runs compiled code from these modules.
public meta import Clean.Examples.SquaresTable.Ensemble
public meta import Clean.Backends.Program
public meta import Clean.Utils.Primes

@[expose] public section

namespace SquaresTable.WitnessGenerationTest

open Air.Flat Air.Flat.WitnessGeneration Backends

abbrev F := _root_.F pBabybear

def result (publicInput : fieldPair F) : Except String (List (List ℕ) × Bool × Bool) :=
  match generate 16 publicInput with
  | .error error => .error (toString error)
  | .ok witness =>
      .ok (witness.tables.flatMap fun table => table.table.map fun row => row.toList.map (·.val),
        constraintsHold witness, channelsBalanced witness)

/-- Row `i` of the generated table, with its window cells: the next row's input, and the
selectors. -/
def expectedRow (i : ℕ) : List ℕ :=
  let next := (i + 1) % 16
  [i, i * i, if i = 15 then 1 else 0, next, next * next, if next = 15 then 1 else 0,
    if i = 0 then 1 else 0, if i = 15 then 1 else 0, if i = 15 then 0 else 1]

-- Sixteen rows of squares, whose last row answers the verifier's pull.
#guard result (15, 225) = .ok ((List.range 16).map expectedRow, true, true)

-- No row carries a wrong square, so the verifier's pull stays unanswered.
#guard result (15, 224) = .error "unhandled channel imbalance on: squares"

def program : Except LoweringError (ComponentProgram F) := do
  let program ← lower (ensemble (p := pBabybear) 16) 1000
  match program.components with
  | [component] => return component
  | _ => throw (.validation (.preallocatedHeight "squares" 0))

/-- Whether the lowered constraints hold on a row whose window cells are filled: each body, times
the selector of its gate. -/
def checkRow (row : List ℕ) : Bool :=
  match program with
  | .error _ => false
  | .ok component =>
      let environment := Environment.fromArray (row.map (FiniteField.fromNat ·)).toArray
        (fun _ _ => #[])
      let width := component.window.getD 0
      component.constraints.all fun constraint =>
        let gate := (constraint.gate.selectorCell width).elim 1 environment.get
        gate * constraint.body.eval environment == 0

-- The constraints are lowered with their gates: the boundary constraints and the transitions to
-- the next row.
#guard (program.toOption.map fun component => component.constraints.map (·.gate)) =
  some [.firstRow, .firstRow, .transition, .transition, .lastRow, .transition]

-- Every row satisfies the lowered constraints, and breaking a transition to the next row, a
-- boundary row, or a selector violates them.
#guard (List.range 16).all fun i => checkRow (expectedRow i)
#guard !checkRow ((expectedRow 3).set 4 17)
#guard !checkRow ((expectedRow 0).set 1 1)
#guard !checkRow ((expectedRow 15).set 7 0 |>.set 8 1)

-- A selector is a factor of the whole constraint, or the constraint can't be gated.
#guard (gateConstraint (some 1) (var ⟨4⟩ * (var ⟨1⟩ - var ⟨0⟩) : Expression F)).map (·.gate) =
  some .transition
#guard (gateConstraint (some 1) (var ⟨2⟩ + var ⟨0⟩ : Expression F)).isNone
#guard (gateConstraint (some 1) (var ⟨2⟩ * var ⟨3⟩ : Expression F)).isNone

end SquaresTable.WitnessGenerationTest
