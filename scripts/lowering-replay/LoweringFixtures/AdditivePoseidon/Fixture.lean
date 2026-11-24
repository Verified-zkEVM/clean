import LoweringFixtures.Common
import LoweringFixtures.AdditivePoseidon.Constants
import Midnight.Poseidon.Configure

/-! `Poseidon.configured`, the Poseidon-only architecture's `ZkStdLib::configure` whose
partial-round gate `additiveGate` builds. Both sides keying `MidnightVK` checks Lean's pinned CS
against Rust's own configure, query registration order included. The stream chains a full round
into two partial-round batches. -/
namespace LoweringFixtures.AdditivePoseidon
open Halo2 Midnight Midnight.Keygen Midnight.Poseidon

def source : CS := Poseidon.configured

def empty : GateSpec := ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def full : GateSpec := (source.gates.find? (·.name == "full_round_gate")).getD empty
def partialRound : GateSpec := source.trashcans[0]?.getD empty

def advices (columns : List Nat) (row : Nat) : RegionOperations F :=
  columns.map fun c => .assignAdvice ⟨c⟩ row witness

def constants (batch row : Nat) : RegionOperations F :=
  (List.range (width + circuitSkips)).map fun i =>
    .assignFixed ⟨i⟩ row ((partialRoundConstants[batch]?.getD #[])[i]?.getD 0)

def fixture : Export.Replay.Fixture where
  source := source
  k := 7
  architecture := Poseidon.architecture
  ops := [
    .region "full round" (advices (List.range (2 * width)) 0 ++
      [.assignFixed ⟨0⟩ 0 ((roundConstants[0]!)[0]!), .assignFixed ⟨1⟩ 0 ((roundConstants[0]!)[1]!),
       .assignFixed ⟨2⟩ 0 ((roundConstants[0]!)[2]!), .enableGate (cleanGate full) 0] ++
      advices (List.range width) 1),
    .region "partial rounds" (advices (List.range (width + circuitSkips)) 0 ++ constants 0 0 ++
      [.enableGate (cleanGate partialRound) 0] ++ advices (List.range (width + circuitSkips)) 1 ++
      constants 1 1 ++ [.enableGate (cleanGate partialRound) 1] ++ advices (List.range width) 2 ++
      [.constrainEqual (cell 0 1 .advice 0) (cell 1 0 .advice 0),
       .constrainEqual (cell 0 1 .advice 2) (cell 1 0 .advice 2)]),
    .constrainInstance (cell 1 2 .advice 0) ⟨1⟩ 0]

-- The additive gate leaves an empty gate entry and one trash argument of eight constraints.
#guard (source.gates.map (·.constraints.size)).toList.getLast? == some 0 &&
  source.trashcans.map (·.constraints.size) == #[8] && partialRound.rows == false

end LoweringFixtures.AdditivePoseidon
