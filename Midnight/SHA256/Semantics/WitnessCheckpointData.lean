import Midnight.SHA256.Semantics.WitnessCheckpointModel
import Midnight.SHA256.WitnessErasureCore
import Midnight.SHA256.Semantics.PreimageSource

/-! GENERATED proof indices from the actual WitnessCircuit, without native capture data.
All metadata must be justified by exact kernel-checked source-return theorems.
The Operations definitions contain the actual witness programs. -/
namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

def beginCursor (offset : Nat) : Cursor := ([],offset)

def inputAction (_offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  assignBytes Semantics.Preimage.privatePrograms
def inputOutput (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 0) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 1) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 2) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 3) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 4) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 5) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 6) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 7) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 8) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 9) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 10) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 11) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 12) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 13) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 14) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 15) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 16) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 17) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 18) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 19) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 20) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 21) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 22) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 23) 0 (⟨1⟩ : Column .advice)⟩] }
def inputAfter (offset : Nat) : Cursor :=
  ([] ++ (beginCursor offset).1, offset + 24)
def inputOperations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (inputAction offset) (beginCursor offset)

def initialAction (_offset : Nat) : Build (Compression) :=
  initialState
def initialOutput (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 24) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 25) 0 (⟨9⟩ : Column .fixed)⟩ }, limbs := { toList := [⟨Cell.of (offset + 26) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 27) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 28) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 29) 0 (⟨9⟩ : Column .fixed)⟩] } }, b := { plain := ⟨Cell.of (offset + 30) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 31) 0 (⟨9⟩ : Column .fixed)⟩ }, c := { plain := ⟨Cell.of (offset + 32) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 33) 0 (⟨9⟩ : Column .fixed)⟩ }, d := ⟨Cell.of (offset + 34) 0 (⟨9⟩ : Column .fixed)⟩, e := { combined := { plain := ⟨Cell.of (offset + 35) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 36) 0 (⟨9⟩ : Column .fixed)⟩ }, limbs := { toList := [⟨Cell.of (offset + 37) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 38) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 39) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 40) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 41) 0 (⟨9⟩ : Column .fixed)⟩] } }, f := { plain := ⟨Cell.of (offset + 42) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 43) 0 (⟨9⟩ : Column .fixed)⟩ }, g := { plain := ⟨Cell.of (offset + 44) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 45) 0 (⟨9⟩ : Column .fixed)⟩ }, h := ⟨Cell.of (offset + 46) 0 (⟨9⟩ : Column .fixed)⟩ }
def initialAfter (offset : Nat) : Cursor :=
  ([(1541459225, ⟨Cell.of (offset + 46) 0 (⟨9⟩ : Column .fixed)⟩), (96053358640579653, ⟨Cell.of (offset + 45) 0 (⟨9⟩ : Column .fixed)⟩), (528734635, ⟨Cell.of (offset + 44) 0 (⟨9⟩ : Column .fixed)⟩), (4703165459212550224, ⟨Cell.of (offset + 43) 0 (⟨9⟩ : Column .fixed)⟩), (2600822924, ⟨Cell.of (offset + 42) 0 (⟨9⟩ : Column .fixed)⟩), (1365, ⟨Cell.of (offset + 41) 0 (⟨9⟩ : Column .fixed)⟩), (65, ⟨Cell.of (offset + 40) 0 (⟨9⟩ : Column .fixed)⟩), (4, ⟨Cell.of (offset + 39) 0 (⟨9⟩ : Column .fixed)⟩), (4199684, ⟨Cell.of (offset + 38) 0 (⟨9⟩ : Column .fixed)⟩), (1088, ⟨Cell.of (offset + 37) 0 (⟨9⟩ : Column .fixed)⟩), (1225260934684218709, ⟨Cell.of (offset + 36) 0 (⟨9⟩ : Column .fixed)⟩), (1359893119, ⟨Cell.of (offset + 35) 0 (⟨9⟩ : Column .fixed)⟩), (2773480762, ⟨Cell.of (offset + 34) 0 (⟨9⟩ : Column .fixed)⟩), (382828320762696964, ⟨Cell.of (offset + 33) 0 (⟨9⟩ : Column .fixed)⟩), (1013904242, ⟨Cell.of (offset + 32) 0 (⟨9⟩ : Column .fixed)⟩), (4991417843583303697, ⟨Cell.of (offset + 31) 0 (⟨9⟩ : Column .fixed)⟩), (3144134277, ⟨Cell.of (offset + 30) 0 (⟨9⟩ : Column .fixed)⟩), (5, ⟨Cell.of (offset + 29) 0 (⟨9⟩ : Column .fixed)⟩), (82241, ⟨Cell.of (offset + 28) 0 (⟨9⟩ : Column .fixed)⟩), (4181, ⟨Cell.of (offset + 27) 0 (⟨9⟩ : Column .fixed)⟩), (83008, ⟨Cell.of (offset + 26) 0 (⟨9⟩ : Column .fixed)⟩), (1460292459758359573, ⟨Cell.of (offset + 25) 0 (⟨9⟩ : Column .fixed)⟩), (1779033703, ⟨Cell.of (offset + 24) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (inputAfter offset).1, offset + 47)
def initialOperations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (initialAction offset) (inputAfter offset)

def paddingAction (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  pad (inputOutput offset)
def paddingOutput (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 0) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 1) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 2) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 3) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 4) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 5) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 6) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 7) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 8) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 9) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 10) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 11) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 12) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 13) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 14) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 15) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 16) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 17) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 18) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 19) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 20) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 21) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 22) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 23) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 47) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 49) 0 (⟨9⟩ : Column .fixed)⟩] }
def paddingAfter (offset : Nat) : Cursor :=
  ([(192, ⟨Cell.of (offset + 49) 0 (⟨9⟩ : Column .fixed)⟩), (0, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩), (128, ⟨Cell.of (offset + 47) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (initialAfter offset).1, offset + 50)
def paddingOperations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (paddingAction offset) (initialAfter offset)

def packingAction (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  blockFromBytes (paddingOutput offset)
def packingOutput (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 50) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 51) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 52) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 53) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 54) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 55) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 56) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 48) 0 (⟨9⟩ : Column .fixed)⟩, ⟨Cell.of (offset + 49) 0 (⟨9⟩ : Column .fixed)⟩] }
def packingAfter (offset : Nat) : Cursor :=
  ([] ++ (paddingAfter offset).1, offset + 57)
def packingOperations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (packingAction offset) (paddingAfter offset)

def prepare0Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[0]!]
    return (#[]).push w
def prepare0Output (offset : Nat) : Array Word :=
  (#[]).push ({ combined := { plain := ⟨Cell.of (offset + 57) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 57) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 57) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 57) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 57) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 57) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 57) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 57) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 57) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 57) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare0After (offset : Nat) : Cursor :=
  ([] ++ (packingAfter offset).1, offset + 58)
def prepare0Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare0Action offset) (packingAfter offset)

def prepare1Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[1]!]
    return ((prepare0Output offset)).push w
def prepare1Output (offset : Nat) : Array Word :=
  ((prepare0Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 58) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 58) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 58) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 58) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 58) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 58) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 58) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 58) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 58) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 58) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare1After (offset : Nat) : Cursor :=
  ([] ++ (prepare0After offset).1, offset + 59)
def prepare1Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare1Action offset) (prepare0After offset)

def prepare2Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[2]!]
    return ((prepare1Output offset)).push w
def prepare2Output (offset : Nat) : Array Word :=
  ((prepare1Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 59) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 59) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 59) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 59) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 59) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 59) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 59) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 59) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 59) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 59) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare2After (offset : Nat) : Cursor :=
  ([] ++ (prepare1After offset).1, offset + 60)
def prepare2Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare2Action offset) (prepare1After offset)

def prepare3Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[3]!]
    return ((prepare2Output offset)).push w
def prepare3Output (offset : Nat) : Array Word :=
  ((prepare2Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 60) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 60) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 60) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 60) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 60) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 60) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 60) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 60) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 60) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 60) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare3After (offset : Nat) : Cursor :=
  ([] ++ (prepare2After offset).1, offset + 61)
def prepare3Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare3Action offset) (prepare2After offset)

def prepare4Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[4]!]
    return ((prepare3Output offset)).push w
def prepare4Output (offset : Nat) : Array Word :=
  ((prepare3Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 61) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 61) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 61) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 61) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 61) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 61) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 61) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 61) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 61) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 61) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare4After (offset : Nat) : Cursor :=
  ([] ++ (prepare3After offset).1, offset + 62)
def prepare4Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare4Action offset) (prepare3After offset)

def prepare5Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[5]!]
    return ((prepare4Output offset)).push w
def prepare5Output (offset : Nat) : Array Word :=
  ((prepare4Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 62) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 62) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 62) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 62) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 62) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 62) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 62) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 62) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 62) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 62) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare5After (offset : Nat) : Cursor :=
  ([] ++ (prepare4After offset).1, offset + 63)
def prepare5Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare5Action offset) (prepare4After offset)

def prepare6Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[6]!]
    return ((prepare5Output offset)).push w
def prepare6Output (offset : Nat) : Array Word :=
  ((prepare5Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 63) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 63) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 63) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 63) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 63) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 63) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 63) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 63) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 63) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 63) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare6After (offset : Nat) : Cursor :=
  ([] ++ (prepare5After offset).1, offset + 64)
def prepare6Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare6Action offset) (prepare5After offset)

def prepare7Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[7]!]
    return ((prepare6Output offset)).push w
def prepare7Output (offset : Nat) : Array Word :=
  ((prepare6Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 64) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 64) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 64) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 64) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 64) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 64) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 64) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 64) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 64) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 64) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare7After (offset : Nat) : Cursor :=
  ([] ++ (prepare6After offset).1, offset + 65)
def prepare7Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare7Action offset) (prepare6After offset)

def prepare8Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[8]!]
    return ((prepare7Output offset)).push w
def prepare8Output (offset : Nat) : Array Word :=
  ((prepare7Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 65) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 65) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 65) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 65) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 65) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 65) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 65) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 65) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 65) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 65) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare8After (offset : Nat) : Cursor :=
  ([] ++ (prepare7After offset).1, offset + 66)
def prepare8Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare8Action offset) (prepare7After offset)

def prepare9Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[9]!]
    return ((prepare8Output offset)).push w
def prepare9Output (offset : Nat) : Array Word :=
  ((prepare8Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 66) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 66) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 66) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 66) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 66) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 66) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 66) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 66) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 66) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 66) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare9After (offset : Nat) : Cursor :=
  ([] ++ (prepare8After offset).1, offset + 67)
def prepare9Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare9Action offset) (prepare8After offset)

def prepare10Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[10]!]
    return ((prepare9Output offset)).push w
def prepare10Output (offset : Nat) : Array Word :=
  ((prepare9Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 67) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 67) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 67) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 67) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 67) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 67) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 67) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 67) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 67) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 67) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare10After (offset : Nat) : Cursor :=
  ([] ++ (prepare9After offset).1, offset + 68)
def prepare10Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare10Action offset) (prepare9After offset)

def prepare11Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[11]!]
    return ((prepare10Output offset)).push w
def prepare11Output (offset : Nat) : Array Word :=
  ((prepare10Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 68) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 68) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 68) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 68) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 68) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 68) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 68) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 68) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 68) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 68) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare11After (offset : Nat) : Cursor :=
  ([] ++ (prepare10After offset).1, offset + 69)
def prepare11Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare11Action offset) (prepare10After offset)

def prepare12Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[12]!]
    return ((prepare11Output offset)).push w
def prepare12Output (offset : Nat) : Array Word :=
  ((prepare11Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 69) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 69) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 69) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 69) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 69) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 69) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 69) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 69) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 69) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 69) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare12After (offset : Nat) : Cursor :=
  ([] ++ (prepare11After offset).1, offset + 70)
def prepare12Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare12Action offset) (prepare11After offset)

def prepare13Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[13]!]
    return ((prepare12Output offset)).push w
def prepare13Output (offset : Nat) : Array Word :=
  ((prepare12Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 70) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 70) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 70) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 70) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 70) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 70) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 70) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 70) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 70) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 70) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare13After (offset : Nat) : Cursor :=
  ([] ++ (prepare12After offset).1, offset + 71)
def prepare13Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare13Action offset) (prepare12After offset)

def prepare14Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[14]!]
    return ((prepare13Output offset)).push w
def prepare14Output (offset : Nat) : Array Word :=
  ((prepare13Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 71) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 71) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 71) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 71) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 71) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 71) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 71) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 71) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 71) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 71) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare14After (offset : Nat) : Cursor :=
  ([] ++ (prepare13After offset).1, offset + 72)
def prepare14Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare14Action offset) (prepare13After offset)

def prepare15Action (offset : Nat) : Build (Array Word) :=
  do
    let w ← prepareMessage #[(packingOutput offset)[15]!]
    return ((prepare14Output offset)).push w
def prepare15Output (offset : Nat) : Array Word :=
  ((prepare14Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 72) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 72) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 72) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 72) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 72) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 72) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 72) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 72) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 72) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 72) 2 (⟨0⟩ : Column .advice)⟩] } })
def prepare15After (offset : Nat) : Cursor :=
  ([] ++ (prepare14After offset).1, offset + 73)
def prepare15Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (prepare15Action offset) (prepare14After offset)

def expand16Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (prepare15Output offset)[1]!
    let s1 ← sigma1 (prepare15Output offset)[14]!
    let w ← prepareMessage #[(prepare15Output offset)[0]!.combined.plain, (prepare15Output offset)[9]!.combined.plain, s0, s1]
    return (prepare15Output offset).push w
def expand16Output (offset : Nat) : Array Word :=
  ((prepare15Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 75) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 75) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 75) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 75) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 75) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 75) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 75) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 75) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 75) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 75) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand16After (offset : Nat) : Cursor :=
  ([] ++ (prepare15After offset).1, offset + 76)
def expand16Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand16Action offset) (prepare15After offset)

def expand17Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand16Output offset)[2]!
    let s1 ← sigma1 (expand16Output offset)[15]!
    let w ← prepareMessage #[(expand16Output offset)[1]!.combined.plain, (expand16Output offset)[10]!.combined.plain, s0, s1]
    return (expand16Output offset).push w
def expand17Output (offset : Nat) : Array Word :=
  ((expand16Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 78) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 78) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 78) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 78) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 78) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 78) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 78) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 78) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 78) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 78) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand17After (offset : Nat) : Cursor :=
  ([] ++ (expand16After offset).1, offset + 79)
def expand17Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand17Action offset) (expand16After offset)

def expand18Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand17Output offset)[3]!
    let s1 ← sigma1 (expand17Output offset)[16]!
    let w ← prepareMessage #[(expand17Output offset)[2]!.combined.plain, (expand17Output offset)[11]!.combined.plain, s0, s1]
    return (expand17Output offset).push w
def expand18Output (offset : Nat) : Array Word :=
  ((expand17Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 81) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 81) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 81) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 81) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 81) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 81) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 81) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 81) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 81) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 81) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand18After (offset : Nat) : Cursor :=
  ([] ++ (expand17After offset).1, offset + 82)
def expand18Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand18Action offset) (expand17After offset)

def expand19Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand18Output offset)[4]!
    let s1 ← sigma1 (expand18Output offset)[17]!
    let w ← prepareMessage #[(expand18Output offset)[3]!.combined.plain, (expand18Output offset)[12]!.combined.plain, s0, s1]
    return (expand18Output offset).push w
def expand19Output (offset : Nat) : Array Word :=
  ((expand18Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 84) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 84) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 84) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 84) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 84) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 84) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 84) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 84) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 84) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 84) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand19After (offset : Nat) : Cursor :=
  ([] ++ (expand18After offset).1, offset + 85)
def expand19Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand19Action offset) (expand18After offset)

def expand20Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand19Output offset)[5]!
    let s1 ← sigma1 (expand19Output offset)[18]!
    let w ← prepareMessage #[(expand19Output offset)[4]!.combined.plain, (expand19Output offset)[13]!.combined.plain, s0, s1]
    return (expand19Output offset).push w
def expand20Output (offset : Nat) : Array Word :=
  ((expand19Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 87) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 87) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 87) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 87) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 87) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 87) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 87) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 87) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 87) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 87) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand20After (offset : Nat) : Cursor :=
  ([] ++ (expand19After offset).1, offset + 88)
def expand20Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand20Action offset) (expand19After offset)

def expand21Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand20Output offset)[6]!
    let s1 ← sigma1 (expand20Output offset)[19]!
    let w ← prepareMessage #[(expand20Output offset)[5]!.combined.plain, (expand20Output offset)[14]!.combined.plain, s0, s1]
    return (expand20Output offset).push w
def expand21Output (offset : Nat) : Array Word :=
  ((expand20Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 90) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 90) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 90) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 90) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 90) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 90) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 90) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 90) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 90) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 90) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand21After (offset : Nat) : Cursor :=
  ([] ++ (expand20After offset).1, offset + 91)
def expand21Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand21Action offset) (expand20After offset)

def expand22Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand21Output offset)[7]!
    let s1 ← sigma1 (expand21Output offset)[20]!
    let w ← prepareMessage #[(expand21Output offset)[6]!.combined.plain, (expand21Output offset)[15]!.combined.plain, s0, s1]
    return (expand21Output offset).push w
def expand22Output (offset : Nat) : Array Word :=
  ((expand21Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 93) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 93) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 93) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 93) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 93) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 93) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 93) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 93) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 93) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 93) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand22After (offset : Nat) : Cursor :=
  ([] ++ (expand21After offset).1, offset + 94)
def expand22Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand22Action offset) (expand21After offset)

def expand23Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand22Output offset)[8]!
    let s1 ← sigma1 (expand22Output offset)[21]!
    let w ← prepareMessage #[(expand22Output offset)[7]!.combined.plain, (expand22Output offset)[16]!.combined.plain, s0, s1]
    return (expand22Output offset).push w
def expand23Output (offset : Nat) : Array Word :=
  ((expand22Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 96) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 96) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 96) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 96) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 96) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 96) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 96) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 96) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 96) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 96) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand23After (offset : Nat) : Cursor :=
  ([] ++ (expand22After offset).1, offset + 97)
def expand23Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand23Action offset) (expand22After offset)

def expand24Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand23Output offset)[9]!
    let s1 ← sigma1 (expand23Output offset)[22]!
    let w ← prepareMessage #[(expand23Output offset)[8]!.combined.plain, (expand23Output offset)[17]!.combined.plain, s0, s1]
    return (expand23Output offset).push w
def expand24Output (offset : Nat) : Array Word :=
  ((expand23Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 99) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 99) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 99) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 99) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 99) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 99) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 99) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 99) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 99) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 99) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand24After (offset : Nat) : Cursor :=
  ([] ++ (expand23After offset).1, offset + 100)
def expand24Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand24Action offset) (expand23After offset)

def expand25Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand24Output offset)[10]!
    let s1 ← sigma1 (expand24Output offset)[23]!
    let w ← prepareMessage #[(expand24Output offset)[9]!.combined.plain, (expand24Output offset)[18]!.combined.plain, s0, s1]
    return (expand24Output offset).push w
def expand25Output (offset : Nat) : Array Word :=
  ((expand24Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 102) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 102) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 102) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 102) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 102) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 102) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 102) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 102) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 102) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 102) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand25After (offset : Nat) : Cursor :=
  ([] ++ (expand24After offset).1, offset + 103)
def expand25Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand25Action offset) (expand24After offset)

def expand26Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand25Output offset)[11]!
    let s1 ← sigma1 (expand25Output offset)[24]!
    let w ← prepareMessage #[(expand25Output offset)[10]!.combined.plain, (expand25Output offset)[19]!.combined.plain, s0, s1]
    return (expand25Output offset).push w
def expand26Output (offset : Nat) : Array Word :=
  ((expand25Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 105) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 105) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 105) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 105) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 105) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 105) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 105) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 105) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 105) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 105) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand26After (offset : Nat) : Cursor :=
  ([] ++ (expand25After offset).1, offset + 106)
def expand26Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand26Action offset) (expand25After offset)

def expand27Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand26Output offset)[12]!
    let s1 ← sigma1 (expand26Output offset)[25]!
    let w ← prepareMessage #[(expand26Output offset)[11]!.combined.plain, (expand26Output offset)[20]!.combined.plain, s0, s1]
    return (expand26Output offset).push w
def expand27Output (offset : Nat) : Array Word :=
  ((expand26Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 108) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 108) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 108) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 108) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 108) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 108) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 108) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 108) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 108) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 108) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand27After (offset : Nat) : Cursor :=
  ([] ++ (expand26After offset).1, offset + 109)
def expand27Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand27Action offset) (expand26After offset)

def expand28Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand27Output offset)[13]!
    let s1 ← sigma1 (expand27Output offset)[26]!
    let w ← prepareMessage #[(expand27Output offset)[12]!.combined.plain, (expand27Output offset)[21]!.combined.plain, s0, s1]
    return (expand27Output offset).push w
def expand28Output (offset : Nat) : Array Word :=
  ((expand27Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 111) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 111) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 111) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 111) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 111) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 111) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 111) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 111) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 111) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 111) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand28After (offset : Nat) : Cursor :=
  ([] ++ (expand27After offset).1, offset + 112)
def expand28Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand28Action offset) (expand27After offset)

def expand29Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand28Output offset)[14]!
    let s1 ← sigma1 (expand28Output offset)[27]!
    let w ← prepareMessage #[(expand28Output offset)[13]!.combined.plain, (expand28Output offset)[22]!.combined.plain, s0, s1]
    return (expand28Output offset).push w
def expand29Output (offset : Nat) : Array Word :=
  ((expand28Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 114) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 114) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 114) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 114) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 114) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 114) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 114) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 114) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 114) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 114) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand29After (offset : Nat) : Cursor :=
  ([] ++ (expand28After offset).1, offset + 115)
def expand29Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand29Action offset) (expand28After offset)

def expand30Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand29Output offset)[15]!
    let s1 ← sigma1 (expand29Output offset)[28]!
    let w ← prepareMessage #[(expand29Output offset)[14]!.combined.plain, (expand29Output offset)[23]!.combined.plain, s0, s1]
    return (expand29Output offset).push w
def expand30Output (offset : Nat) : Array Word :=
  ((expand29Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 117) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 117) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 117) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 117) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 117) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 117) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 117) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 117) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 117) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 117) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand30After (offset : Nat) : Cursor :=
  ([] ++ (expand29After offset).1, offset + 118)
def expand30Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand30Action offset) (expand29After offset)

def expand31Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand30Output offset)[16]!
    let s1 ← sigma1 (expand30Output offset)[29]!
    let w ← prepareMessage #[(expand30Output offset)[15]!.combined.plain, (expand30Output offset)[24]!.combined.plain, s0, s1]
    return (expand30Output offset).push w
def expand31Output (offset : Nat) : Array Word :=
  ((expand30Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 120) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 120) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 120) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 120) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 120) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 120) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 120) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 120) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 120) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 120) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand31After (offset : Nat) : Cursor :=
  ([] ++ (expand30After offset).1, offset + 121)
def expand31Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand31Action offset) (expand30After offset)

def expand32Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand31Output offset)[17]!
    let s1 ← sigma1 (expand31Output offset)[30]!
    let w ← prepareMessage #[(expand31Output offset)[16]!.combined.plain, (expand31Output offset)[25]!.combined.plain, s0, s1]
    return (expand31Output offset).push w
def expand32Output (offset : Nat) : Array Word :=
  ((expand31Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 123) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 123) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 123) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 123) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 123) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 123) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 123) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 123) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 123) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 123) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand32After (offset : Nat) : Cursor :=
  ([] ++ (expand31After offset).1, offset + 124)
def expand32Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand32Action offset) (expand31After offset)

def expand33Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand32Output offset)[18]!
    let s1 ← sigma1 (expand32Output offset)[31]!
    let w ← prepareMessage #[(expand32Output offset)[17]!.combined.plain, (expand32Output offset)[26]!.combined.plain, s0, s1]
    return (expand32Output offset).push w
def expand33Output (offset : Nat) : Array Word :=
  ((expand32Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 126) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 126) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 126) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 126) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 126) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 126) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 126) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 126) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 126) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 126) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand33After (offset : Nat) : Cursor :=
  ([] ++ (expand32After offset).1, offset + 127)
def expand33Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand33Action offset) (expand32After offset)

def expand34Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand33Output offset)[19]!
    let s1 ← sigma1 (expand33Output offset)[32]!
    let w ← prepareMessage #[(expand33Output offset)[18]!.combined.plain, (expand33Output offset)[27]!.combined.plain, s0, s1]
    return (expand33Output offset).push w
def expand34Output (offset : Nat) : Array Word :=
  ((expand33Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 129) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 129) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 129) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 129) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 129) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 129) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 129) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 129) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 129) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 129) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand34After (offset : Nat) : Cursor :=
  ([] ++ (expand33After offset).1, offset + 130)
def expand34Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand34Action offset) (expand33After offset)

def expand35Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand34Output offset)[20]!
    let s1 ← sigma1 (expand34Output offset)[33]!
    let w ← prepareMessage #[(expand34Output offset)[19]!.combined.plain, (expand34Output offset)[28]!.combined.plain, s0, s1]
    return (expand34Output offset).push w
def expand35Output (offset : Nat) : Array Word :=
  ((expand34Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 132) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 132) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 132) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 132) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 132) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 132) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 132) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 132) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 132) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 132) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand35After (offset : Nat) : Cursor :=
  ([] ++ (expand34After offset).1, offset + 133)
def expand35Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand35Action offset) (expand34After offset)

def expand36Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand35Output offset)[21]!
    let s1 ← sigma1 (expand35Output offset)[34]!
    let w ← prepareMessage #[(expand35Output offset)[20]!.combined.plain, (expand35Output offset)[29]!.combined.plain, s0, s1]
    return (expand35Output offset).push w
def expand36Output (offset : Nat) : Array Word :=
  ((expand35Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 135) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 135) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 135) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 135) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 135) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 135) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 135) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 135) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 135) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 135) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand36After (offset : Nat) : Cursor :=
  ([] ++ (expand35After offset).1, offset + 136)
def expand36Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand36Action offset) (expand35After offset)

def expand37Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand36Output offset)[22]!
    let s1 ← sigma1 (expand36Output offset)[35]!
    let w ← prepareMessage #[(expand36Output offset)[21]!.combined.plain, (expand36Output offset)[30]!.combined.plain, s0, s1]
    return (expand36Output offset).push w
def expand37Output (offset : Nat) : Array Word :=
  ((expand36Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 138) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 138) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 138) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 138) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 138) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 138) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 138) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 138) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 138) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 138) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand37After (offset : Nat) : Cursor :=
  ([] ++ (expand36After offset).1, offset + 139)
def expand37Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand37Action offset) (expand36After offset)

def expand38Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand37Output offset)[23]!
    let s1 ← sigma1 (expand37Output offset)[36]!
    let w ← prepareMessage #[(expand37Output offset)[22]!.combined.plain, (expand37Output offset)[31]!.combined.plain, s0, s1]
    return (expand37Output offset).push w
def expand38Output (offset : Nat) : Array Word :=
  ((expand37Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 141) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 141) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 141) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 141) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 141) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 141) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 141) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 141) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 141) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 141) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand38After (offset : Nat) : Cursor :=
  ([] ++ (expand37After offset).1, offset + 142)
def expand38Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand38Action offset) (expand37After offset)

def expand39Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand38Output offset)[24]!
    let s1 ← sigma1 (expand38Output offset)[37]!
    let w ← prepareMessage #[(expand38Output offset)[23]!.combined.plain, (expand38Output offset)[32]!.combined.plain, s0, s1]
    return (expand38Output offset).push w
def expand39Output (offset : Nat) : Array Word :=
  ((expand38Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 144) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 144) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 144) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 144) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 144) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 144) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 144) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 144) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 144) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 144) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand39After (offset : Nat) : Cursor :=
  ([] ++ (expand38After offset).1, offset + 145)
def expand39Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand39Action offset) (expand38After offset)

def expand40Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand39Output offset)[25]!
    let s1 ← sigma1 (expand39Output offset)[38]!
    let w ← prepareMessage #[(expand39Output offset)[24]!.combined.plain, (expand39Output offset)[33]!.combined.plain, s0, s1]
    return (expand39Output offset).push w
def expand40Output (offset : Nat) : Array Word :=
  ((expand39Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 147) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 147) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 147) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 147) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 147) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 147) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 147) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 147) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 147) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 147) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand40After (offset : Nat) : Cursor :=
  ([] ++ (expand39After offset).1, offset + 148)
def expand40Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand40Action offset) (expand39After offset)

def expand41Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand40Output offset)[26]!
    let s1 ← sigma1 (expand40Output offset)[39]!
    let w ← prepareMessage #[(expand40Output offset)[25]!.combined.plain, (expand40Output offset)[34]!.combined.plain, s0, s1]
    return (expand40Output offset).push w
def expand41Output (offset : Nat) : Array Word :=
  ((expand40Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 150) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 150) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 150) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 150) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 150) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 150) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 150) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 150) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 150) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 150) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand41After (offset : Nat) : Cursor :=
  ([] ++ (expand40After offset).1, offset + 151)
def expand41Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand41Action offset) (expand40After offset)

def expand42Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand41Output offset)[27]!
    let s1 ← sigma1 (expand41Output offset)[40]!
    let w ← prepareMessage #[(expand41Output offset)[26]!.combined.plain, (expand41Output offset)[35]!.combined.plain, s0, s1]
    return (expand41Output offset).push w
def expand42Output (offset : Nat) : Array Word :=
  ((expand41Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 153) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 153) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 153) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 153) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 153) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 153) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 153) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 153) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 153) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 153) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand42After (offset : Nat) : Cursor :=
  ([] ++ (expand41After offset).1, offset + 154)
def expand42Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand42Action offset) (expand41After offset)

def expand43Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand42Output offset)[28]!
    let s1 ← sigma1 (expand42Output offset)[41]!
    let w ← prepareMessage #[(expand42Output offset)[27]!.combined.plain, (expand42Output offset)[36]!.combined.plain, s0, s1]
    return (expand42Output offset).push w
def expand43Output (offset : Nat) : Array Word :=
  ((expand42Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 156) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 156) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 156) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 156) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 156) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 156) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 156) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 156) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 156) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 156) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand43After (offset : Nat) : Cursor :=
  ([] ++ (expand42After offset).1, offset + 157)
def expand43Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand43Action offset) (expand42After offset)

def expand44Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand43Output offset)[29]!
    let s1 ← sigma1 (expand43Output offset)[42]!
    let w ← prepareMessage #[(expand43Output offset)[28]!.combined.plain, (expand43Output offset)[37]!.combined.plain, s0, s1]
    return (expand43Output offset).push w
def expand44Output (offset : Nat) : Array Word :=
  ((expand43Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 159) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 159) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 159) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 159) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 159) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 159) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 159) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 159) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 159) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 159) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand44After (offset : Nat) : Cursor :=
  ([] ++ (expand43After offset).1, offset + 160)
def expand44Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand44Action offset) (expand43After offset)

def expand45Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand44Output offset)[30]!
    let s1 ← sigma1 (expand44Output offset)[43]!
    let w ← prepareMessage #[(expand44Output offset)[29]!.combined.plain, (expand44Output offset)[38]!.combined.plain, s0, s1]
    return (expand44Output offset).push w
def expand45Output (offset : Nat) : Array Word :=
  ((expand44Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 162) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 162) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 162) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 162) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 162) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 162) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 162) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 162) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 162) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 162) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand45After (offset : Nat) : Cursor :=
  ([] ++ (expand44After offset).1, offset + 163)
def expand45Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand45Action offset) (expand44After offset)

def expand46Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand45Output offset)[31]!
    let s1 ← sigma1 (expand45Output offset)[44]!
    let w ← prepareMessage #[(expand45Output offset)[30]!.combined.plain, (expand45Output offset)[39]!.combined.plain, s0, s1]
    return (expand45Output offset).push w
def expand46Output (offset : Nat) : Array Word :=
  ((expand45Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 165) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 165) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 165) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 165) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 165) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 165) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 165) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 165) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 165) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 165) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand46After (offset : Nat) : Cursor :=
  ([] ++ (expand45After offset).1, offset + 166)
def expand46Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand46Action offset) (expand45After offset)

def expand47Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand46Output offset)[32]!
    let s1 ← sigma1 (expand46Output offset)[45]!
    let w ← prepareMessage #[(expand46Output offset)[31]!.combined.plain, (expand46Output offset)[40]!.combined.plain, s0, s1]
    return (expand46Output offset).push w
def expand47Output (offset : Nat) : Array Word :=
  ((expand46Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 168) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 168) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 168) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 168) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 168) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 168) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 168) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 168) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 168) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 168) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand47After (offset : Nat) : Cursor :=
  ([] ++ (expand46After offset).1, offset + 169)
def expand47Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand47Action offset) (expand46After offset)

def expand48Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand47Output offset)[33]!
    let s1 ← sigma1 (expand47Output offset)[46]!
    let w ← prepareMessage #[(expand47Output offset)[32]!.combined.plain, (expand47Output offset)[41]!.combined.plain, s0, s1]
    return (expand47Output offset).push w
def expand48Output (offset : Nat) : Array Word :=
  ((expand47Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 171) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 171) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 171) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 171) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 171) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 171) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 171) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 171) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 171) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 171) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand48After (offset : Nat) : Cursor :=
  ([] ++ (expand47After offset).1, offset + 172)
def expand48Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand48Action offset) (expand47After offset)

def expand49Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand48Output offset)[34]!
    let s1 ← sigma1 (expand48Output offset)[47]!
    let w ← prepareMessage #[(expand48Output offset)[33]!.combined.plain, (expand48Output offset)[42]!.combined.plain, s0, s1]
    return (expand48Output offset).push w
def expand49Output (offset : Nat) : Array Word :=
  ((expand48Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 174) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 174) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 174) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 174) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 174) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 174) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 174) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 174) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 174) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 174) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand49After (offset : Nat) : Cursor :=
  ([] ++ (expand48After offset).1, offset + 175)
def expand49Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand49Action offset) (expand48After offset)

def expand50Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand49Output offset)[35]!
    let s1 ← sigma1 (expand49Output offset)[48]!
    let w ← prepareMessage #[(expand49Output offset)[34]!.combined.plain, (expand49Output offset)[43]!.combined.plain, s0, s1]
    return (expand49Output offset).push w
def expand50Output (offset : Nat) : Array Word :=
  ((expand49Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 177) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 177) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 177) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 177) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 177) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 177) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 177) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 177) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 177) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 177) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand50After (offset : Nat) : Cursor :=
  ([] ++ (expand49After offset).1, offset + 178)
def expand50Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand50Action offset) (expand49After offset)

def expand51Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand50Output offset)[36]!
    let s1 ← sigma1 (expand50Output offset)[49]!
    let w ← prepareMessage #[(expand50Output offset)[35]!.combined.plain, (expand50Output offset)[44]!.combined.plain, s0, s1]
    return (expand50Output offset).push w
def expand51Output (offset : Nat) : Array Word :=
  ((expand50Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 180) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 180) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 180) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 180) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 180) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 180) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 180) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 180) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 180) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 180) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand51After (offset : Nat) : Cursor :=
  ([] ++ (expand50After offset).1, offset + 181)
def expand51Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand51Action offset) (expand50After offset)

def expand52Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand51Output offset)[37]!
    let s1 ← sigma1 (expand51Output offset)[50]!
    let w ← prepareMessage #[(expand51Output offset)[36]!.combined.plain, (expand51Output offset)[45]!.combined.plain, s0, s1]
    return (expand51Output offset).push w
def expand52Output (offset : Nat) : Array Word :=
  ((expand51Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 183) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 183) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 183) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 183) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 183) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 183) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 183) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 183) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 183) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 183) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand52After (offset : Nat) : Cursor :=
  ([] ++ (expand51After offset).1, offset + 184)
def expand52Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand52Action offset) (expand51After offset)

def expand53Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand52Output offset)[38]!
    let s1 ← sigma1 (expand52Output offset)[51]!
    let w ← prepareMessage #[(expand52Output offset)[37]!.combined.plain, (expand52Output offset)[46]!.combined.plain, s0, s1]
    return (expand52Output offset).push w
def expand53Output (offset : Nat) : Array Word :=
  ((expand52Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 186) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 186) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 186) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 186) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 186) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 186) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 186) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 186) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 186) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 186) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand53After (offset : Nat) : Cursor :=
  ([] ++ (expand52After offset).1, offset + 187)
def expand53Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand53Action offset) (expand52After offset)

def expand54Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand53Output offset)[39]!
    let s1 ← sigma1 (expand53Output offset)[52]!
    let w ← prepareMessage #[(expand53Output offset)[38]!.combined.plain, (expand53Output offset)[47]!.combined.plain, s0, s1]
    return (expand53Output offset).push w
def expand54Output (offset : Nat) : Array Word :=
  ((expand53Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 189) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 189) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 189) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 189) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 189) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 189) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 189) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 189) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 189) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 189) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand54After (offset : Nat) : Cursor :=
  ([] ++ (expand53After offset).1, offset + 190)
def expand54Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand54Action offset) (expand53After offset)

def expand55Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand54Output offset)[40]!
    let s1 ← sigma1 (expand54Output offset)[53]!
    let w ← prepareMessage #[(expand54Output offset)[39]!.combined.plain, (expand54Output offset)[48]!.combined.plain, s0, s1]
    return (expand54Output offset).push w
def expand55Output (offset : Nat) : Array Word :=
  ((expand54Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 192) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 192) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 192) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 192) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 192) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 192) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 192) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 192) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 192) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 192) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand55After (offset : Nat) : Cursor :=
  ([] ++ (expand54After offset).1, offset + 193)
def expand55Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand55Action offset) (expand54After offset)

def expand56Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand55Output offset)[41]!
    let s1 ← sigma1 (expand55Output offset)[54]!
    let w ← prepareMessage #[(expand55Output offset)[40]!.combined.plain, (expand55Output offset)[49]!.combined.plain, s0, s1]
    return (expand55Output offset).push w
def expand56Output (offset : Nat) : Array Word :=
  ((expand55Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 195) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 195) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 195) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 195) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 195) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 195) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 195) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 195) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 195) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 195) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand56After (offset : Nat) : Cursor :=
  ([] ++ (expand55After offset).1, offset + 196)
def expand56Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand56Action offset) (expand55After offset)

def expand57Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand56Output offset)[42]!
    let s1 ← sigma1 (expand56Output offset)[55]!
    let w ← prepareMessage #[(expand56Output offset)[41]!.combined.plain, (expand56Output offset)[50]!.combined.plain, s0, s1]
    return (expand56Output offset).push w
def expand57Output (offset : Nat) : Array Word :=
  ((expand56Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 198) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 198) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 198) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 198) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 198) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 198) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 198) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 198) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 198) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 198) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand57After (offset : Nat) : Cursor :=
  ([] ++ (expand56After offset).1, offset + 199)
def expand57Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand57Action offset) (expand56After offset)

def expand58Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand57Output offset)[43]!
    let s1 ← sigma1 (expand57Output offset)[56]!
    let w ← prepareMessage #[(expand57Output offset)[42]!.combined.plain, (expand57Output offset)[51]!.combined.plain, s0, s1]
    return (expand57Output offset).push w
def expand58Output (offset : Nat) : Array Word :=
  ((expand57Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 201) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 201) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 201) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 201) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 201) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 201) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 201) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 201) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 201) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 201) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand58After (offset : Nat) : Cursor :=
  ([] ++ (expand57After offset).1, offset + 202)
def expand58Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand58Action offset) (expand57After offset)

def expand59Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand58Output offset)[44]!
    let s1 ← sigma1 (expand58Output offset)[57]!
    let w ← prepareMessage #[(expand58Output offset)[43]!.combined.plain, (expand58Output offset)[52]!.combined.plain, s0, s1]
    return (expand58Output offset).push w
def expand59Output (offset : Nat) : Array Word :=
  ((expand58Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 204) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 204) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 204) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 204) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 204) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 204) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 204) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 204) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 204) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 204) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand59After (offset : Nat) : Cursor :=
  ([] ++ (expand58After offset).1, offset + 205)
def expand59Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand59Action offset) (expand58After offset)

def expand60Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand59Output offset)[45]!
    let s1 ← sigma1 (expand59Output offset)[58]!
    let w ← prepareMessage #[(expand59Output offset)[44]!.combined.plain, (expand59Output offset)[53]!.combined.plain, s0, s1]
    return (expand59Output offset).push w
def expand60Output (offset : Nat) : Array Word :=
  ((expand59Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 207) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 207) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 207) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 207) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 207) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 207) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 207) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 207) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 207) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 207) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand60After (offset : Nat) : Cursor :=
  ([] ++ (expand59After offset).1, offset + 208)
def expand60Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand60Action offset) (expand59After offset)

def expand61Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand60Output offset)[46]!
    let s1 ← sigma1 (expand60Output offset)[59]!
    let w ← prepareMessage #[(expand60Output offset)[45]!.combined.plain, (expand60Output offset)[54]!.combined.plain, s0, s1]
    return (expand60Output offset).push w
def expand61Output (offset : Nat) : Array Word :=
  ((expand60Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 210) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 210) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 210) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 210) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 210) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 210) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 210) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 210) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 210) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 210) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand61After (offset : Nat) : Cursor :=
  ([] ++ (expand60After offset).1, offset + 211)
def expand61Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand61Action offset) (expand60After offset)

def expand62Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand61Output offset)[47]!
    let s1 ← sigma1 (expand61Output offset)[60]!
    let w ← prepareMessage #[(expand61Output offset)[46]!.combined.plain, (expand61Output offset)[55]!.combined.plain, s0, s1]
    return (expand61Output offset).push w
def expand62Output (offset : Nat) : Array Word :=
  ((expand61Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 213) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 213) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 213) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 213) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 213) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 213) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 213) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 213) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 213) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 213) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand62After (offset : Nat) : Cursor :=
  ([] ++ (expand61After offset).1, offset + 214)
def expand62Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand62Action offset) (expand61After offset)

def expand63Action (offset : Nat) : Build (Array Word) :=
  do
    let s0 ← sigma0 (expand62Output offset)[48]!
    let s1 ← sigma1 (expand62Output offset)[61]!
    let w ← prepareMessage #[(expand62Output offset)[47]!.combined.plain, (expand62Output offset)[56]!.combined.plain, s0, s1]
    return (expand62Output offset).push w
def expand63Output (offset : Nat) : Array Word :=
  ((expand62Output offset)).push ({ combined := { plain := ⟨Cell.of (offset + 216) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 216) 0 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 216) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 216) 0 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 216) 1 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 216) 2 (⟨5⟩ : Column .advice)⟩, ⟨Cell.of (offset + 216) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 216) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 216) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 216) 2 (⟨0⟩ : Column .advice)⟩] } })
def expand63After (offset : Nat) : Cursor :=
  ([] ++ (expand62After offset).1, offset + 217)
def expand63Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (expand63Action offset) (expand62After offset)

def scheduleOutput (offset : Nat) : Array WitnessCircuit.Cell := (expand63Output offset).map (·.combined.plain)

def round0Action (offset : Nat) : Build (Compression) :=
  compressionRound (initialOutput offset) Synthesis.roundConstants[0]! (scheduleOutput offset)[0]!
def round0Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 223) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 223) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 223) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 223) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 223) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 223) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 223) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 24) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 25) 0 (⟨9⟩ : Column .fixed)⟩ }, c := { plain := ⟨Cell.of (offset + 30) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 31) 0 (⟨9⟩ : Column .fixed)⟩ }, d := ⟨Cell.of (offset + 32) 0 (⟨9⟩ : Column .fixed)⟩, e := { combined := { plain := ⟨Cell.of (offset + 224) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 224) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 224) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 224) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 224) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 224) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 224) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 35) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 36) 0 (⟨9⟩ : Column .fixed)⟩ }, g := { plain := ⟨Cell.of (offset + 42) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 43) 0 (⟨9⟩ : Column .fixed)⟩ }, h := ⟨Cell.of (offset + 44) 0 (⟨9⟩ : Column .fixed)⟩ }
def round0After (offset : Nat) : Cursor :=
  ([(6148914691236517205, ⟨Cell.of (offset + 221) 0 (⟨9⟩ : Column .fixed)⟩), (1116352408, ⟨Cell.of (offset + 217) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (expand63After offset).1, offset + 225)
def round0Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round0Action offset) (expand63After offset)

def round1Action (offset : Nat) : Build (Compression) :=
  compressionRound (round0Output offset) Synthesis.roundConstants[1]! (scheduleOutput offset)[1]!
def round1Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 230) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 230) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 230) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 230) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 230) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 230) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 230) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 223) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 223) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 24) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 25) 0 (⟨9⟩ : Column .fixed)⟩ }, d := ⟨Cell.of (offset + 30) 0 (⟨9⟩ : Column .fixed)⟩, e := { combined := { plain := ⟨Cell.of (offset + 231) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 231) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 231) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 231) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 231) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 231) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 231) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 224) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 224) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 35) 0 (⟨9⟩ : Column .fixed)⟩, spread := ⟨Cell.of (offset + 36) 0 (⟨9⟩ : Column .fixed)⟩ }, h := ⟨Cell.of (offset + 42) 0 (⟨9⟩ : Column .fixed)⟩ }
def round1After (offset : Nat) : Cursor :=
  ([(1899447441, ⟨Cell.of (offset + 225) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round0After offset).1, offset + 232)
def round1Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round1Action offset) (round0After offset)

def round2Action (offset : Nat) : Build (Compression) :=
  compressionRound (round1Output offset) Synthesis.roundConstants[2]! (scheduleOutput offset)[2]!
def round2Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 237) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 237) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 237) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 237) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 237) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 237) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 237) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 230) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 230) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 223) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 223) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 24) 0 (⟨9⟩ : Column .fixed)⟩, e := { combined := { plain := ⟨Cell.of (offset + 238) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 238) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 238) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 238) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 238) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 238) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 238) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 231) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 231) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 224) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 224) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 35) 0 (⟨9⟩ : Column .fixed)⟩ }
def round2After (offset : Nat) : Cursor :=
  ([(3049323471, ⟨Cell.of (offset + 232) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round1After offset).1, offset + 239)
def round2Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round2Action offset) (round1After offset)

def round3Action (offset : Nat) : Build (Compression) :=
  compressionRound (round2Output offset) Synthesis.roundConstants[3]! (scheduleOutput offset)[3]!
def round3Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 244) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 244) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 244) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 244) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 244) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 244) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 244) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 237) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 237) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 230) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 230) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 223) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 245) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 245) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 245) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 245) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 245) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 245) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 245) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 238) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 238) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 231) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 231) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 224) 0 (⟨2⟩ : Column .advice)⟩ }
def round3After (offset : Nat) : Cursor :=
  ([(3921009573, ⟨Cell.of (offset + 239) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round2After offset).1, offset + 246)
def round3Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round3Action offset) (round2After offset)

def round4Action (offset : Nat) : Build (Compression) :=
  compressionRound (round3Output offset) Synthesis.roundConstants[4]! (scheduleOutput offset)[4]!
def round4Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 251) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 251) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 251) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 251) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 251) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 251) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 251) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 244) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 244) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 237) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 237) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 230) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 252) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 252) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 252) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 252) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 252) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 252) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 252) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 245) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 245) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 238) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 238) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 231) 0 (⟨2⟩ : Column .advice)⟩ }
def round4After (offset : Nat) : Cursor :=
  ([(961987163, ⟨Cell.of (offset + 246) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round3After offset).1, offset + 253)
def round4Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round4Action offset) (round3After offset)

def round5Action (offset : Nat) : Build (Compression) :=
  compressionRound (round4Output offset) Synthesis.roundConstants[5]! (scheduleOutput offset)[5]!
def round5Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 258) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 258) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 258) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 258) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 258) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 258) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 258) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 251) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 251) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 244) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 244) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 237) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 259) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 259) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 259) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 259) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 259) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 259) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 259) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 252) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 252) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 245) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 245) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 238) 0 (⟨2⟩ : Column .advice)⟩ }
def round5After (offset : Nat) : Cursor :=
  ([(1508970993, ⟨Cell.of (offset + 253) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round4After offset).1, offset + 260)
def round5Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round5Action offset) (round4After offset)

def round6Action (offset : Nat) : Build (Compression) :=
  compressionRound (round5Output offset) Synthesis.roundConstants[6]! (scheduleOutput offset)[6]!
def round6Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 265) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 265) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 265) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 265) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 265) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 265) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 265) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 258) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 258) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 251) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 251) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 244) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 266) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 266) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 266) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 266) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 266) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 266) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 266) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 259) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 259) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 252) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 252) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 245) 0 (⟨2⟩ : Column .advice)⟩ }
def round6After (offset : Nat) : Cursor :=
  ([(2453635748, ⟨Cell.of (offset + 260) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round5After offset).1, offset + 267)
def round6Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round6Action offset) (round5After offset)

def round7Action (offset : Nat) : Build (Compression) :=
  compressionRound (round6Output offset) Synthesis.roundConstants[7]! (scheduleOutput offset)[7]!
def round7Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 272) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 272) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 272) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 272) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 272) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 272) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 272) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 265) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 265) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 258) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 258) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 251) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 273) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 273) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 273) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 273) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 273) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 273) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 273) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 266) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 266) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 259) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 259) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 252) 0 (⟨2⟩ : Column .advice)⟩ }
def round7After (offset : Nat) : Cursor :=
  ([(2870763221, ⟨Cell.of (offset + 267) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round6After offset).1, offset + 274)
def round7Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round7Action offset) (round6After offset)

def round8Action (offset : Nat) : Build (Compression) :=
  compressionRound (round7Output offset) Synthesis.roundConstants[8]! (scheduleOutput offset)[8]!
def round8Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 279) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 279) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 279) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 279) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 279) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 279) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 279) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 272) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 272) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 265) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 265) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 258) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 280) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 280) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 280) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 280) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 280) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 280) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 280) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 273) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 273) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 266) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 266) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 259) 0 (⟨2⟩ : Column .advice)⟩ }
def round8After (offset : Nat) : Cursor :=
  ([(3624381080, ⟨Cell.of (offset + 274) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round7After offset).1, offset + 281)
def round8Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round8Action offset) (round7After offset)

def round9Action (offset : Nat) : Build (Compression) :=
  compressionRound (round8Output offset) Synthesis.roundConstants[9]! (scheduleOutput offset)[9]!
def round9Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 286) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 286) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 286) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 286) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 286) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 286) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 286) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 279) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 279) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 272) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 272) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 265) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 287) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 287) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 287) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 287) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 287) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 287) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 287) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 280) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 280) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 273) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 273) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 266) 0 (⟨2⟩ : Column .advice)⟩ }
def round9After (offset : Nat) : Cursor :=
  ([(310598401, ⟨Cell.of (offset + 281) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round8After offset).1, offset + 288)
def round9Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round9Action offset) (round8After offset)

def round10Action (offset : Nat) : Build (Compression) :=
  compressionRound (round9Output offset) Synthesis.roundConstants[10]! (scheduleOutput offset)[10]!
def round10Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 293) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 293) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 293) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 293) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 293) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 293) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 293) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 286) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 286) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 279) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 279) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 272) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 294) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 294) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 294) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 294) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 294) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 294) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 294) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 287) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 287) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 280) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 280) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 273) 0 (⟨2⟩ : Column .advice)⟩ }
def round10After (offset : Nat) : Cursor :=
  ([(607225278, ⟨Cell.of (offset + 288) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round9After offset).1, offset + 295)
def round10Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round10Action offset) (round9After offset)

def round11Action (offset : Nat) : Build (Compression) :=
  compressionRound (round10Output offset) Synthesis.roundConstants[11]! (scheduleOutput offset)[11]!
def round11Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 300) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 300) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 300) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 300) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 300) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 300) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 300) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 293) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 293) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 286) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 286) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 279) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 301) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 301) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 301) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 301) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 301) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 301) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 301) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 294) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 294) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 287) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 287) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 280) 0 (⟨2⟩ : Column .advice)⟩ }
def round11After (offset : Nat) : Cursor :=
  ([(1426881987, ⟨Cell.of (offset + 295) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round10After offset).1, offset + 302)
def round11Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round11Action offset) (round10After offset)

def round12Action (offset : Nat) : Build (Compression) :=
  compressionRound (round11Output offset) Synthesis.roundConstants[12]! (scheduleOutput offset)[12]!
def round12Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 307) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 307) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 307) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 307) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 307) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 307) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 307) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 300) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 300) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 293) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 293) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 286) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 308) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 308) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 308) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 308) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 308) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 308) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 308) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 301) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 301) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 294) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 294) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 287) 0 (⟨2⟩ : Column .advice)⟩ }
def round12After (offset : Nat) : Cursor :=
  ([(1925078388, ⟨Cell.of (offset + 302) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round11After offset).1, offset + 309)
def round12Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round12Action offset) (round11After offset)

def round13Action (offset : Nat) : Build (Compression) :=
  compressionRound (round12Output offset) Synthesis.roundConstants[13]! (scheduleOutput offset)[13]!
def round13Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 314) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 314) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 314) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 314) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 314) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 314) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 314) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 307) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 307) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 300) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 300) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 293) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 315) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 315) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 315) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 315) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 315) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 315) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 315) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 308) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 308) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 301) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 301) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 294) 0 (⟨2⟩ : Column .advice)⟩ }
def round13After (offset : Nat) : Cursor :=
  ([(2162078206, ⟨Cell.of (offset + 309) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round12After offset).1, offset + 316)
def round13Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round13Action offset) (round12After offset)

def round14Action (offset : Nat) : Build (Compression) :=
  compressionRound (round13Output offset) Synthesis.roundConstants[14]! (scheduleOutput offset)[14]!
def round14Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 321) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 321) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 321) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 321) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 321) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 321) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 321) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 314) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 314) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 307) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 307) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 300) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 322) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 322) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 322) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 322) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 322) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 322) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 322) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 315) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 315) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 308) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 308) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 301) 0 (⟨2⟩ : Column .advice)⟩ }
def round14After (offset : Nat) : Cursor :=
  ([(2614888103, ⟨Cell.of (offset + 316) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round13After offset).1, offset + 323)
def round14Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round14Action offset) (round13After offset)

def round15Action (offset : Nat) : Build (Compression) :=
  compressionRound (round14Output offset) Synthesis.roundConstants[15]! (scheduleOutput offset)[15]!
def round15Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 328) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 328) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 328) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 328) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 328) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 328) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 328) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 321) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 321) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 314) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 314) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 307) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 329) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 329) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 329) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 329) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 329) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 329) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 329) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 322) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 322) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 315) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 315) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 308) 0 (⟨2⟩ : Column .advice)⟩ }
def round15After (offset : Nat) : Cursor :=
  ([(3248222580, ⟨Cell.of (offset + 323) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round14After offset).1, offset + 330)
def round15Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round15Action offset) (round14After offset)

def round16Action (offset : Nat) : Build (Compression) :=
  compressionRound (round15Output offset) Synthesis.roundConstants[16]! (scheduleOutput offset)[16]!
def round16Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 335) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 335) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 335) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 335) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 335) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 335) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 335) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 328) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 328) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 321) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 321) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 314) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 336) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 336) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 336) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 336) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 336) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 336) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 336) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 329) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 329) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 322) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 322) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 315) 0 (⟨2⟩ : Column .advice)⟩ }
def round16After (offset : Nat) : Cursor :=
  ([(3835390401, ⟨Cell.of (offset + 330) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round15After offset).1, offset + 337)
def round16Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round16Action offset) (round15After offset)

def round17Action (offset : Nat) : Build (Compression) :=
  compressionRound (round16Output offset) Synthesis.roundConstants[17]! (scheduleOutput offset)[17]!
def round17Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 342) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 342) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 342) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 342) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 342) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 342) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 342) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 335) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 335) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 328) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 328) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 321) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 343) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 343) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 343) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 343) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 343) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 343) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 343) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 336) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 336) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 329) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 329) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 322) 0 (⟨2⟩ : Column .advice)⟩ }
def round17After (offset : Nat) : Cursor :=
  ([(4022224774, ⟨Cell.of (offset + 337) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round16After offset).1, offset + 344)
def round17Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round17Action offset) (round16After offset)

def round18Action (offset : Nat) : Build (Compression) :=
  compressionRound (round17Output offset) Synthesis.roundConstants[18]! (scheduleOutput offset)[18]!
def round18Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 349) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 349) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 349) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 349) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 349) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 349) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 349) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 342) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 342) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 335) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 335) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 328) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 350) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 350) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 350) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 350) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 350) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 350) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 350) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 343) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 343) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 336) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 336) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 329) 0 (⟨2⟩ : Column .advice)⟩ }
def round18After (offset : Nat) : Cursor :=
  ([(264347078, ⟨Cell.of (offset + 344) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round17After offset).1, offset + 351)
def round18Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round18Action offset) (round17After offset)

def round19Action (offset : Nat) : Build (Compression) :=
  compressionRound (round18Output offset) Synthesis.roundConstants[19]! (scheduleOutput offset)[19]!
def round19Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 356) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 356) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 356) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 356) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 356) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 356) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 356) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 349) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 349) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 342) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 342) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 335) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 357) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 357) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 357) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 357) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 357) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 357) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 357) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 350) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 350) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 343) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 343) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 336) 0 (⟨2⟩ : Column .advice)⟩ }
def round19After (offset : Nat) : Cursor :=
  ([(604807628, ⟨Cell.of (offset + 351) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round18After offset).1, offset + 358)
def round19Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round19Action offset) (round18After offset)

def round20Action (offset : Nat) : Build (Compression) :=
  compressionRound (round19Output offset) Synthesis.roundConstants[20]! (scheduleOutput offset)[20]!
def round20Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 363) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 363) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 363) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 363) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 363) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 363) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 363) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 356) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 356) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 349) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 349) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 342) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 364) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 364) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 364) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 364) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 364) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 364) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 364) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 357) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 357) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 350) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 350) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 343) 0 (⟨2⟩ : Column .advice)⟩ }
def round20After (offset : Nat) : Cursor :=
  ([(770255983, ⟨Cell.of (offset + 358) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round19After offset).1, offset + 365)
def round20Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round20Action offset) (round19After offset)

def round21Action (offset : Nat) : Build (Compression) :=
  compressionRound (round20Output offset) Synthesis.roundConstants[21]! (scheduleOutput offset)[21]!
def round21Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 370) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 370) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 370) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 370) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 370) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 370) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 370) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 363) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 363) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 356) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 356) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 349) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 371) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 371) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 371) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 371) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 371) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 371) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 371) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 364) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 364) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 357) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 357) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 350) 0 (⟨2⟩ : Column .advice)⟩ }
def round21After (offset : Nat) : Cursor :=
  ([(1249150122, ⟨Cell.of (offset + 365) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round20After offset).1, offset + 372)
def round21Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round21Action offset) (round20After offset)

def round22Action (offset : Nat) : Build (Compression) :=
  compressionRound (round21Output offset) Synthesis.roundConstants[22]! (scheduleOutput offset)[22]!
def round22Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 377) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 377) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 377) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 377) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 377) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 377) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 377) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 370) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 370) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 363) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 363) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 356) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 378) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 378) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 378) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 378) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 378) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 378) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 378) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 371) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 371) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 364) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 364) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 357) 0 (⟨2⟩ : Column .advice)⟩ }
def round22After (offset : Nat) : Cursor :=
  ([(1555081692, ⟨Cell.of (offset + 372) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round21After offset).1, offset + 379)
def round22Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round22Action offset) (round21After offset)

def round23Action (offset : Nat) : Build (Compression) :=
  compressionRound (round22Output offset) Synthesis.roundConstants[23]! (scheduleOutput offset)[23]!
def round23Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 384) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 384) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 384) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 384) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 384) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 384) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 384) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 377) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 377) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 370) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 370) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 363) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 385) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 385) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 385) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 385) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 385) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 385) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 385) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 378) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 378) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 371) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 371) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 364) 0 (⟨2⟩ : Column .advice)⟩ }
def round23After (offset : Nat) : Cursor :=
  ([(1996064986, ⟨Cell.of (offset + 379) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round22After offset).1, offset + 386)
def round23Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round23Action offset) (round22After offset)

def round24Action (offset : Nat) : Build (Compression) :=
  compressionRound (round23Output offset) Synthesis.roundConstants[24]! (scheduleOutput offset)[24]!
def round24Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 391) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 391) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 391) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 391) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 391) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 391) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 391) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 384) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 384) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 377) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 377) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 370) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 392) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 392) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 392) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 392) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 392) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 392) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 392) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 385) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 385) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 378) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 378) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 371) 0 (⟨2⟩ : Column .advice)⟩ }
def round24After (offset : Nat) : Cursor :=
  ([(2554220882, ⟨Cell.of (offset + 386) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round23After offset).1, offset + 393)
def round24Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round24Action offset) (round23After offset)

def round25Action (offset : Nat) : Build (Compression) :=
  compressionRound (round24Output offset) Synthesis.roundConstants[25]! (scheduleOutput offset)[25]!
def round25Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 398) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 398) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 398) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 398) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 398) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 398) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 398) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 391) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 391) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 384) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 384) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 377) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 399) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 399) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 399) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 399) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 399) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 399) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 399) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 392) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 392) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 385) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 385) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 378) 0 (⟨2⟩ : Column .advice)⟩ }
def round25After (offset : Nat) : Cursor :=
  ([(2821834349, ⟨Cell.of (offset + 393) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round24After offset).1, offset + 400)
def round25Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round25Action offset) (round24After offset)

def round26Action (offset : Nat) : Build (Compression) :=
  compressionRound (round25Output offset) Synthesis.roundConstants[26]! (scheduleOutput offset)[26]!
def round26Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 405) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 405) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 405) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 405) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 405) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 405) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 405) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 398) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 398) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 391) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 391) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 384) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 406) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 406) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 406) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 406) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 406) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 406) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 406) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 399) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 399) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 392) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 392) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 385) 0 (⟨2⟩ : Column .advice)⟩ }
def round26After (offset : Nat) : Cursor :=
  ([(2952996808, ⟨Cell.of (offset + 400) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round25After offset).1, offset + 407)
def round26Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round26Action offset) (round25After offset)

def round27Action (offset : Nat) : Build (Compression) :=
  compressionRound (round26Output offset) Synthesis.roundConstants[27]! (scheduleOutput offset)[27]!
def round27Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 412) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 412) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 412) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 412) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 412) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 412) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 412) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 405) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 405) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 398) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 398) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 391) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 413) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 413) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 413) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 413) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 413) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 413) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 413) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 406) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 406) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 399) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 399) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 392) 0 (⟨2⟩ : Column .advice)⟩ }
def round27After (offset : Nat) : Cursor :=
  ([(3210313671, ⟨Cell.of (offset + 407) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round26After offset).1, offset + 414)
def round27Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round27Action offset) (round26After offset)

def round28Action (offset : Nat) : Build (Compression) :=
  compressionRound (round27Output offset) Synthesis.roundConstants[28]! (scheduleOutput offset)[28]!
def round28Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 419) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 419) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 419) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 419) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 419) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 419) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 419) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 412) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 412) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 405) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 405) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 398) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 420) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 420) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 420) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 420) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 420) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 420) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 420) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 413) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 413) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 406) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 406) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 399) 0 (⟨2⟩ : Column .advice)⟩ }
def round28After (offset : Nat) : Cursor :=
  ([(3336571891, ⟨Cell.of (offset + 414) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round27After offset).1, offset + 421)
def round28Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round28Action offset) (round27After offset)

def round29Action (offset : Nat) : Build (Compression) :=
  compressionRound (round28Output offset) Synthesis.roundConstants[29]! (scheduleOutput offset)[29]!
def round29Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 426) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 426) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 426) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 426) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 426) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 426) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 426) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 419) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 419) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 412) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 412) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 405) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 427) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 427) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 427) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 427) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 427) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 427) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 427) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 420) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 420) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 413) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 413) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 406) 0 (⟨2⟩ : Column .advice)⟩ }
def round29After (offset : Nat) : Cursor :=
  ([(3584528711, ⟨Cell.of (offset + 421) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round28After offset).1, offset + 428)
def round29Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round29Action offset) (round28After offset)

def round30Action (offset : Nat) : Build (Compression) :=
  compressionRound (round29Output offset) Synthesis.roundConstants[30]! (scheduleOutput offset)[30]!
def round30Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 433) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 433) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 433) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 433) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 433) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 433) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 433) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 426) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 426) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 419) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 419) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 412) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 434) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 434) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 434) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 434) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 434) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 434) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 434) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 427) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 427) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 420) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 420) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 413) 0 (⟨2⟩ : Column .advice)⟩ }
def round30After (offset : Nat) : Cursor :=
  ([(113926993, ⟨Cell.of (offset + 428) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round29After offset).1, offset + 435)
def round30Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round30Action offset) (round29After offset)

def round31Action (offset : Nat) : Build (Compression) :=
  compressionRound (round30Output offset) Synthesis.roundConstants[31]! (scheduleOutput offset)[31]!
def round31Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 440) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 440) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 440) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 440) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 440) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 440) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 440) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 433) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 433) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 426) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 426) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 419) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 441) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 441) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 441) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 441) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 441) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 441) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 441) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 434) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 434) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 427) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 427) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 420) 0 (⟨2⟩ : Column .advice)⟩ }
def round31After (offset : Nat) : Cursor :=
  ([(338241895, ⟨Cell.of (offset + 435) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round30After offset).1, offset + 442)
def round31Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round31Action offset) (round30After offset)

def round32Action (offset : Nat) : Build (Compression) :=
  compressionRound (round31Output offset) Synthesis.roundConstants[32]! (scheduleOutput offset)[32]!
def round32Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 447) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 447) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 447) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 447) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 447) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 447) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 447) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 440) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 440) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 433) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 433) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 426) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 448) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 448) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 448) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 448) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 448) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 448) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 448) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 441) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 441) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 434) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 434) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 427) 0 (⟨2⟩ : Column .advice)⟩ }
def round32After (offset : Nat) : Cursor :=
  ([(666307205, ⟨Cell.of (offset + 442) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round31After offset).1, offset + 449)
def round32Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round32Action offset) (round31After offset)

def round33Action (offset : Nat) : Build (Compression) :=
  compressionRound (round32Output offset) Synthesis.roundConstants[33]! (scheduleOutput offset)[33]!
def round33Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 454) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 454) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 454) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 454) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 454) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 454) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 454) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 447) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 447) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 440) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 440) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 433) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 455) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 455) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 455) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 455) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 455) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 455) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 455) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 448) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 448) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 441) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 441) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 434) 0 (⟨2⟩ : Column .advice)⟩ }
def round33After (offset : Nat) : Cursor :=
  ([(773529912, ⟨Cell.of (offset + 449) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round32After offset).1, offset + 456)
def round33Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round33Action offset) (round32After offset)

def round34Action (offset : Nat) : Build (Compression) :=
  compressionRound (round33Output offset) Synthesis.roundConstants[34]! (scheduleOutput offset)[34]!
def round34Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 461) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 461) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 461) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 461) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 461) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 461) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 461) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 454) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 454) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 447) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 447) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 440) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 462) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 462) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 462) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 462) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 462) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 462) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 462) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 455) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 455) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 448) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 448) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 441) 0 (⟨2⟩ : Column .advice)⟩ }
def round34After (offset : Nat) : Cursor :=
  ([(1294757372, ⟨Cell.of (offset + 456) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round33After offset).1, offset + 463)
def round34Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round34Action offset) (round33After offset)

def round35Action (offset : Nat) : Build (Compression) :=
  compressionRound (round34Output offset) Synthesis.roundConstants[35]! (scheduleOutput offset)[35]!
def round35Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 468) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 468) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 468) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 468) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 468) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 468) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 468) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 461) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 461) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 454) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 454) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 447) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 469) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 469) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 469) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 469) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 469) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 469) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 469) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 462) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 462) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 455) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 455) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 448) 0 (⟨2⟩ : Column .advice)⟩ }
def round35After (offset : Nat) : Cursor :=
  ([(1396182291, ⟨Cell.of (offset + 463) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round34After offset).1, offset + 470)
def round35Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round35Action offset) (round34After offset)

def round36Action (offset : Nat) : Build (Compression) :=
  compressionRound (round35Output offset) Synthesis.roundConstants[36]! (scheduleOutput offset)[36]!
def round36Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 475) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 475) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 475) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 475) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 475) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 475) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 475) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 468) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 468) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 461) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 461) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 454) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 476) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 476) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 476) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 476) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 476) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 476) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 476) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 469) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 469) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 462) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 462) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 455) 0 (⟨2⟩ : Column .advice)⟩ }
def round36After (offset : Nat) : Cursor :=
  ([(1695183700, ⟨Cell.of (offset + 470) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round35After offset).1, offset + 477)
def round36Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round36Action offset) (round35After offset)

def round37Action (offset : Nat) : Build (Compression) :=
  compressionRound (round36Output offset) Synthesis.roundConstants[37]! (scheduleOutput offset)[37]!
def round37Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 482) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 482) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 482) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 482) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 482) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 482) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 482) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 475) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 475) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 468) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 468) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 461) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 483) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 483) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 483) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 483) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 483) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 483) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 483) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 476) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 476) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 469) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 469) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 462) 0 (⟨2⟩ : Column .advice)⟩ }
def round37After (offset : Nat) : Cursor :=
  ([(1986661051, ⟨Cell.of (offset + 477) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round36After offset).1, offset + 484)
def round37Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round37Action offset) (round36After offset)

def round38Action (offset : Nat) : Build (Compression) :=
  compressionRound (round37Output offset) Synthesis.roundConstants[38]! (scheduleOutput offset)[38]!
def round38Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 489) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 489) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 489) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 489) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 489) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 489) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 489) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 482) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 482) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 475) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 475) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 468) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 490) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 490) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 490) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 490) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 490) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 490) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 490) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 483) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 483) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 476) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 476) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 469) 0 (⟨2⟩ : Column .advice)⟩ }
def round38After (offset : Nat) : Cursor :=
  ([(2177026350, ⟨Cell.of (offset + 484) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round37After offset).1, offset + 491)
def round38Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round38Action offset) (round37After offset)

def round39Action (offset : Nat) : Build (Compression) :=
  compressionRound (round38Output offset) Synthesis.roundConstants[39]! (scheduleOutput offset)[39]!
def round39Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 496) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 496) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 496) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 496) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 496) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 496) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 496) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 489) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 489) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 482) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 482) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 475) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 497) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 497) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 497) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 497) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 497) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 497) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 497) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 490) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 490) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 483) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 483) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 476) 0 (⟨2⟩ : Column .advice)⟩ }
def round39After (offset : Nat) : Cursor :=
  ([(2456956037, ⟨Cell.of (offset + 491) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round38After offset).1, offset + 498)
def round39Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round39Action offset) (round38After offset)

def round40Action (offset : Nat) : Build (Compression) :=
  compressionRound (round39Output offset) Synthesis.roundConstants[40]! (scheduleOutput offset)[40]!
def round40Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 503) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 503) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 503) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 503) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 503) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 503) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 503) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 496) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 496) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 489) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 489) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 482) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 504) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 504) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 504) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 504) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 504) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 504) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 504) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 497) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 497) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 490) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 490) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 483) 0 (⟨2⟩ : Column .advice)⟩ }
def round40After (offset : Nat) : Cursor :=
  ([(2730485921, ⟨Cell.of (offset + 498) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round39After offset).1, offset + 505)
def round40Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round40Action offset) (round39After offset)

def round41Action (offset : Nat) : Build (Compression) :=
  compressionRound (round40Output offset) Synthesis.roundConstants[41]! (scheduleOutput offset)[41]!
def round41Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 510) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 510) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 510) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 510) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 510) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 510) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 510) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 503) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 503) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 496) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 496) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 489) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 511) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 511) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 511) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 511) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 511) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 511) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 511) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 504) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 504) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 497) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 497) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 490) 0 (⟨2⟩ : Column .advice)⟩ }
def round41After (offset : Nat) : Cursor :=
  ([(2820302411, ⟨Cell.of (offset + 505) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round40After offset).1, offset + 512)
def round41Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round41Action offset) (round40After offset)

def round42Action (offset : Nat) : Build (Compression) :=
  compressionRound (round41Output offset) Synthesis.roundConstants[42]! (scheduleOutput offset)[42]!
def round42Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 517) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 517) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 517) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 517) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 517) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 517) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 517) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 510) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 510) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 503) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 503) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 496) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 518) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 518) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 518) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 518) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 518) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 518) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 518) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 511) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 511) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 504) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 504) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 497) 0 (⟨2⟩ : Column .advice)⟩ }
def round42After (offset : Nat) : Cursor :=
  ([(3259730800, ⟨Cell.of (offset + 512) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round41After offset).1, offset + 519)
def round42Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round42Action offset) (round41After offset)

def round43Action (offset : Nat) : Build (Compression) :=
  compressionRound (round42Output offset) Synthesis.roundConstants[43]! (scheduleOutput offset)[43]!
def round43Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 524) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 524) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 524) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 524) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 524) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 524) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 524) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 517) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 517) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 510) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 510) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 503) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 525) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 525) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 525) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 525) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 525) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 525) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 525) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 518) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 518) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 511) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 511) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 504) 0 (⟨2⟩ : Column .advice)⟩ }
def round43After (offset : Nat) : Cursor :=
  ([(3345764771, ⟨Cell.of (offset + 519) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round42After offset).1, offset + 526)
def round43Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round43Action offset) (round42After offset)

def round44Action (offset : Nat) : Build (Compression) :=
  compressionRound (round43Output offset) Synthesis.roundConstants[44]! (scheduleOutput offset)[44]!
def round44Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 531) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 531) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 531) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 531) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 531) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 531) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 531) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 524) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 524) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 517) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 517) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 510) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 532) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 532) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 532) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 532) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 532) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 532) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 532) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 525) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 525) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 518) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 518) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 511) 0 (⟨2⟩ : Column .advice)⟩ }
def round44After (offset : Nat) : Cursor :=
  ([(3516065817, ⟨Cell.of (offset + 526) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round43After offset).1, offset + 533)
def round44Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round44Action offset) (round43After offset)

def round45Action (offset : Nat) : Build (Compression) :=
  compressionRound (round44Output offset) Synthesis.roundConstants[45]! (scheduleOutput offset)[45]!
def round45Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 538) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 538) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 538) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 538) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 538) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 538) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 538) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 531) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 531) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 524) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 524) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 517) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 539) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 539) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 539) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 539) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 539) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 539) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 539) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 532) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 532) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 525) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 525) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 518) 0 (⟨2⟩ : Column .advice)⟩ }
def round45After (offset : Nat) : Cursor :=
  ([(3600352804, ⟨Cell.of (offset + 533) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round44After offset).1, offset + 540)
def round45Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round45Action offset) (round44After offset)

def round46Action (offset : Nat) : Build (Compression) :=
  compressionRound (round45Output offset) Synthesis.roundConstants[46]! (scheduleOutput offset)[46]!
def round46Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 545) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 545) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 545) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 545) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 545) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 545) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 545) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 538) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 538) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 531) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 531) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 524) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 546) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 546) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 546) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 546) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 546) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 546) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 546) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 539) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 539) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 532) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 532) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 525) 0 (⟨2⟩ : Column .advice)⟩ }
def round46After (offset : Nat) : Cursor :=
  ([(4094571909, ⟨Cell.of (offset + 540) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round45After offset).1, offset + 547)
def round46Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round46Action offset) (round45After offset)

def round47Action (offset : Nat) : Build (Compression) :=
  compressionRound (round46Output offset) Synthesis.roundConstants[47]! (scheduleOutput offset)[47]!
def round47Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 552) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 552) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 552) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 552) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 552) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 552) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 552) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 545) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 545) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 538) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 538) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 531) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 553) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 553) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 553) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 553) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 553) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 553) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 553) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 546) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 546) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 539) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 539) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 532) 0 (⟨2⟩ : Column .advice)⟩ }
def round47After (offset : Nat) : Cursor :=
  ([(275423344, ⟨Cell.of (offset + 547) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round46After offset).1, offset + 554)
def round47Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round47Action offset) (round46After offset)

def round48Action (offset : Nat) : Build (Compression) :=
  compressionRound (round47Output offset) Synthesis.roundConstants[48]! (scheduleOutput offset)[48]!
def round48Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 559) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 559) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 559) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 559) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 559) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 559) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 559) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 552) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 552) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 545) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 545) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 538) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 560) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 560) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 560) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 560) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 560) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 560) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 560) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 553) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 553) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 546) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 546) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 539) 0 (⟨2⟩ : Column .advice)⟩ }
def round48After (offset : Nat) : Cursor :=
  ([(430227734, ⟨Cell.of (offset + 554) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round47After offset).1, offset + 561)
def round48Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round48Action offset) (round47After offset)

def round49Action (offset : Nat) : Build (Compression) :=
  compressionRound (round48Output offset) Synthesis.roundConstants[49]! (scheduleOutput offset)[49]!
def round49Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 566) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 566) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 566) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 566) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 566) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 566) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 566) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 559) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 559) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 552) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 552) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 545) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 567) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 567) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 567) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 567) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 567) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 567) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 567) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 560) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 560) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 553) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 553) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 546) 0 (⟨2⟩ : Column .advice)⟩ }
def round49After (offset : Nat) : Cursor :=
  ([(506948616, ⟨Cell.of (offset + 561) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round48After offset).1, offset + 568)
def round49Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round49Action offset) (round48After offset)

def round50Action (offset : Nat) : Build (Compression) :=
  compressionRound (round49Output offset) Synthesis.roundConstants[50]! (scheduleOutput offset)[50]!
def round50Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 573) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 573) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 573) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 573) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 573) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 573) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 573) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 566) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 566) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 559) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 559) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 552) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 574) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 574) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 574) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 574) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 574) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 574) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 574) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 567) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 567) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 560) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 560) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 553) 0 (⟨2⟩ : Column .advice)⟩ }
def round50After (offset : Nat) : Cursor :=
  ([(659060556, ⟨Cell.of (offset + 568) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round49After offset).1, offset + 575)
def round50Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round50Action offset) (round49After offset)

def round51Action (offset : Nat) : Build (Compression) :=
  compressionRound (round50Output offset) Synthesis.roundConstants[51]! (scheduleOutput offset)[51]!
def round51Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 580) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 580) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 580) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 580) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 580) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 580) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 580) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 573) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 573) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 566) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 566) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 559) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 581) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 581) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 581) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 581) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 581) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 581) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 581) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 574) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 574) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 567) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 567) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 560) 0 (⟨2⟩ : Column .advice)⟩ }
def round51After (offset : Nat) : Cursor :=
  ([(883997877, ⟨Cell.of (offset + 575) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round50After offset).1, offset + 582)
def round51Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round51Action offset) (round50After offset)

def round52Action (offset : Nat) : Build (Compression) :=
  compressionRound (round51Output offset) Synthesis.roundConstants[52]! (scheduleOutput offset)[52]!
def round52Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 587) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 587) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 587) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 587) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 587) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 587) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 587) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 580) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 580) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 573) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 573) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 566) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 588) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 588) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 588) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 588) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 588) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 588) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 588) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 581) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 581) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 574) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 574) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 567) 0 (⟨2⟩ : Column .advice)⟩ }
def round52After (offset : Nat) : Cursor :=
  ([(958139571, ⟨Cell.of (offset + 582) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round51After offset).1, offset + 589)
def round52Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round52Action offset) (round51After offset)

def round53Action (offset : Nat) : Build (Compression) :=
  compressionRound (round52Output offset) Synthesis.roundConstants[53]! (scheduleOutput offset)[53]!
def round53Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 594) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 594) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 594) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 594) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 594) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 594) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 594) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 587) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 587) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 580) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 580) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 573) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 595) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 595) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 595) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 595) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 595) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 595) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 595) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 588) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 588) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 581) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 581) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 574) 0 (⟨2⟩ : Column .advice)⟩ }
def round53After (offset : Nat) : Cursor :=
  ([(1322822218, ⟨Cell.of (offset + 589) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round52After offset).1, offset + 596)
def round53Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round53Action offset) (round52After offset)

def round54Action (offset : Nat) : Build (Compression) :=
  compressionRound (round53Output offset) Synthesis.roundConstants[54]! (scheduleOutput offset)[54]!
def round54Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 601) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 601) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 601) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 601) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 601) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 601) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 601) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 594) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 594) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 587) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 587) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 580) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 602) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 602) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 602) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 602) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 602) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 602) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 602) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 595) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 595) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 588) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 588) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 581) 0 (⟨2⟩ : Column .advice)⟩ }
def round54After (offset : Nat) : Cursor :=
  ([(1537002063, ⟨Cell.of (offset + 596) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round53After offset).1, offset + 603)
def round54Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round54Action offset) (round53After offset)

def round55Action (offset : Nat) : Build (Compression) :=
  compressionRound (round54Output offset) Synthesis.roundConstants[55]! (scheduleOutput offset)[55]!
def round55Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 608) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 608) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 608) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 608) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 608) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 608) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 608) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 601) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 601) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 594) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 594) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 587) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 609) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 609) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 609) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 609) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 609) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 609) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 609) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 602) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 602) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 595) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 595) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 588) 0 (⟨2⟩ : Column .advice)⟩ }
def round55After (offset : Nat) : Cursor :=
  ([(1747873779, ⟨Cell.of (offset + 603) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round54After offset).1, offset + 610)
def round55Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round55Action offset) (round54After offset)

def round56Action (offset : Nat) : Build (Compression) :=
  compressionRound (round55Output offset) Synthesis.roundConstants[56]! (scheduleOutput offset)[56]!
def round56Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 615) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 615) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 615) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 615) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 615) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 615) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 615) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 608) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 608) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 601) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 601) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 594) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 616) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 616) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 616) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 616) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 616) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 616) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 616) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 609) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 609) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 602) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 602) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 595) 0 (⟨2⟩ : Column .advice)⟩ }
def round56After (offset : Nat) : Cursor :=
  ([(1955562222, ⟨Cell.of (offset + 610) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round55After offset).1, offset + 617)
def round56Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round56Action offset) (round55After offset)

def round57Action (offset : Nat) : Build (Compression) :=
  compressionRound (round56Output offset) Synthesis.roundConstants[57]! (scheduleOutput offset)[57]!
def round57Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 622) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 622) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 622) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 622) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 622) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 622) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 622) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 615) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 615) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 608) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 608) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 601) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 623) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 623) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 623) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 623) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 623) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 623) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 623) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 616) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 616) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 609) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 609) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 602) 0 (⟨2⟩ : Column .advice)⟩ }
def round57After (offset : Nat) : Cursor :=
  ([(2024104815, ⟨Cell.of (offset + 617) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round56After offset).1, offset + 624)
def round57Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round57Action offset) (round56After offset)

def round58Action (offset : Nat) : Build (Compression) :=
  compressionRound (round57Output offset) Synthesis.roundConstants[58]! (scheduleOutput offset)[58]!
def round58Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 629) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 629) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 629) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 629) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 629) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 629) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 629) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 622) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 622) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 615) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 615) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 608) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 630) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 630) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 630) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 630) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 630) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 630) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 630) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 623) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 623) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 616) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 616) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 609) 0 (⟨2⟩ : Column .advice)⟩ }
def round58After (offset : Nat) : Cursor :=
  ([(2227730452, ⟨Cell.of (offset + 624) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round57After offset).1, offset + 631)
def round58Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round58Action offset) (round57After offset)

def round59Action (offset : Nat) : Build (Compression) :=
  compressionRound (round58Output offset) Synthesis.roundConstants[59]! (scheduleOutput offset)[59]!
def round59Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 636) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 636) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 636) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 636) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 636) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 636) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 636) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 629) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 629) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 622) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 622) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 615) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 637) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 637) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 637) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 637) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 637) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 637) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 637) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 630) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 630) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 623) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 623) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 616) 0 (⟨2⟩ : Column .advice)⟩ }
def round59After (offset : Nat) : Cursor :=
  ([(2361852424, ⟨Cell.of (offset + 631) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round58After offset).1, offset + 638)
def round59Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round59Action offset) (round58After offset)

def round60Action (offset : Nat) : Build (Compression) :=
  compressionRound (round59Output offset) Synthesis.roundConstants[60]! (scheduleOutput offset)[60]!
def round60Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 643) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 643) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 643) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 643) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 643) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 643) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 643) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 636) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 636) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 629) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 629) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 622) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 644) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 644) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 644) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 644) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 644) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 644) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 644) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 637) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 637) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 630) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 630) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 623) 0 (⟨2⟩ : Column .advice)⟩ }
def round60After (offset : Nat) : Cursor :=
  ([(2428436474, ⟨Cell.of (offset + 638) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round59After offset).1, offset + 645)
def round60Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round60Action offset) (round59After offset)

def round61Action (offset : Nat) : Build (Compression) :=
  compressionRound (round60Output offset) Synthesis.roundConstants[61]! (scheduleOutput offset)[61]!
def round61Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 650) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 650) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 650) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 650) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 650) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 650) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 650) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 643) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 643) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 636) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 636) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 629) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 651) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 651) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 651) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 651) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 651) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 651) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 651) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 644) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 644) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 637) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 637) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 630) 0 (⟨2⟩ : Column .advice)⟩ }
def round61After (offset : Nat) : Cursor :=
  ([(2756734187, ⟨Cell.of (offset + 645) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round60After offset).1, offset + 652)
def round61Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round61Action offset) (round60After offset)

def round62Action (offset : Nat) : Build (Compression) :=
  compressionRound (round61Output offset) Synthesis.roundConstants[62]! (scheduleOutput offset)[62]!
def round62Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 657) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 657) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 657) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 657) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 657) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 657) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 657) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 650) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 650) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 643) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 643) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 636) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 658) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 658) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 658) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 658) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 658) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 658) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 658) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 651) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 651) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 644) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 644) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 637) 0 (⟨2⟩ : Column .advice)⟩ }
def round62After (offset : Nat) : Cursor :=
  ([(3204031479, ⟨Cell.of (offset + 652) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round61After offset).1, offset + 659)
def round62Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round62Action offset) (round61After offset)

def round63Action (offset : Nat) : Build (Compression) :=
  compressionRound (round62Output offset) Synthesis.roundConstants[63]! (scheduleOutput offset)[63]!
def round63Output (offset : Nat) : Compression :=
  { a := { combined := { plain := ⟨Cell.of (offset + 664) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 664) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 664) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 664) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 664) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 664) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 664) 2 (⟨0⟩ : Column .advice)⟩] } }, b := { plain := ⟨Cell.of (offset + 657) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 657) 1 (⟨2⟩ : Column .advice)⟩ }, c := { plain := ⟨Cell.of (offset + 650) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 650) 1 (⟨2⟩ : Column .advice)⟩ }, d := ⟨Cell.of (offset + 643) 0 (⟨2⟩ : Column .advice)⟩, e := { combined := { plain := ⟨Cell.of (offset + 665) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 665) 1 (⟨2⟩ : Column .advice)⟩ }, limbs := { toList := [⟨Cell.of (offset + 665) 0 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 665) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 665) 1 (⟨0⟩ : Column .advice)⟩, ⟨Cell.of (offset + 665) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 665) 2 (⟨0⟩ : Column .advice)⟩] } }, f := { plain := ⟨Cell.of (offset + 658) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 658) 1 (⟨2⟩ : Column .advice)⟩ }, g := { plain := ⟨Cell.of (offset + 651) 0 (⟨2⟩ : Column .advice)⟩, spread := ⟨Cell.of (offset + 651) 1 (⟨2⟩ : Column .advice)⟩ }, h := ⟨Cell.of (offset + 644) 0 (⟨2⟩ : Column .advice)⟩ }
def round63After (offset : Nat) : Cursor :=
  ([(3329325298, ⟨Cell.of (offset + 659) 0 (⟨9⟩ : Column .fixed)⟩)] ++ (round62After offset).1, offset + 666)
def round63Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (round63Action offset) (round62After offset)

def feedforwardAction (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  addStates (initialOutput offset) (round63Output offset)
def feedforwardOutput (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 666) 0 (⟨2⟩ : Column .advice)⟩, ⟨Cell.of (offset + 667) 0 (⟨2⟩ : Column .advice)⟩, ⟨Cell.of (offset + 668) 0 (⟨2⟩ : Column .advice)⟩, ⟨Cell.of (offset + 669) 0 (⟨2⟩ : Column .advice)⟩, ⟨Cell.of (offset + 670) 0 (⟨2⟩ : Column .advice)⟩, ⟨Cell.of (offset + 671) 0 (⟨2⟩ : Column .advice)⟩, ⟨Cell.of (offset + 672) 0 (⟨2⟩ : Column .advice)⟩, ⟨Cell.of (offset + 673) 0 (⟨2⟩ : Column .advice)⟩] }
def feedforwardAfter (offset : Nat) : Cursor :=
  ([] ++ (round63After offset).1, offset + 674)
def feedforwardOperations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (feedforwardAction offset) (round63After offset)

def serialize0Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[0]!
    return (#[]) ++ bytes
def serialize0Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize0After (offset : Nat) : Cursor :=
  ([] ++ (feedforwardAfter offset).1, offset + 676)
def serialize0Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize0Action offset) (feedforwardAfter offset)

def serialize1Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[1]!
    return ((serialize0Output offset)) ++ bytes
def serialize1Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize1After (offset : Nat) : Cursor :=
  ([] ++ (serialize0After offset).1, offset + 678)
def serialize1Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize1Action offset) (serialize0After offset)

def serialize2Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[2]!
    return ((serialize1Output offset)) ++ bytes
def serialize2Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize2After (offset : Nat) : Cursor :=
  ([] ++ (serialize1After offset).1, offset + 680)
def serialize2Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize2Action offset) (serialize1After offset)

def serialize3Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[3]!
    return ((serialize2Output offset)) ++ bytes
def serialize3Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize3After (offset : Nat) : Cursor :=
  ([] ++ (serialize2After offset).1, offset + 682)
def serialize3Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize3Action offset) (serialize2After offset)

def serialize4Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[4]!
    return ((serialize3Output offset)) ++ bytes
def serialize4Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize4After (offset : Nat) : Cursor :=
  ([] ++ (serialize3After offset).1, offset + 684)
def serialize4Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize4Action offset) (serialize3After offset)

def serialize5Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[5]!
    return ((serialize4Output offset)) ++ bytes
def serialize5Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize5After (offset : Nat) : Cursor :=
  ([] ++ (serialize4After offset).1, offset + 686)
def serialize5Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize5Action offset) (serialize4After offset)

def serialize6Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[6]!
    return ((serialize5Output offset)) ++ bytes
def serialize6Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize6After (offset : Nat) : Cursor :=
  ([] ++ (serialize5After offset).1, offset + 688)
def serialize6Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize6Action offset) (serialize5After offset)

def serialize7Action (offset : Nat) : Build (Array WitnessCircuit.Cell) :=
  do
    let bytes ← wordToBytes (feedforwardOutput offset)[7]!
    return ((serialize6Output offset)) ++ bytes
def serialize7Output (offset : Nat) : Array WitnessCircuit.Cell :=
  { toList := [⟨Cell.of (offset + 674) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 674) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 676) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 678) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 680) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 682) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 684) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 686) 0 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 688) 3 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 688) 2 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 688) 1 (⟨1⟩ : Column .advice)⟩, ⟨Cell.of (offset + 688) 0 (⟨1⟩ : Column .advice)⟩] }
def serialize7After (offset : Nat) : Cursor :=
  ([] ++ (serialize6After offset).1, offset + 690)
def serialize7Operations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (serialize7Action offset) (serialize6After offset)

def publicAction (offset : Nat) : Build (Unit) :=
  do
    for i in [:(serialize7Output offset).size] do
      liftM (constrainInstance (serialize7Output offset)[i]! ⟨1⟩ i : Circuit F Unit)
def publicOperations (offset : Nat) : Operations F :=
  Semantics.WitnessCheckpointModel.operations (publicAction offset) (serialize7After offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
