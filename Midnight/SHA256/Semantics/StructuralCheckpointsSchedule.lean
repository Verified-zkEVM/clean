import Midnight.Chips.SynthesisCheckpoint
import Midnight.SHA256.Semantics.StructuralNormalization

/-! GENERATED proof data from Lean source only. Each checkpoint rechecks the actual action for every prior trace. No native capture inputs. -/
namespace Midnight.SHA256.Semantics.StructuralCheckpoints
open Halo2 Chips.SynthesisCheckpoint
set_option Elab.async false
set_option maxRecDepth 10000
attribute [local cbv_opaque] BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing
attribute [local cbv_opaque] Chips.Synthesis.constant Synthesis.blockFromBytes List.map List.append List.concat
attribute [local cbv_eval] StructuralNormalization.blockFromBytes_eq
attribute [local cbv_eval] Reduction.constant_canonical Reduction.cast_val Reduction.beq_val Reduction.zero_val Reduction.one_val
attribute [local cbv_eval] List.map_cons List.map_nil
attribute [local cbv_eval] Midnight.Math.Checkpoint.Reduction.map_append Midnight.Math.Checkpoint.Reduction.nil_append
attribute [local cbv_eval] Midnight.Math.Checkpoint.Reduction.cons_append Midnight.Math.Checkpoint.Reduction.append_nil
attribute [local cbv_eval] Midnight.Math.Checkpoint.Reduction.append_assoc Midnight.Math.Checkpoint.Reduction.concat_append
def beginCursor : Cursor := ⟨0, []⟩

def inputAction : Synthesis.Build (Array Cell) :=
  Synthesis.assignBytes
def inputOutput : Array Cell :=
  { toList := [(Cell.of 0 0 (⟨1⟩ : Column .advice)), (Cell.of 1 0 (⟨1⟩ : Column .advice)), (Cell.of 2 0 (⟨1⟩ : Column .advice)), (Cell.of 3 0 (⟨1⟩ : Column .advice)), (Cell.of 4 0 (⟨1⟩ : Column .advice)), (Cell.of 5 0 (⟨1⟩ : Column .advice)), (Cell.of 6 0 (⟨1⟩ : Column .advice)), (Cell.of 7 0 (⟨1⟩ : Column .advice)), (Cell.of 8 0 (⟨1⟩ : Column .advice)), (Cell.of 9 0 (⟨1⟩ : Column .advice)), (Cell.of 10 0 (⟨1⟩ : Column .advice)), (Cell.of 11 0 (⟨1⟩ : Column .advice)), (Cell.of 12 0 (⟨1⟩ : Column .advice)), (Cell.of 13 0 (⟨1⟩ : Column .advice)), (Cell.of 14 0 (⟨1⟩ : Column .advice)), (Cell.of 15 0 (⟨1⟩ : Column .advice)), (Cell.of 16 0 (⟨1⟩ : Column .advice)), (Cell.of 17 0 (⟨1⟩ : Column .advice)), (Cell.of 18 0 (⟨1⟩ : Column .advice)), (Cell.of 19 0 (⟨1⟩ : Column .advice)), (Cell.of 20 0 (⟨1⟩ : Column .advice)), (Cell.of 21 0 (⟨1⟩ : Column .advice)), (Cell.of 22 0 (⟨1⟩ : Column .advice)), (Cell.of 23 0 (⟨1⟩ : Column .advice))] }
def inputAfter : Cursor :=
  ⟨24, [] ++ beginCursor.constants⟩
def inputChunk : List Step :=
  [.region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0],
  .region "assign_many_small" [.selector 3 0, .fixed 10 0, .advice 1 0]]
theorem inputChecked : Checkpoint inputAction beginCursor inputOutput inputAfter inputChunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def initialAction : Synthesis.Build (Synthesis.Compression) :=
  Synthesis.initialState
def initialOutput : Synthesis.Compression :=
  { a := { combined := { plain := (Cell.of 24 0 (⟨9⟩ : Column .fixed)), spread := (Cell.of 25 0 (⟨9⟩ : Column .fixed)) }, limbs := { toList := [(Cell.of 26 0 (⟨9⟩ : Column .fixed)), (Cell.of 27 0 (⟨9⟩ : Column .fixed)), (Cell.of 28 0 (⟨9⟩ : Column .fixed)), (Cell.of 29 0 (⟨9⟩ : Column .fixed))] } }, b := { plain := (Cell.of 30 0 (⟨9⟩ : Column .fixed)), spread := (Cell.of 31 0 (⟨9⟩ : Column .fixed)) }, c := { plain := (Cell.of 32 0 (⟨9⟩ : Column .fixed)), spread := (Cell.of 33 0 (⟨9⟩ : Column .fixed)) }, d := (Cell.of 34 0 (⟨9⟩ : Column .fixed)), e := { combined := { plain := (Cell.of 35 0 (⟨9⟩ : Column .fixed)), spread := (Cell.of 36 0 (⟨9⟩ : Column .fixed)) }, limbs := { toList := [(Cell.of 37 0 (⟨9⟩ : Column .fixed)), (Cell.of 38 0 (⟨9⟩ : Column .fixed)), (Cell.of 39 0 (⟨9⟩ : Column .fixed)), (Cell.of 40 0 (⟨9⟩ : Column .fixed)), (Cell.of 41 0 (⟨9⟩ : Column .fixed))] } }, f := { plain := (Cell.of 42 0 (⟨9⟩ : Column .fixed)), spread := (Cell.of 43 0 (⟨9⟩ : Column .fixed)) }, g := { plain := (Cell.of 44 0 (⟨9⟩ : Column .fixed)), spread := (Cell.of 45 0 (⟨9⟩ : Column .fixed)) }, h := (Cell.of 46 0 (⟨9⟩ : Column .fixed)) }
def initialAfter : Cursor :=
  ⟨47, [(1541459225, (Cell.of 46 0 (⟨9⟩ : Column .fixed))), (96053358640579653, (Cell.of 45 0 (⟨9⟩ : Column .fixed))), (528734635, (Cell.of 44 0 (⟨9⟩ : Column .fixed))), (4703165459212550224, (Cell.of 43 0 (⟨9⟩ : Column .fixed))), (2600822924, (Cell.of 42 0 (⟨9⟩ : Column .fixed))), (1365, (Cell.of 41 0 (⟨9⟩ : Column .fixed))), (65, (Cell.of 40 0 (⟨9⟩ : Column .fixed))), (4, (Cell.of 39 0 (⟨9⟩ : Column .fixed))), (4199684, (Cell.of 38 0 (⟨9⟩ : Column .fixed))), (1088, (Cell.of 37 0 (⟨9⟩ : Column .fixed))), (1225260934684218709, (Cell.of 36 0 (⟨9⟩ : Column .fixed))), (1359893119, (Cell.of 35 0 (⟨9⟩ : Column .fixed))), (2773480762, (Cell.of 34 0 (⟨9⟩ : Column .fixed))), (382828320762696964, (Cell.of 33 0 (⟨9⟩ : Column .fixed))), (1013904242, (Cell.of 32 0 (⟨9⟩ : Column .fixed))), (4991417843583303697, (Cell.of 31 0 (⟨9⟩ : Column .fixed))), (3144134277, (Cell.of 30 0 (⟨9⟩ : Column .fixed))), (5, (Cell.of 29 0 (⟨9⟩ : Column .fixed))), (82241, (Cell.of 28 0 (⟨9⟩ : Column .fixed))), (4181, (Cell.of 27 0 (⟨9⟩ : Column .fixed))), (83008, (Cell.of 26 0 (⟨9⟩ : Column .fixed))), (1460292459758359573, (Cell.of 25 0 (⟨9⟩ : Column .fixed))), (1779033703, (Cell.of 24 0 (⟨9⟩ : Column .fixed)))] ++ inputAfter.constants⟩
def initialChunk : List Step :=
  [.region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0]]
theorem initialChecked : Checkpoint initialAction inputAfter initialOutput initialAfter initialChunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def paddingAction : Synthesis.Build (Array Cell) :=
  Synthesis.pad inputOutput
def paddingOutput : Array Cell :=
  { toList := [(Cell.of 0 0 (⟨1⟩ : Column .advice)), (Cell.of 1 0 (⟨1⟩ : Column .advice)), (Cell.of 2 0 (⟨1⟩ : Column .advice)), (Cell.of 3 0 (⟨1⟩ : Column .advice)), (Cell.of 4 0 (⟨1⟩ : Column .advice)), (Cell.of 5 0 (⟨1⟩ : Column .advice)), (Cell.of 6 0 (⟨1⟩ : Column .advice)), (Cell.of 7 0 (⟨1⟩ : Column .advice)), (Cell.of 8 0 (⟨1⟩ : Column .advice)), (Cell.of 9 0 (⟨1⟩ : Column .advice)), (Cell.of 10 0 (⟨1⟩ : Column .advice)), (Cell.of 11 0 (⟨1⟩ : Column .advice)), (Cell.of 12 0 (⟨1⟩ : Column .advice)), (Cell.of 13 0 (⟨1⟩ : Column .advice)), (Cell.of 14 0 (⟨1⟩ : Column .advice)), (Cell.of 15 0 (⟨1⟩ : Column .advice)), (Cell.of 16 0 (⟨1⟩ : Column .advice)), (Cell.of 17 0 (⟨1⟩ : Column .advice)), (Cell.of 18 0 (⟨1⟩ : Column .advice)), (Cell.of 19 0 (⟨1⟩ : Column .advice)), (Cell.of 20 0 (⟨1⟩ : Column .advice)), (Cell.of 21 0 (⟨1⟩ : Column .advice)), (Cell.of 22 0 (⟨1⟩ : Column .advice)), (Cell.of 23 0 (⟨1⟩ : Column .advice)), (Cell.of 47 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 49 0 (⟨9⟩ : Column .fixed))] }
def paddingAfter : Cursor :=
  ⟨50, [(192, (Cell.of 49 0 (⟨9⟩ : Column .fixed))), (0, (Cell.of 48 0 (⟨9⟩ : Column .fixed))), (128, (Cell.of 47 0 (⟨9⟩ : Column .fixed)))] ++ initialAfter.constants⟩
def paddingChunk : List Step :=
  [.region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0],
  .region "Assign fixed" [.fixed 9 0]]
theorem paddingChecked : Checkpoint paddingAction initialAfter paddingOutput paddingAfter paddingChunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def packingAction : Synthesis.Build (Array Cell) :=
  Synthesis.blockFromBytes paddingOutput
def packingOutput : Array Cell :=
  { toList := [(Cell.of 50 0 (⟨0⟩ : Column .advice)), (Cell.of 51 0 (⟨0⟩ : Column .advice)), (Cell.of 52 0 (⟨0⟩ : Column .advice)), (Cell.of 53 0 (⟨0⟩ : Column .advice)), (Cell.of 54 0 (⟨0⟩ : Column .advice)), (Cell.of 55 0 (⟨0⟩ : Column .advice)), (Cell.of 56 0 (⟨0⟩ : Column .advice)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 48 0 (⟨9⟩ : Column .fixed)), (Cell.of 49 0 (⟨9⟩ : Column .fixed))] }
def packingAfter : Cursor :=
  ⟨57, [] ++ paddingAfter.constants⟩
def packingChunk : List Step :=
  [.region "Linear combination" [.advice 0 0, .advice 1 0, .advice 2 0, .advice 3 0, .advice 4 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .copy (Cell.of 50 0 (⟨1⟩ : Column .advice)) (Cell.of 3 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 50 0 (⟨2⟩ : Column .advice)) (Cell.of 2 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 50 0 (⟨3⟩ : Column .advice)) (Cell.of 1 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 50 0 (⟨4⟩ : Column .advice)) (Cell.of 0 0 (⟨1⟩ : Column .advice))],
  .region "Linear combination" [.advice 0 0, .advice 1 0, .advice 2 0, .advice 3 0, .advice 4 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .copy (Cell.of 51 0 (⟨1⟩ : Column .advice)) (Cell.of 7 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 51 0 (⟨2⟩ : Column .advice)) (Cell.of 6 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 51 0 (⟨3⟩ : Column .advice)) (Cell.of 5 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 51 0 (⟨4⟩ : Column .advice)) (Cell.of 4 0 (⟨1⟩ : Column .advice))],
  .region "Linear combination" [.advice 0 0, .advice 1 0, .advice 2 0, .advice 3 0, .advice 4 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .copy (Cell.of 52 0 (⟨1⟩ : Column .advice)) (Cell.of 11 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 52 0 (⟨2⟩ : Column .advice)) (Cell.of 10 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 52 0 (⟨3⟩ : Column .advice)) (Cell.of 9 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 52 0 (⟨4⟩ : Column .advice)) (Cell.of 8 0 (⟨1⟩ : Column .advice))],
  .region "Linear combination" [.advice 0 0, .advice 1 0, .advice 2 0, .advice 3 0, .advice 4 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .copy (Cell.of 53 0 (⟨1⟩ : Column .advice)) (Cell.of 15 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 53 0 (⟨2⟩ : Column .advice)) (Cell.of 14 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 53 0 (⟨3⟩ : Column .advice)) (Cell.of 13 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 53 0 (⟨4⟩ : Column .advice)) (Cell.of 12 0 (⟨1⟩ : Column .advice))],
  .region "Linear combination" [.advice 0 0, .advice 1 0, .advice 2 0, .advice 3 0, .advice 4 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .copy (Cell.of 54 0 (⟨1⟩ : Column .advice)) (Cell.of 19 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 54 0 (⟨2⟩ : Column .advice)) (Cell.of 18 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 54 0 (⟨3⟩ : Column .advice)) (Cell.of 17 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 54 0 (⟨4⟩ : Column .advice)) (Cell.of 16 0 (⟨1⟩ : Column .advice))],
  .region "Linear combination" [.advice 0 0, .advice 1 0, .advice 2 0, .advice 3 0, .advice 4 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .copy (Cell.of 55 0 (⟨1⟩ : Column .advice)) (Cell.of 23 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 55 0 (⟨2⟩ : Column .advice)) (Cell.of 22 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 55 0 (⟨3⟩ : Column .advice)) (Cell.of 21 0 (⟨1⟩ : Column .advice)), .copy (Cell.of 55 0 (⟨4⟩ : Column .advice)) (Cell.of 20 0 (⟨1⟩ : Column .advice))],
  .region "Linear combination" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .copy (Cell.of 56 0 (⟨1⟩ : Column .advice)) (Cell.of 47 0 (⟨9⟩ : Column .fixed))]]
theorem packingChecked : Checkpoint packingAction paddingAfter packingOutput packingAfter packingChunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare0Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[0]!]
    return (#[]).push w
def prepare0Output : Array Synthesis.Word :=
  (#[]).push ({ combined := { plain := (Cell.of 57 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 57 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 57 0 (⟨0⟩ : Column .advice)), (Cell.of 57 0 (⟨5⟩ : Column .advice)), (Cell.of 57 1 (⟨5⟩ : Column .advice)), (Cell.of 57 2 (⟨5⟩ : Column .advice)), (Cell.of 57 0 (⟨1⟩ : Column .advice)), (Cell.of 57 1 (⟨0⟩ : Column .advice)), (Cell.of 57 1 (⟨1⟩ : Column .advice)), (Cell.of 57 2 (⟨0⟩ : Column .advice))] } })
def prepare0After : Cursor :=
  ⟨58, [] ++ packingAfter.constants⟩
def prepare0Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 57 0 (⟨3⟩ : Column .advice)) (Cell.of 50 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 57 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 57 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 57 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 57 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 57 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 57 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare0Checked : Checkpoint prepare0Action packingAfter prepare0Output prepare0After prepare0Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare1Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[1]!]
    return (prepare0Output).push w
def prepare1Output : Array Synthesis.Word :=
  (prepare0Output).push ({ combined := { plain := (Cell.of 58 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 58 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 58 0 (⟨0⟩ : Column .advice)), (Cell.of 58 0 (⟨5⟩ : Column .advice)), (Cell.of 58 1 (⟨5⟩ : Column .advice)), (Cell.of 58 2 (⟨5⟩ : Column .advice)), (Cell.of 58 0 (⟨1⟩ : Column .advice)), (Cell.of 58 1 (⟨0⟩ : Column .advice)), (Cell.of 58 1 (⟨1⟩ : Column .advice)), (Cell.of 58 2 (⟨0⟩ : Column .advice))] } })
def prepare1After : Cursor :=
  ⟨59, [] ++ prepare0After.constants⟩
def prepare1Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 58 0 (⟨3⟩ : Column .advice)) (Cell.of 51 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 58 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 58 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 58 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 58 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 58 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 58 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare1Checked : Checkpoint prepare1Action prepare0After prepare1Output prepare1After prepare1Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare2Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[2]!]
    return (prepare1Output).push w
def prepare2Output : Array Synthesis.Word :=
  (prepare1Output).push ({ combined := { plain := (Cell.of 59 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 59 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 59 0 (⟨0⟩ : Column .advice)), (Cell.of 59 0 (⟨5⟩ : Column .advice)), (Cell.of 59 1 (⟨5⟩ : Column .advice)), (Cell.of 59 2 (⟨5⟩ : Column .advice)), (Cell.of 59 0 (⟨1⟩ : Column .advice)), (Cell.of 59 1 (⟨0⟩ : Column .advice)), (Cell.of 59 1 (⟨1⟩ : Column .advice)), (Cell.of 59 2 (⟨0⟩ : Column .advice))] } })
def prepare2After : Cursor :=
  ⟨60, [] ++ prepare1After.constants⟩
def prepare2Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 59 0 (⟨3⟩ : Column .advice)) (Cell.of 52 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 59 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 59 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 59 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 59 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 59 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 59 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare2Checked : Checkpoint prepare2Action prepare1After prepare2Output prepare2After prepare2Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare3Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[3]!]
    return (prepare2Output).push w
def prepare3Output : Array Synthesis.Word :=
  (prepare2Output).push ({ combined := { plain := (Cell.of 60 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 60 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 60 0 (⟨0⟩ : Column .advice)), (Cell.of 60 0 (⟨5⟩ : Column .advice)), (Cell.of 60 1 (⟨5⟩ : Column .advice)), (Cell.of 60 2 (⟨5⟩ : Column .advice)), (Cell.of 60 0 (⟨1⟩ : Column .advice)), (Cell.of 60 1 (⟨0⟩ : Column .advice)), (Cell.of 60 1 (⟨1⟩ : Column .advice)), (Cell.of 60 2 (⟨0⟩ : Column .advice))] } })
def prepare3After : Cursor :=
  ⟨61, [] ++ prepare2After.constants⟩
def prepare3Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 60 0 (⟨3⟩ : Column .advice)) (Cell.of 53 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 60 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 60 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 60 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 60 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 60 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 60 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare3Checked : Checkpoint prepare3Action prepare2After prepare3Output prepare3After prepare3Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare4Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[4]!]
    return (prepare3Output).push w
def prepare4Output : Array Synthesis.Word :=
  (prepare3Output).push ({ combined := { plain := (Cell.of 61 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 61 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 61 0 (⟨0⟩ : Column .advice)), (Cell.of 61 0 (⟨5⟩ : Column .advice)), (Cell.of 61 1 (⟨5⟩ : Column .advice)), (Cell.of 61 2 (⟨5⟩ : Column .advice)), (Cell.of 61 0 (⟨1⟩ : Column .advice)), (Cell.of 61 1 (⟨0⟩ : Column .advice)), (Cell.of 61 1 (⟨1⟩ : Column .advice)), (Cell.of 61 2 (⟨0⟩ : Column .advice))] } })
def prepare4After : Cursor :=
  ⟨62, [] ++ prepare3After.constants⟩
def prepare4Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 61 0 (⟨3⟩ : Column .advice)) (Cell.of 54 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 61 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 61 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 61 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 61 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 61 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 61 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare4Checked : Checkpoint prepare4Action prepare3After prepare4Output prepare4After prepare4Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare5Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[5]!]
    return (prepare4Output).push w
def prepare5Output : Array Synthesis.Word :=
  (prepare4Output).push ({ combined := { plain := (Cell.of 62 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 62 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 62 0 (⟨0⟩ : Column .advice)), (Cell.of 62 0 (⟨5⟩ : Column .advice)), (Cell.of 62 1 (⟨5⟩ : Column .advice)), (Cell.of 62 2 (⟨5⟩ : Column .advice)), (Cell.of 62 0 (⟨1⟩ : Column .advice)), (Cell.of 62 1 (⟨0⟩ : Column .advice)), (Cell.of 62 1 (⟨1⟩ : Column .advice)), (Cell.of 62 2 (⟨0⟩ : Column .advice))] } })
def prepare5After : Cursor :=
  ⟨63, [] ++ prepare4After.constants⟩
def prepare5Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 62 0 (⟨3⟩ : Column .advice)) (Cell.of 55 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 62 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 62 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 62 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 62 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 62 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 62 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare5Checked : Checkpoint prepare5Action prepare4After prepare5Output prepare5After prepare5Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare6Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[6]!]
    return (prepare5Output).push w
def prepare6Output : Array Synthesis.Word :=
  (prepare5Output).push ({ combined := { plain := (Cell.of 63 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 63 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 63 0 (⟨0⟩ : Column .advice)), (Cell.of 63 0 (⟨5⟩ : Column .advice)), (Cell.of 63 1 (⟨5⟩ : Column .advice)), (Cell.of 63 2 (⟨5⟩ : Column .advice)), (Cell.of 63 0 (⟨1⟩ : Column .advice)), (Cell.of 63 1 (⟨0⟩ : Column .advice)), (Cell.of 63 1 (⟨1⟩ : Column .advice)), (Cell.of 63 2 (⟨0⟩ : Column .advice))] } })
def prepare6After : Cursor :=
  ⟨64, [] ++ prepare5After.constants⟩
def prepare6Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 63 0 (⟨3⟩ : Column .advice)) (Cell.of 56 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 63 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 63 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 63 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 63 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 63 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 63 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare6Checked : Checkpoint prepare6Action prepare5After prepare6Output prepare6After prepare6Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare7Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[7]!]
    return (prepare6Output).push w
def prepare7Output : Array Synthesis.Word :=
  (prepare6Output).push ({ combined := { plain := (Cell.of 64 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 64 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 64 0 (⟨0⟩ : Column .advice)), (Cell.of 64 0 (⟨5⟩ : Column .advice)), (Cell.of 64 1 (⟨5⟩ : Column .advice)), (Cell.of 64 2 (⟨5⟩ : Column .advice)), (Cell.of 64 0 (⟨1⟩ : Column .advice)), (Cell.of 64 1 (⟨0⟩ : Column .advice)), (Cell.of 64 1 (⟨1⟩ : Column .advice)), (Cell.of 64 2 (⟨0⟩ : Column .advice))] } })
def prepare7After : Cursor :=
  ⟨65, [] ++ prepare6After.constants⟩
def prepare7Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 64 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 64 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 64 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 64 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 64 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 64 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 64 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare7Checked : Checkpoint prepare7Action prepare6After prepare7Output prepare7After prepare7Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare8Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[8]!]
    return (prepare7Output).push w
def prepare8Output : Array Synthesis.Word :=
  (prepare7Output).push ({ combined := { plain := (Cell.of 65 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 65 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 65 0 (⟨0⟩ : Column .advice)), (Cell.of 65 0 (⟨5⟩ : Column .advice)), (Cell.of 65 1 (⟨5⟩ : Column .advice)), (Cell.of 65 2 (⟨5⟩ : Column .advice)), (Cell.of 65 0 (⟨1⟩ : Column .advice)), (Cell.of 65 1 (⟨0⟩ : Column .advice)), (Cell.of 65 1 (⟨1⟩ : Column .advice)), (Cell.of 65 2 (⟨0⟩ : Column .advice))] } })
def prepare8After : Cursor :=
  ⟨66, [] ++ prepare7After.constants⟩
def prepare8Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 65 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 65 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 65 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 65 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 65 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 65 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 65 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare8Checked : Checkpoint prepare8Action prepare7After prepare8Output prepare8After prepare8Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare9Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[9]!]
    return (prepare8Output).push w
def prepare9Output : Array Synthesis.Word :=
  (prepare8Output).push ({ combined := { plain := (Cell.of 66 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 66 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 66 0 (⟨0⟩ : Column .advice)), (Cell.of 66 0 (⟨5⟩ : Column .advice)), (Cell.of 66 1 (⟨5⟩ : Column .advice)), (Cell.of 66 2 (⟨5⟩ : Column .advice)), (Cell.of 66 0 (⟨1⟩ : Column .advice)), (Cell.of 66 1 (⟨0⟩ : Column .advice)), (Cell.of 66 1 (⟨1⟩ : Column .advice)), (Cell.of 66 2 (⟨0⟩ : Column .advice))] } })
def prepare9After : Cursor :=
  ⟨67, [] ++ prepare8After.constants⟩
def prepare9Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 66 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 66 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 66 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 66 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 66 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 66 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 66 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare9Checked : Checkpoint prepare9Action prepare8After prepare9Output prepare9After prepare9Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare10Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[10]!]
    return (prepare9Output).push w
def prepare10Output : Array Synthesis.Word :=
  (prepare9Output).push ({ combined := { plain := (Cell.of 67 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 67 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 67 0 (⟨0⟩ : Column .advice)), (Cell.of 67 0 (⟨5⟩ : Column .advice)), (Cell.of 67 1 (⟨5⟩ : Column .advice)), (Cell.of 67 2 (⟨5⟩ : Column .advice)), (Cell.of 67 0 (⟨1⟩ : Column .advice)), (Cell.of 67 1 (⟨0⟩ : Column .advice)), (Cell.of 67 1 (⟨1⟩ : Column .advice)), (Cell.of 67 2 (⟨0⟩ : Column .advice))] } })
def prepare10After : Cursor :=
  ⟨68, [] ++ prepare9After.constants⟩
def prepare10Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 67 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 67 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 67 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 67 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 67 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 67 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 67 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare10Checked : Checkpoint prepare10Action prepare9After prepare10Output prepare10After prepare10Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare11Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[11]!]
    return (prepare10Output).push w
def prepare11Output : Array Synthesis.Word :=
  (prepare10Output).push ({ combined := { plain := (Cell.of 68 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 68 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 68 0 (⟨0⟩ : Column .advice)), (Cell.of 68 0 (⟨5⟩ : Column .advice)), (Cell.of 68 1 (⟨5⟩ : Column .advice)), (Cell.of 68 2 (⟨5⟩ : Column .advice)), (Cell.of 68 0 (⟨1⟩ : Column .advice)), (Cell.of 68 1 (⟨0⟩ : Column .advice)), (Cell.of 68 1 (⟨1⟩ : Column .advice)), (Cell.of 68 2 (⟨0⟩ : Column .advice))] } })
def prepare11After : Cursor :=
  ⟨69, [] ++ prepare10After.constants⟩
def prepare11Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 68 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 68 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 68 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 68 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 68 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 68 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 68 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare11Checked : Checkpoint prepare11Action prepare10After prepare11Output prepare11After prepare11Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare12Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[12]!]
    return (prepare11Output).push w
def prepare12Output : Array Synthesis.Word :=
  (prepare11Output).push ({ combined := { plain := (Cell.of 69 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 69 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 69 0 (⟨0⟩ : Column .advice)), (Cell.of 69 0 (⟨5⟩ : Column .advice)), (Cell.of 69 1 (⟨5⟩ : Column .advice)), (Cell.of 69 2 (⟨5⟩ : Column .advice)), (Cell.of 69 0 (⟨1⟩ : Column .advice)), (Cell.of 69 1 (⟨0⟩ : Column .advice)), (Cell.of 69 1 (⟨1⟩ : Column .advice)), (Cell.of 69 2 (⟨0⟩ : Column .advice))] } })
def prepare12After : Cursor :=
  ⟨70, [] ++ prepare11After.constants⟩
def prepare12Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 69 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 69 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 69 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 69 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 69 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 69 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 69 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare12Checked : Checkpoint prepare12Action prepare11After prepare12Output prepare12After prepare12Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare13Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[13]!]
    return (prepare12Output).push w
def prepare13Output : Array Synthesis.Word :=
  (prepare12Output).push ({ combined := { plain := (Cell.of 70 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 70 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 70 0 (⟨0⟩ : Column .advice)), (Cell.of 70 0 (⟨5⟩ : Column .advice)), (Cell.of 70 1 (⟨5⟩ : Column .advice)), (Cell.of 70 2 (⟨5⟩ : Column .advice)), (Cell.of 70 0 (⟨1⟩ : Column .advice)), (Cell.of 70 1 (⟨0⟩ : Column .advice)), (Cell.of 70 1 (⟨1⟩ : Column .advice)), (Cell.of 70 2 (⟨0⟩ : Column .advice))] } })
def prepare13After : Cursor :=
  ⟨71, [] ++ prepare12After.constants⟩
def prepare13Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 70 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 70 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 70 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 70 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 70 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 70 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 70 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare13Checked : Checkpoint prepare13Action prepare12After prepare13Output prepare13After prepare13Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare14Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[14]!]
    return (prepare13Output).push w
def prepare14Output : Array Synthesis.Word :=
  (prepare13Output).push ({ combined := { plain := (Cell.of 71 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 71 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 71 0 (⟨0⟩ : Column .advice)), (Cell.of 71 0 (⟨5⟩ : Column .advice)), (Cell.of 71 1 (⟨5⟩ : Column .advice)), (Cell.of 71 2 (⟨5⟩ : Column .advice)), (Cell.of 71 0 (⟨1⟩ : Column .advice)), (Cell.of 71 1 (⟨0⟩ : Column .advice)), (Cell.of 71 1 (⟨1⟩ : Column .advice)), (Cell.of 71 2 (⟨0⟩ : Column .advice))] } })
def prepare14After : Cursor :=
  ⟨72, [] ++ prepare13After.constants⟩
def prepare14Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 71 0 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 71 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 71 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 71 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 71 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 71 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 71 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare14Checked : Checkpoint prepare14Action prepare13After prepare14Output prepare14After prepare14Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def prepare15Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let w ← Synthesis.prepareMessage #[packingOutput[15]!]
    return (prepare14Output).push w
def prepare15Output : Array Synthesis.Word :=
  (prepare14Output).push ({ combined := { plain := (Cell.of 72 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 72 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 72 0 (⟨0⟩ : Column .advice)), (Cell.of 72 0 (⟨5⟩ : Column .advice)), (Cell.of 72 1 (⟨5⟩ : Column .advice)), (Cell.of 72 2 (⟨5⟩ : Column .advice)), (Cell.of 72 0 (⟨1⟩ : Column .advice)), (Cell.of 72 1 (⟨0⟩ : Column .advice)), (Cell.of 72 1 (⟨1⟩ : Column .advice)), (Cell.of 72 2 (⟨0⟩ : Column .advice))] } })
def prepare15After : Cursor :=
  ⟨73, [] ++ prepare14After.constants⟩
def prepare15Chunk : List Step :=
  [.region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 72 0 (⟨3⟩ : Column .advice)) (Cell.of 49 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 72 0 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 1, .copy (Cell.of 72 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 72 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 72 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 72 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 72 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem prepare15Checked : Checkpoint prepare15Action prepare14After prepare15Output prepare15After prepare15Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def expand16Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 prepare15Output[1]!
    let s1 ← Synthesis.sigma1 prepare15Output[14]!
    let w ← Synthesis.prepareMessage #[prepare15Output[0]!.combined.plain, prepare15Output[9]!.combined.plain, s0, s1]
    return prepare15Output.push w
def expand16Output : Array Synthesis.Word :=
  (prepare15Output).push ({ combined := { plain := (Cell.of 75 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 75 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 75 0 (⟨0⟩ : Column .advice)), (Cell.of 75 0 (⟨5⟩ : Column .advice)), (Cell.of 75 1 (⟨5⟩ : Column .advice)), (Cell.of 75 2 (⟨5⟩ : Column .advice)), (Cell.of 75 0 (⟨1⟩ : Column .advice)), (Cell.of 75 1 (⟨0⟩ : Column .advice)), (Cell.of 75 1 (⟨1⟩ : Column .advice)), (Cell.of 75 2 (⟨0⟩ : Column .advice))] } })
def expand16After : Cursor :=
  ⟨76, [] ++ prepare15After.constants⟩
def expand16Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 73 0 (⟨3⟩ : Column .advice)) (Cell.of 58 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 73 0 (⟨4⟩ : Column .advice)) (Cell.of 58 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 73 1 (⟨2⟩ : Column .advice)) (Cell.of 58 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 73 1 (⟨3⟩ : Column .advice)) (Cell.of 58 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 73 1 (⟨4⟩ : Column .advice)) (Cell.of 58 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 73 2 (⟨2⟩ : Column .advice)) (Cell.of 58 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 73 2 (⟨3⟩ : Column .advice)) (Cell.of 58 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 73 2 (⟨4⟩ : Column .advice)) (Cell.of 58 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 74 0 (⟨3⟩ : Column .advice)) (Cell.of 71 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 74 0 (⟨4⟩ : Column .advice)) (Cell.of 71 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 74 1 (⟨2⟩ : Column .advice)) (Cell.of 71 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 74 1 (⟨3⟩ : Column .advice)) (Cell.of 71 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 74 1 (⟨4⟩ : Column .advice)) (Cell.of 71 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 74 2 (⟨2⟩ : Column .advice)) (Cell.of 71 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 74 2 (⟨3⟩ : Column .advice)) (Cell.of 71 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 74 2 (⟨4⟩ : Column .advice)) (Cell.of 71 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 75 0 (⟨3⟩ : Column .advice)) (Cell.of 57 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 75 0 (⟨4⟩ : Column .advice)) (Cell.of 66 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 75 1 (⟨3⟩ : Column .advice)) (Cell.of 73 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 75 1 (⟨4⟩ : Column .advice)) (Cell.of 74 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 75 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 75 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 75 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand16Checked : Checkpoint expand16Action prepare15After expand16Output expand16After expand16Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand16Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand17Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand16Output[2]!
    let s1 ← Synthesis.sigma1 expand16Output[15]!
    let w ← Synthesis.prepareMessage #[expand16Output[1]!.combined.plain, expand16Output[10]!.combined.plain, s0, s1]
    return expand16Output.push w
def expand17Output : Array Synthesis.Word :=
  (expand16Output).push ({ combined := { plain := (Cell.of 78 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 78 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 78 0 (⟨0⟩ : Column .advice)), (Cell.of 78 0 (⟨5⟩ : Column .advice)), (Cell.of 78 1 (⟨5⟩ : Column .advice)), (Cell.of 78 2 (⟨5⟩ : Column .advice)), (Cell.of 78 0 (⟨1⟩ : Column .advice)), (Cell.of 78 1 (⟨0⟩ : Column .advice)), (Cell.of 78 1 (⟨1⟩ : Column .advice)), (Cell.of 78 2 (⟨0⟩ : Column .advice))] } })
def expand17After : Cursor :=
  ⟨79, [] ++ expand16After.constants⟩
def expand17Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 76 0 (⟨3⟩ : Column .advice)) (Cell.of 59 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 76 0 (⟨4⟩ : Column .advice)) (Cell.of 59 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 76 1 (⟨2⟩ : Column .advice)) (Cell.of 59 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 76 1 (⟨3⟩ : Column .advice)) (Cell.of 59 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 76 1 (⟨4⟩ : Column .advice)) (Cell.of 59 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 76 2 (⟨2⟩ : Column .advice)) (Cell.of 59 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 76 2 (⟨3⟩ : Column .advice)) (Cell.of 59 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 76 2 (⟨4⟩ : Column .advice)) (Cell.of 59 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 77 0 (⟨3⟩ : Column .advice)) (Cell.of 72 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 77 0 (⟨4⟩ : Column .advice)) (Cell.of 72 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 77 1 (⟨2⟩ : Column .advice)) (Cell.of 72 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 77 1 (⟨3⟩ : Column .advice)) (Cell.of 72 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 77 1 (⟨4⟩ : Column .advice)) (Cell.of 72 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 77 2 (⟨2⟩ : Column .advice)) (Cell.of 72 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 77 2 (⟨3⟩ : Column .advice)) (Cell.of 72 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 77 2 (⟨4⟩ : Column .advice)) (Cell.of 72 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 78 0 (⟨3⟩ : Column .advice)) (Cell.of 58 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 78 0 (⟨4⟩ : Column .advice)) (Cell.of 67 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 78 1 (⟨3⟩ : Column .advice)) (Cell.of 76 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 78 1 (⟨4⟩ : Column .advice)) (Cell.of 77 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 78 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 78 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 78 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand17Checked : Checkpoint expand17Action expand16After expand17Output expand17After expand17Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand17Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand18Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand17Output[3]!
    let s1 ← Synthesis.sigma1 expand17Output[16]!
    let w ← Synthesis.prepareMessage #[expand17Output[2]!.combined.plain, expand17Output[11]!.combined.plain, s0, s1]
    return expand17Output.push w
def expand18Output : Array Synthesis.Word :=
  (expand17Output).push ({ combined := { plain := (Cell.of 81 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 81 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 81 0 (⟨0⟩ : Column .advice)), (Cell.of 81 0 (⟨5⟩ : Column .advice)), (Cell.of 81 1 (⟨5⟩ : Column .advice)), (Cell.of 81 2 (⟨5⟩ : Column .advice)), (Cell.of 81 0 (⟨1⟩ : Column .advice)), (Cell.of 81 1 (⟨0⟩ : Column .advice)), (Cell.of 81 1 (⟨1⟩ : Column .advice)), (Cell.of 81 2 (⟨0⟩ : Column .advice))] } })
def expand18After : Cursor :=
  ⟨82, [] ++ expand17After.constants⟩
def expand18Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 79 0 (⟨3⟩ : Column .advice)) (Cell.of 60 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 79 0 (⟨4⟩ : Column .advice)) (Cell.of 60 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 79 1 (⟨2⟩ : Column .advice)) (Cell.of 60 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 79 1 (⟨3⟩ : Column .advice)) (Cell.of 60 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 79 1 (⟨4⟩ : Column .advice)) (Cell.of 60 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 79 2 (⟨2⟩ : Column .advice)) (Cell.of 60 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 79 2 (⟨3⟩ : Column .advice)) (Cell.of 60 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 79 2 (⟨4⟩ : Column .advice)) (Cell.of 60 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 80 0 (⟨3⟩ : Column .advice)) (Cell.of 75 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 80 0 (⟨4⟩ : Column .advice)) (Cell.of 75 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 80 1 (⟨2⟩ : Column .advice)) (Cell.of 75 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 80 1 (⟨3⟩ : Column .advice)) (Cell.of 75 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 80 1 (⟨4⟩ : Column .advice)) (Cell.of 75 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 80 2 (⟨2⟩ : Column .advice)) (Cell.of 75 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 80 2 (⟨3⟩ : Column .advice)) (Cell.of 75 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 80 2 (⟨4⟩ : Column .advice)) (Cell.of 75 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 81 0 (⟨3⟩ : Column .advice)) (Cell.of 59 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 81 0 (⟨4⟩ : Column .advice)) (Cell.of 68 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 81 1 (⟨3⟩ : Column .advice)) (Cell.of 79 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 81 1 (⟨4⟩ : Column .advice)) (Cell.of 80 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 81 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 81 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 81 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand18Checked : Checkpoint expand18Action expand17After expand18Output expand18After expand18Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand18Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand19Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand18Output[4]!
    let s1 ← Synthesis.sigma1 expand18Output[17]!
    let w ← Synthesis.prepareMessage #[expand18Output[3]!.combined.plain, expand18Output[12]!.combined.plain, s0, s1]
    return expand18Output.push w
def expand19Output : Array Synthesis.Word :=
  (expand18Output).push ({ combined := { plain := (Cell.of 84 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 84 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 84 0 (⟨0⟩ : Column .advice)), (Cell.of 84 0 (⟨5⟩ : Column .advice)), (Cell.of 84 1 (⟨5⟩ : Column .advice)), (Cell.of 84 2 (⟨5⟩ : Column .advice)), (Cell.of 84 0 (⟨1⟩ : Column .advice)), (Cell.of 84 1 (⟨0⟩ : Column .advice)), (Cell.of 84 1 (⟨1⟩ : Column .advice)), (Cell.of 84 2 (⟨0⟩ : Column .advice))] } })
def expand19After : Cursor :=
  ⟨85, [] ++ expand18After.constants⟩
def expand19Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 82 0 (⟨3⟩ : Column .advice)) (Cell.of 61 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 82 0 (⟨4⟩ : Column .advice)) (Cell.of 61 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 82 1 (⟨2⟩ : Column .advice)) (Cell.of 61 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 82 1 (⟨3⟩ : Column .advice)) (Cell.of 61 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 82 1 (⟨4⟩ : Column .advice)) (Cell.of 61 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 82 2 (⟨2⟩ : Column .advice)) (Cell.of 61 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 82 2 (⟨3⟩ : Column .advice)) (Cell.of 61 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 82 2 (⟨4⟩ : Column .advice)) (Cell.of 61 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 83 0 (⟨3⟩ : Column .advice)) (Cell.of 78 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 83 0 (⟨4⟩ : Column .advice)) (Cell.of 78 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 83 1 (⟨2⟩ : Column .advice)) (Cell.of 78 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 83 1 (⟨3⟩ : Column .advice)) (Cell.of 78 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 83 1 (⟨4⟩ : Column .advice)) (Cell.of 78 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 83 2 (⟨2⟩ : Column .advice)) (Cell.of 78 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 83 2 (⟨3⟩ : Column .advice)) (Cell.of 78 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 83 2 (⟨4⟩ : Column .advice)) (Cell.of 78 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 84 0 (⟨3⟩ : Column .advice)) (Cell.of 60 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 84 0 (⟨4⟩ : Column .advice)) (Cell.of 69 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 84 1 (⟨3⟩ : Column .advice)) (Cell.of 82 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 84 1 (⟨4⟩ : Column .advice)) (Cell.of 83 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 84 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 84 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 84 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand19Checked : Checkpoint expand19Action expand18After expand19Output expand19After expand19Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand19Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand20Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand19Output[5]!
    let s1 ← Synthesis.sigma1 expand19Output[18]!
    let w ← Synthesis.prepareMessage #[expand19Output[4]!.combined.plain, expand19Output[13]!.combined.plain, s0, s1]
    return expand19Output.push w
def expand20Output : Array Synthesis.Word :=
  (expand19Output).push ({ combined := { plain := (Cell.of 87 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 87 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 87 0 (⟨0⟩ : Column .advice)), (Cell.of 87 0 (⟨5⟩ : Column .advice)), (Cell.of 87 1 (⟨5⟩ : Column .advice)), (Cell.of 87 2 (⟨5⟩ : Column .advice)), (Cell.of 87 0 (⟨1⟩ : Column .advice)), (Cell.of 87 1 (⟨0⟩ : Column .advice)), (Cell.of 87 1 (⟨1⟩ : Column .advice)), (Cell.of 87 2 (⟨0⟩ : Column .advice))] } })
def expand20After : Cursor :=
  ⟨88, [] ++ expand19After.constants⟩
def expand20Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 85 0 (⟨3⟩ : Column .advice)) (Cell.of 62 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 85 0 (⟨4⟩ : Column .advice)) (Cell.of 62 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 85 1 (⟨2⟩ : Column .advice)) (Cell.of 62 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 85 1 (⟨3⟩ : Column .advice)) (Cell.of 62 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 85 1 (⟨4⟩ : Column .advice)) (Cell.of 62 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 85 2 (⟨2⟩ : Column .advice)) (Cell.of 62 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 85 2 (⟨3⟩ : Column .advice)) (Cell.of 62 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 85 2 (⟨4⟩ : Column .advice)) (Cell.of 62 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 86 0 (⟨3⟩ : Column .advice)) (Cell.of 81 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 86 0 (⟨4⟩ : Column .advice)) (Cell.of 81 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 86 1 (⟨2⟩ : Column .advice)) (Cell.of 81 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 86 1 (⟨3⟩ : Column .advice)) (Cell.of 81 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 86 1 (⟨4⟩ : Column .advice)) (Cell.of 81 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 86 2 (⟨2⟩ : Column .advice)) (Cell.of 81 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 86 2 (⟨3⟩ : Column .advice)) (Cell.of 81 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 86 2 (⟨4⟩ : Column .advice)) (Cell.of 81 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 87 0 (⟨3⟩ : Column .advice)) (Cell.of 61 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 87 0 (⟨4⟩ : Column .advice)) (Cell.of 70 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 87 1 (⟨3⟩ : Column .advice)) (Cell.of 85 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 87 1 (⟨4⟩ : Column .advice)) (Cell.of 86 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 87 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 87 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 87 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand20Checked : Checkpoint expand20Action expand19After expand20Output expand20After expand20Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand20Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand21Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand20Output[6]!
    let s1 ← Synthesis.sigma1 expand20Output[19]!
    let w ← Synthesis.prepareMessage #[expand20Output[5]!.combined.plain, expand20Output[14]!.combined.plain, s0, s1]
    return expand20Output.push w
def expand21Output : Array Synthesis.Word :=
  (expand20Output).push ({ combined := { plain := (Cell.of 90 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 90 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 90 0 (⟨0⟩ : Column .advice)), (Cell.of 90 0 (⟨5⟩ : Column .advice)), (Cell.of 90 1 (⟨5⟩ : Column .advice)), (Cell.of 90 2 (⟨5⟩ : Column .advice)), (Cell.of 90 0 (⟨1⟩ : Column .advice)), (Cell.of 90 1 (⟨0⟩ : Column .advice)), (Cell.of 90 1 (⟨1⟩ : Column .advice)), (Cell.of 90 2 (⟨0⟩ : Column .advice))] } })
def expand21After : Cursor :=
  ⟨91, [] ++ expand20After.constants⟩
def expand21Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 88 0 (⟨3⟩ : Column .advice)) (Cell.of 63 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 88 0 (⟨4⟩ : Column .advice)) (Cell.of 63 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 88 1 (⟨2⟩ : Column .advice)) (Cell.of 63 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 88 1 (⟨3⟩ : Column .advice)) (Cell.of 63 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 88 1 (⟨4⟩ : Column .advice)) (Cell.of 63 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 88 2 (⟨2⟩ : Column .advice)) (Cell.of 63 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 88 2 (⟨3⟩ : Column .advice)) (Cell.of 63 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 88 2 (⟨4⟩ : Column .advice)) (Cell.of 63 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 89 0 (⟨3⟩ : Column .advice)) (Cell.of 84 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 89 0 (⟨4⟩ : Column .advice)) (Cell.of 84 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 89 1 (⟨2⟩ : Column .advice)) (Cell.of 84 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 89 1 (⟨3⟩ : Column .advice)) (Cell.of 84 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 89 1 (⟨4⟩ : Column .advice)) (Cell.of 84 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 89 2 (⟨2⟩ : Column .advice)) (Cell.of 84 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 89 2 (⟨3⟩ : Column .advice)) (Cell.of 84 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 89 2 (⟨4⟩ : Column .advice)) (Cell.of 84 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 90 0 (⟨3⟩ : Column .advice)) (Cell.of 62 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 90 0 (⟨4⟩ : Column .advice)) (Cell.of 71 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 90 1 (⟨3⟩ : Column .advice)) (Cell.of 88 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 90 1 (⟨4⟩ : Column .advice)) (Cell.of 89 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 90 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 90 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 90 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand21Checked : Checkpoint expand21Action expand20After expand21Output expand21After expand21Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand21Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand22Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand21Output[7]!
    let s1 ← Synthesis.sigma1 expand21Output[20]!
    let w ← Synthesis.prepareMessage #[expand21Output[6]!.combined.plain, expand21Output[15]!.combined.plain, s0, s1]
    return expand21Output.push w
def expand22Output : Array Synthesis.Word :=
  (expand21Output).push ({ combined := { plain := (Cell.of 93 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 93 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 93 0 (⟨0⟩ : Column .advice)), (Cell.of 93 0 (⟨5⟩ : Column .advice)), (Cell.of 93 1 (⟨5⟩ : Column .advice)), (Cell.of 93 2 (⟨5⟩ : Column .advice)), (Cell.of 93 0 (⟨1⟩ : Column .advice)), (Cell.of 93 1 (⟨0⟩ : Column .advice)), (Cell.of 93 1 (⟨1⟩ : Column .advice)), (Cell.of 93 2 (⟨0⟩ : Column .advice))] } })
def expand22After : Cursor :=
  ⟨94, [] ++ expand21After.constants⟩
def expand22Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 91 0 (⟨3⟩ : Column .advice)) (Cell.of 64 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 91 0 (⟨4⟩ : Column .advice)) (Cell.of 64 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 91 1 (⟨2⟩ : Column .advice)) (Cell.of 64 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 91 1 (⟨3⟩ : Column .advice)) (Cell.of 64 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 91 1 (⟨4⟩ : Column .advice)) (Cell.of 64 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 91 2 (⟨2⟩ : Column .advice)) (Cell.of 64 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 91 2 (⟨3⟩ : Column .advice)) (Cell.of 64 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 91 2 (⟨4⟩ : Column .advice)) (Cell.of 64 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 92 0 (⟨3⟩ : Column .advice)) (Cell.of 87 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 92 0 (⟨4⟩ : Column .advice)) (Cell.of 87 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 92 1 (⟨2⟩ : Column .advice)) (Cell.of 87 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 92 1 (⟨3⟩ : Column .advice)) (Cell.of 87 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 92 1 (⟨4⟩ : Column .advice)) (Cell.of 87 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 92 2 (⟨2⟩ : Column .advice)) (Cell.of 87 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 92 2 (⟨3⟩ : Column .advice)) (Cell.of 87 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 92 2 (⟨4⟩ : Column .advice)) (Cell.of 87 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 93 0 (⟨3⟩ : Column .advice)) (Cell.of 63 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 93 0 (⟨4⟩ : Column .advice)) (Cell.of 72 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 93 1 (⟨3⟩ : Column .advice)) (Cell.of 91 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 93 1 (⟨4⟩ : Column .advice)) (Cell.of 92 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 93 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 93 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 93 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand22Checked : Checkpoint expand22Action expand21After expand22Output expand22After expand22Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand22Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand23Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand22Output[8]!
    let s1 ← Synthesis.sigma1 expand22Output[21]!
    let w ← Synthesis.prepareMessage #[expand22Output[7]!.combined.plain, expand22Output[16]!.combined.plain, s0, s1]
    return expand22Output.push w
def expand23Output : Array Synthesis.Word :=
  (expand22Output).push ({ combined := { plain := (Cell.of 96 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 96 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 96 0 (⟨0⟩ : Column .advice)), (Cell.of 96 0 (⟨5⟩ : Column .advice)), (Cell.of 96 1 (⟨5⟩ : Column .advice)), (Cell.of 96 2 (⟨5⟩ : Column .advice)), (Cell.of 96 0 (⟨1⟩ : Column .advice)), (Cell.of 96 1 (⟨0⟩ : Column .advice)), (Cell.of 96 1 (⟨1⟩ : Column .advice)), (Cell.of 96 2 (⟨0⟩ : Column .advice))] } })
def expand23After : Cursor :=
  ⟨97, [] ++ expand22After.constants⟩
def expand23Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 94 0 (⟨3⟩ : Column .advice)) (Cell.of 65 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 94 0 (⟨4⟩ : Column .advice)) (Cell.of 65 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 94 1 (⟨2⟩ : Column .advice)) (Cell.of 65 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 94 1 (⟨3⟩ : Column .advice)) (Cell.of 65 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 94 1 (⟨4⟩ : Column .advice)) (Cell.of 65 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 94 2 (⟨2⟩ : Column .advice)) (Cell.of 65 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 94 2 (⟨3⟩ : Column .advice)) (Cell.of 65 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 94 2 (⟨4⟩ : Column .advice)) (Cell.of 65 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 95 0 (⟨3⟩ : Column .advice)) (Cell.of 90 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 95 0 (⟨4⟩ : Column .advice)) (Cell.of 90 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 95 1 (⟨2⟩ : Column .advice)) (Cell.of 90 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 95 1 (⟨3⟩ : Column .advice)) (Cell.of 90 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 95 1 (⟨4⟩ : Column .advice)) (Cell.of 90 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 95 2 (⟨2⟩ : Column .advice)) (Cell.of 90 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 95 2 (⟨3⟩ : Column .advice)) (Cell.of 90 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 95 2 (⟨4⟩ : Column .advice)) (Cell.of 90 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 96 0 (⟨3⟩ : Column .advice)) (Cell.of 64 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 96 0 (⟨4⟩ : Column .advice)) (Cell.of 75 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 96 1 (⟨3⟩ : Column .advice)) (Cell.of 94 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 96 1 (⟨4⟩ : Column .advice)) (Cell.of 95 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 96 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 96 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 96 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand23Checked : Checkpoint expand23Action expand22After expand23Output expand23After expand23Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand23Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand24Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand23Output[9]!
    let s1 ← Synthesis.sigma1 expand23Output[22]!
    let w ← Synthesis.prepareMessage #[expand23Output[8]!.combined.plain, expand23Output[17]!.combined.plain, s0, s1]
    return expand23Output.push w
def expand24Output : Array Synthesis.Word :=
  (expand23Output).push ({ combined := { plain := (Cell.of 99 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 99 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 99 0 (⟨0⟩ : Column .advice)), (Cell.of 99 0 (⟨5⟩ : Column .advice)), (Cell.of 99 1 (⟨5⟩ : Column .advice)), (Cell.of 99 2 (⟨5⟩ : Column .advice)), (Cell.of 99 0 (⟨1⟩ : Column .advice)), (Cell.of 99 1 (⟨0⟩ : Column .advice)), (Cell.of 99 1 (⟨1⟩ : Column .advice)), (Cell.of 99 2 (⟨0⟩ : Column .advice))] } })
def expand24After : Cursor :=
  ⟨100, [] ++ expand23After.constants⟩
def expand24Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 97 0 (⟨3⟩ : Column .advice)) (Cell.of 66 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 97 0 (⟨4⟩ : Column .advice)) (Cell.of 66 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 97 1 (⟨2⟩ : Column .advice)) (Cell.of 66 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 97 1 (⟨3⟩ : Column .advice)) (Cell.of 66 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 97 1 (⟨4⟩ : Column .advice)) (Cell.of 66 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 97 2 (⟨2⟩ : Column .advice)) (Cell.of 66 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 97 2 (⟨3⟩ : Column .advice)) (Cell.of 66 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 97 2 (⟨4⟩ : Column .advice)) (Cell.of 66 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 98 0 (⟨3⟩ : Column .advice)) (Cell.of 93 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 98 0 (⟨4⟩ : Column .advice)) (Cell.of 93 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 98 1 (⟨2⟩ : Column .advice)) (Cell.of 93 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 98 1 (⟨3⟩ : Column .advice)) (Cell.of 93 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 98 1 (⟨4⟩ : Column .advice)) (Cell.of 93 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 98 2 (⟨2⟩ : Column .advice)) (Cell.of 93 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 98 2 (⟨3⟩ : Column .advice)) (Cell.of 93 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 98 2 (⟨4⟩ : Column .advice)) (Cell.of 93 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 99 0 (⟨3⟩ : Column .advice)) (Cell.of 65 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 99 0 (⟨4⟩ : Column .advice)) (Cell.of 78 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 99 1 (⟨3⟩ : Column .advice)) (Cell.of 97 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 99 1 (⟨4⟩ : Column .advice)) (Cell.of 98 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 99 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 99 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 99 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand24Checked : Checkpoint expand24Action expand23After expand24Output expand24After expand24Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand24Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand25Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand24Output[10]!
    let s1 ← Synthesis.sigma1 expand24Output[23]!
    let w ← Synthesis.prepareMessage #[expand24Output[9]!.combined.plain, expand24Output[18]!.combined.plain, s0, s1]
    return expand24Output.push w
def expand25Output : Array Synthesis.Word :=
  (expand24Output).push ({ combined := { plain := (Cell.of 102 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 102 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 102 0 (⟨0⟩ : Column .advice)), (Cell.of 102 0 (⟨5⟩ : Column .advice)), (Cell.of 102 1 (⟨5⟩ : Column .advice)), (Cell.of 102 2 (⟨5⟩ : Column .advice)), (Cell.of 102 0 (⟨1⟩ : Column .advice)), (Cell.of 102 1 (⟨0⟩ : Column .advice)), (Cell.of 102 1 (⟨1⟩ : Column .advice)), (Cell.of 102 2 (⟨0⟩ : Column .advice))] } })
def expand25After : Cursor :=
  ⟨103, [] ++ expand24After.constants⟩
def expand25Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 100 0 (⟨3⟩ : Column .advice)) (Cell.of 67 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 100 0 (⟨4⟩ : Column .advice)) (Cell.of 67 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 100 1 (⟨2⟩ : Column .advice)) (Cell.of 67 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 100 1 (⟨3⟩ : Column .advice)) (Cell.of 67 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 100 1 (⟨4⟩ : Column .advice)) (Cell.of 67 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 100 2 (⟨2⟩ : Column .advice)) (Cell.of 67 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 100 2 (⟨3⟩ : Column .advice)) (Cell.of 67 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 100 2 (⟨4⟩ : Column .advice)) (Cell.of 67 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 101 0 (⟨3⟩ : Column .advice)) (Cell.of 96 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 101 0 (⟨4⟩ : Column .advice)) (Cell.of 96 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 101 1 (⟨2⟩ : Column .advice)) (Cell.of 96 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 101 1 (⟨3⟩ : Column .advice)) (Cell.of 96 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 101 1 (⟨4⟩ : Column .advice)) (Cell.of 96 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 101 2 (⟨2⟩ : Column .advice)) (Cell.of 96 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 101 2 (⟨3⟩ : Column .advice)) (Cell.of 96 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 101 2 (⟨4⟩ : Column .advice)) (Cell.of 96 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 102 0 (⟨3⟩ : Column .advice)) (Cell.of 66 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 102 0 (⟨4⟩ : Column .advice)) (Cell.of 81 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 102 1 (⟨3⟩ : Column .advice)) (Cell.of 100 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 102 1 (⟨4⟩ : Column .advice)) (Cell.of 101 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 102 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 102 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 102 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand25Checked : Checkpoint expand25Action expand24After expand25Output expand25After expand25Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand25Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand26Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand25Output[11]!
    let s1 ← Synthesis.sigma1 expand25Output[24]!
    let w ← Synthesis.prepareMessage #[expand25Output[10]!.combined.plain, expand25Output[19]!.combined.plain, s0, s1]
    return expand25Output.push w
def expand26Output : Array Synthesis.Word :=
  (expand25Output).push ({ combined := { plain := (Cell.of 105 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 105 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 105 0 (⟨0⟩ : Column .advice)), (Cell.of 105 0 (⟨5⟩ : Column .advice)), (Cell.of 105 1 (⟨5⟩ : Column .advice)), (Cell.of 105 2 (⟨5⟩ : Column .advice)), (Cell.of 105 0 (⟨1⟩ : Column .advice)), (Cell.of 105 1 (⟨0⟩ : Column .advice)), (Cell.of 105 1 (⟨1⟩ : Column .advice)), (Cell.of 105 2 (⟨0⟩ : Column .advice))] } })
def expand26After : Cursor :=
  ⟨106, [] ++ expand25After.constants⟩
def expand26Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 103 0 (⟨3⟩ : Column .advice)) (Cell.of 68 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 103 0 (⟨4⟩ : Column .advice)) (Cell.of 68 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 103 1 (⟨2⟩ : Column .advice)) (Cell.of 68 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 103 1 (⟨3⟩ : Column .advice)) (Cell.of 68 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 103 1 (⟨4⟩ : Column .advice)) (Cell.of 68 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 103 2 (⟨2⟩ : Column .advice)) (Cell.of 68 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 103 2 (⟨3⟩ : Column .advice)) (Cell.of 68 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 103 2 (⟨4⟩ : Column .advice)) (Cell.of 68 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 104 0 (⟨3⟩ : Column .advice)) (Cell.of 99 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 104 0 (⟨4⟩ : Column .advice)) (Cell.of 99 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 104 1 (⟨2⟩ : Column .advice)) (Cell.of 99 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 104 1 (⟨3⟩ : Column .advice)) (Cell.of 99 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 104 1 (⟨4⟩ : Column .advice)) (Cell.of 99 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 104 2 (⟨2⟩ : Column .advice)) (Cell.of 99 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 104 2 (⟨3⟩ : Column .advice)) (Cell.of 99 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 104 2 (⟨4⟩ : Column .advice)) (Cell.of 99 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 105 0 (⟨3⟩ : Column .advice)) (Cell.of 67 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 105 0 (⟨4⟩ : Column .advice)) (Cell.of 84 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 105 1 (⟨3⟩ : Column .advice)) (Cell.of 103 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 105 1 (⟨4⟩ : Column .advice)) (Cell.of 104 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 105 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 105 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 105 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand26Checked : Checkpoint expand26Action expand25After expand26Output expand26After expand26Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand26Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand27Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand26Output[12]!
    let s1 ← Synthesis.sigma1 expand26Output[25]!
    let w ← Synthesis.prepareMessage #[expand26Output[11]!.combined.plain, expand26Output[20]!.combined.plain, s0, s1]
    return expand26Output.push w
def expand27Output : Array Synthesis.Word :=
  (expand26Output).push ({ combined := { plain := (Cell.of 108 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 108 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 108 0 (⟨0⟩ : Column .advice)), (Cell.of 108 0 (⟨5⟩ : Column .advice)), (Cell.of 108 1 (⟨5⟩ : Column .advice)), (Cell.of 108 2 (⟨5⟩ : Column .advice)), (Cell.of 108 0 (⟨1⟩ : Column .advice)), (Cell.of 108 1 (⟨0⟩ : Column .advice)), (Cell.of 108 1 (⟨1⟩ : Column .advice)), (Cell.of 108 2 (⟨0⟩ : Column .advice))] } })
def expand27After : Cursor :=
  ⟨109, [] ++ expand26After.constants⟩
def expand27Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 106 0 (⟨3⟩ : Column .advice)) (Cell.of 69 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 106 0 (⟨4⟩ : Column .advice)) (Cell.of 69 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 106 1 (⟨2⟩ : Column .advice)) (Cell.of 69 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 106 1 (⟨3⟩ : Column .advice)) (Cell.of 69 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 106 1 (⟨4⟩ : Column .advice)) (Cell.of 69 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 106 2 (⟨2⟩ : Column .advice)) (Cell.of 69 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 106 2 (⟨3⟩ : Column .advice)) (Cell.of 69 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 106 2 (⟨4⟩ : Column .advice)) (Cell.of 69 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 107 0 (⟨3⟩ : Column .advice)) (Cell.of 102 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 107 0 (⟨4⟩ : Column .advice)) (Cell.of 102 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 107 1 (⟨2⟩ : Column .advice)) (Cell.of 102 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 107 1 (⟨3⟩ : Column .advice)) (Cell.of 102 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 107 1 (⟨4⟩ : Column .advice)) (Cell.of 102 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 107 2 (⟨2⟩ : Column .advice)) (Cell.of 102 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 107 2 (⟨3⟩ : Column .advice)) (Cell.of 102 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 107 2 (⟨4⟩ : Column .advice)) (Cell.of 102 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 108 0 (⟨3⟩ : Column .advice)) (Cell.of 68 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 108 0 (⟨4⟩ : Column .advice)) (Cell.of 87 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 108 1 (⟨3⟩ : Column .advice)) (Cell.of 106 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 108 1 (⟨4⟩ : Column .advice)) (Cell.of 107 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 108 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 108 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 108 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand27Checked : Checkpoint expand27Action expand26After expand27Output expand27After expand27Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand27Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand28Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand27Output[13]!
    let s1 ← Synthesis.sigma1 expand27Output[26]!
    let w ← Synthesis.prepareMessage #[expand27Output[12]!.combined.plain, expand27Output[21]!.combined.plain, s0, s1]
    return expand27Output.push w
def expand28Output : Array Synthesis.Word :=
  (expand27Output).push ({ combined := { plain := (Cell.of 111 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 111 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 111 0 (⟨0⟩ : Column .advice)), (Cell.of 111 0 (⟨5⟩ : Column .advice)), (Cell.of 111 1 (⟨5⟩ : Column .advice)), (Cell.of 111 2 (⟨5⟩ : Column .advice)), (Cell.of 111 0 (⟨1⟩ : Column .advice)), (Cell.of 111 1 (⟨0⟩ : Column .advice)), (Cell.of 111 1 (⟨1⟩ : Column .advice)), (Cell.of 111 2 (⟨0⟩ : Column .advice))] } })
def expand28After : Cursor :=
  ⟨112, [] ++ expand27After.constants⟩
def expand28Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 109 0 (⟨3⟩ : Column .advice)) (Cell.of 70 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 109 0 (⟨4⟩ : Column .advice)) (Cell.of 70 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 109 1 (⟨2⟩ : Column .advice)) (Cell.of 70 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 109 1 (⟨3⟩ : Column .advice)) (Cell.of 70 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 109 1 (⟨4⟩ : Column .advice)) (Cell.of 70 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 109 2 (⟨2⟩ : Column .advice)) (Cell.of 70 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 109 2 (⟨3⟩ : Column .advice)) (Cell.of 70 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 109 2 (⟨4⟩ : Column .advice)) (Cell.of 70 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 110 0 (⟨3⟩ : Column .advice)) (Cell.of 105 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 110 0 (⟨4⟩ : Column .advice)) (Cell.of 105 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 110 1 (⟨2⟩ : Column .advice)) (Cell.of 105 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 110 1 (⟨3⟩ : Column .advice)) (Cell.of 105 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 110 1 (⟨4⟩ : Column .advice)) (Cell.of 105 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 110 2 (⟨2⟩ : Column .advice)) (Cell.of 105 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 110 2 (⟨3⟩ : Column .advice)) (Cell.of 105 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 110 2 (⟨4⟩ : Column .advice)) (Cell.of 105 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 111 0 (⟨3⟩ : Column .advice)) (Cell.of 69 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 111 0 (⟨4⟩ : Column .advice)) (Cell.of 90 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 111 1 (⟨3⟩ : Column .advice)) (Cell.of 109 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 111 1 (⟨4⟩ : Column .advice)) (Cell.of 110 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 111 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 111 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 111 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand28Checked : Checkpoint expand28Action expand27After expand28Output expand28After expand28Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand28Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand29Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand28Output[14]!
    let s1 ← Synthesis.sigma1 expand28Output[27]!
    let w ← Synthesis.prepareMessage #[expand28Output[13]!.combined.plain, expand28Output[22]!.combined.plain, s0, s1]
    return expand28Output.push w
def expand29Output : Array Synthesis.Word :=
  (expand28Output).push ({ combined := { plain := (Cell.of 114 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 114 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 114 0 (⟨0⟩ : Column .advice)), (Cell.of 114 0 (⟨5⟩ : Column .advice)), (Cell.of 114 1 (⟨5⟩ : Column .advice)), (Cell.of 114 2 (⟨5⟩ : Column .advice)), (Cell.of 114 0 (⟨1⟩ : Column .advice)), (Cell.of 114 1 (⟨0⟩ : Column .advice)), (Cell.of 114 1 (⟨1⟩ : Column .advice)), (Cell.of 114 2 (⟨0⟩ : Column .advice))] } })
def expand29After : Cursor :=
  ⟨115, [] ++ expand28After.constants⟩
def expand29Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 112 0 (⟨3⟩ : Column .advice)) (Cell.of 71 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 112 0 (⟨4⟩ : Column .advice)) (Cell.of 71 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 112 1 (⟨2⟩ : Column .advice)) (Cell.of 71 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 112 1 (⟨3⟩ : Column .advice)) (Cell.of 71 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 112 1 (⟨4⟩ : Column .advice)) (Cell.of 71 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 112 2 (⟨2⟩ : Column .advice)) (Cell.of 71 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 112 2 (⟨3⟩ : Column .advice)) (Cell.of 71 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 112 2 (⟨4⟩ : Column .advice)) (Cell.of 71 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 113 0 (⟨3⟩ : Column .advice)) (Cell.of 108 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 113 0 (⟨4⟩ : Column .advice)) (Cell.of 108 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 113 1 (⟨2⟩ : Column .advice)) (Cell.of 108 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 113 1 (⟨3⟩ : Column .advice)) (Cell.of 108 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 113 1 (⟨4⟩ : Column .advice)) (Cell.of 108 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 113 2 (⟨2⟩ : Column .advice)) (Cell.of 108 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 113 2 (⟨3⟩ : Column .advice)) (Cell.of 108 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 113 2 (⟨4⟩ : Column .advice)) (Cell.of 108 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 114 0 (⟨3⟩ : Column .advice)) (Cell.of 70 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 114 0 (⟨4⟩ : Column .advice)) (Cell.of 93 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 114 1 (⟨3⟩ : Column .advice)) (Cell.of 112 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 114 1 (⟨4⟩ : Column .advice)) (Cell.of 113 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 114 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 114 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 114 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand29Checked : Checkpoint expand29Action expand28After expand29Output expand29After expand29Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand29Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand30Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand29Output[15]!
    let s1 ← Synthesis.sigma1 expand29Output[28]!
    let w ← Synthesis.prepareMessage #[expand29Output[14]!.combined.plain, expand29Output[23]!.combined.plain, s0, s1]
    return expand29Output.push w
def expand30Output : Array Synthesis.Word :=
  (expand29Output).push ({ combined := { plain := (Cell.of 117 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 117 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 117 0 (⟨0⟩ : Column .advice)), (Cell.of 117 0 (⟨5⟩ : Column .advice)), (Cell.of 117 1 (⟨5⟩ : Column .advice)), (Cell.of 117 2 (⟨5⟩ : Column .advice)), (Cell.of 117 0 (⟨1⟩ : Column .advice)), (Cell.of 117 1 (⟨0⟩ : Column .advice)), (Cell.of 117 1 (⟨1⟩ : Column .advice)), (Cell.of 117 2 (⟨0⟩ : Column .advice))] } })
def expand30After : Cursor :=
  ⟨118, [] ++ expand29After.constants⟩
def expand30Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 115 0 (⟨3⟩ : Column .advice)) (Cell.of 72 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 115 0 (⟨4⟩ : Column .advice)) (Cell.of 72 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 115 1 (⟨2⟩ : Column .advice)) (Cell.of 72 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 115 1 (⟨3⟩ : Column .advice)) (Cell.of 72 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 115 1 (⟨4⟩ : Column .advice)) (Cell.of 72 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 115 2 (⟨2⟩ : Column .advice)) (Cell.of 72 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 115 2 (⟨3⟩ : Column .advice)) (Cell.of 72 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 115 2 (⟨4⟩ : Column .advice)) (Cell.of 72 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 116 0 (⟨3⟩ : Column .advice)) (Cell.of 111 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 116 0 (⟨4⟩ : Column .advice)) (Cell.of 111 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 116 1 (⟨2⟩ : Column .advice)) (Cell.of 111 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 116 1 (⟨3⟩ : Column .advice)) (Cell.of 111 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 116 1 (⟨4⟩ : Column .advice)) (Cell.of 111 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 116 2 (⟨2⟩ : Column .advice)) (Cell.of 111 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 116 2 (⟨3⟩ : Column .advice)) (Cell.of 111 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 116 2 (⟨4⟩ : Column .advice)) (Cell.of 111 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 117 0 (⟨3⟩ : Column .advice)) (Cell.of 71 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 117 0 (⟨4⟩ : Column .advice)) (Cell.of 96 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 117 1 (⟨3⟩ : Column .advice)) (Cell.of 115 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 117 1 (⟨4⟩ : Column .advice)) (Cell.of 116 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 117 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 117 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 117 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand30Checked : Checkpoint expand30Action expand29After expand30Output expand30After expand30Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand30Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand31Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand30Output[16]!
    let s1 ← Synthesis.sigma1 expand30Output[29]!
    let w ← Synthesis.prepareMessage #[expand30Output[15]!.combined.plain, expand30Output[24]!.combined.plain, s0, s1]
    return expand30Output.push w
def expand31Output : Array Synthesis.Word :=
  (expand30Output).push ({ combined := { plain := (Cell.of 120 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 120 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 120 0 (⟨0⟩ : Column .advice)), (Cell.of 120 0 (⟨5⟩ : Column .advice)), (Cell.of 120 1 (⟨5⟩ : Column .advice)), (Cell.of 120 2 (⟨5⟩ : Column .advice)), (Cell.of 120 0 (⟨1⟩ : Column .advice)), (Cell.of 120 1 (⟨0⟩ : Column .advice)), (Cell.of 120 1 (⟨1⟩ : Column .advice)), (Cell.of 120 2 (⟨0⟩ : Column .advice))] } })
def expand31After : Cursor :=
  ⟨121, [] ++ expand30After.constants⟩
def expand31Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 118 0 (⟨3⟩ : Column .advice)) (Cell.of 75 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 118 0 (⟨4⟩ : Column .advice)) (Cell.of 75 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 118 1 (⟨2⟩ : Column .advice)) (Cell.of 75 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 118 1 (⟨3⟩ : Column .advice)) (Cell.of 75 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 118 1 (⟨4⟩ : Column .advice)) (Cell.of 75 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 118 2 (⟨2⟩ : Column .advice)) (Cell.of 75 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 118 2 (⟨3⟩ : Column .advice)) (Cell.of 75 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 118 2 (⟨4⟩ : Column .advice)) (Cell.of 75 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 119 0 (⟨3⟩ : Column .advice)) (Cell.of 114 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 119 0 (⟨4⟩ : Column .advice)) (Cell.of 114 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 119 1 (⟨2⟩ : Column .advice)) (Cell.of 114 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 119 1 (⟨3⟩ : Column .advice)) (Cell.of 114 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 119 1 (⟨4⟩ : Column .advice)) (Cell.of 114 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 119 2 (⟨2⟩ : Column .advice)) (Cell.of 114 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 119 2 (⟨3⟩ : Column .advice)) (Cell.of 114 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 119 2 (⟨4⟩ : Column .advice)) (Cell.of 114 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 120 0 (⟨3⟩ : Column .advice)) (Cell.of 72 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 120 0 (⟨4⟩ : Column .advice)) (Cell.of 99 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 120 1 (⟨3⟩ : Column .advice)) (Cell.of 118 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 120 1 (⟨4⟩ : Column .advice)) (Cell.of 119 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 120 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 120 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 120 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand31Checked : Checkpoint expand31Action expand30After expand31Output expand31After expand31Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand31Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand32Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand31Output[17]!
    let s1 ← Synthesis.sigma1 expand31Output[30]!
    let w ← Synthesis.prepareMessage #[expand31Output[16]!.combined.plain, expand31Output[25]!.combined.plain, s0, s1]
    return expand31Output.push w
def expand32Output : Array Synthesis.Word :=
  (expand31Output).push ({ combined := { plain := (Cell.of 123 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 123 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 123 0 (⟨0⟩ : Column .advice)), (Cell.of 123 0 (⟨5⟩ : Column .advice)), (Cell.of 123 1 (⟨5⟩ : Column .advice)), (Cell.of 123 2 (⟨5⟩ : Column .advice)), (Cell.of 123 0 (⟨1⟩ : Column .advice)), (Cell.of 123 1 (⟨0⟩ : Column .advice)), (Cell.of 123 1 (⟨1⟩ : Column .advice)), (Cell.of 123 2 (⟨0⟩ : Column .advice))] } })
def expand32After : Cursor :=
  ⟨124, [] ++ expand31After.constants⟩
def expand32Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 121 0 (⟨3⟩ : Column .advice)) (Cell.of 78 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 121 0 (⟨4⟩ : Column .advice)) (Cell.of 78 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 121 1 (⟨2⟩ : Column .advice)) (Cell.of 78 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 121 1 (⟨3⟩ : Column .advice)) (Cell.of 78 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 121 1 (⟨4⟩ : Column .advice)) (Cell.of 78 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 121 2 (⟨2⟩ : Column .advice)) (Cell.of 78 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 121 2 (⟨3⟩ : Column .advice)) (Cell.of 78 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 121 2 (⟨4⟩ : Column .advice)) (Cell.of 78 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 122 0 (⟨3⟩ : Column .advice)) (Cell.of 117 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 122 0 (⟨4⟩ : Column .advice)) (Cell.of 117 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 122 1 (⟨2⟩ : Column .advice)) (Cell.of 117 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 122 1 (⟨3⟩ : Column .advice)) (Cell.of 117 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 122 1 (⟨4⟩ : Column .advice)) (Cell.of 117 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 122 2 (⟨2⟩ : Column .advice)) (Cell.of 117 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 122 2 (⟨3⟩ : Column .advice)) (Cell.of 117 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 122 2 (⟨4⟩ : Column .advice)) (Cell.of 117 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 123 0 (⟨3⟩ : Column .advice)) (Cell.of 75 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 123 0 (⟨4⟩ : Column .advice)) (Cell.of 102 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 123 1 (⟨3⟩ : Column .advice)) (Cell.of 121 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 123 1 (⟨4⟩ : Column .advice)) (Cell.of 122 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 123 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 123 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 123 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand32Checked : Checkpoint expand32Action expand31After expand32Output expand32After expand32Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand32Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand33Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand32Output[18]!
    let s1 ← Synthesis.sigma1 expand32Output[31]!
    let w ← Synthesis.prepareMessage #[expand32Output[17]!.combined.plain, expand32Output[26]!.combined.plain, s0, s1]
    return expand32Output.push w
def expand33Output : Array Synthesis.Word :=
  (expand32Output).push ({ combined := { plain := (Cell.of 126 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 126 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 126 0 (⟨0⟩ : Column .advice)), (Cell.of 126 0 (⟨5⟩ : Column .advice)), (Cell.of 126 1 (⟨5⟩ : Column .advice)), (Cell.of 126 2 (⟨5⟩ : Column .advice)), (Cell.of 126 0 (⟨1⟩ : Column .advice)), (Cell.of 126 1 (⟨0⟩ : Column .advice)), (Cell.of 126 1 (⟨1⟩ : Column .advice)), (Cell.of 126 2 (⟨0⟩ : Column .advice))] } })
def expand33After : Cursor :=
  ⟨127, [] ++ expand32After.constants⟩
def expand33Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 124 0 (⟨3⟩ : Column .advice)) (Cell.of 81 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 124 0 (⟨4⟩ : Column .advice)) (Cell.of 81 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 124 1 (⟨2⟩ : Column .advice)) (Cell.of 81 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 124 1 (⟨3⟩ : Column .advice)) (Cell.of 81 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 124 1 (⟨4⟩ : Column .advice)) (Cell.of 81 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 124 2 (⟨2⟩ : Column .advice)) (Cell.of 81 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 124 2 (⟨3⟩ : Column .advice)) (Cell.of 81 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 124 2 (⟨4⟩ : Column .advice)) (Cell.of 81 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 125 0 (⟨3⟩ : Column .advice)) (Cell.of 120 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 125 0 (⟨4⟩ : Column .advice)) (Cell.of 120 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 125 1 (⟨2⟩ : Column .advice)) (Cell.of 120 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 125 1 (⟨3⟩ : Column .advice)) (Cell.of 120 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 125 1 (⟨4⟩ : Column .advice)) (Cell.of 120 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 125 2 (⟨2⟩ : Column .advice)) (Cell.of 120 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 125 2 (⟨3⟩ : Column .advice)) (Cell.of 120 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 125 2 (⟨4⟩ : Column .advice)) (Cell.of 120 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 126 0 (⟨3⟩ : Column .advice)) (Cell.of 78 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 126 0 (⟨4⟩ : Column .advice)) (Cell.of 105 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 126 1 (⟨3⟩ : Column .advice)) (Cell.of 124 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 126 1 (⟨4⟩ : Column .advice)) (Cell.of 125 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 126 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 126 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 126 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand33Checked : Checkpoint expand33Action expand32After expand33Output expand33After expand33Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand33Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand34Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand33Output[19]!
    let s1 ← Synthesis.sigma1 expand33Output[32]!
    let w ← Synthesis.prepareMessage #[expand33Output[18]!.combined.plain, expand33Output[27]!.combined.plain, s0, s1]
    return expand33Output.push w
def expand34Output : Array Synthesis.Word :=
  (expand33Output).push ({ combined := { plain := (Cell.of 129 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 129 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 129 0 (⟨0⟩ : Column .advice)), (Cell.of 129 0 (⟨5⟩ : Column .advice)), (Cell.of 129 1 (⟨5⟩ : Column .advice)), (Cell.of 129 2 (⟨5⟩ : Column .advice)), (Cell.of 129 0 (⟨1⟩ : Column .advice)), (Cell.of 129 1 (⟨0⟩ : Column .advice)), (Cell.of 129 1 (⟨1⟩ : Column .advice)), (Cell.of 129 2 (⟨0⟩ : Column .advice))] } })
def expand34After : Cursor :=
  ⟨130, [] ++ expand33After.constants⟩
def expand34Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 127 0 (⟨3⟩ : Column .advice)) (Cell.of 84 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 127 0 (⟨4⟩ : Column .advice)) (Cell.of 84 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 127 1 (⟨2⟩ : Column .advice)) (Cell.of 84 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 127 1 (⟨3⟩ : Column .advice)) (Cell.of 84 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 127 1 (⟨4⟩ : Column .advice)) (Cell.of 84 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 127 2 (⟨2⟩ : Column .advice)) (Cell.of 84 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 127 2 (⟨3⟩ : Column .advice)) (Cell.of 84 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 127 2 (⟨4⟩ : Column .advice)) (Cell.of 84 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 128 0 (⟨3⟩ : Column .advice)) (Cell.of 123 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 128 0 (⟨4⟩ : Column .advice)) (Cell.of 123 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 128 1 (⟨2⟩ : Column .advice)) (Cell.of 123 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 128 1 (⟨3⟩ : Column .advice)) (Cell.of 123 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 128 1 (⟨4⟩ : Column .advice)) (Cell.of 123 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 128 2 (⟨2⟩ : Column .advice)) (Cell.of 123 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 128 2 (⟨3⟩ : Column .advice)) (Cell.of 123 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 128 2 (⟨4⟩ : Column .advice)) (Cell.of 123 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 129 0 (⟨3⟩ : Column .advice)) (Cell.of 81 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 129 0 (⟨4⟩ : Column .advice)) (Cell.of 108 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 129 1 (⟨3⟩ : Column .advice)) (Cell.of 127 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 129 1 (⟨4⟩ : Column .advice)) (Cell.of 128 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 129 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 129 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 129 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand34Checked : Checkpoint expand34Action expand33After expand34Output expand34After expand34Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand34Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand35Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand34Output[20]!
    let s1 ← Synthesis.sigma1 expand34Output[33]!
    let w ← Synthesis.prepareMessage #[expand34Output[19]!.combined.plain, expand34Output[28]!.combined.plain, s0, s1]
    return expand34Output.push w
def expand35Output : Array Synthesis.Word :=
  (expand34Output).push ({ combined := { plain := (Cell.of 132 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 132 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 132 0 (⟨0⟩ : Column .advice)), (Cell.of 132 0 (⟨5⟩ : Column .advice)), (Cell.of 132 1 (⟨5⟩ : Column .advice)), (Cell.of 132 2 (⟨5⟩ : Column .advice)), (Cell.of 132 0 (⟨1⟩ : Column .advice)), (Cell.of 132 1 (⟨0⟩ : Column .advice)), (Cell.of 132 1 (⟨1⟩ : Column .advice)), (Cell.of 132 2 (⟨0⟩ : Column .advice))] } })
def expand35After : Cursor :=
  ⟨133, [] ++ expand34After.constants⟩
def expand35Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 130 0 (⟨3⟩ : Column .advice)) (Cell.of 87 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 130 0 (⟨4⟩ : Column .advice)) (Cell.of 87 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 130 1 (⟨2⟩ : Column .advice)) (Cell.of 87 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 130 1 (⟨3⟩ : Column .advice)) (Cell.of 87 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 130 1 (⟨4⟩ : Column .advice)) (Cell.of 87 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 130 2 (⟨2⟩ : Column .advice)) (Cell.of 87 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 130 2 (⟨3⟩ : Column .advice)) (Cell.of 87 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 130 2 (⟨4⟩ : Column .advice)) (Cell.of 87 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 131 0 (⟨3⟩ : Column .advice)) (Cell.of 126 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 131 0 (⟨4⟩ : Column .advice)) (Cell.of 126 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 131 1 (⟨2⟩ : Column .advice)) (Cell.of 126 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 131 1 (⟨3⟩ : Column .advice)) (Cell.of 126 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 131 1 (⟨4⟩ : Column .advice)) (Cell.of 126 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 131 2 (⟨2⟩ : Column .advice)) (Cell.of 126 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 131 2 (⟨3⟩ : Column .advice)) (Cell.of 126 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 131 2 (⟨4⟩ : Column .advice)) (Cell.of 126 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 132 0 (⟨3⟩ : Column .advice)) (Cell.of 84 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 132 0 (⟨4⟩ : Column .advice)) (Cell.of 111 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 132 1 (⟨3⟩ : Column .advice)) (Cell.of 130 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 132 1 (⟨4⟩ : Column .advice)) (Cell.of 131 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 132 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 132 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 132 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand35Checked : Checkpoint expand35Action expand34After expand35Output expand35After expand35Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand35Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand36Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand35Output[21]!
    let s1 ← Synthesis.sigma1 expand35Output[34]!
    let w ← Synthesis.prepareMessage #[expand35Output[20]!.combined.plain, expand35Output[29]!.combined.plain, s0, s1]
    return expand35Output.push w
def expand36Output : Array Synthesis.Word :=
  (expand35Output).push ({ combined := { plain := (Cell.of 135 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 135 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 135 0 (⟨0⟩ : Column .advice)), (Cell.of 135 0 (⟨5⟩ : Column .advice)), (Cell.of 135 1 (⟨5⟩ : Column .advice)), (Cell.of 135 2 (⟨5⟩ : Column .advice)), (Cell.of 135 0 (⟨1⟩ : Column .advice)), (Cell.of 135 1 (⟨0⟩ : Column .advice)), (Cell.of 135 1 (⟨1⟩ : Column .advice)), (Cell.of 135 2 (⟨0⟩ : Column .advice))] } })
def expand36After : Cursor :=
  ⟨136, [] ++ expand35After.constants⟩
def expand36Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 133 0 (⟨3⟩ : Column .advice)) (Cell.of 90 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 133 0 (⟨4⟩ : Column .advice)) (Cell.of 90 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 133 1 (⟨2⟩ : Column .advice)) (Cell.of 90 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 133 1 (⟨3⟩ : Column .advice)) (Cell.of 90 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 133 1 (⟨4⟩ : Column .advice)) (Cell.of 90 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 133 2 (⟨2⟩ : Column .advice)) (Cell.of 90 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 133 2 (⟨3⟩ : Column .advice)) (Cell.of 90 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 133 2 (⟨4⟩ : Column .advice)) (Cell.of 90 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 134 0 (⟨3⟩ : Column .advice)) (Cell.of 129 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 134 0 (⟨4⟩ : Column .advice)) (Cell.of 129 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 134 1 (⟨2⟩ : Column .advice)) (Cell.of 129 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 134 1 (⟨3⟩ : Column .advice)) (Cell.of 129 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 134 1 (⟨4⟩ : Column .advice)) (Cell.of 129 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 134 2 (⟨2⟩ : Column .advice)) (Cell.of 129 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 134 2 (⟨3⟩ : Column .advice)) (Cell.of 129 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 134 2 (⟨4⟩ : Column .advice)) (Cell.of 129 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 135 0 (⟨3⟩ : Column .advice)) (Cell.of 87 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 135 0 (⟨4⟩ : Column .advice)) (Cell.of 114 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 135 1 (⟨3⟩ : Column .advice)) (Cell.of 133 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 135 1 (⟨4⟩ : Column .advice)) (Cell.of 134 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 135 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 135 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 135 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand36Checked : Checkpoint expand36Action expand35After expand36Output expand36After expand36Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand36Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand37Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand36Output[22]!
    let s1 ← Synthesis.sigma1 expand36Output[35]!
    let w ← Synthesis.prepareMessage #[expand36Output[21]!.combined.plain, expand36Output[30]!.combined.plain, s0, s1]
    return expand36Output.push w
def expand37Output : Array Synthesis.Word :=
  (expand36Output).push ({ combined := { plain := (Cell.of 138 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 138 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 138 0 (⟨0⟩ : Column .advice)), (Cell.of 138 0 (⟨5⟩ : Column .advice)), (Cell.of 138 1 (⟨5⟩ : Column .advice)), (Cell.of 138 2 (⟨5⟩ : Column .advice)), (Cell.of 138 0 (⟨1⟩ : Column .advice)), (Cell.of 138 1 (⟨0⟩ : Column .advice)), (Cell.of 138 1 (⟨1⟩ : Column .advice)), (Cell.of 138 2 (⟨0⟩ : Column .advice))] } })
def expand37After : Cursor :=
  ⟨139, [] ++ expand36After.constants⟩
def expand37Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 136 0 (⟨3⟩ : Column .advice)) (Cell.of 93 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 136 0 (⟨4⟩ : Column .advice)) (Cell.of 93 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 136 1 (⟨2⟩ : Column .advice)) (Cell.of 93 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 136 1 (⟨3⟩ : Column .advice)) (Cell.of 93 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 136 1 (⟨4⟩ : Column .advice)) (Cell.of 93 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 136 2 (⟨2⟩ : Column .advice)) (Cell.of 93 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 136 2 (⟨3⟩ : Column .advice)) (Cell.of 93 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 136 2 (⟨4⟩ : Column .advice)) (Cell.of 93 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 137 0 (⟨3⟩ : Column .advice)) (Cell.of 132 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 137 0 (⟨4⟩ : Column .advice)) (Cell.of 132 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 137 1 (⟨2⟩ : Column .advice)) (Cell.of 132 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 137 1 (⟨3⟩ : Column .advice)) (Cell.of 132 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 137 1 (⟨4⟩ : Column .advice)) (Cell.of 132 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 137 2 (⟨2⟩ : Column .advice)) (Cell.of 132 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 137 2 (⟨3⟩ : Column .advice)) (Cell.of 132 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 137 2 (⟨4⟩ : Column .advice)) (Cell.of 132 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 138 0 (⟨3⟩ : Column .advice)) (Cell.of 90 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 138 0 (⟨4⟩ : Column .advice)) (Cell.of 117 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 138 1 (⟨3⟩ : Column .advice)) (Cell.of 136 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 138 1 (⟨4⟩ : Column .advice)) (Cell.of 137 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 138 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 138 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 138 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand37Checked : Checkpoint expand37Action expand36After expand37Output expand37After expand37Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand37Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand38Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand37Output[23]!
    let s1 ← Synthesis.sigma1 expand37Output[36]!
    let w ← Synthesis.prepareMessage #[expand37Output[22]!.combined.plain, expand37Output[31]!.combined.plain, s0, s1]
    return expand37Output.push w
def expand38Output : Array Synthesis.Word :=
  (expand37Output).push ({ combined := { plain := (Cell.of 141 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 141 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 141 0 (⟨0⟩ : Column .advice)), (Cell.of 141 0 (⟨5⟩ : Column .advice)), (Cell.of 141 1 (⟨5⟩ : Column .advice)), (Cell.of 141 2 (⟨5⟩ : Column .advice)), (Cell.of 141 0 (⟨1⟩ : Column .advice)), (Cell.of 141 1 (⟨0⟩ : Column .advice)), (Cell.of 141 1 (⟨1⟩ : Column .advice)), (Cell.of 141 2 (⟨0⟩ : Column .advice))] } })
def expand38After : Cursor :=
  ⟨142, [] ++ expand37After.constants⟩
def expand38Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 139 0 (⟨3⟩ : Column .advice)) (Cell.of 96 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 139 0 (⟨4⟩ : Column .advice)) (Cell.of 96 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 139 1 (⟨2⟩ : Column .advice)) (Cell.of 96 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 139 1 (⟨3⟩ : Column .advice)) (Cell.of 96 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 139 1 (⟨4⟩ : Column .advice)) (Cell.of 96 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 139 2 (⟨2⟩ : Column .advice)) (Cell.of 96 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 139 2 (⟨3⟩ : Column .advice)) (Cell.of 96 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 139 2 (⟨4⟩ : Column .advice)) (Cell.of 96 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 140 0 (⟨3⟩ : Column .advice)) (Cell.of 135 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 140 0 (⟨4⟩ : Column .advice)) (Cell.of 135 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 140 1 (⟨2⟩ : Column .advice)) (Cell.of 135 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 140 1 (⟨3⟩ : Column .advice)) (Cell.of 135 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 140 1 (⟨4⟩ : Column .advice)) (Cell.of 135 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 140 2 (⟨2⟩ : Column .advice)) (Cell.of 135 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 140 2 (⟨3⟩ : Column .advice)) (Cell.of 135 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 140 2 (⟨4⟩ : Column .advice)) (Cell.of 135 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 141 0 (⟨3⟩ : Column .advice)) (Cell.of 93 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 141 0 (⟨4⟩ : Column .advice)) (Cell.of 120 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 141 1 (⟨3⟩ : Column .advice)) (Cell.of 139 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 141 1 (⟨4⟩ : Column .advice)) (Cell.of 140 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 141 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 141 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 141 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand38Checked : Checkpoint expand38Action expand37After expand38Output expand38After expand38Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand38Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand39Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand38Output[24]!
    let s1 ← Synthesis.sigma1 expand38Output[37]!
    let w ← Synthesis.prepareMessage #[expand38Output[23]!.combined.plain, expand38Output[32]!.combined.plain, s0, s1]
    return expand38Output.push w
def expand39Output : Array Synthesis.Word :=
  (expand38Output).push ({ combined := { plain := (Cell.of 144 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 144 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 144 0 (⟨0⟩ : Column .advice)), (Cell.of 144 0 (⟨5⟩ : Column .advice)), (Cell.of 144 1 (⟨5⟩ : Column .advice)), (Cell.of 144 2 (⟨5⟩ : Column .advice)), (Cell.of 144 0 (⟨1⟩ : Column .advice)), (Cell.of 144 1 (⟨0⟩ : Column .advice)), (Cell.of 144 1 (⟨1⟩ : Column .advice)), (Cell.of 144 2 (⟨0⟩ : Column .advice))] } })
def expand39After : Cursor :=
  ⟨145, [] ++ expand38After.constants⟩
def expand39Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 142 0 (⟨3⟩ : Column .advice)) (Cell.of 99 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 142 0 (⟨4⟩ : Column .advice)) (Cell.of 99 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 142 1 (⟨2⟩ : Column .advice)) (Cell.of 99 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 142 1 (⟨3⟩ : Column .advice)) (Cell.of 99 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 142 1 (⟨4⟩ : Column .advice)) (Cell.of 99 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 142 2 (⟨2⟩ : Column .advice)) (Cell.of 99 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 142 2 (⟨3⟩ : Column .advice)) (Cell.of 99 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 142 2 (⟨4⟩ : Column .advice)) (Cell.of 99 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 143 0 (⟨3⟩ : Column .advice)) (Cell.of 138 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 143 0 (⟨4⟩ : Column .advice)) (Cell.of 138 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 143 1 (⟨2⟩ : Column .advice)) (Cell.of 138 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 143 1 (⟨3⟩ : Column .advice)) (Cell.of 138 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 143 1 (⟨4⟩ : Column .advice)) (Cell.of 138 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 143 2 (⟨2⟩ : Column .advice)) (Cell.of 138 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 143 2 (⟨3⟩ : Column .advice)) (Cell.of 138 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 143 2 (⟨4⟩ : Column .advice)) (Cell.of 138 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 144 0 (⟨3⟩ : Column .advice)) (Cell.of 96 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 144 0 (⟨4⟩ : Column .advice)) (Cell.of 123 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 144 1 (⟨3⟩ : Column .advice)) (Cell.of 142 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 144 1 (⟨4⟩ : Column .advice)) (Cell.of 143 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 144 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 144 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 144 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand39Checked : Checkpoint expand39Action expand38After expand39Output expand39After expand39Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand39Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand40Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand39Output[25]!
    let s1 ← Synthesis.sigma1 expand39Output[38]!
    let w ← Synthesis.prepareMessage #[expand39Output[24]!.combined.plain, expand39Output[33]!.combined.plain, s0, s1]
    return expand39Output.push w
def expand40Output : Array Synthesis.Word :=
  (expand39Output).push ({ combined := { plain := (Cell.of 147 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 147 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 147 0 (⟨0⟩ : Column .advice)), (Cell.of 147 0 (⟨5⟩ : Column .advice)), (Cell.of 147 1 (⟨5⟩ : Column .advice)), (Cell.of 147 2 (⟨5⟩ : Column .advice)), (Cell.of 147 0 (⟨1⟩ : Column .advice)), (Cell.of 147 1 (⟨0⟩ : Column .advice)), (Cell.of 147 1 (⟨1⟩ : Column .advice)), (Cell.of 147 2 (⟨0⟩ : Column .advice))] } })
def expand40After : Cursor :=
  ⟨148, [] ++ expand39After.constants⟩
def expand40Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 145 0 (⟨3⟩ : Column .advice)) (Cell.of 102 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 145 0 (⟨4⟩ : Column .advice)) (Cell.of 102 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 145 1 (⟨2⟩ : Column .advice)) (Cell.of 102 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 145 1 (⟨3⟩ : Column .advice)) (Cell.of 102 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 145 1 (⟨4⟩ : Column .advice)) (Cell.of 102 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 145 2 (⟨2⟩ : Column .advice)) (Cell.of 102 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 145 2 (⟨3⟩ : Column .advice)) (Cell.of 102 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 145 2 (⟨4⟩ : Column .advice)) (Cell.of 102 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 146 0 (⟨3⟩ : Column .advice)) (Cell.of 141 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 146 0 (⟨4⟩ : Column .advice)) (Cell.of 141 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 146 1 (⟨2⟩ : Column .advice)) (Cell.of 141 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 146 1 (⟨3⟩ : Column .advice)) (Cell.of 141 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 146 1 (⟨4⟩ : Column .advice)) (Cell.of 141 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 146 2 (⟨2⟩ : Column .advice)) (Cell.of 141 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 146 2 (⟨3⟩ : Column .advice)) (Cell.of 141 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 146 2 (⟨4⟩ : Column .advice)) (Cell.of 141 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 147 0 (⟨3⟩ : Column .advice)) (Cell.of 99 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 147 0 (⟨4⟩ : Column .advice)) (Cell.of 126 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 147 1 (⟨3⟩ : Column .advice)) (Cell.of 145 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 147 1 (⟨4⟩ : Column .advice)) (Cell.of 146 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 147 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 147 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 147 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand40Checked : Checkpoint expand40Action expand39After expand40Output expand40After expand40Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand40Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand41Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand40Output[26]!
    let s1 ← Synthesis.sigma1 expand40Output[39]!
    let w ← Synthesis.prepareMessage #[expand40Output[25]!.combined.plain, expand40Output[34]!.combined.plain, s0, s1]
    return expand40Output.push w
def expand41Output : Array Synthesis.Word :=
  (expand40Output).push ({ combined := { plain := (Cell.of 150 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 150 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 150 0 (⟨0⟩ : Column .advice)), (Cell.of 150 0 (⟨5⟩ : Column .advice)), (Cell.of 150 1 (⟨5⟩ : Column .advice)), (Cell.of 150 2 (⟨5⟩ : Column .advice)), (Cell.of 150 0 (⟨1⟩ : Column .advice)), (Cell.of 150 1 (⟨0⟩ : Column .advice)), (Cell.of 150 1 (⟨1⟩ : Column .advice)), (Cell.of 150 2 (⟨0⟩ : Column .advice))] } })
def expand41After : Cursor :=
  ⟨151, [] ++ expand40After.constants⟩
def expand41Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 148 0 (⟨3⟩ : Column .advice)) (Cell.of 105 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 148 0 (⟨4⟩ : Column .advice)) (Cell.of 105 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 148 1 (⟨2⟩ : Column .advice)) (Cell.of 105 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 148 1 (⟨3⟩ : Column .advice)) (Cell.of 105 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 148 1 (⟨4⟩ : Column .advice)) (Cell.of 105 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 148 2 (⟨2⟩ : Column .advice)) (Cell.of 105 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 148 2 (⟨3⟩ : Column .advice)) (Cell.of 105 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 148 2 (⟨4⟩ : Column .advice)) (Cell.of 105 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 149 0 (⟨3⟩ : Column .advice)) (Cell.of 144 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 149 0 (⟨4⟩ : Column .advice)) (Cell.of 144 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 149 1 (⟨2⟩ : Column .advice)) (Cell.of 144 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 149 1 (⟨3⟩ : Column .advice)) (Cell.of 144 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 149 1 (⟨4⟩ : Column .advice)) (Cell.of 144 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 149 2 (⟨2⟩ : Column .advice)) (Cell.of 144 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 149 2 (⟨3⟩ : Column .advice)) (Cell.of 144 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 149 2 (⟨4⟩ : Column .advice)) (Cell.of 144 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 150 0 (⟨3⟩ : Column .advice)) (Cell.of 102 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 150 0 (⟨4⟩ : Column .advice)) (Cell.of 129 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 150 1 (⟨3⟩ : Column .advice)) (Cell.of 148 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 150 1 (⟨4⟩ : Column .advice)) (Cell.of 149 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 150 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 150 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 150 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand41Checked : Checkpoint expand41Action expand40After expand41Output expand41After expand41Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand41Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand42Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand41Output[27]!
    let s1 ← Synthesis.sigma1 expand41Output[40]!
    let w ← Synthesis.prepareMessage #[expand41Output[26]!.combined.plain, expand41Output[35]!.combined.plain, s0, s1]
    return expand41Output.push w
def expand42Output : Array Synthesis.Word :=
  (expand41Output).push ({ combined := { plain := (Cell.of 153 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 153 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 153 0 (⟨0⟩ : Column .advice)), (Cell.of 153 0 (⟨5⟩ : Column .advice)), (Cell.of 153 1 (⟨5⟩ : Column .advice)), (Cell.of 153 2 (⟨5⟩ : Column .advice)), (Cell.of 153 0 (⟨1⟩ : Column .advice)), (Cell.of 153 1 (⟨0⟩ : Column .advice)), (Cell.of 153 1 (⟨1⟩ : Column .advice)), (Cell.of 153 2 (⟨0⟩ : Column .advice))] } })
def expand42After : Cursor :=
  ⟨154, [] ++ expand41After.constants⟩
def expand42Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 151 0 (⟨3⟩ : Column .advice)) (Cell.of 108 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 151 0 (⟨4⟩ : Column .advice)) (Cell.of 108 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 151 1 (⟨2⟩ : Column .advice)) (Cell.of 108 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 151 1 (⟨3⟩ : Column .advice)) (Cell.of 108 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 151 1 (⟨4⟩ : Column .advice)) (Cell.of 108 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 151 2 (⟨2⟩ : Column .advice)) (Cell.of 108 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 151 2 (⟨3⟩ : Column .advice)) (Cell.of 108 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 151 2 (⟨4⟩ : Column .advice)) (Cell.of 108 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 152 0 (⟨3⟩ : Column .advice)) (Cell.of 147 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 152 0 (⟨4⟩ : Column .advice)) (Cell.of 147 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 152 1 (⟨2⟩ : Column .advice)) (Cell.of 147 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 152 1 (⟨3⟩ : Column .advice)) (Cell.of 147 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 152 1 (⟨4⟩ : Column .advice)) (Cell.of 147 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 152 2 (⟨2⟩ : Column .advice)) (Cell.of 147 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 152 2 (⟨3⟩ : Column .advice)) (Cell.of 147 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 152 2 (⟨4⟩ : Column .advice)) (Cell.of 147 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 153 0 (⟨3⟩ : Column .advice)) (Cell.of 105 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 153 0 (⟨4⟩ : Column .advice)) (Cell.of 132 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 153 1 (⟨3⟩ : Column .advice)) (Cell.of 151 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 153 1 (⟨4⟩ : Column .advice)) (Cell.of 152 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 153 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 153 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 153 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand42Checked : Checkpoint expand42Action expand41After expand42Output expand42After expand42Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand42Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand43Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand42Output[28]!
    let s1 ← Synthesis.sigma1 expand42Output[41]!
    let w ← Synthesis.prepareMessage #[expand42Output[27]!.combined.plain, expand42Output[36]!.combined.plain, s0, s1]
    return expand42Output.push w
def expand43Output : Array Synthesis.Word :=
  (expand42Output).push ({ combined := { plain := (Cell.of 156 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 156 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 156 0 (⟨0⟩ : Column .advice)), (Cell.of 156 0 (⟨5⟩ : Column .advice)), (Cell.of 156 1 (⟨5⟩ : Column .advice)), (Cell.of 156 2 (⟨5⟩ : Column .advice)), (Cell.of 156 0 (⟨1⟩ : Column .advice)), (Cell.of 156 1 (⟨0⟩ : Column .advice)), (Cell.of 156 1 (⟨1⟩ : Column .advice)), (Cell.of 156 2 (⟨0⟩ : Column .advice))] } })
def expand43After : Cursor :=
  ⟨157, [] ++ expand42After.constants⟩
def expand43Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 154 0 (⟨3⟩ : Column .advice)) (Cell.of 111 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 154 0 (⟨4⟩ : Column .advice)) (Cell.of 111 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 154 1 (⟨2⟩ : Column .advice)) (Cell.of 111 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 154 1 (⟨3⟩ : Column .advice)) (Cell.of 111 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 154 1 (⟨4⟩ : Column .advice)) (Cell.of 111 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 154 2 (⟨2⟩ : Column .advice)) (Cell.of 111 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 154 2 (⟨3⟩ : Column .advice)) (Cell.of 111 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 154 2 (⟨4⟩ : Column .advice)) (Cell.of 111 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 155 0 (⟨3⟩ : Column .advice)) (Cell.of 150 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 155 0 (⟨4⟩ : Column .advice)) (Cell.of 150 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 155 1 (⟨2⟩ : Column .advice)) (Cell.of 150 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 155 1 (⟨3⟩ : Column .advice)) (Cell.of 150 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 155 1 (⟨4⟩ : Column .advice)) (Cell.of 150 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 155 2 (⟨2⟩ : Column .advice)) (Cell.of 150 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 155 2 (⟨3⟩ : Column .advice)) (Cell.of 150 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 155 2 (⟨4⟩ : Column .advice)) (Cell.of 150 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 156 0 (⟨3⟩ : Column .advice)) (Cell.of 108 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 156 0 (⟨4⟩ : Column .advice)) (Cell.of 135 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 156 1 (⟨3⟩ : Column .advice)) (Cell.of 154 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 156 1 (⟨4⟩ : Column .advice)) (Cell.of 155 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 156 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 156 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 156 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand43Checked : Checkpoint expand43Action expand42After expand43Output expand43After expand43Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand43Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand44Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand43Output[29]!
    let s1 ← Synthesis.sigma1 expand43Output[42]!
    let w ← Synthesis.prepareMessage #[expand43Output[28]!.combined.plain, expand43Output[37]!.combined.plain, s0, s1]
    return expand43Output.push w
def expand44Output : Array Synthesis.Word :=
  (expand43Output).push ({ combined := { plain := (Cell.of 159 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 159 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 159 0 (⟨0⟩ : Column .advice)), (Cell.of 159 0 (⟨5⟩ : Column .advice)), (Cell.of 159 1 (⟨5⟩ : Column .advice)), (Cell.of 159 2 (⟨5⟩ : Column .advice)), (Cell.of 159 0 (⟨1⟩ : Column .advice)), (Cell.of 159 1 (⟨0⟩ : Column .advice)), (Cell.of 159 1 (⟨1⟩ : Column .advice)), (Cell.of 159 2 (⟨0⟩ : Column .advice))] } })
def expand44After : Cursor :=
  ⟨160, [] ++ expand43After.constants⟩
def expand44Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 157 0 (⟨3⟩ : Column .advice)) (Cell.of 114 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 157 0 (⟨4⟩ : Column .advice)) (Cell.of 114 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 157 1 (⟨2⟩ : Column .advice)) (Cell.of 114 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 157 1 (⟨3⟩ : Column .advice)) (Cell.of 114 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 157 1 (⟨4⟩ : Column .advice)) (Cell.of 114 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 157 2 (⟨2⟩ : Column .advice)) (Cell.of 114 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 157 2 (⟨3⟩ : Column .advice)) (Cell.of 114 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 157 2 (⟨4⟩ : Column .advice)) (Cell.of 114 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 158 0 (⟨3⟩ : Column .advice)) (Cell.of 153 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 158 0 (⟨4⟩ : Column .advice)) (Cell.of 153 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 158 1 (⟨2⟩ : Column .advice)) (Cell.of 153 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 158 1 (⟨3⟩ : Column .advice)) (Cell.of 153 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 158 1 (⟨4⟩ : Column .advice)) (Cell.of 153 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 158 2 (⟨2⟩ : Column .advice)) (Cell.of 153 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 158 2 (⟨3⟩ : Column .advice)) (Cell.of 153 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 158 2 (⟨4⟩ : Column .advice)) (Cell.of 153 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 159 0 (⟨3⟩ : Column .advice)) (Cell.of 111 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 159 0 (⟨4⟩ : Column .advice)) (Cell.of 138 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 159 1 (⟨3⟩ : Column .advice)) (Cell.of 157 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 159 1 (⟨4⟩ : Column .advice)) (Cell.of 158 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 159 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 159 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 159 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand44Checked : Checkpoint expand44Action expand43After expand44Output expand44After expand44Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand44Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand45Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand44Output[30]!
    let s1 ← Synthesis.sigma1 expand44Output[43]!
    let w ← Synthesis.prepareMessage #[expand44Output[29]!.combined.plain, expand44Output[38]!.combined.plain, s0, s1]
    return expand44Output.push w
def expand45Output : Array Synthesis.Word :=
  (expand44Output).push ({ combined := { plain := (Cell.of 162 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 162 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 162 0 (⟨0⟩ : Column .advice)), (Cell.of 162 0 (⟨5⟩ : Column .advice)), (Cell.of 162 1 (⟨5⟩ : Column .advice)), (Cell.of 162 2 (⟨5⟩ : Column .advice)), (Cell.of 162 0 (⟨1⟩ : Column .advice)), (Cell.of 162 1 (⟨0⟩ : Column .advice)), (Cell.of 162 1 (⟨1⟩ : Column .advice)), (Cell.of 162 2 (⟨0⟩ : Column .advice))] } })
def expand45After : Cursor :=
  ⟨163, [] ++ expand44After.constants⟩
def expand45Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 160 0 (⟨3⟩ : Column .advice)) (Cell.of 117 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 160 0 (⟨4⟩ : Column .advice)) (Cell.of 117 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 160 1 (⟨2⟩ : Column .advice)) (Cell.of 117 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 160 1 (⟨3⟩ : Column .advice)) (Cell.of 117 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 160 1 (⟨4⟩ : Column .advice)) (Cell.of 117 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 160 2 (⟨2⟩ : Column .advice)) (Cell.of 117 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 160 2 (⟨3⟩ : Column .advice)) (Cell.of 117 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 160 2 (⟨4⟩ : Column .advice)) (Cell.of 117 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 161 0 (⟨3⟩ : Column .advice)) (Cell.of 156 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 161 0 (⟨4⟩ : Column .advice)) (Cell.of 156 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 161 1 (⟨2⟩ : Column .advice)) (Cell.of 156 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 161 1 (⟨3⟩ : Column .advice)) (Cell.of 156 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 161 1 (⟨4⟩ : Column .advice)) (Cell.of 156 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 161 2 (⟨2⟩ : Column .advice)) (Cell.of 156 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 161 2 (⟨3⟩ : Column .advice)) (Cell.of 156 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 161 2 (⟨4⟩ : Column .advice)) (Cell.of 156 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 162 0 (⟨3⟩ : Column .advice)) (Cell.of 114 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 162 0 (⟨4⟩ : Column .advice)) (Cell.of 141 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 162 1 (⟨3⟩ : Column .advice)) (Cell.of 160 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 162 1 (⟨4⟩ : Column .advice)) (Cell.of 161 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 162 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 162 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 162 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand45Checked : Checkpoint expand45Action expand44After expand45Output expand45After expand45Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand45Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand46Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand45Output[31]!
    let s1 ← Synthesis.sigma1 expand45Output[44]!
    let w ← Synthesis.prepareMessage #[expand45Output[30]!.combined.plain, expand45Output[39]!.combined.plain, s0, s1]
    return expand45Output.push w
def expand46Output : Array Synthesis.Word :=
  (expand45Output).push ({ combined := { plain := (Cell.of 165 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 165 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 165 0 (⟨0⟩ : Column .advice)), (Cell.of 165 0 (⟨5⟩ : Column .advice)), (Cell.of 165 1 (⟨5⟩ : Column .advice)), (Cell.of 165 2 (⟨5⟩ : Column .advice)), (Cell.of 165 0 (⟨1⟩ : Column .advice)), (Cell.of 165 1 (⟨0⟩ : Column .advice)), (Cell.of 165 1 (⟨1⟩ : Column .advice)), (Cell.of 165 2 (⟨0⟩ : Column .advice))] } })
def expand46After : Cursor :=
  ⟨166, [] ++ expand45After.constants⟩
def expand46Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 163 0 (⟨3⟩ : Column .advice)) (Cell.of 120 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 163 0 (⟨4⟩ : Column .advice)) (Cell.of 120 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 163 1 (⟨2⟩ : Column .advice)) (Cell.of 120 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 163 1 (⟨3⟩ : Column .advice)) (Cell.of 120 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 163 1 (⟨4⟩ : Column .advice)) (Cell.of 120 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 163 2 (⟨2⟩ : Column .advice)) (Cell.of 120 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 163 2 (⟨3⟩ : Column .advice)) (Cell.of 120 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 163 2 (⟨4⟩ : Column .advice)) (Cell.of 120 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 164 0 (⟨3⟩ : Column .advice)) (Cell.of 159 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 164 0 (⟨4⟩ : Column .advice)) (Cell.of 159 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 164 1 (⟨2⟩ : Column .advice)) (Cell.of 159 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 164 1 (⟨3⟩ : Column .advice)) (Cell.of 159 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 164 1 (⟨4⟩ : Column .advice)) (Cell.of 159 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 164 2 (⟨2⟩ : Column .advice)) (Cell.of 159 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 164 2 (⟨3⟩ : Column .advice)) (Cell.of 159 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 164 2 (⟨4⟩ : Column .advice)) (Cell.of 159 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 165 0 (⟨3⟩ : Column .advice)) (Cell.of 117 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 165 0 (⟨4⟩ : Column .advice)) (Cell.of 144 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 165 1 (⟨3⟩ : Column .advice)) (Cell.of 163 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 165 1 (⟨4⟩ : Column .advice)) (Cell.of 164 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 165 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 165 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 165 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand46Checked : Checkpoint expand46Action expand45After expand46Output expand46After expand46Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand46Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand47Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand46Output[32]!
    let s1 ← Synthesis.sigma1 expand46Output[45]!
    let w ← Synthesis.prepareMessage #[expand46Output[31]!.combined.plain, expand46Output[40]!.combined.plain, s0, s1]
    return expand46Output.push w
def expand47Output : Array Synthesis.Word :=
  (expand46Output).push ({ combined := { plain := (Cell.of 168 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 168 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 168 0 (⟨0⟩ : Column .advice)), (Cell.of 168 0 (⟨5⟩ : Column .advice)), (Cell.of 168 1 (⟨5⟩ : Column .advice)), (Cell.of 168 2 (⟨5⟩ : Column .advice)), (Cell.of 168 0 (⟨1⟩ : Column .advice)), (Cell.of 168 1 (⟨0⟩ : Column .advice)), (Cell.of 168 1 (⟨1⟩ : Column .advice)), (Cell.of 168 2 (⟨0⟩ : Column .advice))] } })
def expand47After : Cursor :=
  ⟨169, [] ++ expand46After.constants⟩
def expand47Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 166 0 (⟨3⟩ : Column .advice)) (Cell.of 123 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 166 0 (⟨4⟩ : Column .advice)) (Cell.of 123 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 166 1 (⟨2⟩ : Column .advice)) (Cell.of 123 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 166 1 (⟨3⟩ : Column .advice)) (Cell.of 123 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 166 1 (⟨4⟩ : Column .advice)) (Cell.of 123 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 166 2 (⟨2⟩ : Column .advice)) (Cell.of 123 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 166 2 (⟨3⟩ : Column .advice)) (Cell.of 123 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 166 2 (⟨4⟩ : Column .advice)) (Cell.of 123 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 167 0 (⟨3⟩ : Column .advice)) (Cell.of 162 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 167 0 (⟨4⟩ : Column .advice)) (Cell.of 162 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 167 1 (⟨2⟩ : Column .advice)) (Cell.of 162 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 167 1 (⟨3⟩ : Column .advice)) (Cell.of 162 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 167 1 (⟨4⟩ : Column .advice)) (Cell.of 162 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 167 2 (⟨2⟩ : Column .advice)) (Cell.of 162 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 167 2 (⟨3⟩ : Column .advice)) (Cell.of 162 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 167 2 (⟨4⟩ : Column .advice)) (Cell.of 162 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 168 0 (⟨3⟩ : Column .advice)) (Cell.of 120 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 168 0 (⟨4⟩ : Column .advice)) (Cell.of 147 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 168 1 (⟨3⟩ : Column .advice)) (Cell.of 166 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 168 1 (⟨4⟩ : Column .advice)) (Cell.of 167 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 168 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 168 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 168 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand47Checked : Checkpoint expand47Action expand46After expand47Output expand47After expand47Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand47Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand48Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand47Output[33]!
    let s1 ← Synthesis.sigma1 expand47Output[46]!
    let w ← Synthesis.prepareMessage #[expand47Output[32]!.combined.plain, expand47Output[41]!.combined.plain, s0, s1]
    return expand47Output.push w
def expand48Output : Array Synthesis.Word :=
  (expand47Output).push ({ combined := { plain := (Cell.of 171 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 171 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 171 0 (⟨0⟩ : Column .advice)), (Cell.of 171 0 (⟨5⟩ : Column .advice)), (Cell.of 171 1 (⟨5⟩ : Column .advice)), (Cell.of 171 2 (⟨5⟩ : Column .advice)), (Cell.of 171 0 (⟨1⟩ : Column .advice)), (Cell.of 171 1 (⟨0⟩ : Column .advice)), (Cell.of 171 1 (⟨1⟩ : Column .advice)), (Cell.of 171 2 (⟨0⟩ : Column .advice))] } })
def expand48After : Cursor :=
  ⟨172, [] ++ expand47After.constants⟩
def expand48Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 169 0 (⟨3⟩ : Column .advice)) (Cell.of 126 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 169 0 (⟨4⟩ : Column .advice)) (Cell.of 126 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 169 1 (⟨2⟩ : Column .advice)) (Cell.of 126 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 169 1 (⟨3⟩ : Column .advice)) (Cell.of 126 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 169 1 (⟨4⟩ : Column .advice)) (Cell.of 126 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 169 2 (⟨2⟩ : Column .advice)) (Cell.of 126 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 169 2 (⟨3⟩ : Column .advice)) (Cell.of 126 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 169 2 (⟨4⟩ : Column .advice)) (Cell.of 126 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 170 0 (⟨3⟩ : Column .advice)) (Cell.of 165 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 170 0 (⟨4⟩ : Column .advice)) (Cell.of 165 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 170 1 (⟨2⟩ : Column .advice)) (Cell.of 165 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 170 1 (⟨3⟩ : Column .advice)) (Cell.of 165 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 170 1 (⟨4⟩ : Column .advice)) (Cell.of 165 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 170 2 (⟨2⟩ : Column .advice)) (Cell.of 165 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 170 2 (⟨3⟩ : Column .advice)) (Cell.of 165 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 170 2 (⟨4⟩ : Column .advice)) (Cell.of 165 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 171 0 (⟨3⟩ : Column .advice)) (Cell.of 123 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 171 0 (⟨4⟩ : Column .advice)) (Cell.of 150 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 171 1 (⟨3⟩ : Column .advice)) (Cell.of 169 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 171 1 (⟨4⟩ : Column .advice)) (Cell.of 170 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 171 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 171 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 171 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand48Checked : Checkpoint expand48Action expand47After expand48Output expand48After expand48Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand48Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand49Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand48Output[34]!
    let s1 ← Synthesis.sigma1 expand48Output[47]!
    let w ← Synthesis.prepareMessage #[expand48Output[33]!.combined.plain, expand48Output[42]!.combined.plain, s0, s1]
    return expand48Output.push w
def expand49Output : Array Synthesis.Word :=
  (expand48Output).push ({ combined := { plain := (Cell.of 174 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 174 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 174 0 (⟨0⟩ : Column .advice)), (Cell.of 174 0 (⟨5⟩ : Column .advice)), (Cell.of 174 1 (⟨5⟩ : Column .advice)), (Cell.of 174 2 (⟨5⟩ : Column .advice)), (Cell.of 174 0 (⟨1⟩ : Column .advice)), (Cell.of 174 1 (⟨0⟩ : Column .advice)), (Cell.of 174 1 (⟨1⟩ : Column .advice)), (Cell.of 174 2 (⟨0⟩ : Column .advice))] } })
def expand49After : Cursor :=
  ⟨175, [] ++ expand48After.constants⟩
def expand49Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 172 0 (⟨3⟩ : Column .advice)) (Cell.of 129 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 172 0 (⟨4⟩ : Column .advice)) (Cell.of 129 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 172 1 (⟨2⟩ : Column .advice)) (Cell.of 129 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 172 1 (⟨3⟩ : Column .advice)) (Cell.of 129 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 172 1 (⟨4⟩ : Column .advice)) (Cell.of 129 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 172 2 (⟨2⟩ : Column .advice)) (Cell.of 129 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 172 2 (⟨3⟩ : Column .advice)) (Cell.of 129 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 172 2 (⟨4⟩ : Column .advice)) (Cell.of 129 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 173 0 (⟨3⟩ : Column .advice)) (Cell.of 168 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 173 0 (⟨4⟩ : Column .advice)) (Cell.of 168 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 173 1 (⟨2⟩ : Column .advice)) (Cell.of 168 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 173 1 (⟨3⟩ : Column .advice)) (Cell.of 168 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 173 1 (⟨4⟩ : Column .advice)) (Cell.of 168 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 173 2 (⟨2⟩ : Column .advice)) (Cell.of 168 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 173 2 (⟨3⟩ : Column .advice)) (Cell.of 168 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 173 2 (⟨4⟩ : Column .advice)) (Cell.of 168 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 174 0 (⟨3⟩ : Column .advice)) (Cell.of 126 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 174 0 (⟨4⟩ : Column .advice)) (Cell.of 153 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 174 1 (⟨3⟩ : Column .advice)) (Cell.of 172 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 174 1 (⟨4⟩ : Column .advice)) (Cell.of 173 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 174 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 174 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 174 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand49Checked : Checkpoint expand49Action expand48After expand49Output expand49After expand49Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand49Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand50Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand49Output[35]!
    let s1 ← Synthesis.sigma1 expand49Output[48]!
    let w ← Synthesis.prepareMessage #[expand49Output[34]!.combined.plain, expand49Output[43]!.combined.plain, s0, s1]
    return expand49Output.push w
def expand50Output : Array Synthesis.Word :=
  (expand49Output).push ({ combined := { plain := (Cell.of 177 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 177 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 177 0 (⟨0⟩ : Column .advice)), (Cell.of 177 0 (⟨5⟩ : Column .advice)), (Cell.of 177 1 (⟨5⟩ : Column .advice)), (Cell.of 177 2 (⟨5⟩ : Column .advice)), (Cell.of 177 0 (⟨1⟩ : Column .advice)), (Cell.of 177 1 (⟨0⟩ : Column .advice)), (Cell.of 177 1 (⟨1⟩ : Column .advice)), (Cell.of 177 2 (⟨0⟩ : Column .advice))] } })
def expand50After : Cursor :=
  ⟨178, [] ++ expand49After.constants⟩
def expand50Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 175 0 (⟨3⟩ : Column .advice)) (Cell.of 132 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 175 0 (⟨4⟩ : Column .advice)) (Cell.of 132 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 175 1 (⟨2⟩ : Column .advice)) (Cell.of 132 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 175 1 (⟨3⟩ : Column .advice)) (Cell.of 132 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 175 1 (⟨4⟩ : Column .advice)) (Cell.of 132 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 175 2 (⟨2⟩ : Column .advice)) (Cell.of 132 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 175 2 (⟨3⟩ : Column .advice)) (Cell.of 132 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 175 2 (⟨4⟩ : Column .advice)) (Cell.of 132 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 176 0 (⟨3⟩ : Column .advice)) (Cell.of 171 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 176 0 (⟨4⟩ : Column .advice)) (Cell.of 171 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 176 1 (⟨2⟩ : Column .advice)) (Cell.of 171 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 176 1 (⟨3⟩ : Column .advice)) (Cell.of 171 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 176 1 (⟨4⟩ : Column .advice)) (Cell.of 171 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 176 2 (⟨2⟩ : Column .advice)) (Cell.of 171 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 176 2 (⟨3⟩ : Column .advice)) (Cell.of 171 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 176 2 (⟨4⟩ : Column .advice)) (Cell.of 171 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 177 0 (⟨3⟩ : Column .advice)) (Cell.of 129 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 177 0 (⟨4⟩ : Column .advice)) (Cell.of 156 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 177 1 (⟨3⟩ : Column .advice)) (Cell.of 175 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 177 1 (⟨4⟩ : Column .advice)) (Cell.of 176 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 177 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 177 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 177 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand50Checked : Checkpoint expand50Action expand49After expand50Output expand50After expand50Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand50Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand51Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand50Output[36]!
    let s1 ← Synthesis.sigma1 expand50Output[49]!
    let w ← Synthesis.prepareMessage #[expand50Output[35]!.combined.plain, expand50Output[44]!.combined.plain, s0, s1]
    return expand50Output.push w
def expand51Output : Array Synthesis.Word :=
  (expand50Output).push ({ combined := { plain := (Cell.of 180 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 180 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 180 0 (⟨0⟩ : Column .advice)), (Cell.of 180 0 (⟨5⟩ : Column .advice)), (Cell.of 180 1 (⟨5⟩ : Column .advice)), (Cell.of 180 2 (⟨5⟩ : Column .advice)), (Cell.of 180 0 (⟨1⟩ : Column .advice)), (Cell.of 180 1 (⟨0⟩ : Column .advice)), (Cell.of 180 1 (⟨1⟩ : Column .advice)), (Cell.of 180 2 (⟨0⟩ : Column .advice))] } })
def expand51After : Cursor :=
  ⟨181, [] ++ expand50After.constants⟩
def expand51Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 178 0 (⟨3⟩ : Column .advice)) (Cell.of 135 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 178 0 (⟨4⟩ : Column .advice)) (Cell.of 135 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 178 1 (⟨2⟩ : Column .advice)) (Cell.of 135 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 178 1 (⟨3⟩ : Column .advice)) (Cell.of 135 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 178 1 (⟨4⟩ : Column .advice)) (Cell.of 135 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 178 2 (⟨2⟩ : Column .advice)) (Cell.of 135 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 178 2 (⟨3⟩ : Column .advice)) (Cell.of 135 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 178 2 (⟨4⟩ : Column .advice)) (Cell.of 135 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 179 0 (⟨3⟩ : Column .advice)) (Cell.of 174 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 179 0 (⟨4⟩ : Column .advice)) (Cell.of 174 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 179 1 (⟨2⟩ : Column .advice)) (Cell.of 174 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 179 1 (⟨3⟩ : Column .advice)) (Cell.of 174 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 179 1 (⟨4⟩ : Column .advice)) (Cell.of 174 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 179 2 (⟨2⟩ : Column .advice)) (Cell.of 174 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 179 2 (⟨3⟩ : Column .advice)) (Cell.of 174 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 179 2 (⟨4⟩ : Column .advice)) (Cell.of 174 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 180 0 (⟨3⟩ : Column .advice)) (Cell.of 132 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 180 0 (⟨4⟩ : Column .advice)) (Cell.of 159 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 180 1 (⟨3⟩ : Column .advice)) (Cell.of 178 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 180 1 (⟨4⟩ : Column .advice)) (Cell.of 179 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 180 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 180 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 180 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand51Checked : Checkpoint expand51Action expand50After expand51Output expand51After expand51Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand51Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand52Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand51Output[37]!
    let s1 ← Synthesis.sigma1 expand51Output[50]!
    let w ← Synthesis.prepareMessage #[expand51Output[36]!.combined.plain, expand51Output[45]!.combined.plain, s0, s1]
    return expand51Output.push w
def expand52Output : Array Synthesis.Word :=
  (expand51Output).push ({ combined := { plain := (Cell.of 183 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 183 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 183 0 (⟨0⟩ : Column .advice)), (Cell.of 183 0 (⟨5⟩ : Column .advice)), (Cell.of 183 1 (⟨5⟩ : Column .advice)), (Cell.of 183 2 (⟨5⟩ : Column .advice)), (Cell.of 183 0 (⟨1⟩ : Column .advice)), (Cell.of 183 1 (⟨0⟩ : Column .advice)), (Cell.of 183 1 (⟨1⟩ : Column .advice)), (Cell.of 183 2 (⟨0⟩ : Column .advice))] } })
def expand52After : Cursor :=
  ⟨184, [] ++ expand51After.constants⟩
def expand52Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 181 0 (⟨3⟩ : Column .advice)) (Cell.of 138 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 181 0 (⟨4⟩ : Column .advice)) (Cell.of 138 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 181 1 (⟨2⟩ : Column .advice)) (Cell.of 138 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 181 1 (⟨3⟩ : Column .advice)) (Cell.of 138 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 181 1 (⟨4⟩ : Column .advice)) (Cell.of 138 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 181 2 (⟨2⟩ : Column .advice)) (Cell.of 138 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 181 2 (⟨3⟩ : Column .advice)) (Cell.of 138 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 181 2 (⟨4⟩ : Column .advice)) (Cell.of 138 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 182 0 (⟨3⟩ : Column .advice)) (Cell.of 177 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 182 0 (⟨4⟩ : Column .advice)) (Cell.of 177 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 182 1 (⟨2⟩ : Column .advice)) (Cell.of 177 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 182 1 (⟨3⟩ : Column .advice)) (Cell.of 177 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 182 1 (⟨4⟩ : Column .advice)) (Cell.of 177 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 182 2 (⟨2⟩ : Column .advice)) (Cell.of 177 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 182 2 (⟨3⟩ : Column .advice)) (Cell.of 177 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 182 2 (⟨4⟩ : Column .advice)) (Cell.of 177 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 183 0 (⟨3⟩ : Column .advice)) (Cell.of 135 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 183 0 (⟨4⟩ : Column .advice)) (Cell.of 162 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 183 1 (⟨3⟩ : Column .advice)) (Cell.of 181 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 183 1 (⟨4⟩ : Column .advice)) (Cell.of 182 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 183 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 183 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 183 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand52Checked : Checkpoint expand52Action expand51After expand52Output expand52After expand52Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand52Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand53Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand52Output[38]!
    let s1 ← Synthesis.sigma1 expand52Output[51]!
    let w ← Synthesis.prepareMessage #[expand52Output[37]!.combined.plain, expand52Output[46]!.combined.plain, s0, s1]
    return expand52Output.push w
def expand53Output : Array Synthesis.Word :=
  (expand52Output).push ({ combined := { plain := (Cell.of 186 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 186 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 186 0 (⟨0⟩ : Column .advice)), (Cell.of 186 0 (⟨5⟩ : Column .advice)), (Cell.of 186 1 (⟨5⟩ : Column .advice)), (Cell.of 186 2 (⟨5⟩ : Column .advice)), (Cell.of 186 0 (⟨1⟩ : Column .advice)), (Cell.of 186 1 (⟨0⟩ : Column .advice)), (Cell.of 186 1 (⟨1⟩ : Column .advice)), (Cell.of 186 2 (⟨0⟩ : Column .advice))] } })
def expand53After : Cursor :=
  ⟨187, [] ++ expand52After.constants⟩
def expand53Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 184 0 (⟨3⟩ : Column .advice)) (Cell.of 141 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 184 0 (⟨4⟩ : Column .advice)) (Cell.of 141 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 184 1 (⟨2⟩ : Column .advice)) (Cell.of 141 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 184 1 (⟨3⟩ : Column .advice)) (Cell.of 141 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 184 1 (⟨4⟩ : Column .advice)) (Cell.of 141 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 184 2 (⟨2⟩ : Column .advice)) (Cell.of 141 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 184 2 (⟨3⟩ : Column .advice)) (Cell.of 141 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 184 2 (⟨4⟩ : Column .advice)) (Cell.of 141 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 185 0 (⟨3⟩ : Column .advice)) (Cell.of 180 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 185 0 (⟨4⟩ : Column .advice)) (Cell.of 180 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 185 1 (⟨2⟩ : Column .advice)) (Cell.of 180 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 185 1 (⟨3⟩ : Column .advice)) (Cell.of 180 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 185 1 (⟨4⟩ : Column .advice)) (Cell.of 180 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 185 2 (⟨2⟩ : Column .advice)) (Cell.of 180 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 185 2 (⟨3⟩ : Column .advice)) (Cell.of 180 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 185 2 (⟨4⟩ : Column .advice)) (Cell.of 180 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 186 0 (⟨3⟩ : Column .advice)) (Cell.of 138 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 186 0 (⟨4⟩ : Column .advice)) (Cell.of 165 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 186 1 (⟨3⟩ : Column .advice)) (Cell.of 184 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 186 1 (⟨4⟩ : Column .advice)) (Cell.of 185 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 186 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 186 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 186 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand53Checked : Checkpoint expand53Action expand52After expand53Output expand53After expand53Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand53Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand54Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand53Output[39]!
    let s1 ← Synthesis.sigma1 expand53Output[52]!
    let w ← Synthesis.prepareMessage #[expand53Output[38]!.combined.plain, expand53Output[47]!.combined.plain, s0, s1]
    return expand53Output.push w
def expand54Output : Array Synthesis.Word :=
  (expand53Output).push ({ combined := { plain := (Cell.of 189 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 189 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 189 0 (⟨0⟩ : Column .advice)), (Cell.of 189 0 (⟨5⟩ : Column .advice)), (Cell.of 189 1 (⟨5⟩ : Column .advice)), (Cell.of 189 2 (⟨5⟩ : Column .advice)), (Cell.of 189 0 (⟨1⟩ : Column .advice)), (Cell.of 189 1 (⟨0⟩ : Column .advice)), (Cell.of 189 1 (⟨1⟩ : Column .advice)), (Cell.of 189 2 (⟨0⟩ : Column .advice))] } })
def expand54After : Cursor :=
  ⟨190, [] ++ expand53After.constants⟩
def expand54Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 187 0 (⟨3⟩ : Column .advice)) (Cell.of 144 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 187 0 (⟨4⟩ : Column .advice)) (Cell.of 144 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 187 1 (⟨2⟩ : Column .advice)) (Cell.of 144 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 187 1 (⟨3⟩ : Column .advice)) (Cell.of 144 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 187 1 (⟨4⟩ : Column .advice)) (Cell.of 144 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 187 2 (⟨2⟩ : Column .advice)) (Cell.of 144 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 187 2 (⟨3⟩ : Column .advice)) (Cell.of 144 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 187 2 (⟨4⟩ : Column .advice)) (Cell.of 144 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 188 0 (⟨3⟩ : Column .advice)) (Cell.of 183 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 188 0 (⟨4⟩ : Column .advice)) (Cell.of 183 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 188 1 (⟨2⟩ : Column .advice)) (Cell.of 183 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 188 1 (⟨3⟩ : Column .advice)) (Cell.of 183 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 188 1 (⟨4⟩ : Column .advice)) (Cell.of 183 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 188 2 (⟨2⟩ : Column .advice)) (Cell.of 183 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 188 2 (⟨3⟩ : Column .advice)) (Cell.of 183 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 188 2 (⟨4⟩ : Column .advice)) (Cell.of 183 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 189 0 (⟨3⟩ : Column .advice)) (Cell.of 141 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 189 0 (⟨4⟩ : Column .advice)) (Cell.of 168 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 189 1 (⟨3⟩ : Column .advice)) (Cell.of 187 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 189 1 (⟨4⟩ : Column .advice)) (Cell.of 188 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 189 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 189 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 189 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand54Checked : Checkpoint expand54Action expand53After expand54Output expand54After expand54Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand54Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand55Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand54Output[40]!
    let s1 ← Synthesis.sigma1 expand54Output[53]!
    let w ← Synthesis.prepareMessage #[expand54Output[39]!.combined.plain, expand54Output[48]!.combined.plain, s0, s1]
    return expand54Output.push w
def expand55Output : Array Synthesis.Word :=
  (expand54Output).push ({ combined := { plain := (Cell.of 192 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 192 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 192 0 (⟨0⟩ : Column .advice)), (Cell.of 192 0 (⟨5⟩ : Column .advice)), (Cell.of 192 1 (⟨5⟩ : Column .advice)), (Cell.of 192 2 (⟨5⟩ : Column .advice)), (Cell.of 192 0 (⟨1⟩ : Column .advice)), (Cell.of 192 1 (⟨0⟩ : Column .advice)), (Cell.of 192 1 (⟨1⟩ : Column .advice)), (Cell.of 192 2 (⟨0⟩ : Column .advice))] } })
def expand55After : Cursor :=
  ⟨193, [] ++ expand54After.constants⟩
def expand55Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 190 0 (⟨3⟩ : Column .advice)) (Cell.of 147 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 190 0 (⟨4⟩ : Column .advice)) (Cell.of 147 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 190 1 (⟨2⟩ : Column .advice)) (Cell.of 147 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 190 1 (⟨3⟩ : Column .advice)) (Cell.of 147 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 190 1 (⟨4⟩ : Column .advice)) (Cell.of 147 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 190 2 (⟨2⟩ : Column .advice)) (Cell.of 147 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 190 2 (⟨3⟩ : Column .advice)) (Cell.of 147 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 190 2 (⟨4⟩ : Column .advice)) (Cell.of 147 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 191 0 (⟨3⟩ : Column .advice)) (Cell.of 186 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 191 0 (⟨4⟩ : Column .advice)) (Cell.of 186 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 191 1 (⟨2⟩ : Column .advice)) (Cell.of 186 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 191 1 (⟨3⟩ : Column .advice)) (Cell.of 186 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 191 1 (⟨4⟩ : Column .advice)) (Cell.of 186 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 191 2 (⟨2⟩ : Column .advice)) (Cell.of 186 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 191 2 (⟨3⟩ : Column .advice)) (Cell.of 186 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 191 2 (⟨4⟩ : Column .advice)) (Cell.of 186 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 192 0 (⟨3⟩ : Column .advice)) (Cell.of 144 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 192 0 (⟨4⟩ : Column .advice)) (Cell.of 171 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 192 1 (⟨3⟩ : Column .advice)) (Cell.of 190 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 192 1 (⟨4⟩ : Column .advice)) (Cell.of 191 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 192 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 192 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 192 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand55Checked : Checkpoint expand55Action expand54After expand55Output expand55After expand55Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand55Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand56Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand55Output[41]!
    let s1 ← Synthesis.sigma1 expand55Output[54]!
    let w ← Synthesis.prepareMessage #[expand55Output[40]!.combined.plain, expand55Output[49]!.combined.plain, s0, s1]
    return expand55Output.push w
def expand56Output : Array Synthesis.Word :=
  (expand55Output).push ({ combined := { plain := (Cell.of 195 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 195 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 195 0 (⟨0⟩ : Column .advice)), (Cell.of 195 0 (⟨5⟩ : Column .advice)), (Cell.of 195 1 (⟨5⟩ : Column .advice)), (Cell.of 195 2 (⟨5⟩ : Column .advice)), (Cell.of 195 0 (⟨1⟩ : Column .advice)), (Cell.of 195 1 (⟨0⟩ : Column .advice)), (Cell.of 195 1 (⟨1⟩ : Column .advice)), (Cell.of 195 2 (⟨0⟩ : Column .advice))] } })
def expand56After : Cursor :=
  ⟨196, [] ++ expand55After.constants⟩
def expand56Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 193 0 (⟨3⟩ : Column .advice)) (Cell.of 150 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 193 0 (⟨4⟩ : Column .advice)) (Cell.of 150 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 193 1 (⟨2⟩ : Column .advice)) (Cell.of 150 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 193 1 (⟨3⟩ : Column .advice)) (Cell.of 150 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 193 1 (⟨4⟩ : Column .advice)) (Cell.of 150 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 193 2 (⟨2⟩ : Column .advice)) (Cell.of 150 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 193 2 (⟨3⟩ : Column .advice)) (Cell.of 150 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 193 2 (⟨4⟩ : Column .advice)) (Cell.of 150 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 194 0 (⟨3⟩ : Column .advice)) (Cell.of 189 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 194 0 (⟨4⟩ : Column .advice)) (Cell.of 189 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 194 1 (⟨2⟩ : Column .advice)) (Cell.of 189 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 194 1 (⟨3⟩ : Column .advice)) (Cell.of 189 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 194 1 (⟨4⟩ : Column .advice)) (Cell.of 189 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 194 2 (⟨2⟩ : Column .advice)) (Cell.of 189 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 194 2 (⟨3⟩ : Column .advice)) (Cell.of 189 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 194 2 (⟨4⟩ : Column .advice)) (Cell.of 189 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 195 0 (⟨3⟩ : Column .advice)) (Cell.of 147 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 195 0 (⟨4⟩ : Column .advice)) (Cell.of 174 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 195 1 (⟨3⟩ : Column .advice)) (Cell.of 193 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 195 1 (⟨4⟩ : Column .advice)) (Cell.of 194 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 195 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 195 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 195 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand56Checked : Checkpoint expand56Action expand55After expand56Output expand56After expand56Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand56Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand57Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand56Output[42]!
    let s1 ← Synthesis.sigma1 expand56Output[55]!
    let w ← Synthesis.prepareMessage #[expand56Output[41]!.combined.plain, expand56Output[50]!.combined.plain, s0, s1]
    return expand56Output.push w
def expand57Output : Array Synthesis.Word :=
  (expand56Output).push ({ combined := { plain := (Cell.of 198 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 198 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 198 0 (⟨0⟩ : Column .advice)), (Cell.of 198 0 (⟨5⟩ : Column .advice)), (Cell.of 198 1 (⟨5⟩ : Column .advice)), (Cell.of 198 2 (⟨5⟩ : Column .advice)), (Cell.of 198 0 (⟨1⟩ : Column .advice)), (Cell.of 198 1 (⟨0⟩ : Column .advice)), (Cell.of 198 1 (⟨1⟩ : Column .advice)), (Cell.of 198 2 (⟨0⟩ : Column .advice))] } })
def expand57After : Cursor :=
  ⟨199, [] ++ expand56After.constants⟩
def expand57Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 196 0 (⟨3⟩ : Column .advice)) (Cell.of 153 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 196 0 (⟨4⟩ : Column .advice)) (Cell.of 153 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 196 1 (⟨2⟩ : Column .advice)) (Cell.of 153 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 196 1 (⟨3⟩ : Column .advice)) (Cell.of 153 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 196 1 (⟨4⟩ : Column .advice)) (Cell.of 153 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 196 2 (⟨2⟩ : Column .advice)) (Cell.of 153 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 196 2 (⟨3⟩ : Column .advice)) (Cell.of 153 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 196 2 (⟨4⟩ : Column .advice)) (Cell.of 153 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 197 0 (⟨3⟩ : Column .advice)) (Cell.of 192 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 197 0 (⟨4⟩ : Column .advice)) (Cell.of 192 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 197 1 (⟨2⟩ : Column .advice)) (Cell.of 192 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 197 1 (⟨3⟩ : Column .advice)) (Cell.of 192 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 197 1 (⟨4⟩ : Column .advice)) (Cell.of 192 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 197 2 (⟨2⟩ : Column .advice)) (Cell.of 192 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 197 2 (⟨3⟩ : Column .advice)) (Cell.of 192 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 197 2 (⟨4⟩ : Column .advice)) (Cell.of 192 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 198 0 (⟨3⟩ : Column .advice)) (Cell.of 150 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 198 0 (⟨4⟩ : Column .advice)) (Cell.of 177 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 198 1 (⟨3⟩ : Column .advice)) (Cell.of 196 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 198 1 (⟨4⟩ : Column .advice)) (Cell.of 197 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 198 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 198 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 198 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand57Checked : Checkpoint expand57Action expand56After expand57Output expand57After expand57Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand57Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand58Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand57Output[43]!
    let s1 ← Synthesis.sigma1 expand57Output[56]!
    let w ← Synthesis.prepareMessage #[expand57Output[42]!.combined.plain, expand57Output[51]!.combined.plain, s0, s1]
    return expand57Output.push w
def expand58Output : Array Synthesis.Word :=
  (expand57Output).push ({ combined := { plain := (Cell.of 201 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 201 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 201 0 (⟨0⟩ : Column .advice)), (Cell.of 201 0 (⟨5⟩ : Column .advice)), (Cell.of 201 1 (⟨5⟩ : Column .advice)), (Cell.of 201 2 (⟨5⟩ : Column .advice)), (Cell.of 201 0 (⟨1⟩ : Column .advice)), (Cell.of 201 1 (⟨0⟩ : Column .advice)), (Cell.of 201 1 (⟨1⟩ : Column .advice)), (Cell.of 201 2 (⟨0⟩ : Column .advice))] } })
def expand58After : Cursor :=
  ⟨202, [] ++ expand57After.constants⟩
def expand58Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 199 0 (⟨3⟩ : Column .advice)) (Cell.of 156 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 199 0 (⟨4⟩ : Column .advice)) (Cell.of 156 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 199 1 (⟨2⟩ : Column .advice)) (Cell.of 156 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 199 1 (⟨3⟩ : Column .advice)) (Cell.of 156 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 199 1 (⟨4⟩ : Column .advice)) (Cell.of 156 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 199 2 (⟨2⟩ : Column .advice)) (Cell.of 156 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 199 2 (⟨3⟩ : Column .advice)) (Cell.of 156 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 199 2 (⟨4⟩ : Column .advice)) (Cell.of 156 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 200 0 (⟨3⟩ : Column .advice)) (Cell.of 195 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 200 0 (⟨4⟩ : Column .advice)) (Cell.of 195 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 200 1 (⟨2⟩ : Column .advice)) (Cell.of 195 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 200 1 (⟨3⟩ : Column .advice)) (Cell.of 195 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 200 1 (⟨4⟩ : Column .advice)) (Cell.of 195 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 200 2 (⟨2⟩ : Column .advice)) (Cell.of 195 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 200 2 (⟨3⟩ : Column .advice)) (Cell.of 195 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 200 2 (⟨4⟩ : Column .advice)) (Cell.of 195 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 201 0 (⟨3⟩ : Column .advice)) (Cell.of 153 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 201 0 (⟨4⟩ : Column .advice)) (Cell.of 180 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 201 1 (⟨3⟩ : Column .advice)) (Cell.of 199 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 201 1 (⟨4⟩ : Column .advice)) (Cell.of 200 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 201 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 201 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 201 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand58Checked : Checkpoint expand58Action expand57After expand58Output expand58After expand58Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand58Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand59Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand58Output[44]!
    let s1 ← Synthesis.sigma1 expand58Output[57]!
    let w ← Synthesis.prepareMessage #[expand58Output[43]!.combined.plain, expand58Output[52]!.combined.plain, s0, s1]
    return expand58Output.push w
def expand59Output : Array Synthesis.Word :=
  (expand58Output).push ({ combined := { plain := (Cell.of 204 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 204 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 204 0 (⟨0⟩ : Column .advice)), (Cell.of 204 0 (⟨5⟩ : Column .advice)), (Cell.of 204 1 (⟨5⟩ : Column .advice)), (Cell.of 204 2 (⟨5⟩ : Column .advice)), (Cell.of 204 0 (⟨1⟩ : Column .advice)), (Cell.of 204 1 (⟨0⟩ : Column .advice)), (Cell.of 204 1 (⟨1⟩ : Column .advice)), (Cell.of 204 2 (⟨0⟩ : Column .advice))] } })
def expand59After : Cursor :=
  ⟨205, [] ++ expand58After.constants⟩
def expand59Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 202 0 (⟨3⟩ : Column .advice)) (Cell.of 159 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 202 0 (⟨4⟩ : Column .advice)) (Cell.of 159 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 202 1 (⟨2⟩ : Column .advice)) (Cell.of 159 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 202 1 (⟨3⟩ : Column .advice)) (Cell.of 159 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 202 1 (⟨4⟩ : Column .advice)) (Cell.of 159 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 202 2 (⟨2⟩ : Column .advice)) (Cell.of 159 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 202 2 (⟨3⟩ : Column .advice)) (Cell.of 159 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 202 2 (⟨4⟩ : Column .advice)) (Cell.of 159 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 203 0 (⟨3⟩ : Column .advice)) (Cell.of 198 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 203 0 (⟨4⟩ : Column .advice)) (Cell.of 198 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 203 1 (⟨2⟩ : Column .advice)) (Cell.of 198 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 203 1 (⟨3⟩ : Column .advice)) (Cell.of 198 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 203 1 (⟨4⟩ : Column .advice)) (Cell.of 198 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 203 2 (⟨2⟩ : Column .advice)) (Cell.of 198 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 203 2 (⟨3⟩ : Column .advice)) (Cell.of 198 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 203 2 (⟨4⟩ : Column .advice)) (Cell.of 198 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 204 0 (⟨3⟩ : Column .advice)) (Cell.of 156 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 204 0 (⟨4⟩ : Column .advice)) (Cell.of 183 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 204 1 (⟨3⟩ : Column .advice)) (Cell.of 202 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 204 1 (⟨4⟩ : Column .advice)) (Cell.of 203 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 204 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 204 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 204 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand59Checked : Checkpoint expand59Action expand58After expand59Output expand59After expand59Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand59Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand60Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand59Output[45]!
    let s1 ← Synthesis.sigma1 expand59Output[58]!
    let w ← Synthesis.prepareMessage #[expand59Output[44]!.combined.plain, expand59Output[53]!.combined.plain, s0, s1]
    return expand59Output.push w
def expand60Output : Array Synthesis.Word :=
  (expand59Output).push ({ combined := { plain := (Cell.of 207 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 207 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 207 0 (⟨0⟩ : Column .advice)), (Cell.of 207 0 (⟨5⟩ : Column .advice)), (Cell.of 207 1 (⟨5⟩ : Column .advice)), (Cell.of 207 2 (⟨5⟩ : Column .advice)), (Cell.of 207 0 (⟨1⟩ : Column .advice)), (Cell.of 207 1 (⟨0⟩ : Column .advice)), (Cell.of 207 1 (⟨1⟩ : Column .advice)), (Cell.of 207 2 (⟨0⟩ : Column .advice))] } })
def expand60After : Cursor :=
  ⟨208, [] ++ expand59After.constants⟩
def expand60Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 205 0 (⟨3⟩ : Column .advice)) (Cell.of 162 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 205 0 (⟨4⟩ : Column .advice)) (Cell.of 162 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 205 1 (⟨2⟩ : Column .advice)) (Cell.of 162 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 205 1 (⟨3⟩ : Column .advice)) (Cell.of 162 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 205 1 (⟨4⟩ : Column .advice)) (Cell.of 162 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 205 2 (⟨2⟩ : Column .advice)) (Cell.of 162 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 205 2 (⟨3⟩ : Column .advice)) (Cell.of 162 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 205 2 (⟨4⟩ : Column .advice)) (Cell.of 162 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 206 0 (⟨3⟩ : Column .advice)) (Cell.of 201 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 206 0 (⟨4⟩ : Column .advice)) (Cell.of 201 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 206 1 (⟨2⟩ : Column .advice)) (Cell.of 201 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 206 1 (⟨3⟩ : Column .advice)) (Cell.of 201 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 206 1 (⟨4⟩ : Column .advice)) (Cell.of 201 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 206 2 (⟨2⟩ : Column .advice)) (Cell.of 201 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 206 2 (⟨3⟩ : Column .advice)) (Cell.of 201 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 206 2 (⟨4⟩ : Column .advice)) (Cell.of 201 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 207 0 (⟨3⟩ : Column .advice)) (Cell.of 159 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 207 0 (⟨4⟩ : Column .advice)) (Cell.of 186 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 207 1 (⟨3⟩ : Column .advice)) (Cell.of 205 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 207 1 (⟨4⟩ : Column .advice)) (Cell.of 206 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 207 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 207 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 207 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand60Checked : Checkpoint expand60Action expand59After expand60Output expand60After expand60Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand60Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand61Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand60Output[46]!
    let s1 ← Synthesis.sigma1 expand60Output[59]!
    let w ← Synthesis.prepareMessage #[expand60Output[45]!.combined.plain, expand60Output[54]!.combined.plain, s0, s1]
    return expand60Output.push w
def expand61Output : Array Synthesis.Word :=
  (expand60Output).push ({ combined := { plain := (Cell.of 210 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 210 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 210 0 (⟨0⟩ : Column .advice)), (Cell.of 210 0 (⟨5⟩ : Column .advice)), (Cell.of 210 1 (⟨5⟩ : Column .advice)), (Cell.of 210 2 (⟨5⟩ : Column .advice)), (Cell.of 210 0 (⟨1⟩ : Column .advice)), (Cell.of 210 1 (⟨0⟩ : Column .advice)), (Cell.of 210 1 (⟨1⟩ : Column .advice)), (Cell.of 210 2 (⟨0⟩ : Column .advice))] } })
def expand61After : Cursor :=
  ⟨211, [] ++ expand60After.constants⟩
def expand61Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 208 0 (⟨3⟩ : Column .advice)) (Cell.of 165 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 208 0 (⟨4⟩ : Column .advice)) (Cell.of 165 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 208 1 (⟨2⟩ : Column .advice)) (Cell.of 165 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 208 1 (⟨3⟩ : Column .advice)) (Cell.of 165 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 208 1 (⟨4⟩ : Column .advice)) (Cell.of 165 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 208 2 (⟨2⟩ : Column .advice)) (Cell.of 165 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 208 2 (⟨3⟩ : Column .advice)) (Cell.of 165 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 208 2 (⟨4⟩ : Column .advice)) (Cell.of 165 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 209 0 (⟨3⟩ : Column .advice)) (Cell.of 204 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 209 0 (⟨4⟩ : Column .advice)) (Cell.of 204 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 209 1 (⟨2⟩ : Column .advice)) (Cell.of 204 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 209 1 (⟨3⟩ : Column .advice)) (Cell.of 204 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 209 1 (⟨4⟩ : Column .advice)) (Cell.of 204 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 209 2 (⟨2⟩ : Column .advice)) (Cell.of 204 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 209 2 (⟨3⟩ : Column .advice)) (Cell.of 204 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 209 2 (⟨4⟩ : Column .advice)) (Cell.of 204 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 210 0 (⟨3⟩ : Column .advice)) (Cell.of 162 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 210 0 (⟨4⟩ : Column .advice)) (Cell.of 189 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 210 1 (⟨3⟩ : Column .advice)) (Cell.of 208 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 210 1 (⟨4⟩ : Column .advice)) (Cell.of 209 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 210 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 210 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 210 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand61Checked : Checkpoint expand61Action expand60After expand61Output expand61After expand61Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand61Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand62Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand61Output[47]!
    let s1 ← Synthesis.sigma1 expand61Output[60]!
    let w ← Synthesis.prepareMessage #[expand61Output[46]!.combined.plain, expand61Output[55]!.combined.plain, s0, s1]
    return expand61Output.push w
def expand62Output : Array Synthesis.Word :=
  (expand61Output).push ({ combined := { plain := (Cell.of 213 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 213 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 213 0 (⟨0⟩ : Column .advice)), (Cell.of 213 0 (⟨5⟩ : Column .advice)), (Cell.of 213 1 (⟨5⟩ : Column .advice)), (Cell.of 213 2 (⟨5⟩ : Column .advice)), (Cell.of 213 0 (⟨1⟩ : Column .advice)), (Cell.of 213 1 (⟨0⟩ : Column .advice)), (Cell.of 213 1 (⟨1⟩ : Column .advice)), (Cell.of 213 2 (⟨0⟩ : Column .advice))] } })
def expand62After : Cursor :=
  ⟨214, [] ++ expand61After.constants⟩
def expand62Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 211 0 (⟨3⟩ : Column .advice)) (Cell.of 168 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 211 0 (⟨4⟩ : Column .advice)) (Cell.of 168 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 211 1 (⟨2⟩ : Column .advice)) (Cell.of 168 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 211 1 (⟨3⟩ : Column .advice)) (Cell.of 168 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 211 1 (⟨4⟩ : Column .advice)) (Cell.of 168 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 211 2 (⟨2⟩ : Column .advice)) (Cell.of 168 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 211 2 (⟨3⟩ : Column .advice)) (Cell.of 168 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 211 2 (⟨4⟩ : Column .advice)) (Cell.of 168 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 212 0 (⟨3⟩ : Column .advice)) (Cell.of 207 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 212 0 (⟨4⟩ : Column .advice)) (Cell.of 207 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 212 1 (⟨2⟩ : Column .advice)) (Cell.of 207 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 212 1 (⟨3⟩ : Column .advice)) (Cell.of 207 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 212 1 (⟨4⟩ : Column .advice)) (Cell.of 207 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 212 2 (⟨2⟩ : Column .advice)) (Cell.of 207 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 212 2 (⟨3⟩ : Column .advice)) (Cell.of 207 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 212 2 (⟨4⟩ : Column .advice)) (Cell.of 207 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 213 0 (⟨3⟩ : Column .advice)) (Cell.of 165 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 213 0 (⟨4⟩ : Column .advice)) (Cell.of 192 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 213 1 (⟨3⟩ : Column .advice)) (Cell.of 211 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 213 1 (⟨4⟩ : Column .advice)) (Cell.of 212 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 213 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 213 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 213 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand62Checked : Checkpoint expand62Action expand61After expand62Output expand62After expand62Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand62Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def expand63Action : Synthesis.Build (Array Synthesis.Word) :=
  do
    let s0 ← Synthesis.sigma0 expand62Output[48]!
    let s1 ← Synthesis.sigma1 expand62Output[61]!
    let w ← Synthesis.prepareMessage #[expand62Output[47]!.combined.plain, expand62Output[56]!.combined.plain, s0, s1]
    return expand62Output.push w
def expand63Output : Array Synthesis.Word :=
  (expand62Output).push ({ combined := { plain := (Cell.of 216 0 (⟨2⟩ : Column .advice)), spread := (Cell.of 216 0 (⟨2⟩ : Column .advice)) }, limbs := { toList := [(Cell.of 216 0 (⟨0⟩ : Column .advice)), (Cell.of 216 0 (⟨5⟩ : Column .advice)), (Cell.of 216 1 (⟨5⟩ : Column .advice)), (Cell.of 216 2 (⟨5⟩ : Column .advice)), (Cell.of 216 0 (⟨1⟩ : Column .advice)), (Cell.of 216 1 (⟨0⟩ : Column .advice)), (Cell.of 216 1 (⟨1⟩ : Column .advice)), (Cell.of 216 2 (⟨0⟩ : Column .advice))] } })
def expand63After : Cursor :=
  ⟨217, [] ++ expand62After.constants⟩
def expand63Chunk : List Step :=
  [.region "σ₀(W)" [.selector 9 1, .advice 3 0, .copy (Cell.of 214 0 (⟨3⟩ : Column .advice)) (Cell.of 171 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 214 0 (⟨4⟩ : Column .advice)) (Cell.of 171 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 214 1 (⟨2⟩ : Column .advice)) (Cell.of 171 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 214 1 (⟨3⟩ : Column .advice)) (Cell.of 171 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 214 1 (⟨4⟩ : Column .advice)) (Cell.of 171 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 214 2 (⟨2⟩ : Column .advice)) (Cell.of 171 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 214 2 (⟨3⟩ : Column .advice)) (Cell.of 171 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 214 2 (⟨4⟩ : Column .advice)) (Cell.of 171 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "σ₁(W)" [.selector 10 1, .advice 3 0, .copy (Cell.of 215 0 (⟨3⟩ : Column .advice)) (Cell.of 210 0 (⟨0⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 215 0 (⟨4⟩ : Column .advice)) (Cell.of 210 0 (⟨5⟩ : Column .advice)), .advice 2 1, .copy (Cell.of 215 1 (⟨2⟩ : Column .advice)) (Cell.of 210 1 (⟨5⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 215 1 (⟨3⟩ : Column .advice)) (Cell.of 210 2 (⟨5⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 215 1 (⟨4⟩ : Column .advice)) (Cell.of 210 0 (⟨1⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 215 2 (⟨2⟩ : Column .advice)) (Cell.of 210 1 (⟨0⟩ : Column .advice)), .advice 3 2, .copy (Cell.of 215 2 (⟨3⟩ : Column .advice)) (Cell.of 210 1 (⟨1⟩ : Column .advice)), .advice 4 2, .copy (Cell.of 215 2 (⟨4⟩ : Column .advice)) (Cell.of 210 2 (⟨0⟩ : Column .advice)), .selector 11 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0],
  .region "prepare message word" [.selector 14 1, .selector 15 1, .advice 3 0, .copy (Cell.of 216 0 (⟨3⟩ : Column .advice)) (Cell.of 168 0 (⟨2⟩ : Column .advice)), .advice 4 0, .copy (Cell.of 216 0 (⟨4⟩ : Column .advice)) (Cell.of 195 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 216 1 (⟨3⟩ : Column .advice)) (Cell.of 214 0 (⟨2⟩ : Column .advice)), .advice 4 1, .copy (Cell.of 216 1 (⟨4⟩ : Column .advice)) (Cell.of 215 0 (⟨2⟩ : Column .advice)), .advice 2 2, .copy (Cell.of 216 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 216 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 216 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2, .advice 5 0, .advice 5 1, .advice 5 2]]
theorem expand63Checked : Checkpoint expand63Action expand62After expand63Output expand63After expand63Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    dsimp only [expand63Action, Synthesis.compressionRound, Synthesis.bigSigma0,
      Synthesis.bigSigma1, Synthesis.sigma0, Synthesis.sigma1, Synthesis.sigma,
      Synthesis.spread111110, Synthesis.plainAndSpread, Synthesis.scopy, Synthesis.sa]
    cbv

def scheduleOutput : Array Cell := expand63Output.map (·.combined.plain)

end Midnight.SHA256.Semantics.StructuralCheckpoints
