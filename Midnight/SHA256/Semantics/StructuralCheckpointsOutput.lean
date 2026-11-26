import Midnight.SHA256.Semantics.StructuralCheckpointsRounds7
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

def feedforwardAction : Synthesis.Build (Array Cell) :=
  Synthesis.addStates initialOutput round63Output
def feedforwardOutput : Array Cell :=
  { toList := [(Cell.of 666 0 (⟨2⟩ : Column .advice)), (Cell.of 667 0 (⟨2⟩ : Column .advice)), (Cell.of 668 0 (⟨2⟩ : Column .advice)), (Cell.of 669 0 (⟨2⟩ : Column .advice)), (Cell.of 670 0 (⟨2⟩ : Column .advice)), (Cell.of 671 0 (⟨2⟩ : Column .advice)), (Cell.of 672 0 (⟨2⟩ : Column .advice)), (Cell.of 673 0 (⟨2⟩ : Column .advice))] }
def feedforwardAfter : Cursor :=
  ⟨674, [] ++ round63After.constants⟩
def feedforwardChunk : List Step :=
  [.region "decompose A in 10-9-11-2" [.selector 12 1, .selector 15 1, .advice 3 0, .copy (Cell.of 666 0 (⟨3⟩ : Column .advice)) (Cell.of 24 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 666 0 (⟨4⟩ : Column .advice)) (Cell.of 664 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 666 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 666 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 666 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 666 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 666 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2],
  .region "decompose A in 10-9-11-2" [.selector 12 1, .selector 15 1, .advice 3 0, .copy (Cell.of 667 0 (⟨3⟩ : Column .advice)) (Cell.of 30 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 667 0 (⟨4⟩ : Column .advice)) (Cell.of 657 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 667 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 667 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 667 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 667 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 667 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2],
  .region "decompose A in 10-9-11-2" [.selector 12 1, .selector 15 1, .advice 3 0, .copy (Cell.of 668 0 (⟨3⟩ : Column .advice)) (Cell.of 32 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 668 0 (⟨4⟩ : Column .advice)) (Cell.of 650 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 668 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 668 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 668 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 668 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 668 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2],
  .region "decompose A in 10-9-11-2" [.selector 12 1, .selector 15 1, .advice 3 0, .copy (Cell.of 669 0 (⟨3⟩ : Column .advice)) (Cell.of 34 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 669 0 (⟨4⟩ : Column .advice)) (Cell.of 643 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 669 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 669 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 669 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 669 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 669 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2],
  .region "decompose E in 7-12-2-5-6" [.selector 13 1, .selector 15 1, .advice 3 0, .copy (Cell.of 670 0 (⟨3⟩ : Column .advice)) (Cell.of 35 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 670 0 (⟨4⟩ : Column .advice)) (Cell.of 665 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 670 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 670 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 670 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 670 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 670 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2],
  .region "decompose E in 7-12-2-5-6" [.selector 13 1, .selector 15 1, .advice 3 0, .copy (Cell.of 671 0 (⟨3⟩ : Column .advice)) (Cell.of 42 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 671 0 (⟨4⟩ : Column .advice)) (Cell.of 658 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 671 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 671 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 671 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 671 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 671 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2],
  .region "decompose E in 7-12-2-5-6" [.selector 13 1, .selector 15 1, .advice 3 0, .copy (Cell.of 672 0 (⟨3⟩ : Column .advice)) (Cell.of 44 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 672 0 (⟨4⟩ : Column .advice)) (Cell.of 651 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 672 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 672 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 672 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 672 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 672 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2],
  .region "decompose E in 7-12-2-5-6" [.selector 13 1, .selector 15 1, .advice 3 0, .copy (Cell.of 673 0 (⟨3⟩ : Column .advice)) (Cell.of 46 0 (⟨9⟩ : Column .fixed)), .advice 4 0, .copy (Cell.of 673 0 (⟨4⟩ : Column .advice)) (Cell.of 644 0 (⟨2⟩ : Column .advice)), .advice 3 1, .copy (Cell.of 673 1 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 1, .copy (Cell.of 673 1 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 2 2, .copy (Cell.of 673 2 (⟨2⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 3 2, .copy (Cell.of 673 2 (⟨3⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .advice 4 2, .copy (Cell.of 673 2 (⟨4⟩ : Column .advice)) (Cell.of 48 0 (⟨9⟩ : Column .fixed)), .selector 4 2, .fixed 1 2, .advice 7 2, .advice 1 2, .advice 2 0, .advice 2 1, .selector 4 0, .fixed 0 0, .advice 6 0, .advice 0 0, .selector 4 0, .fixed 1 0, .advice 7 0, .advice 1 0, .selector 4 1, .fixed 0 1, .advice 6 1, .advice 0 1, .selector 4 1, .fixed 1 1, .advice 7 1, .advice 1 1, .selector 4 2, .fixed 0 2, .advice 6 2, .advice 0 2]]
theorem feedforwardChecked : Checkpoint feedforwardAction round63After feedforwardOutput feedforwardAfter feedforwardChunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize0Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[0]!
    return (#[]) ++ bytes
def serialize0Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice))] }
def serialize0After : Cursor :=
  ⟨676, [] ++ feedforwardAfter.constants⟩
def serialize0Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 666 0 (⟨2⟩ : Column .advice)) (Cell.of 674 0 (⟨0⟩ : Column .advice))]]
theorem serialize0Checked : Checkpoint serialize0Action feedforwardAfter serialize0Output serialize0After serialize0Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize1Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[1]!
    return (serialize0Output) ++ bytes
def serialize1Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice)), (Cell.of 676 3 (⟨1⟩ : Column .advice)), (Cell.of 676 2 (⟨1⟩ : Column .advice)), (Cell.of 676 1 (⟨1⟩ : Column .advice)), (Cell.of 676 0 (⟨1⟩ : Column .advice))] }
def serialize1After : Cursor :=
  ⟨678, [] ++ serialize0After.constants⟩
def serialize1Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 667 0 (⟨2⟩ : Column .advice)) (Cell.of 676 0 (⟨0⟩ : Column .advice))]]
theorem serialize1Checked : Checkpoint serialize1Action serialize0After serialize1Output serialize1After serialize1Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize2Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[2]!
    return (serialize1Output) ++ bytes
def serialize2Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice)), (Cell.of 676 3 (⟨1⟩ : Column .advice)), (Cell.of 676 2 (⟨1⟩ : Column .advice)), (Cell.of 676 1 (⟨1⟩ : Column .advice)), (Cell.of 676 0 (⟨1⟩ : Column .advice)), (Cell.of 678 3 (⟨1⟩ : Column .advice)), (Cell.of 678 2 (⟨1⟩ : Column .advice)), (Cell.of 678 1 (⟨1⟩ : Column .advice)), (Cell.of 678 0 (⟨1⟩ : Column .advice))] }
def serialize2After : Cursor :=
  ⟨680, [] ++ serialize1After.constants⟩
def serialize2Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 668 0 (⟨2⟩ : Column .advice)) (Cell.of 678 0 (⟨0⟩ : Column .advice))]]
theorem serialize2Checked : Checkpoint serialize2Action serialize1After serialize2Output serialize2After serialize2Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize3Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[3]!
    return (serialize2Output) ++ bytes
def serialize3Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice)), (Cell.of 676 3 (⟨1⟩ : Column .advice)), (Cell.of 676 2 (⟨1⟩ : Column .advice)), (Cell.of 676 1 (⟨1⟩ : Column .advice)), (Cell.of 676 0 (⟨1⟩ : Column .advice)), (Cell.of 678 3 (⟨1⟩ : Column .advice)), (Cell.of 678 2 (⟨1⟩ : Column .advice)), (Cell.of 678 1 (⟨1⟩ : Column .advice)), (Cell.of 678 0 (⟨1⟩ : Column .advice)), (Cell.of 680 3 (⟨1⟩ : Column .advice)), (Cell.of 680 2 (⟨1⟩ : Column .advice)), (Cell.of 680 1 (⟨1⟩ : Column .advice)), (Cell.of 680 0 (⟨1⟩ : Column .advice))] }
def serialize3After : Cursor :=
  ⟨682, [] ++ serialize2After.constants⟩
def serialize3Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 669 0 (⟨2⟩ : Column .advice)) (Cell.of 680 0 (⟨0⟩ : Column .advice))]]
theorem serialize3Checked : Checkpoint serialize3Action serialize2After serialize3Output serialize3After serialize3Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize4Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[4]!
    return (serialize3Output) ++ bytes
def serialize4Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice)), (Cell.of 676 3 (⟨1⟩ : Column .advice)), (Cell.of 676 2 (⟨1⟩ : Column .advice)), (Cell.of 676 1 (⟨1⟩ : Column .advice)), (Cell.of 676 0 (⟨1⟩ : Column .advice)), (Cell.of 678 3 (⟨1⟩ : Column .advice)), (Cell.of 678 2 (⟨1⟩ : Column .advice)), (Cell.of 678 1 (⟨1⟩ : Column .advice)), (Cell.of 678 0 (⟨1⟩ : Column .advice)), (Cell.of 680 3 (⟨1⟩ : Column .advice)), (Cell.of 680 2 (⟨1⟩ : Column .advice)), (Cell.of 680 1 (⟨1⟩ : Column .advice)), (Cell.of 680 0 (⟨1⟩ : Column .advice)), (Cell.of 682 3 (⟨1⟩ : Column .advice)), (Cell.of 682 2 (⟨1⟩ : Column .advice)), (Cell.of 682 1 (⟨1⟩ : Column .advice)), (Cell.of 682 0 (⟨1⟩ : Column .advice))] }
def serialize4After : Cursor :=
  ⟨684, [] ++ serialize3After.constants⟩
def serialize4Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 670 0 (⟨2⟩ : Column .advice)) (Cell.of 682 0 (⟨0⟩ : Column .advice))]]
theorem serialize4Checked : Checkpoint serialize4Action serialize3After serialize4Output serialize4After serialize4Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize5Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[5]!
    return (serialize4Output) ++ bytes
def serialize5Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice)), (Cell.of 676 3 (⟨1⟩ : Column .advice)), (Cell.of 676 2 (⟨1⟩ : Column .advice)), (Cell.of 676 1 (⟨1⟩ : Column .advice)), (Cell.of 676 0 (⟨1⟩ : Column .advice)), (Cell.of 678 3 (⟨1⟩ : Column .advice)), (Cell.of 678 2 (⟨1⟩ : Column .advice)), (Cell.of 678 1 (⟨1⟩ : Column .advice)), (Cell.of 678 0 (⟨1⟩ : Column .advice)), (Cell.of 680 3 (⟨1⟩ : Column .advice)), (Cell.of 680 2 (⟨1⟩ : Column .advice)), (Cell.of 680 1 (⟨1⟩ : Column .advice)), (Cell.of 680 0 (⟨1⟩ : Column .advice)), (Cell.of 682 3 (⟨1⟩ : Column .advice)), (Cell.of 682 2 (⟨1⟩ : Column .advice)), (Cell.of 682 1 (⟨1⟩ : Column .advice)), (Cell.of 682 0 (⟨1⟩ : Column .advice)), (Cell.of 684 3 (⟨1⟩ : Column .advice)), (Cell.of 684 2 (⟨1⟩ : Column .advice)), (Cell.of 684 1 (⟨1⟩ : Column .advice)), (Cell.of 684 0 (⟨1⟩ : Column .advice))] }
def serialize5After : Cursor :=
  ⟨686, [] ++ serialize4After.constants⟩
def serialize5Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 671 0 (⟨2⟩ : Column .advice)) (Cell.of 684 0 (⟨0⟩ : Column .advice))]]
theorem serialize5Checked : Checkpoint serialize5Action serialize4After serialize5Output serialize5After serialize5Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize6Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[6]!
    return (serialize5Output) ++ bytes
def serialize6Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice)), (Cell.of 676 3 (⟨1⟩ : Column .advice)), (Cell.of 676 2 (⟨1⟩ : Column .advice)), (Cell.of 676 1 (⟨1⟩ : Column .advice)), (Cell.of 676 0 (⟨1⟩ : Column .advice)), (Cell.of 678 3 (⟨1⟩ : Column .advice)), (Cell.of 678 2 (⟨1⟩ : Column .advice)), (Cell.of 678 1 (⟨1⟩ : Column .advice)), (Cell.of 678 0 (⟨1⟩ : Column .advice)), (Cell.of 680 3 (⟨1⟩ : Column .advice)), (Cell.of 680 2 (⟨1⟩ : Column .advice)), (Cell.of 680 1 (⟨1⟩ : Column .advice)), (Cell.of 680 0 (⟨1⟩ : Column .advice)), (Cell.of 682 3 (⟨1⟩ : Column .advice)), (Cell.of 682 2 (⟨1⟩ : Column .advice)), (Cell.of 682 1 (⟨1⟩ : Column .advice)), (Cell.of 682 0 (⟨1⟩ : Column .advice)), (Cell.of 684 3 (⟨1⟩ : Column .advice)), (Cell.of 684 2 (⟨1⟩ : Column .advice)), (Cell.of 684 1 (⟨1⟩ : Column .advice)), (Cell.of 684 0 (⟨1⟩ : Column .advice)), (Cell.of 686 3 (⟨1⟩ : Column .advice)), (Cell.of 686 2 (⟨1⟩ : Column .advice)), (Cell.of 686 1 (⟨1⟩ : Column .advice)), (Cell.of 686 0 (⟨1⟩ : Column .advice))] }
def serialize6After : Cursor :=
  ⟨688, [] ++ serialize5After.constants⟩
def serialize6Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 672 0 (⟨2⟩ : Column .advice)) (Cell.of 686 0 (⟨0⟩ : Column .advice))]]
theorem serialize6Checked : Checkpoint serialize6Action serialize5After serialize6Output serialize6After serialize6Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def serialize7Action : Synthesis.Build (Array Cell) :=
  do
    let bytes ← Synthesis.wordToBytes feedforwardOutput[7]!
    return (serialize6Output) ++ bytes
def serialize7Output : Array Cell :=
  { toList := [(Cell.of 674 3 (⟨1⟩ : Column .advice)), (Cell.of 674 2 (⟨1⟩ : Column .advice)), (Cell.of 674 1 (⟨1⟩ : Column .advice)), (Cell.of 674 0 (⟨1⟩ : Column .advice)), (Cell.of 676 3 (⟨1⟩ : Column .advice)), (Cell.of 676 2 (⟨1⟩ : Column .advice)), (Cell.of 676 1 (⟨1⟩ : Column .advice)), (Cell.of 676 0 (⟨1⟩ : Column .advice)), (Cell.of 678 3 (⟨1⟩ : Column .advice)), (Cell.of 678 2 (⟨1⟩ : Column .advice)), (Cell.of 678 1 (⟨1⟩ : Column .advice)), (Cell.of 678 0 (⟨1⟩ : Column .advice)), (Cell.of 680 3 (⟨1⟩ : Column .advice)), (Cell.of 680 2 (⟨1⟩ : Column .advice)), (Cell.of 680 1 (⟨1⟩ : Column .advice)), (Cell.of 680 0 (⟨1⟩ : Column .advice)), (Cell.of 682 3 (⟨1⟩ : Column .advice)), (Cell.of 682 2 (⟨1⟩ : Column .advice)), (Cell.of 682 1 (⟨1⟩ : Column .advice)), (Cell.of 682 0 (⟨1⟩ : Column .advice)), (Cell.of 684 3 (⟨1⟩ : Column .advice)), (Cell.of 684 2 (⟨1⟩ : Column .advice)), (Cell.of 684 1 (⟨1⟩ : Column .advice)), (Cell.of 684 0 (⟨1⟩ : Column .advice)), (Cell.of 686 3 (⟨1⟩ : Column .advice)), (Cell.of 686 2 (⟨1⟩ : Column .advice)), (Cell.of 686 1 (⟨1⟩ : Column .advice)), (Cell.of 686 0 (⟨1⟩ : Column .advice)), (Cell.of 688 3 (⟨1⟩ : Column .advice)), (Cell.of 688 2 (⟨1⟩ : Column .advice)), (Cell.of 688 1 (⟨1⟩ : Column .advice)), (Cell.of 688 0 (⟨1⟩ : Column .advice))] }
def serialize7After : Cursor :=
  ⟨690, [] ++ serialize6After.constants⟩
def serialize7Chunk : List Step :=
  [.region "decompose core" [.advice 0 0, .advice 1 0, .selector 0 0, .fixed 4 0, .fixed 5 0, .fixed 6 0, .fixed 7 0, .fixed 8 0, .fixed 0 0, .fixed 1 0, .fixed 2 0, .fixed 3 0, .advice 0 1, .advice 1 1, .selector 0 1, .fixed 4 1, .fixed 5 1, .fixed 6 1, .fixed 7 1, .fixed 8 1, .fixed 0 1, .fixed 1 1, .fixed 2 1, .fixed 3 1, .advice 0 2, .advice 1 2, .selector 0 2, .fixed 4 2, .fixed 5 2, .fixed 6 2, .fixed 7 2, .fixed 8 2, .fixed 0 2, .fixed 1 2, .fixed 2 2, .fixed 3 2, .advice 0 3, .advice 1 3, .selector 0 3, .fixed 4 3, .fixed 5 3, .fixed 6 3, .fixed 7 3, .fixed 8 3, .fixed 0 3, .fixed 1 3, .fixed 2 3, .fixed 3 3, .selector 3 3, .fixed 10 3, .selector 3 2, .fixed 10 2, .selector 3 1, .fixed 10 1, .selector 3 0, .fixed 10 0],
  .region "copy" [.copy (Cell.of 673 0 (⟨2⟩ : Column .advice)) (Cell.of 688 0 (⟨0⟩ : Column .advice))]]
theorem serialize7Checked : Checkpoint serialize7Action serialize6After serialize7Output serialize7After serialize7Chunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

def publicAction : Synthesis.Build (Unit) :=
  do
    for i in [:serialize7Output.size] do
      modify fun st => { st with steps := st.steps.push (.publicInput serialize7Output[i]! i) }
def publicOutput : Unit :=
  ()
def publicAfter : Cursor :=
  ⟨690, [] ++ serialize7After.constants⟩
def publicChunk : List Step :=
  [.publicInput (Cell.of 674 3 (⟨1⟩ : Column .advice)) 0,
  .publicInput (Cell.of 674 2 (⟨1⟩ : Column .advice)) 1,
  .publicInput (Cell.of 674 1 (⟨1⟩ : Column .advice)) 2,
  .publicInput (Cell.of 674 0 (⟨1⟩ : Column .advice)) 3,
  .publicInput (Cell.of 676 3 (⟨1⟩ : Column .advice)) 4,
  .publicInput (Cell.of 676 2 (⟨1⟩ : Column .advice)) 5,
  .publicInput (Cell.of 676 1 (⟨1⟩ : Column .advice)) 6,
  .publicInput (Cell.of 676 0 (⟨1⟩ : Column .advice)) 7,
  .publicInput (Cell.of 678 3 (⟨1⟩ : Column .advice)) 8,
  .publicInput (Cell.of 678 2 (⟨1⟩ : Column .advice)) 9,
  .publicInput (Cell.of 678 1 (⟨1⟩ : Column .advice)) 10,
  .publicInput (Cell.of 678 0 (⟨1⟩ : Column .advice)) 11,
  .publicInput (Cell.of 680 3 (⟨1⟩ : Column .advice)) 12,
  .publicInput (Cell.of 680 2 (⟨1⟩ : Column .advice)) 13,
  .publicInput (Cell.of 680 1 (⟨1⟩ : Column .advice)) 14,
  .publicInput (Cell.of 680 0 (⟨1⟩ : Column .advice)) 15,
  .publicInput (Cell.of 682 3 (⟨1⟩ : Column .advice)) 16,
  .publicInput (Cell.of 682 2 (⟨1⟩ : Column .advice)) 17,
  .publicInput (Cell.of 682 1 (⟨1⟩ : Column .advice)) 18,
  .publicInput (Cell.of 682 0 (⟨1⟩ : Column .advice)) 19,
  .publicInput (Cell.of 684 3 (⟨1⟩ : Column .advice)) 20,
  .publicInput (Cell.of 684 2 (⟨1⟩ : Column .advice)) 21,
  .publicInput (Cell.of 684 1 (⟨1⟩ : Column .advice)) 22,
  .publicInput (Cell.of 684 0 (⟨1⟩ : Column .advice)) 23,
  .publicInput (Cell.of 686 3 (⟨1⟩ : Column .advice)) 24,
  .publicInput (Cell.of 686 2 (⟨1⟩ : Column .advice)) 25,
  .publicInput (Cell.of 686 1 (⟨1⟩ : Column .advice)) 26,
  .publicInput (Cell.of 686 0 (⟨1⟩ : Column .advice)) 27,
  .publicInput (Cell.of 688 3 (⟨1⟩ : Column .advice)) 28,
  .publicInput (Cell.of 688 2 (⟨1⟩ : Column .advice)) 29,
  .publicInput (Cell.of 688 1 (⟨1⟩ : Column .advice)) 30,
  .publicInput (Cell.of 688 0 (⟨1⟩ : Column .advice)) 31]
theorem publicChecked : Checkpoint publicAction serialize7After publicOutput publicAfter publicChunk := by
  intro priorTrace
  cases priorTrace with
  | mk data => cbv

end Midnight.SHA256.Semantics.StructuralCheckpoints
