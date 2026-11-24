import Midnight.SHA256.WitnessCircuit
import Clean.Halo2.Lemmas

/-!
Finite, proof-friendly expansions of the actual SHA preparation regions. The
equalities retain every witness program, lookup, copy, and fixed assignment;
they are stronger than advice erasure. Synthesis continues to use the source
definitions in `WitnessCircuit`.
-/
namespace Midnight.SHA256.WitnessPrepare
open Halo2 WitnessCircuit

abbrev Cell := WitnessCircuit.Cell

attribute [local irreducible] Midnight.SHA256.activation WitnessCircuit.addMod

attribute [local cbv_opaque] WitnessCircuit.enable WitnessCircuit.addMod
  WitnessCircuit.sa WitnessCircuit.scopy WitnessCircuit.plainAndSpread
  WitnessIR.readNat WitnessIR.spread32 WitnessIR.limb WitnessIR.carry32 WitnessIR.sum32
  BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing HAppend.hAppend

/-- All seven copy operations occur before the carry and remainder witnesses. -/
def addModExpanded (summands : Array Cell) (zero : Cell) : Region Cell := do
  enable 15 1
  let terms := summands ++ Array.replicate (7 - summands.size) zero
  let values := terms.toList.map WitnessIR.readNat
  let _ ← scopy terms[0]! 5 0
  let _ ← scopy terms[1]! 6 0
  let _ ← scopy terms[2]! 5 1
  let _ ← scopy terms[3]! 6 1
  let _ ← scopy terms[4]! 4 2
  let _ ← scopy terms[5]! 5 2
  let _ ← scopy terms[6]! 6 2
  let _ ← plainAndSpread 3 2 1 (WitnessIR.carry32 values)
  sa 4 0 (WitnessIR.sum32 values)

section
attribute [local cbv_opaque] getElem!

theorem addMod_eq (summands : Array Cell) (zero : Cell) :
    addMod summands zero = addModExpanded summands zero := by
  funext self
  unfold addMod addModExpanded
  generalize summands ++ Array.replicate (7 - summands.size) zero = terms
  generalize terms.toList.map WitnessIR.readNat = values
  cbv

end

def aRegion (summands : Array Cell) (zero : Cell) : Region Word := do
  enable 12 1
  let plain ← addMod summands zero
  let value := WitnessIR.readNat plain
  let expanded ← sa 4 1 (WitnessIR.spread32 value)
  let a ← plainAndSpread 10 0 0 (WitnessIR.limb value (22, 10))
  let b ← plainAndSpread 9 0 1 (WitnessIR.limb value (13, 9))
  let c ← plainAndSpread 11 1 0 (WitnessIR.limb value (2, 11))
  let d ← plainAndSpread 2 1 1 (WitnessIR.limb value (0, 2))
  let e ← plainAndSpread 0 2 0 (WitnessIR.limb value (0, 0))
  return ⟨⟨plain, expanded⟩, #[a.spread, b.spread, c.spread, d.spread, e.spread]⟩

def eRegion (summands : Array Cell) (zero : Cell) : Region Word := do
  enable 13 1
  let plain ← addMod summands zero
  let value := WitnessIR.readNat plain
  let expanded ← sa 4 1 (WitnessIR.spread32 value)
  let a ← plainAndSpread 7 0 0 (WitnessIR.limb value (25, 7))
  let b ← plainAndSpread 12 0 1 (WitnessIR.limb value (13, 12))
  let c ← plainAndSpread 2 1 0 (WitnessIR.limb value (11, 2))
  let d ← plainAndSpread 5 1 1 (WitnessIR.limb value (6, 5))
  let e ← plainAndSpread 6 2 0 (WitnessIR.limb value (0, 6))
  return ⟨⟨plain, expanded⟩, #[a.spread, b.spread, c.spread, d.spread, e.spread]⟩

def messageRegion (summands : Array Cell) (zero : Cell) : Region Word := do
  enable 14 1
  let plain ← addMod summands zero
  let value := WitnessIR.readNat plain
  let a ← plainAndSpread 12 0 0 (WitnessIR.limb value (20, 12))
  let e ← plainAndSpread 7 0 1 (WitnessIR.limb value (10, 7))
  let f ← plainAndSpread 3 1 0 (WitnessIR.limb value (7, 3))
  let g ← plainAndSpread 4 1 1 (WitnessIR.limb value (3, 4))
  let h ← plainAndSpread 3 2 0 (WitnessIR.limb value (0, 3))
  let b ← sa 7 0 (WitnessIR.limb value (19, 1))
  let c ← sa 7 1 (WitnessIR.limb value (18, 1))
  let d ← sa 7 2 (WitnessIR.limb value (17, 1))
  return ⟨⟨plain, plain⟩, #[a.spread, b, c, d, e.spread, f.spread, g.spread, h.spread]⟩

theorem prepareARegion_eq (summands : Array Cell) (zero : Cell) :
    prepareRegion 12 #[10,9,11,2,0] summands zero = aRegion summands zero := by
  funext self
  unfold prepareRegion aRegion
  cbv
  simp only [List.append_nil]

theorem prepareERegion_eq (summands : Array Cell) (zero : Cell) :
    prepareRegion 13 #[7,12,2,5,6] summands zero = eRegion summands zero := by
  funext self
  unfold prepareRegion eRegion
  cbv
  simp only [List.append_nil]

theorem prepareMessageRegion_eq (summands : Array Cell) (zero : Cell) :
    prepareMessageRegion summands zero = messageRegion summands zero := by
  funext self
  unfold prepareMessageRegion messageRegion WitnessIR.limbs Witness.messageLayout
  cbv

/-- The physical advice cell corresponding to a source SHA column index. -/
def shaCell (self : RegionIndex) (index row : Nat) : Cell :=
  .of self row (⟨Synthesis.shaAdvice[index]!⟩ : Column .advice)

@[circuit_norm, keygen_norm, keygen_output_norm]
theorem addMod_output (summands : Array Cell) (zero : Cell) (self : RegionIndex) :
    (addMod summands zero).output self = shaCell self 4 0 := by
  rw [addMod_eq]
  simp only [addModExpanded, sa, circuit_norm]
  rfl

/-- A/E have identical cell shapes, although their lookup tags and programs differ. -/
def aeOutput (self : RegionIndex) : Word :=
  ⟨⟨shaCell self 4 0, shaCell self 4 1⟩,
    #[shaCell self 1 0, shaCell self 3 0, shaCell self 1 1,
      shaCell self 3 1, shaCell self 1 2]⟩

def messageOutput (self : RegionIndex) : Word :=
  ⟨⟨shaCell self 4 0, shaCell self 4 0⟩,
    #[shaCell self 1 0, shaCell self 7 0, shaCell self 7 1, shaCell self 7 2,
      shaCell self 3 0, shaCell self 1 1, shaCell self 3 1, shaCell self 1 2]⟩

@[circuit_norm, keygen_norm, keygen_output_norm]
theorem aRegion_output (summands : Array Cell) (zero : Cell) (self : RegionIndex) :
    (aRegion summands zero).output self = aeOutput self := by
  simp only [aRegion, plainAndSpread, sa, circuit_norm, aeOutput]
  rfl

@[circuit_norm, keygen_norm, keygen_output_norm]
theorem eRegion_output (summands : Array Cell) (zero : Cell) (self : RegionIndex) :
    (eRegion summands zero).output self = aeOutput self := by
  simp only [eRegion, plainAndSpread, sa, circuit_norm, aeOutput]
  rfl

@[circuit_norm, keygen_norm, keygen_output_norm]
theorem messageRegion_output (summands : Array Cell) (zero : Cell) (self : RegionIndex) :
    (messageRegion summands zero).output self = messageOutput self := by
  simp only [messageRegion, plainAndSpread, sa, circuit_norm, messageOutput]
  rfl

/-- The copy loop and honest sum have the same seven terms on the source's
supported fragment. More than seven summands is not supported by `addMod`. -/
theorem paddedTerms_size (summands : Array Cell) (zero : Cell)
    (bound : summands.size ≤ 7) :
    (summands ++ Array.replicate (7 - summands.size) zero).size = 7 := by
  simp only [Array.size_append, Array.size_replicate]
  omega

/-- Padding by the cached zero does not change the integer input sum. -/
theorem paddedTerms_sum (summands : Array Cell) (zero : Cell) (value : Cell → Nat)
    (zero_value : value zero = 0) :
    ((summands ++ Array.replicate (7 - summands.size) zero).toList.map value).sum =
      (summands.toList.map value).sum := by
  simp [zero_value]

end Midnight.SHA256.WitnessPrepare
