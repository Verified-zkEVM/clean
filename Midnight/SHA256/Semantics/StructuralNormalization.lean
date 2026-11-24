import Midnight.Chips.SynthesisCheckpoint
import Midnight.SHA256.Synthesis

/-! Proof-only normalization of the original keygen schedule's integer branch
tests. The source fixed values and all operations remain identical. -/
namespace Midnight.SHA256.Semantics.StructuralNormalization
open Halo2 Chips.SynthesisCheckpoint.Reduction

def natBlockFromBytes (bytes : Array Cell) : Synthesis.Build (Array Cell) := do
  let mut words := #[]
  for word in [:16] do
    let terms := (Array.range 4).map fun i => (256^i, bytes[word*4+3-i]!)
    words := words.push (← natLinearCombination terms)
  return words

theorem blockFromBytes_eq (bytes : Array Cell) :
    Synthesis.blockFromBytes bytes = natBlockFromBytes bytes := by
  unfold Synthesis.blockFromBytes natBlockFromBytes
  simp only [← linearCombination_cast, castTerms, Array.map_map, Function.comp_def]

end Midnight.SHA256.Semantics.StructuralNormalization
