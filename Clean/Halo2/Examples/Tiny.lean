import Clean.Halo2.Basic

namespace Halo2.Examples.Tiny

open Halo2

def configure {F : Type} [Field F] : Configure F (Column .advice × Selector) := do
  let a ← adviceColumn
  let s ← selector

  createGate "tiny transition" do
    let s ← querySelector s
    let aCur ← queryAdvice a 0
    let aNext ← queryAdvice a 1
    return #[
      { expression := s * (aCur * aNext - aCur) }
    ]

  return (a, s)

def configured {F : Type} [Field F] : ConfigureState F :=
  configure.run {} |>.2

example {F : Type} [Field F] : (configured (F := F)).nextAdvice = 1 := rfl

example {F : Type} [Field F] : (configured (F := F)).nextSelector = 1 := rfl

example {F : Type} [Field F] : (configured (F := F)).gates.size = 1 := rfl

example {F : Type} [Field F] :
    (configured (F := F)).gates[0]?.map (fun gate => gate.queriedSelectors.size) = some 1 := rfl

example {F : Type} [Field F] :
    (configured (F := F)).gates[0]?.map (fun gate => gate.queriedCells.size) = some 2 := rfl

end Halo2.Examples.Tiny
