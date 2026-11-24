import Midnight.SHA256.WitnessCircuit

/-! Exact proof-side normalization of native linear combinations with integer
coefficients. Only coefficient branch tests change representation: the actual
field coefficients, witness programs, assignments and copy order remain intact. -/
namespace Midnight.SHA256.Semantics.LinearNormalization
open Halo2 WitnessCircuit

/-- Canonical integer cache keys, exactly equal to the source field-value keys.
This normalization is for proofs; it does not replace the circuit definition. -/
def canonicalConstant (n : Nat) : Build WitnessCircuit.Cell := do
  let key := n % BLS12_381.scalarFieldSize
  if let some (_, cell) := (← get).find? (fun entry => entry.1 == key) then return cell
  let cell ← region "Assign fixed" (assignFixed ⟨9⟩ 0 (n : F))
  modify ((key, cell) :: ·)
  return cell

theorem constant_eq (n : Nat) : constant n = canonicalConstant n := by
  unfold constant canonicalConstant
  rw [ZMod.val_natCast]
  rfl

def castTerms (terms : Array (Nat × WitnessCircuit.Cell)) : Array (F × WitnessCircuit.Cell) :=
  terms.map fun (coefficient, cell) => ((coefficient : F), cell)

theorem cast_beq (n m : Nat) :
    ((n : F) == (m : F)) = (n % BLS12_381.scalarFieldSize == m % BLS12_381.scalarFieldSize) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact (ZMod.val_injective BLS12_381.scalarFieldSize).eq_iff.symm.trans
    (by simp only [ZMod.val_natCast])

theorem cast_beq_zero (n : Nat) : ((n : F) == 0) = (n % BLS12_381.scalarFieldSize == 0) := by
  simpa only [Nat.cast_zero, Nat.zero_mod] using cast_beq n 0

theorem cast_beq_one (n : Nat) : ((n : F) == 1) = (n % BLS12_381.scalarFieldSize == 1) := by
  simpa only [Nat.cast_one, Nat.one_mod_eq_one.mpr (by decide : BLS12_381.scalarFieldSize ≠ 1)]
    using cast_beq n 1

theorem filter_cast (input : Array (Nat × WitnessCircuit.Cell)) (zero : WitnessCircuit.Cell) :
    (castTerms input).filter (fun (coefficient, cell) => coefficient != 0 && cell != zero) =
      castTerms (input.filter fun (coefficient, cell) =>
        coefficient % BLS12_381.scalarFieldSize != 0 && cell != zero) := by
  simp only [castTerms, Array.filter_map, Function.comp_def, bne, cast_beq_zero]

def natLinearCombination (input : Array (Nat × WitnessCircuit.Cell)) : Build WitnessCircuit.Cell := do
  let zero ← constant 0
  let terms := input.filter fun (coefficient, cell) =>
    coefficient % BLS12_381.scalarFieldSize != 0 && cell != zero
  if terms.isEmpty then return zero
  if terms.size == 1 && terms[0]!.1 % BLS12_381.scalarFieldSize == 1 then return terms[0]!.2
  let casted := castTerms terms
  region "Linear combination" do
    let values := casted.map fun (coefficient, cell) => (coefficient, (.expr cell : FExpr F))
    let resultValue := values.foldl (fun acc (coeff, value) => acc + .const coeff * value)
      (.const 0)
    let (result, assigned) ← linearAux values resultValue 4
    for i in [:casted.size] do constrainEqual assigned[i]! casted[i]!.2
    return result

theorem linearCombination_cast (input : Array (Nat × WitnessCircuit.Cell)) :
    linearCombination (castTerms input) = natLinearCombination input := by
  unfold linearCombination natLinearCombination
  congr 1
  funext zero
  rw [filter_cast]
  let terms := input.filter fun (coefficient, cell) =>
    coefficient % BLS12_381.scalarFieldSize != 0 && cell != zero
  change (if (castTerms terms).isEmpty then _ else _) = (if terms.isEmpty then _ else _)
  simp only [castTerms, Array.isEmpty, Array.size_map]
  split
  · rfl
  · rename_i nonempty
    simp only [decide_eq_true_eq] at nonempty
    have bound : 0 < terms.size := by omega
    have first : (terms.map fun x => ((x.1 : F), x.2))[0]! =
        ((terms[0]!.1 : F), terms[0]!.2) := by
      rw [getElem!_pos (terms.map fun x => ((x.1 : F), x.2)) 0 (by simpa using bound),
        getElem!_pos terms 0 bound]
      exact Array.getElem_map _ _
    dsimp only [terms] at first
    rw [first, cast_beq_one]

/-- The same sixteen source packing calls, with integer branch tests. -/
def natBlockFromBytes (bytes : Array WitnessCircuit.Cell) : Build (Array WitnessCircuit.Cell) := do
  let mut words := #[]
  for word in [:16] do
    let terms := (Array.range 4).map fun i => (256^i, bytes[word*4+3-i]!)
    words := words.push (← natLinearCombination terms)
  return words

theorem blockFromBytes_eq (bytes : Array WitnessCircuit.Cell) :
    blockFromBytes bytes = natBlockFromBytes bytes := by
  unfold blockFromBytes natBlockFromBytes
  simp only [← linearCombination_cast, castTerms, Array.map_map, Function.comp_def]

end Midnight.SHA256.Semantics.LinearNormalization
