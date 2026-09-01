import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

namespace Addition8Full

/--
Compute the 8-bit addition of two numbers with a carry-in bit.
Returns the sum.
-/
@[implicit_reducible]
def main (inputs : Var Addition8FullCarry.Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
  let output ← Addition8FullCarry.circuit inputs
  return output.z

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Addition8FullCarry.Inputs field main := by
  elaborate_circuit_with {
    localLength _ := 2
    output _ i₀ := var ⟨i₀⟩
  } using by
    constructor
    · intro input
      rfl
    · constructor
      · intro input i₀
        rfl
      · simp only [circuit_norm]

def Assumptions (input : Addition8FullCarry.Inputs (F p)) : Prop :=
  input.x.val < 256 ∧ input.y.val < 256 ∧ IsBool input.carryIn

def Spec (input : Addition8FullCarry.Inputs (F p)) (z : F p) : Prop :=
  z.val = (input.x.val + input.y.val + input.carryIn.val) % 256

-- The proofs are immediate from the bundled child circuit's semantic contract.
theorem soundness : Soundness (F p) main Assumptions Spec := by
  simp_all [circuit_norm, main, Assumptions, Spec,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]

theorem completeness : Completeness (F p) main Assumptions := by
  simp_all [circuit_norm, main, Assumptions,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions]

@[implicit_reducible]
def circuit : FormalCircuit (F p) Addition8FullCarry.Inputs field where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

@[circuit_norm ↓, explicit_circuit_norm]
lemma elaborated_eq : (circuit (p:=p)).elaborated = elaborated := rfl

@[circuit_norm, explicit_circuit_norm]
lemma localLength_eq (input : Var Addition8FullCarry.Inputs (F p)) :
    circuit.localLength input = 2 := by
  simp only [circuit_norm, circuit]

@[circuit_norm, explicit_circuit_norm]
lemma output_eq (input : Var Addition8FullCarry.Inputs (F p)) (offset : ℕ) :
    circuit.output input offset = var ⟨offset⟩ := by
  simp only [circuit_norm, circuit]

end Addition8Full

namespace Addition8
structure Inputs (F : Type) where
  x: F
  y: F
deriving ProvableStruct

/--
Compute the 8-bit addition of two numbers.
Returns the sum.
-/
@[implicit_reducible]
def main (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) :=
  Addition8Full.circuit { x := input.x, y := input.y, carryIn := 0 }

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs field main := by
  elaborate_circuit_with {
    localLength _ := 2
    output _ i₀ := var ⟨i₀⟩
  } using by
    constructor
    · intro input
      rfl
    · constructor
      · intro input i₀
        rfl
      · simp only [circuit_norm]

def Assumptions (input : Inputs (F p)) : Prop :=
  input.x.val < 256 ∧ input.y.val < 256

def Spec (input : Inputs (F p)) (z : F p) : Prop :=
  z.val = (input.x.val + input.y.val) % 256

-- The proofs are immediate from the bundled `Addition8Full` contract at carry-in zero.
theorem soundness : Soundness (F p) main Assumptions Spec := by
  simp_all [circuit_norm, main, Assumptions, Spec, Addition8Full.circuit,
    Addition8Full.Assumptions, Addition8Full.Spec, IsBool]

theorem completeness : Completeness (F p) main Assumptions := by
  simp_all [circuit_norm, main, Assumptions, Addition8Full.circuit,
    Addition8Full.Assumptions, IsBool]

@[implicit_reducible]
def circuit : FormalCircuit (F p) Inputs field where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

@[circuit_norm ↓, explicit_circuit_norm]
lemma elaborated_eq : (circuit (p:=p)).elaborated = elaborated := rfl

@[circuit_norm, explicit_circuit_norm]
lemma localLength_eq (input : Var Inputs (F p)) : circuit.localLength input = 2 := by
  simp only [circuit_norm, circuit]

@[circuit_norm, explicit_circuit_norm]
lemma output_eq (input : Var Inputs (F p)) (offset : ℕ) :
    circuit.output input offset = var ⟨offset⟩ := by
  simp only [circuit_norm, circuit]

end Addition8
end Gadgets
