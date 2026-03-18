import Clean.Circuit

namespace Examples.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct


def main (prover_input : Row (F p)) (_input : Unit) : Circuit (F p) (Unit × Var Row (F p)) := do
  let row : Var Row _ ← witness fun _env => prover_input
  let ⟨x, y, z⟩ := row
  assertZero (x*y - z)
  return ⟨(), ⟨x, y, z⟩⟩

def Assumptions (_inputs : Unit) := True

def Spec (_inputs : Unit) (output : Row (F p)) :=
  output.x * output.y = output.z

def ProverAssumptions (prover_input : Row (F p)) :=
  prover_input.x * prover_input.y = prover_input.z

def ProverSpec (prover_input : Row (F p)) (_prover_output : Unit) (_input : Unit) (output : Row (F p)) :=
  prover_input = output

instance elaborated : ElaboratedCircuit' (F p) unit Row Row unit where
  main
  localLength _ := 3

theorem soundness : GeneralFormalCircuit'.Soundness (F p) elaborated Assumptions Spec := by
  simp [circuit_norm]
  rintro offset env ⟨prover_x, prover_y, prover_z⟩ input input_var h_assumptions
  simp [circuit_norm, elaborated, main, Spec]
  rw [add_neg_eq_zero]
  simp only [imp_self]

theorem completeness : GeneralFormalCircuit'.Completeness (F p) elaborated ProverAssumptions ProverSpec := by
  simp [circuit_norm]
  rintro offset env ⟨prover_x, prover_y, prover_z⟩ input_var h_honest_prover input h_prover_assumptions
  simp [ProverAssumptions] at h_prover_assumptions
  simp [circuit_norm, elaborated, main] at h_honest_prover
  simp [circuit_norm, elaborated, main, ProverSpec]
  have env0 := h_honest_prover 0
  have env1 := h_honest_prover 1
  have env2 := h_honest_prover 2
  simp [circuit_norm, toElements] at env0 env1 env2
  simp [env0, env1, env2]
  sorry

def circuit : GeneralFormalCircuit' (F p) unit Row Row unit :=
  { elaborated with Assumptions, Spec, ProverAssumptions, ProverSpec, soundness, completeness }

end Examples.Circuits.Core.AllocMul


namespace Examples.Circuits.Core.Mul
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct


def main (prover_input : Input (F p)) (input : Var Input (F p)) : Circuit (F p) (Unit × Var field (F p)) := do
  let ⟨(), ⟨x, y, z⟩⟩ ← subcircuitWithAssertion' Examples.Circuits.Core.AllocMul.circuit
    ⟨prover_input.x, prover_input.y, prover_input.x * prover_input.y⟩ ()
  assertZero (x - input.x)
  assertZero (y - input.y)
  return ⟨(), z⟩

def Assumptions (_inputs : Input (F p)) := True

def Spec (input : Input (F p)) (output : field (F p)) := input.x * input.y = output

def ProverAssumptions (_prover_input : Input (F p)) := True

def ProverSpec (prover_input : Input (F p)) (_prover_output : Unit) (_input : Input (F p)) (output : field (F p)) :=
  prover_input.x * prover_input.y = output

instance elaborated : ElaboratedCircuit' (F p) Input field Input unit where
  main
  localLength _ := 3
  localLength_eq := by sorry

theorem soundness : GeneralFormalCircuit'.Soundness (F p) elaborated Assumptions Spec := by
  sorry

theorem completeness : GeneralFormalCircuit'.Completeness (F p) elaborated ProverAssumptions ProverSpec := by
  sorry

def circuit : GeneralFormalCircuit' (F p) Input field Input unit :=
  { elaborated with Assumptions, Spec, ProverAssumptions, ProverSpec, soundness, completeness }

end Examples.Circuits.Core.Mul
