import Clean.Circuit

namespace ReduceDataExperiment

variable {F : Type} [Field F]

namespace Small

/-- A tiny formal subcircuit with one local witness. -/
def main (x : Expression F) : Circuit F (Expression F) := do
  let y ← witness fun _ => (0 : F)
  return y + x

@[reducible]
instance elaborated : ElaboratedCircuit F field field main := by
  elaborate_circuit_naive

def circuit : FormalCircuit F field field where
  main := main
  elaborated := elaborated
  Assumptions _ := True
  Spec _ _ := True
  soundness := by
    intro offset env input_var input h_input h_assumptions h_holds
    simp only [circuit_norm, Small.main]
  completeness := by
    intro offset env input_var h_env input h_input h_assumptions
    simp only [circuit_norm, Small.main]

end Small

namespace Deep

/-- A non-loop baseline: deeply nested subcircuits. -/
def main (x : Expression F) : Circuit F (Expression F) := do
  let x ← Small.circuit x
  let x ← Small.circuit x
  let x ← Small.circuit x
  let x ← Small.circuit x
  let x ← Small.circuit x
  return x

example (x : Expression F) : ExplicitCircuit (main x) := by
  unfold main
  simp only [Small.circuit]
  infer_explicit_circuit

@[reducible]
instance elaborated : ElaboratedCircuit F field field main := by
  elaborate_circuit_naive

/-- Kernel reduction of the derived projection computes the expected compact length. -/
example (x : Expression F) :
    ElaboratedCircuit.localLength (F:=F) (Input:=field) (Output:=field) main x = 5 := rfl

end Deep

namespace LoopDeep

/--
A fast representative of the Keccak elaboration-data problem: nested loops whose bodies are formal
subcircuits.  This exercises both `mapFinRange` explicit derivation and subcircuit metadata.
-/
def main (x : Expression F) : Circuit F (Vector (Expression F) 8) := do
  let ys ← Circuit.mapFinRange 8 fun _ => Small.circuit x
  let zs ← Circuit.mapFinRange 8 fun i => Small.circuit ys[i]
  return zs

example (x : Expression F) : ExplicitCircuit (main x) := by
  unfold main
  simp only [Small.circuit]
  infer_explicit_circuit

/-- The explicit derivation tree reduces to a compact constant length. -/
example (x : Expression F) (n : ℕ) :
    (by
      unfold main
      simp only [Small.circuit]
      infer_explicit_circuit : ExplicitCircuit (main x)).localLength n = 16 := rfl

@[reducible]
instance reducedElaborated : ElaboratedCircuit F field (fields 8) main := by
  elaborate_circuit

example : ElaboratedCircuit F field (fields 8) main := by
  elaborate_circuit_with {
    localLength _ := 16
  } using by
    simp only [circuit_norm]

/-- The reduced elaboration tactic stores the compact length directly. -/
example (x : Expression F) :
    ElaboratedCircuit.localLength (F:=F) (Input:=field) (Output:=fields 8) main x = 16 := rfl

/-- A manually written version of the local-length part that the tactic is meant to avoid. -/
example : ElaboratedCircuit F field (fields 8) main where
  localLength _ := 16
  localLength_eq x n := by
    rw [(by
      unfold main
      simp only [Small.circuit]
      infer_explicit_circuit : ExplicitCircuit (main x)).localLength_eq]
    rfl
  output_eq x n := by
    rw [(by
      unfold main
      simp only [Small.circuit]
      infer_explicit_circuit : ExplicitCircuit (main x)).output_eq]
  subcircuitsConsistent x n := by
    exact (by
      unfold main
      simp only [Small.circuit]
      infer_explicit_circuit : ExplicitCircuit (main x)).subcircuitsConsistent n
  channelsLawful x n := by
    exact (by
      unfold main
      simp only [Small.circuit]
      infer_explicit_circuit : ExplicitCircuit (main x)).channelsLawful n

end LoopDeep

end ReduceDataExperiment
