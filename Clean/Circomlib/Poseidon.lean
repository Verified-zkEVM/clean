module

public import Clean.Circomlib.Poseidon.Generic

@[expose] public section

/-
Poseidon Hash Circuit Implementation

The generic implementation lives in `Clean.Circomlib.Poseidon.Generic` and
follows circomlib's optimized six-phase schedule. This module provides the
stable arity-specific public wrappers.

Original circomlib source:
https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom
-/

namespace Circomlib.Poseidon

open Specs.Poseidon (F)
open Specs.PoseidonOptimized (params_t2 params_t3 params_t4)

namespace Poseidon1

/-- Scalar-input compatibility wrapper for the generic state-width-two
Poseidon circuit. -/
def main (input : Expression F) : Circuit F (Expression F) :=
  Circomlib.Poseidon.circuit params_t2 #v[input]

def Spec (input output : F) : Prop :=
  output = Specs.PoseidonOptimized.poseidon1Opt input

instance elaborated : ElaboratedCircuit F field field main := by
  elaborate_circuit

/-- The generic `MixLast` layout removes the legacy circuit's unused second
final-state witness while leaving the returned output at local offset 400. -/
theorem localLength_eq (input : Expression F) :
    ElaboratedCircuit.localLength (F := F) (Input := field) (Output := field)
      main input = 401 := by
  dsimp +instances only [elaborated]
  norm_num [params_t2]

theorem output_eq (input : Expression F) :
    ElaboratedCircuit.output (F := F) (Input := field) (Output := field)
      main input 0 = var { index := 400 } := by
  dsimp +instances only [elaborated]
  norm_num [params_t2]
  rfl

theorem soundness :
    Soundness F (Input := field) (Output := field)
      main (fun _ => True) Spec := by
  circuit_proof_start [Circomlib.Poseidon.circuit, Circomlib.Poseidon.Spec]
  simp only [Specs.PoseidonOptimized.poseidon_params_t2_eq_poseidon1Opt] at h_holds
  simp [circuit_norm] at h_holds
  exact h_holds

theorem completeness :
    Completeness F (Input := field) (Output := field)
      main (fun _ => True) := by
  circuit_proof_start [Circomlib.Poseidon.circuit]

/-- The verified one-input Poseidon circuit, retained under its original
public name. Soundness and completeness are inherited from the generic
parameterized circuit. -/
def circuit : FormalCircuit F field field where
  main
  elaborated
  Spec
  soundness
  completeness

end Poseidon1

namespace Poseidon2

/-- The verified two-input Poseidon circuit, obtained by specializing the
generic circuit to state width three. -/
def circuit : FormalCircuit F (fields 2) field :=
  Circomlib.Poseidon.circuit params_t3

end Poseidon2

namespace Poseidon3

/-- The verified three-input Poseidon circuit, obtained by specializing the
generic circuit to state width four. -/
def circuit : FormalCircuit F (fields 3) field :=
  Circomlib.Poseidon.circuit params_t4

end Poseidon3

namespace Poseidon4

def circuit : FormalCircuit F (fields 4) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t5

end Poseidon4

namespace Poseidon5

def circuit : FormalCircuit F (fields 5) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t6

end Poseidon5

namespace Poseidon6

def circuit : FormalCircuit F (fields 6) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t7

end Poseidon6

namespace Poseidon7

def circuit : FormalCircuit F (fields 7) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t8

end Poseidon7

namespace Poseidon8

def circuit : FormalCircuit F (fields 8) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t9

end Poseidon8

namespace Poseidon9

def circuit : FormalCircuit F (fields 9) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t10

end Poseidon9

namespace Poseidon10

def circuit : FormalCircuit F (fields 10) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t11

end Poseidon10

namespace Poseidon11

def circuit : FormalCircuit F (fields 11) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t12

end Poseidon11

namespace Poseidon12

def circuit : FormalCircuit F (fields 12) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t13

end Poseidon12

namespace Poseidon13

def circuit : FormalCircuit F (fields 13) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t14

end Poseidon13

namespace Poseidon14

def circuit : FormalCircuit F (fields 14) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t15

end Poseidon14

namespace Poseidon15

def circuit : FormalCircuit F (fields 15) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t16

end Poseidon15

namespace Poseidon16

def circuit : FormalCircuit F (fields 16) field :=
  Circomlib.Poseidon.circuit Specs.PoseidonOptimized.params_t17

end Poseidon16

end Circomlib.Poseidon
