import Clean.Gadgets.Addition32.Addition32Full
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Addition32
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256)
open FieldUtils (floorDiv)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let ⟨x, y⟩ := input
  let ⟨z, _⟩ ← Addition32Full.circuit {x, y, carryIn := 0}
  return z

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = (x.value + y.value) % 2^32 ∧ z.Normalized

instance elaborated : ElaboratedCircuit (F p) Inputs U32 main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ ⟨ x, y, carry_in ⟩ h_inputs as h
  rw [←elaborated.output_eq] -- replace explicit output with internal output, which is derived from the subcircuit
  simp_all [circuit_norm, Spec, main, Addition32Full.circuit,
  Addition32Full.Assumptions, Addition32Full.Spec, Assumptions]

theorem completeness : Completeness (F p) main Assumptions := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ henv  ⟨ x, y, carry_in ⟩ h_inputs as
  simp_all [circuit_norm, main, Addition32Full.circuit,
  Addition32Full.Assumptions, Addition32Full.Spec, Assumptions, IsBool]

def circuit : FormalCircuit (F p) Inputs U32 where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness
/-- The output is a fresh witness window (the interleaved sum limbs): evaluating it reads
the environment only below `n + localLength`, independently of the circuit's input. -/
lemma output_congr {env env' : ProverEnvironment (F p)} {v : Var Inputs (F p)} {n : ℕ}
    (h : env.AgreesBelow (n + 8) env') :
    eval env.toEnvironment ((circuit (p:=p)).output v n) =
      eval env'.toEnvironment ((circuit (p:=p)).output v n) := by
  simp only [circuit_norm, ComputableWitnesses.reduceOutputMetadata, U32.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact h.1 _ (by omega)

end Gadgets.Addition32
