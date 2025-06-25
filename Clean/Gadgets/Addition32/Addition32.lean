import Clean.Gadgets.Addition32.Addition32Full
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Addition32
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod_256 floordiv_256)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F

instance : ProvableStruct Inputs where
  components := [U32, U32]
  toComponents := fun {x, y} => .cons x ( .cons y .nil)
  fromComponents := fun (.cons x ( .cons y .nil)) => ⟨ x, y ⟩

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let ⟨x, y⟩ := input
  let ⟨z, _⟩ ← subcircuit Addition32Full.circuit {x, y, carry_in := 0}
  return z

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def spec (input : Inputs (F p)) (z: U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = (x.value + y.value) % 2^32 ∧ z.Normalized


-- def c := main (p:=p_babybear) default
-- #eval c.localLength
-- #eval c.output
instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main := main
  localLength _ := 8
  output _ i0 := ⟨var ⟨i0⟩, var ⟨i0 + 2⟩, var ⟨i0 + 4⟩, var ⟨i0 + 6⟩ ⟩

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ ⟨ x, y, carry_in ⟩ h_inputs as h
  rw [←elaborated.output_eq] -- replace explicit output with internal output, which is derived from the subcircuit
  simp_all [circuit_norm, spec, main, Addition32Full.circuit, subcircuit_norm,
  Addition32Full.assumptions, Addition32Full.spec, assumptions]

theorem completeness : Completeness (F p) elaborated assumptions := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ henv  ⟨ x, y, carry_in ⟩ h_inputs as
  simp_all [circuit_norm, main, Addition32Full.circuit, Addition32Full.elaborated, subcircuit_norm,
  Addition32Full.assumptions, Addition32Full.spec, assumptions]

def circuit : FormalCircuit (F p) Inputs U32 where
  assumptions
  spec
  soundness
  completeness
end Gadgets.Addition32
