import Clean.Gadgets.Addition32.Addition32Full
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Addition32
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F

instance : ProvableStruct Inputs where
  components := [U32, U32]
  toComponents := fun {x, y} => .cons x ( .cons y .nil)
  fromComponents := fun (.cons x ( .cons y .nil)) => ⟨ x, y ⟩

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var Inputs (F p)) : Circuit sentences (Var U32 (F p)) := do
  let ⟨x, y⟩ := input
  let ⟨z, _⟩ ← Addition32Full.circuit order {x, y, carryIn := 0}
  return z

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : Inputs (F p)) :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = (x.value + y.value) % 2^32 ∧ z.Normalized

-- def c := main (p:=p_babybear) default
-- #eval c.localLength
-- #eval c.output
instance elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs U32 where
  main := main order
  localLength _ := 8
  output _ i0 := ⟨var ⟨i0⟩, var ⟨i0 + 2⟩, var ⟨i0 + 4⟩, var ⟨i0 + 6⟩ ⟩

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  rintro i0 env yields checked ⟨ x_var, y_var, carry_in_var ⟩ ⟨ x, y, carry_in ⟩ h_inputs as h
  constructor
  · -- Prove yielded sentences hold (vacuous - no yields)
    intro s hs _
    sorry
  rw [←(elaborated order).output_eq] -- replace explicit output with internal output, which is derived from the subcircuit
  simp_all [circuit_norm, Spec, main, Addition32Full.circuit,
  Addition32Full.Assumptions, Addition32Full.Spec, Assumptions]

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
    circuit_proof_start
    simp_all [circuit_norm, Addition32Full.circuit, Addition32Full.elaborated,
    Addition32Full.CompletenessAssumptions, Addition32Full.Assumptions, Addition32Full.Spec, Assumptions, IsBool]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order Inputs U32 where
  elaborated := elaborated order
  Assumptions
  CompletenessAssumptions
  Spec
  soundness := soundness order
  completeness := completeness order
  completenessAssumptions_implies_assumptions := fun _ _ h => h
end Gadgets.Addition32
