import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Utils.Tactics
import Clean.Gadgets.ConditionalU32
import Clean.Circuit.Loops

namespace Gadgets.ConditionalVector8U32

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Inputs for conditional Vector8 U32 selection.
Contains a condition bit and two Vector (U32 F) 8 values to select from.
-/
structure Inputs (F : Type) where
  cond : F                     -- 0 or 1 (boolean flag)
  ifTrue : Vector (U32 F) 8    -- Vector to return if cond = 1
  ifFalse : Vector (U32 F) 8   -- Vector to return if cond = 0

instance : ProvableStruct Inputs where
  components := [field, ProvableVector U32 8, ProvableVector U32 8]
  toComponents := fun { cond, ifTrue, ifFalse } =>
    .cons cond (.cons ifTrue (.cons ifFalse .nil))
  fromComponents := fun xss =>
    match xss with
    | .cons cond (.cons ifTrue (.cons ifFalse .nil)) =>
      { cond := cond, ifTrue := ifTrue, ifFalse := ifFalse }
  fromComponents_toComponents := by
    intros; rfl

/--
Main circuit that performs conditional selection for Vector (U32 F) 8.
If cond = 1, returns ifTrue; if cond = 0, returns ifFalse.
Uses Circuit.map to apply ConditionalU32 to each element of the vector.
-/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var (ProvableVector U32 8) (F p)) := do
  let { cond, ifTrue, ifFalse } := input

  -- Create a vector of indices
  let indices : Vector (Fin 8) 8 := Vector.ofFn id

  -- Map over indices, applying ConditionalU32 to each pair of elements
  Circuit.map indices fun i => do
    let condInput : Var ConditionalU32.Inputs (F p) := {
      cond := cond
      ifTrue := ifTrue[i]
      ifFalse := ifFalse[i]
    }
    ConditionalU32.circuit condInput

instance elaborated : ElaboratedCircuit (F p) Inputs (ProvableVector U32 8) where
  main := main
  localLength _ := 8 * 4  -- 8 calls to ConditionalU32, each with localLength 4
  localLength_eq _ _ := by simp only [main, circuit_norm, ConditionalU32.circuit]
  output_eq _ _ := by simp only [main, circuit_norm, ConditionalU32.circuit]
  subcircuitsConsistent _ _ := by simp only [main, circuit_norm, ConditionalU32.circuit]

def Assumptions (input : Inputs (F p)) : Prop :=
  input.cond = 0 ∨ input.cond = 1

def Spec (input : Inputs (F p)) (output : Vector (U32 (F p)) 8) : Prop :=
  output = if input.cond = 1 then input.ifTrue else input.ifFalse

omit [Fact (p > 512)] in
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  ext1
  rename_i i h_i
  simp only [eval_vector, Vector.getElem_map, Vector.getElem_mapIdx]
  specialize h_holds ⟨ i, h_i ⟩
  simp only [ConditionalU32.circuit, ConditionalU32.Assumptions] at h_holds
  specialize h_holds h_assumptions
  simp only [ConditionalU32.Spec] at h_holds
  simp only [h_holds, id]
  -- the following is for adding [i] to h_input equations, automate
  simp only [eval_vector] at h_input
  simp only [Vector.ext_iff] at h_input
  rcases h_input with ⟨ h_input, h_true, h_false ⟩
  specialize h_true i h_i
  specialize h_false i h_i
  simp only [Vector.getElem_map] at h_true h_false
  norm_num
  simp only [h_true, h_false]
  split <;> rfl

omit [Fact (p > 512)] in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  intro i
  simp only [ConditionalU32.circuit, ConditionalU32.Assumptions, h_input, h_assumptions]

def circuit : FormalCircuit (F p) Inputs (ProvableVector U32 8) := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.ConditionalVector8U32
