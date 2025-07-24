import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Utils.Tactics

namespace Gadgets.ConditionalU32

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Inputs for conditional U32 selection.
Contains a condition bit and two U32 values to select from.
-/
structure Inputs (F : Type) where
  cond : F          -- 0 or 1 (boolean flag)
  ifTrue : U32 F    -- Value to return if cond = 1
  ifFalse : U32 F   -- Value to return if cond = 0

instance : ProvableStruct Inputs where
  components := [field, U32, U32]
  toComponents := fun { cond, ifTrue, ifFalse } =>
    .cons cond (.cons ifTrue (.cons ifFalse .nil))
  fromComponents := fun xss =>
    match xss with
    | .cons cond (.cons ifTrue (.cons ifFalse .nil)) =>
      { cond := cond, ifTrue := ifTrue, ifFalse := ifFalse }
  fromComponents_toComponents := by
    intros; rfl

/--
Main circuit that performs conditional selection for U32.
If cond = 1, returns ifTrue; if cond = 0, returns ifFalse.
Uses the formula: result = cond * ifTrue + (1 - cond) * ifFalse
-/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let { cond, ifTrue, ifFalse } := input

  -- For each limb, compute: result_limb = cond * ifTrue_limb + (1 - cond) * ifFalse_limb
  let x0 <== cond * ifTrue.x0 + (1 - cond) * ifFalse.x0
  let x1 <== cond * ifTrue.x1 + (1 - cond) * ifFalse.x1
  let x2 <== cond * ifTrue.x2 + (1 - cond) * ifFalse.x2
  let x3 <== cond * ifTrue.x3 + (1 - cond) * ifFalse.x3

  return ⟨x0, x1, x2, x3⟩

instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main := main
  localLength _ := 4  -- 1 constraint for boolean + 4 for limbs

def Assumptions (input : Inputs (F p)) : Prop :=
  input.cond = 0 ∨ input.cond = 1

def Spec (input : Inputs (F p)) (output : U32 (F p)) : Prop :=
  output = if input.cond = 1 then input.ifTrue else input.ifFalse

omit [Fact (p > 512)] in
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro offset env
    ⟨ cond_var, ⟨ x0_var, x1_var, x2_var, x3_var ⟩, ⟨ y0_var, y1_var, y2_var, y3_var ⟩ ⟩
    ⟨ cond, ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩ ⟩
    h_eval h_assumptions h_holds
  simp only [circuit_norm, Inputs.mk.injEq, U32.mk.injEq, explicit_provable_type] at h_eval
  simp only [main, circuit_norm, explicit_provable_type, Spec, Assumptions, h_eval] at *
  simp only [h_holds]
  rcases h_assumptions with h_asm|h_asm <;> simp [h_asm]

omit [Fact (p > 512)] in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro offset env input_var h_env_uses input h_eval h_assumptions
  simp only [Assumptions] at h_assumptions
  decompose_provable_struct
  simp only [circuit_norm, Inputs.mk.injEq] at h_eval
  simp only [main, circuit_norm]

  -- The constraints are satisfied by construction of the witnesses
  -- Limb constraints - all follow from witness construction
  have h_uses : env.UsesLocalWitnessesCompleteness offset (main input_var (offset)).2 := by
    simp only [elaborated, ElaboratedCircuit.main] at h_env_uses
    exact h_env_uses
  simp only [main, circuit_norm] at h_uses
  obtain ⟨h_wit0, h_wit1, h_wit2, h_wit3⟩ := h_uses
  -- The witnesses are exactly what the constraints require
  exact ⟨h_wit0, h_wit1, h_wit2, h_wit3⟩

def circuit : FormalCircuit (F p) Inputs U32 := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.ConditionalU32
