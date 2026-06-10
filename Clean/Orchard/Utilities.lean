import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Gadgets.Equality
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard utility gadgets

Clean approximations of small utility gates used by Orchard and `halo2_gadgets`.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/cond_swap.rs`
- `CondSwapChip::configure`
- `CondSwapInstructions::swap`
- `CondSwapInstructions::mux`

These gadgets model the arithmetic gate constraints, not Halo2 selectors, regions, or
column layout.
-/

namespace Orchard
namespace Utilities

variable {F : Type} [Field F]

def ternary (choice ifTrue ifFalse : F) : F :=
  choice * ifTrue + (1 - choice) * ifFalse

structure CondSwapInputs (F : Type) where
  a : F
  b : F
  swap : F
deriving ProvableStruct

structure CondSwapOutput (F : Type) where
  aSwapped : F
  bSwapped : F
deriving ProvableStruct

namespace CondSwap

def outputValue (input : CondSwapInputs F) : CondSwapOutput F where
  aSwapped := ternary input.swap input.b input.a
  bSwapped := ternary input.swap input.a input.b

def main (input : Var CondSwapInputs F) : Circuit F (Var CondSwapOutput F) := do
  let aSwapped ← witnessField fun env => ternary (env input.swap) (env input.b) (env input.a)
  let bSwapped ← witnessField fun env => ternary (env input.swap) (env input.a) (env input.b)
  aSwapped === input.swap * input.b + (1 - input.swap) * input.a
  bSwapped === input.swap * input.a + (1 - input.swap) * input.b
  assertZero (input.swap * (input.swap - 1))
  return { aSwapped, bSwapped }

@[circuit_norm]
def Assumptions (input : CondSwapInputs F) : Prop :=
  IsBool input.swap

@[circuit_norm]
def Spec [DecidableEq F] (input : CondSwapInputs F) (output : CondSwapOutput F) : Prop :=
  output = if input.swap = 1 then
    { aSwapped := input.b, bSwapped := input.a }
  else
    { aSwapped := input.a, bSwapped := input.b }

instance elaborated : ElaboratedCircuit F CondSwapInputs CondSwapOutput main := by
  elaborate_circuit

theorem outputValue_eq_of_bool [DecidableEq F] {input : CondSwapInputs F}
    (hbool : IsBool input.swap) :
    outputValue input = if input.swap = 1 then
      { aSwapped := input.b, bSwapped := input.a }
    else
      { aSwapped := input.a, bSwapped := input.b } := by
  rcases hbool with hzero | hone
  · simp [outputValue, ternary, hzero]
  · simp [outputValue, ternary, hone]

theorem soundness [DecidableEq F] :
    Soundness F main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, outputValue, ternary]
  have hbool : IsBool input_swap :=
    IsBool.iff_mul_sub_one.mpr (by simpa [sub_eq_add_neg] using h_holds.2.2)
  rcases hbool with hzero | hone
  · rw [h_holds.1, h_holds.2.1]
    simp [hzero]
  · rw [h_holds.1, h_holds.2.1]
    simp [hone]

theorem completeness [DecidableEq F] :
    Completeness F main Assumptions := by
  circuit_proof_start [main, Assumptions, outputValue, ternary]
  constructor
  · rw [h_env.1]
    ring_nf
  · constructor
    · rw [h_env.2]
      ring_nf
    · simpa [sub_eq_add_neg] using IsBool.iff_mul_sub_one.mp h_assumptions

def circuit [DecidableEq F] : FormalCircuit F CondSwapInputs CondSwapOutput where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end CondSwap

/-!
Reference:
`orchard@0.14.0/src/circuit/gadget/add_chip.rs`
- `Field element addition: c = a + b`

This is the small Orchard-specific addition chip used where the Rust circuit wants a
copy-constrained field addition result.
-/

namespace AddChip

def main (input : Var fieldPair F) : Circuit F (Var field F) := do
  let (a, b) := input
  let c ← witnessField fun env => env a + env b
  assertZero (a + b - c)
  return c

def Spec (input : fieldPair F) (output : F) : Prop :=
  output = input.1 + input.2

instance elaborated : ElaboratedCircuit F fieldPair field main := by
  elaborate_circuit

theorem soundness : Soundness F main (fun _ => True) Spec := by
  circuit_proof_start [main, Spec]
  rcases input with ⟨a, b⟩
  simp only [Prod.mk.injEq] at h_input
  rcases h_input with ⟨ha, hb⟩
  rw [← ha, ← hb]
  exact (eq_of_add_neg_eq_zero h_holds).symm

theorem completeness : Completeness F main (fun _ => True) := by
  circuit_proof_start [main, Spec]
  rw [h_env]
  ring

def circuit : FormalCircuit F fieldPair field where
  main
  elaborated
  Assumptions := fun _ => True
  Spec
  soundness
  completeness

end AddChip

/-!
References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities.rs`
- `range_check`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/decompose_running_sum.rs`
- `RunningSumConfig::configure`
- `range check`

The source helper constrains `WINDOW_NUM_BITS <= 3`; this assertion models one enabled
running-sum row for any fixed `windowNumBits`, with the same arithmetic relation:
`word = z_cur - 2^K * z_next` and `range_check(word, 2^K) = 0`.
-/

namespace RunningSum

structure Step (F : Type) where
  zCur : F
  zNext : F
deriving ProvableStruct

def twoPowWindow (windowNumBits : ℕ) : F :=
  (2 ^ windowNumBits : ℕ)

def rangeCheckValues (range : ℕ) : List F :=
  (List.range range).drop 1 |>.map fun i => (i : F)

def rangeCheckPoly (range : ℕ) (word : F) : F :=
  rangeCheckValues (F := F) range |>.foldl (fun acc i => acc * (i - word)) word

def word (windowNumBits : ℕ) (step : Step F) : F :=
  step.zCur - twoPowWindow windowNumBits * step.zNext

def Spec (windowNumBits : ℕ) (step : Step F) : Prop :=
  rangeCheckPoly (2 ^ windowNumBits) (word windowNumBits step) = 0

def rangeCheckPolyExpr (range : ℕ) (word : Expression F) : Expression F :=
  rangeCheckValues (F := F) range |>.foldl (fun acc i => acc * (Expression.const i - word)) word

private theorem eval_rangeCheckFoldl
    (env : Environment F) (xs : List F) (word acc : Expression F) :
    Expression.eval env (xs.foldl (fun acc i => acc * (Expression.const i - word)) acc) =
      xs.foldl (fun acc i => acc * (i - Expression.eval env word))
        (Expression.eval env acc) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Expression.eval, sub_eq_add_neg]

private theorem eval_rangeCheckPolyExpr
    (env : Environment F) (range : ℕ) (word : Expression F) :
    Expression.eval env (rangeCheckPolyExpr range word) =
      rangeCheckPoly range (Expression.eval env word) := by
  unfold rangeCheckPolyExpr rangeCheckPoly
  exact eval_rangeCheckFoldl env (rangeCheckValues range) word word

def main (windowNumBits : ℕ) (step : Var Step F) : Circuit F Unit := do
  let word := step.zCur - (twoPowWindow windowNumBits : F) * step.zNext
  assertZero (rangeCheckPolyExpr (2 ^ windowNumBits) word)

def circuit (windowNumBits : ℕ) : FormalAssertion F Step where
  main := main windowNumBits
  Spec := Spec windowNumBits
  soundness := by
    circuit_proof_start [main, Spec, word, rangeCheckPoly, rangeCheckPolyExpr, twoPowWindow]
    change Expression.eval env
        (rangeCheckPolyExpr (2 ^ windowNumBits)
          (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)) = 0 at h_holds
    have h_eval :
        Expression.eval env
          (rangeCheckPolyExpr (2 ^ windowNumBits)
            (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)) =
          rangeCheckPoly (2 ^ windowNumBits)
            (Expression.eval env
              (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)) := by
      exact eval_rangeCheckPolyExpr env (2 ^ windowNumBits)
        (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)
    rw [h_eval] at h_holds
    rcases h_input with ⟨hzCur, hzNext⟩
    have hword :
        Expression.eval env
            (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext) =
          input_zCur - twoPowWindow windowNumBits * input_zNext := by
      simp only [Expression.eval, hzCur, hzNext, twoPowWindow]
      ring
    rw [hword] at h_holds
    simpa [word, rangeCheckPoly, twoPowWindow] using h_holds
  completeness := by
    circuit_proof_start [main, Spec, word, rangeCheckPoly, rangeCheckPolyExpr, twoPowWindow]
    change Expression.eval env.toEnvironment
        (rangeCheckPolyExpr (2 ^ windowNumBits)
          (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)) = 0
    have h_eval :
        Expression.eval env.toEnvironment
          (rangeCheckPolyExpr (2 ^ windowNumBits)
            (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)) =
          rangeCheckPoly (2 ^ windowNumBits)
            (Expression.eval env.toEnvironment
              (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)) := by
      exact eval_rangeCheckPolyExpr env.toEnvironment (2 ^ windowNumBits)
        (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext)
    rw [h_eval]
    rcases h_input with ⟨hzCur, hzNext⟩
    have hword :
        Expression.eval env.toEnvironment
            (input_var_zCur - (twoPowWindow windowNumBits : F) * input_var_zNext) =
          input_zCur - twoPowWindow windowNumBits * input_zNext := by
      simp only [Expression.eval, hzCur, hzNext, twoPowWindow]
      ring
    rw [hword]
    simpa [word, rangeCheckPoly, twoPowWindow] using h_spec

end RunningSum

end Utilities
end Orchard
