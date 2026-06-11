import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Gadgets.Equality
import Clean.Orchard.Ecc
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

def outputValue (input : CondSwapInputs Ecc.PallasBaseField) :
    CondSwapOutput Ecc.PallasBaseField where
  aSwapped := ternary input.swap input.b input.a
  bSwapped := ternary input.swap input.a input.b

def main (input : Var CondSwapInputs Ecc.PallasBaseField) :
    Circuit Ecc.PallasBaseField (Var CondSwapOutput Ecc.PallasBaseField) := do
  let aSwapped ← witnessField fun env => ternary (env input.swap) (env input.b) (env input.a)
  let bSwapped ← witnessField fun env => ternary (env input.swap) (env input.a) (env input.b)
  aSwapped === input.swap * input.b + (1 - input.swap) * input.a
  bSwapped === input.swap * input.a + (1 - input.swap) * input.b
  assertZero (input.swap * (input.swap - 1))
  return { aSwapped, bSwapped }

@[circuit_norm]
def Assumptions (input : CondSwapInputs Ecc.PallasBaseField) : Prop :=
  IsBool input.swap

@[circuit_norm]
def Spec (input : CondSwapInputs Ecc.PallasBaseField)
    (output : CondSwapOutput Ecc.PallasBaseField) : Prop :=
  output = if input.swap = 1 then
    { aSwapped := input.b, bSwapped := input.a }
  else
    { aSwapped := input.a, bSwapped := input.b }

instance elaborated :
    ElaboratedCircuit Ecc.PallasBaseField CondSwapInputs CondSwapOutput main := by
  elaborate_circuit

theorem outputValue_eq_of_bool {input : CondSwapInputs Ecc.PallasBaseField}
    (hbool : IsBool input.swap) :
    outputValue input = if input.swap = 1 then
      { aSwapped := input.b, bSwapped := input.a }
    else
      { aSwapped := input.a, bSwapped := input.b } := by
  rcases hbool with hzero | hone
  · simp [outputValue, ternary, hzero]
  · simp [outputValue, ternary, hone]

theorem soundness :
    Soundness Ecc.PallasBaseField main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, outputValue, ternary]
  have hbool : IsBool input_swap :=
    IsBool.iff_mul_sub_one.mpr (by simpa [sub_eq_add_neg] using h_holds.2.2)
  rcases hbool with hzero | hone
  · rw [h_holds.1, h_holds.2.1]
    simp [hzero]
  · rw [h_holds.1, h_holds.2.1]
    simp [hone]

theorem completeness :
    Completeness Ecc.PallasBaseField main Assumptions := by
  circuit_proof_start [main, Assumptions, outputValue, ternary]
  constructor
  · rw [h_env.1]
    ring_nf
  · constructor
    · rw [h_env.2]
      ring_nf
    · simpa [sub_eq_add_neg] using IsBool.iff_mul_sub_one.mp h_assumptions

def circuit : FormalCircuit Ecc.PallasBaseField CondSwapInputs CondSwapOutput where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end CondSwap

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/cond_swap.rs`
- `CondSwapChip<pallas::Base>::mux_on_points`

The Rust helper runs the field mux on both coordinates and returns the selected point.
-/

namespace PointMux

structure Inputs (F : Type) where
  choice : F
  left : Ecc.Point F
  right : Ecc.Point F
deriving ProvableStruct

def xInput {K : Type} (input : Inputs K) : CondSwapInputs K where
  a := input.left.x
  b := input.right.x
  swap := input.choice

def yInput {K : Type} (input : Inputs K) : CondSwapInputs K where
  a := input.left.y
  b := input.right.y
  swap := input.choice

@[circuit_norm]
def Assumptions (input : Inputs Ecc.PallasBaseField) : Prop :=
  IsBool input.choice

@[circuit_norm]
def Spec (input : Inputs Ecc.PallasBaseField) (output : Ecc.Point Ecc.PallasBaseField) :
    Prop :=
  output = if input.choice = 1 then input.right else input.left

def main (input : Var Inputs Ecc.PallasBaseField) :
    Circuit Ecc.PallasBaseField (Var Ecc.Point Ecc.PallasBaseField) := do
  let xOut ← CondSwap.circuit (xInput input)
  let yOut ← CondSwap.circuit (yInput input)
  return { x := xOut.aSwapped, y := yOut.aSwapped }

instance elaborated : ElaboratedCircuit Ecc.PallasBaseField Inputs Ecc.Point main := by
  elaborate_circuit

theorem soundness :
    Soundness Ecc.PallasBaseField main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, xInput, yInput,
    CondSwap.circuit, CondSwap.Spec]
  rcases h_holds with ⟨hX, hY⟩
  have hXMux := hX h_assumptions
  have hYMux := hY h_assumptions
  have hLeftX : Expression.eval env input_var_left.x = input_left.x := by
    have h := congrArg Ecc.Point.x h_input.2.1
    simpa [circuit_norm] using h
  have hLeftY : Expression.eval env input_var_left.y = input_left.y := by
    have h := congrArg Ecc.Point.y h_input.2.1
    simpa [circuit_norm] using h
  have hRightX : Expression.eval env input_var_right.x = input_right.x := by
    have h := congrArg Ecc.Point.x h_input.2.2
    simpa [circuit_norm] using h
  have hRightY : Expression.eval env input_var_right.y = input_right.y := by
    have h := congrArg Ecc.Point.y h_input.2.2
    simpa [circuit_norm] using h
  by_cases hChoiceOne : input_choice = 1
  · simp [hChoiceOne, hLeftX, hLeftY, hRightX, hRightY] at hXMux hYMux ⊢
    apply congrArg₂ Ecc.Point.mk
    · exact hXMux.1
    · exact hYMux.1
  · simp [hChoiceOne, hLeftX, hLeftY, hRightX, hRightY] at hXMux hYMux ⊢
    apply congrArg₂ Ecc.Point.mk
    · exact hXMux.1
    · exact hYMux.1

theorem completeness :
    Completeness Ecc.PallasBaseField main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, xInput, yInput,
    CondSwap.circuit, CondSwap.Spec]
  rcases h_assumptions with hChoiceZero | hChoiceOne
  · exact Or.inl hChoiceZero
  · exact Or.inr hChoiceOne

def circuit : FormalCircuit Ecc.PallasBaseField Inputs Ecc.Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end PointMux

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/cond_swap.rs`
- `CondSwapChip<pallas::Base>::mux_on_non_identity_points`

This is the non-identity point variant of `PointMux`: it selects one input point and
asserts that the selected output satisfies the Pallas curve equation.
-/

namespace NonIdentityPointMux

abbrev Inputs := PointMux.Inputs

@[circuit_norm]
def Assumptions (input : Inputs Ecc.PallasBaseField) : Prop :=
  PointMux.Assumptions input ∧ Ecc.onCurve input.left ∧ Ecc.onCurve input.right

@[circuit_norm]
def Spec (input : Inputs Ecc.PallasBaseField) (output : Ecc.Point Ecc.PallasBaseField) :
    Prop :=
  PointMux.Spec input output ∧ Ecc.onCurve output

def main (input : Var Inputs Ecc.PallasBaseField) :
    Circuit Ecc.PallasBaseField (Var Ecc.Point Ecc.PallasBaseField) := do
  let output ← PointMux.circuit input
  Ecc.NonIdentityPoint.circuit output
  return output

instance elaborated : ElaboratedCircuit Ecc.PallasBaseField Inputs Ecc.Point main := by
  elaborate_circuit

theorem onCurve_of_spec_and_assumptions
    {input : Inputs Ecc.PallasBaseField} {output : Ecc.Point Ecc.PallasBaseField}
    (hAssumptions : Assumptions input)
    (hSpec : PointMux.Spec input output) :
    Ecc.onCurve output := by
  rcases hAssumptions with ⟨_, hLeft, hRight⟩
  by_cases hChoiceOne : input.choice = 1
  · simp [PointMux.Spec, hChoiceOne] at hSpec
    rw [hSpec]
    exact hRight
  · simp [PointMux.Spec, hChoiceOne] at hSpec
    rw [hSpec]
    exact hLeft

theorem soundness :
    Soundness Ecc.PallasBaseField main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, PointMux.circuit, PointMux.Spec,
    Ecc.NonIdentityPoint.circuit, Ecc.onCurve]
  rcases h_assumptions with ⟨hMuxAssumptions, _, _⟩
  rcases h_holds with ⟨hMux, hOnCurve⟩
  exact ⟨hMux hMuxAssumptions, hOnCurve⟩

theorem completeness :
    Completeness Ecc.PallasBaseField main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, PointMux.circuit, PointMux.Spec,
    Ecc.NonIdentityPoint.circuit, Ecc.onCurve]
  have hAllAssumptions := h_assumptions
  change Assumptions
    ({ choice := input_choice, left := input_left, right := input_right } :
      Inputs Ecc.PallasBaseField) at hAllAssumptions
  rcases h_assumptions with ⟨hMuxAssumptions, _, _⟩
  constructor
  · exact hMuxAssumptions
  · exact (onCurve_of_spec_and_assumptions hAllAssumptions (h_env hMuxAssumptions))

def circuit : FormalCircuit Ecc.PallasBaseField Inputs Ecc.Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end NonIdentityPointMux

/-!
Reference:
`orchard@0.14.0/src/circuit/gadget/add_chip.rs`
- `Field element addition: c = a + b`

This is the small Orchard-specific addition chip used where the Rust circuit wants a
copy-constrained field addition result.
-/

namespace AddChip

def main (input : Var fieldPair Ecc.PallasBaseField) :
    Circuit Ecc.PallasBaseField (Var field Ecc.PallasBaseField) := do
  let (a, b) := input
  let c ← witnessField fun env => env a + env b
  assertZero (a + b - c)
  return c

def Spec (input : fieldPair Ecc.PallasBaseField) (output : Ecc.PallasBaseField) : Prop :=
  output = input.1 + input.2

instance elaborated : ElaboratedCircuit Ecc.PallasBaseField fieldPair field main := by
  elaborate_circuit

theorem soundness : Soundness Ecc.PallasBaseField main (fun _ => True) Spec := by
  circuit_proof_start [main, Spec]
  rcases input with ⟨a, b⟩
  simp only [Prod.mk.injEq] at h_input
  rcases h_input with ⟨ha, hb⟩
  rw [← ha, ← hb]
  exact (eq_of_add_neg_eq_zero h_holds).symm

theorem completeness : Completeness Ecc.PallasBaseField main (fun _ => True) := by
  circuit_proof_start [main, Spec]
  rw [h_env]
  ring

def circuit : FormalCircuit Ecc.PallasBaseField fieldPair field where
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

def InRange (range : ℕ) (word : F) : Prop :=
  word = 0 ∨ ∃ i, i ∈ rangeCheckValues (F := F) range ∧ word = i

def Spec (windowNumBits : ℕ) (step : Step F) : Prop :=
  InRange (2 ^ windowNumBits) (word windowNumBits step)

private theorem rangeCheckFoldl_eq_zero_iff
    (xs : List F) (word acc : F) :
    xs.foldl (fun acc i => acc * (i - word)) acc = 0 ↔
      acc = 0 ∨ ∃ i, i ∈ xs ∧ word = i := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.mem_cons]
      rw [ih (acc * (i - word))]
      constructor
      · intro h
        rcases h with hprod | hmem
        · rcases mul_eq_zero.mp hprod with hacc | hi
          · exact Or.inl hacc
          · exact Or.inr ⟨i, Or.inl rfl, (sub_eq_zero.mp hi).symm⟩
        · rcases hmem with ⟨j, hj, hword⟩
          exact Or.inr ⟨j, Or.inr hj, hword⟩
      · intro h
        rcases h with hacc | hmem
        · exact Or.inl (by rw [hacc]; simp)
        · rcases hmem with ⟨j, hj, hword⟩
          rcases hj with hj | hj
          · subst j
            exact Or.inl (by rw [hj]; ring)
          · exact Or.inr ⟨j, hj, hword⟩

theorem rangeCheckPoly_eq_zero_iff (range : ℕ) (word : F) :
    rangeCheckPoly range word = 0 ↔ InRange range word := by
  unfold rangeCheckPoly InRange
  exact rangeCheckFoldl_eq_zero_iff (rangeCheckValues range) word word

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
    circuit_proof_start [main, Spec, word, rangeCheckPoly, rangeCheckPolyExpr, twoPowWindow,
      InRange]
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
    exact (rangeCheckPoly_eq_zero_iff (2 ^ windowNumBits)
      (input_zCur - twoPowWindow windowNumBits * input_zNext)).mp h_holds
  completeness := by
    circuit_proof_start [main, Spec, word, rangeCheckPoly, rangeCheckPolyExpr, twoPowWindow,
      InRange]
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
    exact (rangeCheckPoly_eq_zero_iff (2 ^ windowNumBits)
      (input_zCur - twoPowWindow windowNumBits * input_zNext)).mpr h_spec

end RunningSum

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/lookup_range_check.rs`
- `Short lookup bitshift`

This custom gate is shared by both lookup range-check configurations. It checks the
assignment used by short range checks:
`shifted_word = word * 2^K * inv_two_pow_s`.
-/

namespace LookupRangeCheck

structure ShortLookupBitshift (F : Type) where
  word : F
  shiftedWord : F
  invTwoPowS : F
deriving ProvableStruct

structure ShortRangeCheck (F : Type) where
  word : F
deriving ProvableStruct

def twoPowK (k : ℕ) : F :=
  (2 ^ k : ℕ)

def poly (k : ℕ) (input : ShortLookupBitshift F) : F :=
  input.word * twoPowK k * input.invTwoPowS - input.shiftedWord

def bitshiftSpec (k : ℕ) (input : ShortLookupBitshift F) : Prop :=
  input.shiftedWord = input.word * twoPowK k * input.invTwoPowS

def main (k : ℕ) (input : Var ShortLookupBitshift F) : Circuit F Unit := do
  assertZero (input.word * (twoPowK k : F) * input.invTwoPowS - input.shiftedWord)

def circuit (k : ℕ) : FormalAssertion F ShortLookupBitshift where
  main := main k
  Spec := bitshiftSpec k
  soundness := by
    circuit_proof_start [main, bitshiftSpec, poly, twoPowK]
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h_holds)).symm
  completeness := by
    circuit_proof_start [main, bitshiftSpec, poly, twoPowK]
    rw [h_spec]
    ring

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/lookup_range_check.rs`
- `LookupRangeCheck4_5BConfig::short_range_check`
- combined lookup tagged with 4- and 5-bit table rows

The Halo2 source enforces the short 4- and 5-bit cases with a tagged lookup table. This
Clean approximation models the same range membership as a polynomial over the allowed
values.
-/

def shortRangeSpec (numBits : ℕ) (input : ShortRangeCheck F) : Prop :=
  RunningSum.InRange (2 ^ numBits) input.word

def shortRangeMain (numBits : ℕ) (input : Var ShortRangeCheck F) : Circuit F Unit := do
  assertZero (RunningSum.rangeCheckPolyExpr (2 ^ numBits) input.word)

def shortRangeCircuit (numBits : ℕ) : FormalAssertion F ShortRangeCheck where
  main := shortRangeMain numBits
  Spec := shortRangeSpec numBits
  soundness := by
    circuit_proof_start [shortRangeMain, shortRangeSpec, RunningSum.rangeCheckPoly,
      RunningSum.rangeCheckPolyExpr, RunningSum.InRange]
    change Expression.eval env
        (RunningSum.rangeCheckPolyExpr (2 ^ numBits) input_var_word) = 0 at h_holds
    rw [RunningSum.eval_rangeCheckPolyExpr] at h_holds
    rw [h_input] at h_holds
    exact (RunningSum.rangeCheckPoly_eq_zero_iff (2 ^ numBits) input_word).mp h_holds
  completeness := by
    circuit_proof_start [shortRangeMain, shortRangeSpec, RunningSum.rangeCheckPoly,
      RunningSum.rangeCheckPolyExpr, RunningSum.InRange]
    change Expression.eval env.toEnvironment
        (RunningSum.rangeCheckPolyExpr (2 ^ numBits) input_var_word) = 0
    rw [RunningSum.eval_rangeCheckPolyExpr]
    rw [h_input]
    exact (RunningSum.rangeCheckPoly_eq_zero_iff (2 ^ numBits) input_word).mpr h_spec

end LookupRangeCheck

end Utilities
end Orchard
