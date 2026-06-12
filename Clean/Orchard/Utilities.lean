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

namespace Gate

structure Input (F : Type) where
  a : F
  b : F
  aSwapped : F
  bSwapped : F
  swap : F
deriving ProvableStruct

def Spec (input : Input Fp) : Prop :=
  input.aSwapped = ternary input.swap input.b input.a ∧
    input.bSwapped = ternary input.swap input.a input.b ∧
    IsBool input.swap

def main (input : Var Input Fp) : Circuit Fp Unit := do
  assertZero (input.aSwapped - (input.swap * input.b + (1 - input.swap) * input.a))
  assertZero (input.bSwapped - (input.swap * input.a + (1 - input.swap) * input.b))
  assertZero (input.swap * (input.swap - 1))

def circuit : FormalAssertion Fp Input where
  name := "GATE a' = b ⋅ swap + a ⋅ (1-swap)"
  main
  Spec
  soundness := by
    circuit_proof_start [main, Spec, ternary]
    rcases h_holds with ⟨hA, hB, hBool⟩
    refine ⟨?_, ?_, ?_⟩
    · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hA)
    · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hB)
    · exact IsBool.iff_mul_sub_one.mpr (by simpa [sub_eq_add_neg] using hBool)
  completeness := by
    circuit_proof_start [main, Spec, ternary]
    rcases h_spec with ⟨hA, hB, hSwap⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hA]
      ring
    · rw [hB]
      ring
    · simpa [sub_eq_add_neg] using IsBool.iff_mul_sub_one.mp hSwap

end Gate

def outputValue (input : CondSwapInputs Fp) :
    CondSwapOutput Fp where
  aSwapped := ternary input.swap input.b input.a
  bSwapped := ternary input.swap input.a input.b

def main (input : Var CondSwapInputs Fp) :
    Circuit Fp (Var CondSwapOutput Fp) := do
  let aSwapped ← witnessField fun env => ternary (env input.swap) (env input.b) (env input.a)
  let bSwapped ← witnessField fun env => ternary (env input.swap) (env input.a) (env input.b)
  Gate.circuit { a := input.a, b := input.b, aSwapped, bSwapped, swap := input.swap }
  return { aSwapped, bSwapped }

def Assumptions (input : CondSwapInputs Fp) : Prop :=
  IsBool input.swap

def Spec (input : CondSwapInputs Fp)
    (output : CondSwapOutput Fp) : Prop :=
  output = if input.swap = 1 then
    { aSwapped := input.b, bSwapped := input.a }
  else
    { aSwapped := input.a, bSwapped := input.b }

instance elaborated :
    ElaboratedCircuit Fp CondSwapInputs CondSwapOutput main := by
  elaborate_circuit

theorem outputValue_eq_of_bool {input : CondSwapInputs Fp}
    (hbool : IsBool input.swap) :
    outputValue input = if input.swap = 1 then
      { aSwapped := input.b, bSwapped := input.a }
    else
      { aSwapped := input.a, bSwapped := input.b } := by
  rcases hbool with hzero | hone
  · simp [outputValue, ternary, hzero]
  · simp [outputValue, ternary, hone]

theorem soundness :
    Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, outputValue, ternary]
  rcases h_holds trivial with ⟨hA, hB, hbool⟩
  simp only at hA hB hbool
  rcases hbool with hzero | hone
  · constructor
    · rw [hA, hB]
      simp [hzero, ternary]
    · exact Or.inr trivial
  · constructor
    · rw [hA, hB]
      simp [hone, ternary]
    · exact Or.inr trivial

theorem completeness :
    Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, outputValue, ternary]
  constructor
  · trivial
  · exact ⟨h_env.1, h_env.2, h_assumptions⟩

def circuit : FormalCircuit Fp CondSwapInputs CondSwapOutput where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/cond_swap.rs`
- `CondSwapInstructions::swap`

This is the CondSwap entry API actually used by Orchard's Merkle path calculation. The
existing `a` cell is copied into the gate row, while `b` and the boolean `swap` flag are
prover-side `Value`s witnessed inside this region.
-/

namespace Swap

structure Input (F : Type) where
  a : F
  b : UnconstrainedDep field F
  swap : Unconstrained Bool F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ a := default, b := fun _ => default, swap := fun _ => default }⟩

def outputValue (input : Input.ProverValue Fp) :
    CondSwapOutput Fp where
  aSwapped := if input.swap then input.b else input.a
  bSwapped := if input.swap then input.a else input.b

def main (input : Input.Var Fp) :
    Circuit Fp (Var CondSwapOutput Fp) := do
  let a <== input.a
  let b ← witness input.b
  let swap ← witness fun env => if input.swap env then 1 else 0
  let aSwapped ← witness fun env => if input.swap env then env b else env a
  let bSwapped ← witness fun env => if input.swap env then env a else env b
  Gate.circuit { a, b, aSwapped, bSwapped, swap }
  return { aSwapped, bSwapped }

def Spec (input : Input.Value Fp) (output : CondSwapOutput Fp)
    (_ : ProverData Fp) : Prop :=
  ∃ (b swap : Fp), IsBool swap ∧
    output = if swap = 1 then
      { aSwapped := b, bSwapped := input.a }
    else
      { aSwapped := input.a, bSwapped := b }

def ProverSpec (input : Input.ProverValue Fp)
    (output : CondSwapOutput Fp) (_ : ProverHint Fp) : Prop :=
  output = outputValue input

instance elaborated : ElaboratedCircuit Fp Input CondSwapOutput main := by
  elaborate_circuit

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (Input:=Input) (Output:=CondSwapOutput)
      Fp main (fun _ _ => True) Spec := by
  circuit_proof_start [main, Spec, ternary]
  rcases h_holds with ⟨hCopy, hGate⟩
  rcases hGate trivial with ⟨hA, hB, hSwap⟩
  constructor
  · refine ⟨env.get (i₀ + 1), env.get (i₀ + 1 + 1), hSwap, ?_⟩
    simp only at hA hB hSwap
    rcases hSwap with hzero | hone
    · rw [hA, hB, hCopy]
      simp [hzero, ternary]
    · rw [hA, hB, hCopy]
      simp [hone, ternary]
  · exact Or.inr trivial

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (Input:=Input) (Output:=CondSwapOutput)
      Fp main (fun _ _ _ => True) ProverSpec := by
  circuit_proof_start [main, ProverSpec, outputValue, Gate.circuit, Gate.Spec, ternary]
  obtain ⟨hCopy, hB, hSwap, hASwapped, hBSwapped⟩ := h_env
  constructor
  · refine ⟨hCopy, ?_, ?_, ?_⟩
    · by_cases h : input_swap
      · rw [hASwapped, hSwap, hB, hCopy]
        simp [h]
      · rw [hASwapped, hSwap, hB, hCopy]
        simp [h]
    · by_cases h : input_swap
      · rw [hBSwapped, hSwap, hB, hCopy]
        simp [h]
      · rw [hBSwapped, hSwap, hB, hCopy]
        simp [h]
    · by_cases h : input_swap
      · rw [hSwap]
        exact Or.inr (by simp [h])
      · rw [hSwap]
        exact Or.inl (by simp [h])
  · rw [hASwapped, hBSwapped, hB, hCopy]

def circuit : GeneralFormalCircuit.WithHint Fp Input CondSwapOutput where
  main
  elaborated
  Spec
  ProverSpec
  soundness
  completeness

end Swap

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
def Assumptions (input : Inputs Fp) : Prop :=
  IsBool input.choice

@[circuit_norm]
def Spec (input : Inputs Fp) (output : Ecc.Point Fp) :
    Prop :=
  output = if input.choice = 1 then input.right else input.left

def main (input : Var Inputs Fp) :
    Circuit Fp (Var Ecc.Point Fp) := do
  let xOut ← CondSwap.circuit (xInput input)
  let yOut ← CondSwap.circuit (yInput input)
  return { x := xOut.aSwapped, y := yOut.aSwapped }

instance elaborated : ElaboratedCircuit Fp Inputs Ecc.Point main := by
  elaborate_circuit

theorem soundness :
    Soundness Fp main Assumptions Spec := by
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
    Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, xInput, yInput,
    CondSwap.circuit, CondSwap.Spec, CondSwap.Assumptions]
  rcases h_assumptions with hChoiceZero | hChoiceOne
  · exact Or.inl hChoiceZero
  · exact Or.inr hChoiceOne

def circuit : FormalCircuit Fp Inputs Ecc.Point where
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

open CompElliptic.Curves.Pasta in
@[circuit_norm]
def Assumptions (input : Inputs Fp) : Prop :=
  PointMux.Assumptions input ∧ Pallas.OnCurve input.left.coords ∧
    Pallas.OnCurve input.right.coords

open CompElliptic.Curves.Pasta in
@[circuit_norm]
def Spec (input : Inputs Fp) (output : Ecc.Point Fp) :
    Prop :=
  PointMux.Spec input output ∧ Pallas.OnCurve output.coords

def main (input : Var Inputs Fp) :
    Circuit Fp (Var Ecc.Point Fp) := do
  let output ← PointMux.circuit input
  return output

instance elaborated : ElaboratedCircuit Fp Inputs Ecc.Point main := by
  elaborate_circuit

open CompElliptic.Curves.Pasta in
theorem onCurve_of_spec_and_assumptions
    {input : Inputs Fp} {output : Ecc.Point Fp}
    (hAssumptions : Assumptions input)
    (hSpec : PointMux.Spec input output) :
    Pallas.OnCurve output.coords := by
  rcases hAssumptions with ⟨_, hLeft, hRight⟩
  by_cases hChoiceOne : input.choice = 1
  · simp [PointMux.Spec, hChoiceOne] at hSpec
    rw [hSpec]
    exact hRight
  · simp [PointMux.Spec, hChoiceOne] at hSpec
    rw [hSpec]
    exact hLeft

theorem soundness :
    Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, PointMux.circuit, PointMux.Spec,
    onCurve_of_spec_and_assumptions]
  rcases h_assumptions with ⟨hMuxAssumptions, hLeft, hRight⟩
  have hMux := h_holds hMuxAssumptions
  constructor
  · exact hMux
  · by_cases hChoiceOne : input_choice = 1
    · simp [hChoiceOne] at hMux
      rw [hMux]
      exact hRight
    · simp [hChoiceOne] at hMux
      rw [hMux]
      exact hLeft

theorem completeness :
    Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, PointMux.circuit, PointMux.Spec]
  exact h_assumptions.1

def circuit : FormalCircuit Fp Inputs Ecc.Point where
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

namespace Gate

def main (input : Var fieldTriple Fp) : Circuit Fp Unit := do
  assertZero (input.1 + input.2.1 - input.2.2)

def Spec (input : fieldTriple Fp) : Prop :=
  input.2.2 = input.1 + input.2.1

def circuit : FormalAssertion Fp fieldTriple where
  name := "GATE Field element addition: c = a + b"
  main
  Spec
  soundness := by
    circuit_proof_start
    rcases input with ⟨a, b, c⟩
    simp only [Prod.mk.injEq] at h_input
    rcases h_input with ⟨ha, hb, hc⟩
    rw [← ha, ← hb, ← hc]
    exact (eq_of_add_neg_eq_zero h_holds).symm
  completeness := by
    circuit_proof_start
    rw [← h_input] at h_spec
    simpa [sub_eq_add_neg] using sub_eq_zero.mpr h_spec.symm

end Gate

def main (input : Var fieldPair Fp) :
    Circuit Fp (Var field Fp) := do
  let (a, b) := input
  let c ← witnessField fun env => env a + env b
  Gate.circuit (a, b, c)
  return c

def Spec (input : fieldPair Fp) (output : Fp) : Prop :=
  output = input.1 + input.2

instance elaborated : ElaboratedCircuit Fp fieldPair field main := by
  elaborate_circuit

theorem soundness : Soundness Fp main (fun _ => True) Spec := by
  circuit_proof_start
  constructor
  · rw [← h_input]
    exact h_holds trivial
  · exact Or.inr trivial

theorem completeness : Completeness Fp main (fun _ => True) := by
  circuit_proof_start
  exact ⟨trivial, by simpa [Gate.Spec] using h_env⟩

def circuit : FormalCircuit Fp fieldPair field where
  main
  elaborated
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
  name := "GATE range check"
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
  name := "GATE Short lookup bitshift"
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

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/lookup_range_check.rs`
- `PallasLookupRangeCheck::copy_check` / `range_check` (with `strict = false`)

`copy_check` copies an element into a fresh running-sum cell `z_0` and decomposes it
into `K`-bit words via the running sum `z_{i+1} = (z_i - a_i) / 2^K`. Each word
`a_i = z_i - 2^K * z_{i+1}` is constrained by a lookup into the 10-bit `table_idx`
table. With `strict = false`, the final `z_{numWords}` is not constrained to zero; for
an honest prover it carries the high bits `element >> (K * numWords)`.
-/

/-- Number of bits constrained per lookup word (`sinsemilla::K`). -/
def K : ℕ := 10

/-- The 10-bit range table `table_idx`. In Orchard it is preloaded by the Sinsemilla
chip; here it is the static table of the field elements `0, …, 2^K - 1`. -/
def tableIdx : Table Fp field := .fromStatic {
  name := "table_idx"
  length := 2 ^ K
  row i := (i.val : Fp)
  index := fun (x : Fp) => x.val
  Spec := fun (x : Fp) => x.val < 2 ^ K
  contains_iff := by
    intro (x : Fp)
    constructor
    · rintro ⟨i, rfl⟩
      show ((i.val : Fp)).val < 2 ^ K
      rw [ZMod.val_natCast_of_lt (lt_trans i.is_lt (by norm_num [K]))]
      exact i.is_lt
    · intro h
      exact ⟨⟨x.val, h⟩, (ZMod.natCast_zmod_val x).symm⟩
}

namespace CopyCheck

def main (numWords : ℕ) (element : Expression Fp) :
    Circuit Fp (Var (fields (numWords + 1)) Fp) := do
  -- copy `element` into the running-sum column as `z_0`
  let z₀ <== element
  -- z_{i+1} = (z_i - a_i) / 2^K; for the honest prover, z_i = element >> (K * i)
  let zRest ← witnessVector numWords fun env =>
    .ofFn fun (i : Fin numWords) =>
      (((env element).val / 2 ^ (K * (i.val + 1)) : ℕ) : Fp)
  let zs := Vector.cast (Nat.add_comm 1 numWords) (#v[z₀] ++ zRest)
  let words : Vector (Expression Fp) numWords := .ofFn fun i =>
    zs[i.val]'(Nat.lt_succ_of_lt i.isLt) -
      (2 ^ K : Fp) * zs[i.val + 1]'(Nat.succ_lt_succ i.isLt)
  Circuit.forEach words (lookup tableIdx)
  return zs

/-- The output cells form a `K`-bit running-sum decomposition of `element`:
`z_0 = element` and each step satisfies `z_i = 2^K * z_{i+1} + a_i` for a `K`-bit
word `a_i`. -/
def Spec (numWords : ℕ) (element : Fp) (zs : fields (numWords + 1) Fp)
    (_ : ProverData Fp) : Prop :=
  zs[0]'(Nat.succ_pos numWords) = element ∧
    ∀ i : Fin numWords, ∃ word : ℕ, word < 2 ^ K ∧
      zs[i.val]'(Nat.lt_succ_of_lt i.isLt) =
        2 ^ K * zs[i.val + 1]'(Nat.succ_lt_succ i.isLt) + (word : Fp)

/-- The honest prover assigns the canonical decomposition: `z_i = element >> (K * i)`. -/
def ProverSpec (numWords : ℕ) (element : Fp) (zs : fields (numWords + 1) Fp)
    (_ : ProverHint Fp) : Prop :=
  ∀ i : Fin (numWords + 1),
    zs[i.val] = ((element.val / 2 ^ (K * i.val) : ℕ) : Fp)

instance elaborated (numWords : ℕ) :
    ElaboratedCircuit Fp field (fields (numWords + 1)) (main numWords) := by
  elaborate_circuit

theorem soundness (numWords : ℕ) :
    GeneralFormalCircuit.WithHint.Soundness (Input:=field)
      (Output:=fields (numWords + 1)) Fp (main numWords)
      (fun _ _ => True) (Spec numWords) := by
  circuit_proof_start [main, Spec, tableIdx]
  obtain ⟨h_copy, h_lookup⟩ := h_holds
  constructor
  · simpa [circuit_norm] using h_copy
  · intro i
    have h := h_lookup i
    simp only [Vector.getElem_ofFn] at h
    refine ⟨_, h, ?_⟩
    rw [ZMod.natCast_zmod_val]
    simp only [circuit_norm]
    ring

/-- The honest word `z_i - 2^K * z_{i+1}` with `z_i = a, z_{i+1} = a / 2^K` is the low
`K`-bit chunk of `a`, hence in range. -/
private theorem word_val_lt (a : ℕ) :
    ZMod.val ((a : Fp) - 2 ^ K * ((a / 2 ^ K : ℕ) : Fp)) < 2 ^ K := by
  have h2K : (2 ^ K : ℕ) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  have hsub : (a : Fp) - 2 ^ K * ((a / 2 ^ K : ℕ) : Fp)
      = ((a % 2 ^ K : ℕ) : Fp) := by
    have h := congrArg (Nat.cast (R := Fp)) (Nat.mod_add_div a (2 ^ K))
    push_cast at h
    linear_combination -h
  rw [hsub, ZMod.val_natCast_of_lt (lt_trans (Nat.mod_lt _ (by norm_num [K])) h2K)]
  exact Nat.mod_lt _ (by norm_num [K])

theorem completeness (numWords : ℕ) :
    GeneralFormalCircuit.WithHint.Completeness (Input:=field)
      (Output:=fields (numWords + 1)) Fp (main numWords)
      (fun _ _ _ => True) (ProverSpec numWords) := by
  circuit_proof_start [main, ProverSpec, tableIdx]
  obtain ⟨h_z0, h_zs⟩ := h_env
  set x : Fp := input with hx
  have h_zval : ∀ (j : ℕ) (hj : j < numWords),
      env.get (i₀ + 1 + j) = ((x.val / 2 ^ (K * (j + 1)) : ℕ) : Fp) := by
    intro j hj
    have h := h_zs ⟨j, hj⟩
    simpa using h
  constructor
  · refine ⟨h_z0, fun i => ?_⟩
    simp only [Vector.getElem_ofFn]
    rcases i with ⟨_ | j, hi⟩
    · have h1 := h_zval 0 hi
      norm_num at h1
      simp only [Vector.getElem_append, Vector.getElem_mapRange]
      norm_num
      simp only [Expression.eval]
      rw [h_z0, h1]
      have h := word_val_lt x.val
      rw [ZMod.natCast_zmod_val] at h
      simpa [sub_eq_add_neg] using h
    · have h1 := h_zval j (by omega)
      have h2 := h_zval (j + 1) hi
      simp only [Vector.getElem_append, Vector.getElem_mapRange]
      norm_num
      simp only [Expression.eval]
      rw [h1, h2]
      have h := word_val_lt (x.val / 2 ^ (K * (j + 1)))
      rw [Nat.div_div_eq_div_mul, ← pow_add,
        show K * (j + 1) + K = K * (j + 1 + 1) by ring] at h
      simpa [sub_eq_add_neg] using h
  · intro i
    rcases i with ⟨_ | j, hi⟩
    · simp only [Vector.getElem_append, Vector.getElem_mapRange]
      norm_num
      simp only [Expression.eval]
      rw [h_z0]
    · have h1 := h_zval j (by omega)
      simp only [Vector.getElem_append, Vector.getElem_mapRange]
      norm_num
      simp only [Expression.eval]
      exact h1

def circuit (numWords : ℕ) :
    GeneralFormalCircuit.WithHint Fp field (fields (numWords + 1)) where
  main := main numWords
  Spec := Spec numWords
  ProverSpec := ProverSpec numWords
  soundness := soundness numWords
  completeness := completeness numWords

end CopyCheck

end LookupRangeCheck

end Utilities
end Orchard
