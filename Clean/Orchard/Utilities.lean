import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Gadgets.Equality
import Clean.Orchard.Ecc
import Clean.Orchard.Specs.Bitrange
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

open Orchard.Specs (K)

variable {F : Type} [FiniteField F]

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
  let aSwapped ← witness (.ite (input.swap =? 1) input.b input.a)
  let bSwapped ← witness (.ite (input.swap =? 1) input.a input.b)
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
  circuit_proof_start [main, Assumptions, outputValue, ternary, Gate.circuit, Gate.Spec, IsBool]
  obtain ⟨hA, hB⟩ := h_env
  rcases h_assumptions with hzero | hone <;> simp_all

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
  b : Unconstrained field F
  swap : UnconstrainedBool F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ a := default, b := unconstrained (do return default),
     swap := unconstrainedBool (do return .false) }⟩

def outputValue (input : Input.ProverValue Fp) :
    CondSwapOutput Fp where
  aSwapped := if input.swap then input.b else input.a
  bSwapped := if input.swap then input.a else input.b

def main (input : Input.Var Fp) :
    Circuit Fp (Var CondSwapOutput Fp) := do
  let a <== input.a
  let b ← witnessProgram input.b
  let swap ← witnessProgram (do return (← input.swap).toField)
  let aSwapped ← witnessProgram (do return .ite (← input.swap) b (Witgen.FExpr.expr a))
  let bSwapped ← witnessProgram (do return .ite (← input.swap) (Witgen.FExpr.expr a) b)
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
  left : Point F
  right : Point F
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
def Spec (input : Inputs Fp) (output : Point Fp) : Prop :=
  output = if input.choice = 1 then input.right else input.left

def main (input : Var Inputs Fp) :
    Circuit Fp (Var Point Fp) := do
  let xOut ← CondSwap.circuit (xInput input)
  let yOut ← CondSwap.circuit (yInput input)
  return { x := xOut.aSwapped, y := yOut.aSwapped }

instance elaborated : ElaboratedCircuit Fp Inputs Point main := by
  elaborate_circuit

theorem soundness :
    Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, xInput, yInput,
    CondSwap.circuit, CondSwap.Spec]
  rcases h_holds with ⟨hX, hY⟩
  have hXMux := hX h_assumptions
  have hYMux := hY h_assumptions
  have hLeftX : Expression.eval env input_var_left.x = input_left.x := by
    have h := congrArg Point.x h_input.2.1
    simpa [circuit_norm] using h
  have hLeftY : Expression.eval env input_var_left.y = input_left.y := by
    have h := congrArg Point.y h_input.2.1
    simpa [circuit_norm] using h
  have hRightX : Expression.eval env input_var_right.x = input_right.x := by
    have h := congrArg Point.x h_input.2.2
    simpa [circuit_norm] using h
  have hRightY : Expression.eval env input_var_right.y = input_right.y := by
    have h := congrArg Point.y h_input.2.2
    simpa [circuit_norm] using h
  by_cases hChoiceOne : input_choice = 1
  · simp [hChoiceOne, hLeftX, hLeftY, hRightX, hRightY] at hXMux hYMux ⊢
    rw [Point.mk.injEq]
    exact ⟨hXMux.1, hYMux.1⟩
  · simp [hChoiceOne, hLeftX, hLeftY, hRightX, hRightY] at hXMux hYMux ⊢
    rw [Point.mk.injEq]
    exact ⟨hXMux.1, hYMux.1⟩

theorem completeness :
    Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, xInput, yInput,
    CondSwap.circuit, CondSwap.Spec, CondSwap.Assumptions]
  rcases h_assumptions with hChoiceZero | hChoiceOne
  · exact Or.inl hChoiceZero
  · exact Or.inr hChoiceOne

def circuit : FormalCircuit Fp Inputs Point where
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

def circuit : FormalCircuit Fp PointMux.Inputs Point where
  main input := PointMux.circuit input
  Assumptions input :=
    IsBool input.choice ∧
    input.left.OnCurve ∧ input.right.OnCurve
  Spec input output :=
    (output = if input.choice = 1 then input.right else input.left) ∧
    output.OnCurve
  soundness := by circuit_proof_all [PointMux.circuit, IsBool]
  completeness := by circuit_proof_all [PointMux.circuit]

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
    exact (sub_eq_zero.mp h_holds).symm
  completeness := by
    circuit_proof_start
    rw [← h_input] at h_spec
    exact sub_eq_zero.mpr h_spec.symm

end Gate

def main (input : Var fieldPair Fp) :
    Circuit Fp (Var field Fp) := do
  let (a, b) := input
  let c ← witness (a + b)
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

def Spec (windowNumBits : ℕ) (step : Step Fp) : Prop :=
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

def main (windowNumBits : ℕ) (step : Var Step Fp) : Circuit Fp Unit := do
  let word := step.zCur - (twoPowWindow windowNumBits : Fp) * step.zNext
  assertZero (rangeCheckPolyExpr (2 ^ windowNumBits) word)

def circuit (windowNumBits : ℕ) : FormalAssertion Fp Step where
  name := "GATE range check"
  main := main windowNumBits
  Spec := Spec windowNumBits
  soundness := by
    circuit_proof_start [main, Spec, word, rangeCheckPoly, rangeCheckPolyExpr, twoPowWindow,
      InRange]
    change Expression.eval env
        (rangeCheckPolyExpr (2 ^ windowNumBits)
          (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)) = 0 at h_holds
    have h_eval :
        Expression.eval env
          (rangeCheckPolyExpr (2 ^ windowNumBits)
            (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)) =
          rangeCheckPoly (2 ^ windowNumBits)
            (Expression.eval env
              (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)) := by
      exact eval_rangeCheckPolyExpr env (2 ^ windowNumBits)
        (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)
    rw [h_eval] at h_holds
    rcases h_input with ⟨hzCur, hzNext⟩
    have hword :
        Expression.eval env
            (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext) =
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
          (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)) = 0
    have h_eval :
        Expression.eval env.toEnvironment
          (rangeCheckPolyExpr (2 ^ windowNumBits)
            (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)) =
          rangeCheckPoly (2 ^ windowNumBits)
            (Expression.eval env.toEnvironment
              (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)) := by
      exact eval_rangeCheckPolyExpr env.toEnvironment (2 ^ windowNumBits)
        (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext)
    rw [h_eval]
    rcases h_input with ⟨hzCur, hzNext⟩
    have hword :
        Expression.eval env.toEnvironment
            (input_var_zCur - (twoPowWindow windowNumBits : Fp) * input_var_zNext) =
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

def bitshiftSpec (k : ℕ) (input : ShortLookupBitshift Fp) : Prop :=
  input.shiftedWord = input.word * twoPowK k * input.invTwoPowS

def main (k : ℕ) (input : Var ShortLookupBitshift Fp) : Circuit Fp Unit := do
  assertZero (input.word * (twoPowK k : Fp) * input.invTwoPowS - input.shiftedWord)

def circuit (k : ℕ) : FormalAssertion Fp ShortLookupBitshift where
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
- `PallasLookupRangeCheck::copy_check` / `range_check` (with `strict = false`)

`copy_check` copies an element into a fresh running-sum cell `z_0` and decomposes it
into `K`-bit words via the running sum `z_{i+1} = (z_i - a_i) / 2^K`. Each word
`a_i = z_i - 2^K * z_{i+1}` is constrained by a lookup into the 10-bit `table_idx`
table. With `strict = false`, the final `z_{numWords}` is not constrained to zero; for
an honest prover it carries the high bits `element >> (K * numWords)`.
-/

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

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/lookup_range_check.rs`
- `LookupRangeCheckConfig::short_range_check`

The generic short range-check path uses two lookups into `table_idx`: one for the
word itself and one for `word * 2^(K - num_bits)`, plus the `Short lookup bitshift`
gate tying the assigned shifted word to the original word.
-/

def shortRangeSpec (numBits : ℕ) (input : ShortRangeCheck Fp) : Prop :=
  input.word.val < 2 ^ numBits

private theorem pow_two_pos (n : ℕ) : 0 < 2 ^ n := by
  exact pow_pos (by norm_num : (0 : ℕ) < 2) n

private theorem shortRange_soundness_aux (numBits : ℕ) (hNumBits : numBits ≤ K)
    (word shifted : Fp)
    (hWord : word.val < 2 ^ K)
    (hShifted : shifted.val < 2 ^ K)
    (hEq : shifted = word * (2 ^ (K - numBits) : Fp)) :
    word.val < 2 ^ numBits := by
  have hCard : 2 ^ K * 2 ^ K < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  have hProdLtCard : word.val * 2 ^ (K - numBits) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    calc
      word.val * 2 ^ (K - numBits) < 2 ^ K * 2 ^ K := by
        exact Nat.mul_lt_mul_of_lt_of_le hWord
          (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le K numBits))
          (pow_two_pos _)
      _ < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := hCard
  have hShiftedVal :
      shifted.val = word.val * 2 ^ (K - numBits) := by
    rw [hEq, ← ZMod.natCast_zmod_val word]
    have hPowCast : (2 ^ (K - numBits) : Fp) = ((2 ^ (K - numBits) : ℕ) : Fp) := by
      norm_num
    rw [hPowCast, ← Nat.cast_mul]
    rw [ZMod.val_natCast_of_lt word.val_lt]
    exact ZMod.val_natCast_of_lt hProdLtCard
  by_contra h
  have hge : 2 ^ numBits ≤ word.val := Nat.le_of_not_gt h
  have hle : 2 ^ K ≤ word.val * 2 ^ (K - numBits) := by
    calc
      2 ^ K = 2 ^ numBits * 2 ^ (K - numBits) := by
        rw [Nat.mul_comm, ← pow_add]
        congr 1
        omega
      _ ≤ word.val * 2 ^ (K - numBits) := by
        exact Nat.mul_le_mul_right _ hge
  rw [hShiftedVal] at hShifted
  exact Nat.not_lt_of_ge hle hShifted

private theorem shortRange_completeness_shifted (numBits : ℕ) (hNumBits : numBits ≤ K)
    (word : Fp) (hWord : word.val < 2 ^ numBits) :
    (word * (2 ^ (K - numBits) : Fp)).val < 2 ^ K := by
  have hProdLt : word.val * 2 ^ (K - numBits) < 2 ^ K := by
    calc
      word.val * 2 ^ (K - numBits) < 2 ^ numBits * 2 ^ (K - numBits) := by
        exact Nat.mul_lt_mul_of_pos_right hWord (pow_two_pos _)
      _ = 2 ^ K := by
        rw [Nat.mul_comm, ← pow_add]
        congr 1
        omega
  have hProdLtCard :
      word.val * 2 ^ (K - numBits) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    exact lt_trans hProdLt (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  rw [← ZMod.natCast_zmod_val word]
  have hPowCast : (2 ^ (K - numBits) : Fp) = ((2 ^ (K - numBits) : ℕ) : Fp) := by
    norm_num
  rw [hPowCast, ← Nat.cast_mul]
  rw [ZMod.val_natCast_of_lt hProdLtCard]
  exact hProdLt

def shortRangeMain (numBits : ℕ) (_hNumBits : numBits ≤ K)
    (input : Var ShortRangeCheck Fp) : Circuit Fp Unit := do
  lookup tableIdx input.word
  let shiftedWord ← witness (input.word * (2 ^ (K - numBits) : Fp))
  lookup tableIdx shiftedWord
  circuit K {
    word := input.word
    shiftedWord
    invTwoPowS := Expression.const ((2 ^ numBits : Fp)⁻¹)
  }

def shortRangeCircuit (numBits : ℕ) (hNumBits : numBits ≤ K) :
    FormalAssertion Fp ShortRangeCheck where
  main := shortRangeMain numBits hNumBits
  Spec := shortRangeSpec numBits
  soundness := by
    circuit_proof_start [shortRangeMain, shortRangeSpec, tableIdx, bitshiftSpec, twoPowK]
    obtain ⟨hLookupWord, hRest⟩ := h_holds
    obtain ⟨hLookupShifted, hBitshift⟩ := hRest
    have hBitshift := hBitshift trivial
    simp only [circuit_norm] at hLookupWord hLookupShifted hBitshift h_input
    constructor
    · exact shortRange_soundness_aux numBits hNumBits input_word (env.get i₀)
        hLookupWord hLookupShifted (by
          change env.get i₀ = input_word * (2 ^ K : Fp) * ((2 ^ numBits : Fp)⁻¹) at hBitshift
          rw [hBitshift]
          have hPowLtCard : 2 ^ numBits < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
            exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hNumBits)
              (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
          have hPowNe : (2 ^ numBits : Fp) ≠ 0 := by
            intro hzero
            have hzero' : ((2 ^ numBits : ℕ) : Fp) = 0 := by
              simpa using hzero
            have hdiv := (ZMod.natCast_eq_zero_iff (2 ^ numBits)
              CompElliptic.Fields.Pasta.PALLAS_BASE_CARD).mp hzero'
            exact (Nat.not_dvd_of_pos_of_lt (pow_two_pos _) hPowLtCard) hdiv
          have hPowSplitFp :
              (2 ^ K : Fp) = (2 ^ (K - numBits) : Fp) * (2 ^ numBits : Fp) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hPowSplitFp]
          field_simp [hPowNe])
    · exact Or.inr trivial
  completeness := by
    circuit_proof_start [shortRangeMain, shortRangeSpec, tableIdx, bitshiftSpec, twoPowK]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le h_spec (Nat.pow_le_pow_right (by norm_num) hNumBits)
    · rw [h_env]
      exact shortRange_completeness_shifted numBits hNumBits input_word h_spec
    · trivial
    · change env.get i₀ = input_word * (2 ^ K : Fp) * ((2 ^ numBits : Fp)⁻¹)
      rw [h_env]
      have hPowLtCard : 2 ^ numBits < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
        exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hNumBits)
          (by norm_num [K, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      have hPowNe : (2 ^ numBits : Fp) ≠ 0 := by
        intro hzero
        have hzero' : ((2 ^ numBits : ℕ) : Fp) = 0 := by
          simpa using hzero
        have hdiv := (ZMod.natCast_eq_zero_iff (2 ^ numBits)
          CompElliptic.Fields.Pasta.PALLAS_BASE_CARD).mp hzero'
        exact (Nat.not_dvd_of_pos_of_lt (pow_two_pos _) hPowLtCard) hdiv
      have hPowSplitFp :
          (2 ^ K : Fp) = (2 ^ (K - numBits) : Fp) * (2 ^ numBits : Fp) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hPowSplitFp]
      field_simp [hPowNe]

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/lookup_range_check.rs`
- `LookupRangeCheck4_5BConfig::short_range_check`
- combined lookup tagged with 4- and 5-bit table rows

The optimized path for `num_bits = 4` and `num_bits = 5` skips the shifted-word row
and instead looks up `(word, num_bits)` in a tagged duplicate of `table_idx`.
-/

def taggedTable : Table Fp fieldPair := .fromStatic {
  name := "table_idx_with_range_check_tag"
  length := 2 ^ 4 + 2 ^ 5
  row i :=
    if h : i.val < 2 ^ 4 then
      ((i.val : Fp), (4 : Fp))
    else
      (((i.val - 2 ^ 4 : ℕ) : Fp), (5 : Fp))
  index := fun x => if x.2 = (4 : Fp) then x.1.val else 2 ^ 4 + x.1.val
  Spec := fun x =>
    (x.2 = (4 : Fp) ∧ x.1.val < 2 ^ 4) ∨
      (x.2 = (5 : Fp) ∧ x.1.val < 2 ^ 5)
  contains_iff := by
    intro x
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i.val < 2 ^ 4
      · left
        simp only [hi, dite_true, true_and]
        rw [ZMod.val_natCast_of_lt (lt_trans hi (by
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))]
        exact hi
      · right
        have hsub : i.val - 2 ^ 4 < 2 ^ 5 := by
          have hi' := i.is_lt
          omega
        simp only [hi, dite_false, true_and]
        rw [ZMod.val_natCast_of_lt (lt_trans hsub (by
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))]
        exact hsub
    · intro h
      rcases h with ⟨htag, hword⟩ | ⟨htag, hword⟩
      · refine ⟨⟨x.1.val, by omega⟩, ?_⟩
        simp only
        rw [dif_pos hword]
        ext <;> simp [htag]
      · refine ⟨⟨2 ^ 4 + x.1.val, by omega⟩, ?_⟩
        simp only
        have hnot : ¬2 ^ 4 + x.1.val < 2 ^ 4 := by omega
        rw [dif_neg hnot]
        ext <;> simp [htag]
}

def taggedShortRangeMain (numBits : ℕ) (_hBits : numBits = 4 ∨ numBits = 5)
    (input : Var ShortRangeCheck Fp) : Circuit Fp Unit := do
  lookup taggedTable (input.word, Expression.const (numBits : Fp))

private theorem tag_four_ne_five : (4 : Fp) ≠ 5 := by
  native_decide

private theorem tag_five_ne_four : (5 : Fp) ≠ 4 := by
  exact fun h => tag_four_ne_five h.symm

def taggedShortRangeCircuit (numBits : ℕ) (hBits : numBits = 4 ∨ numBits = 5) :
    FormalAssertion Fp ShortRangeCheck where
  main := taggedShortRangeMain numBits hBits
  Spec := shortRangeSpec numBits
  soundness := by
    circuit_proof_start [taggedShortRangeMain, shortRangeSpec, taggedTable]
    rcases hBits with rfl | rfl
    · rcases h_holds with h | h
      · exact h.2
      · exfalso
        exact tag_four_ne_five h.1
    · rcases h_holds with h | h
      · exfalso
        exact tag_five_ne_four h.1
      · exact h.2
  completeness := by
    circuit_proof_start [taggedShortRangeMain, shortRangeSpec, taggedTable]
    rcases hBits with rfl | rfl
    · exact Or.inl ⟨by norm_num, h_spec⟩
    · exact Or.inr ⟨by norm_num, h_spec⟩

namespace WitnessShort

open Orchard.Specs (bitrange bitrange_lt)

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/lookup_range_check.rs`
- `RangeConstrained::witness_short`
- `LookupRangeCheck::witness_short_check`

This source-level wrapper witnesses the `bitrange` subset `value >> start mod 2^numBits`
from prover data, then calls the appropriate short range-check path. The verifier-side spec
can only state that the output is range-constrained; the prover spec records the honest
`bitrange` assignment as a `.val` equation.
-/

def main (start numBits : ℕ) (hNumBits : numBits ≤ K)
    (input : Var (Unconstrained field) Fp) : Circuit Fp (Var field Fp) := do
  let word ← witnessProgram do
    let v ← input
    return (v.val.bitrange start numBits).toField
  shortRangeCircuit numBits hNumBits { word }
  return word

def taggedMain (start numBits : ℕ) (hBits : numBits = 4 ∨ numBits = 5)
    (input : Var (Unconstrained field) Fp) : Circuit Fp (Var field Fp) := do
  let word ← witnessProgram do
    let v ← input
    return (v.val.bitrange start numBits).toField
  taggedShortRangeCircuit numBits hBits { word }
  return word

def Spec (numBits : ℕ) (_input : Value (Unconstrained field) Fp) (output : Fp)
    (_ : ProverData Fp) : Prop :=
  output.val < 2 ^ numBits

def ProverSpec (start numBits : ℕ) (input : ProverValue (Unconstrained field) Fp)
    (output : Fp) (_ : ProverHint Fp) : Prop :=
  let v : Fp := input
  output.val = bitrange v.val start numBits

instance elaborated (start numBits : ℕ) (hNumBits : numBits ≤ K) :
    ElaboratedCircuit Fp (Unconstrained field) field (main start numBits hNumBits) := by
  elaborate_circuit

instance taggedElaborated (start numBits : ℕ) (hBits : numBits = 4 ∨ numBits = 5) :
    ElaboratedCircuit Fp (Unconstrained field) field (taggedMain start numBits hBits) := by
  elaborate_circuit

theorem soundness (start numBits : ℕ) (hNumBits : numBits ≤ K) :
    GeneralFormalCircuit.WithHint.Soundness (Input:=Unconstrained field) (Output:=field)
      Fp (main start numBits hNumBits) (fun _ _ => True) (Spec numBits) := by
  circuit_proof_start [main, Spec, shortRangeCircuit]
  exact h_holds

theorem taggedSoundness (start numBits : ℕ) (hBits : numBits = 4 ∨ numBits = 5) :
    GeneralFormalCircuit.WithHint.Soundness (Input:=Unconstrained field) (Output:=field)
      Fp (taggedMain start numBits hBits) (fun _ _ => True) (Spec numBits) := by
  circuit_proof_start [taggedMain, Spec, taggedShortRangeCircuit]
  exact h_holds

theorem completeness (start numBits : ℕ) (hNumBits : numBits ≤ K) :
    GeneralFormalCircuit.WithHint.Completeness (Input:=Unconstrained field) (Output:=field)
      Fp (main start numBits hNumBits) (fun _ _ _ => True) (ProverSpec start numBits) := by
  circuit_proof_start [main, ProverSpec, shortRangeCircuit, shortRangeSpec]
  have numBits_le : numBits ≤ 254 := by grw [hNumBits, K]; norm_num
  have hval := Specs.cast_bitrange_val (start:=start) numBits_le input
  simp [h_env, hval]

theorem taggedCompleteness (start numBits : ℕ) (hBits : numBits = 4 ∨ numBits = 5) :
    GeneralFormalCircuit.WithHint.Completeness (Input:=Unconstrained field) (Output:=field)
      Fp (taggedMain start numBits hBits) (fun _ _ _ => True) (ProverSpec start numBits) := by
  circuit_proof_start [taggedMain, ProverSpec, taggedShortRangeCircuit, shortRangeSpec]
  have numBits_le : numBits ≤ 254 := by grind
  have hval := Specs.cast_bitrange_val (start:=start) numBits_le input
  simp [h_env, hval]

def circuit (start numBits : ℕ) (hNumBits : numBits ≤ K) :
    GeneralFormalCircuit.WithHint Fp (Unconstrained field) field where
  main := main start numBits hNumBits
  elaborated := elaborated start numBits hNumBits
  Spec := Spec numBits
  ProverSpec := ProverSpec start numBits
  soundness := soundness start numBits hNumBits
  completeness := completeness start numBits hNumBits

def taggedCircuit (start numBits : ℕ) (hBits : numBits = 4 ∨ numBits = 5) :
    GeneralFormalCircuit.WithHint Fp (Unconstrained field) field where
  main := taggedMain start numBits hBits
  elaborated := taggedElaborated start numBits hBits
  Spec := Spec numBits
  ProverSpec := ProverSpec start numBits
  soundness := taggedSoundness start numBits hBits
  completeness := taggedCompleteness start numBits hBits

end WitnessShort

namespace CopyCheck

def main (numWords : ℕ) (element : Expression Fp) :
    Circuit Fp (Var (fields (numWords + 1)) Fp) := do
  -- copy `element` into the running-sum column as `z_0`
  let z₀ <== element
  -- z_{i+1} = (z_i - a_i) / 2^K; for the honest prover, z_i = element >> (K * i)
  let zRest : Vector (Expression Fp) numWords ← witness (var := Var (fields numWords))
    (Vector.ofFn fun (i : Fin numWords) => (element.val / (2 ^ (K * (i.val + 1)) : ℕ)).toField)
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

/-- Telescoping a `K`-bit running-sum chain: `f 0` splits into `K * k` low bits and
`2^(K*k) * f k`. -/
theorem chain_telescope (f : ℕ → Fp) :
    ∀ k : ℕ,
    (∀ i, i < k → ∃ w : ℕ, w < 2 ^ K ∧ f i = 2 ^ K * f (i + 1) + (w : Fp)) →
    ∃ lo : ℕ, lo < 2 ^ (K * k) ∧ f 0 = (lo : Fp) + 2 ^ (K * k) * f k
  | 0, _ => ⟨0, by norm_num, by norm_num⟩
  | k + 1, h => by
    obtain ⟨lo, hlt, heq⟩ := chain_telescope f k fun i hi => h i (by omega)
    obtain ⟨w, hw, hstep⟩ := h k (by omega)
    refine ⟨lo + w * 2 ^ (K * k), ?_, ?_⟩
    · have hsplit : (2 : ℕ) ^ (K * (k + 1)) = 2 ^ K * 2 ^ (K * k) := by
        rw [← pow_add]
        ring_nf
      have hbound : lo + w * 2 ^ (K * k) < (w + 1) * 2 ^ (K * k) := by
        have := Nat.two_pow_pos (K * k)
        nlinarith
      have : (w + 1) * 2 ^ (K * k) ≤ 2 ^ K * 2 ^ (K * k) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [heq, hstep]
      push_cast
      rw [show K * (k + 1) = K * k + K from by ring, pow_add]
      ring

/-- A `CopyCheck.Spec` running-sum vector telescopes from `z₀` to any later `z_k`. -/
theorem spec_telescope {numWords : ℕ} {element : Fp} {zs : fields (numWords + 1) Fp}
    {data : ProverData Fp} (h : Spec numWords element zs data) (k : ℕ) (hk : k ≤ numWords) :
    ∃ lo : ℕ, lo < 2 ^ (K * k) ∧
      zs[0]'(Nat.succ_pos numWords) =
        (lo : Fp) + 2 ^ (K * k) * zs[k]'(Nat.lt_succ_of_le hk) := by
  let f : ℕ → Fp := fun i => if hi : i < numWords + 1 then zs[i]'hi else 0
  have hchain : ∀ i, i < k → ∃ w : ℕ, w < 2 ^ K ∧
      f i = 2 ^ K * f (i + 1) + (w : Fp) := by
    intro i hi
    have hiN : i < numWords := lt_of_lt_of_le hi hk
    have hiS : i + 1 < numWords + 1 := Nat.succ_lt_succ hiN
    obtain ⟨w, hw, hstep⟩ := h.2 ⟨i, hiN⟩
    refine ⟨w, hw, ?_⟩
    dsimp [f]
    simp only [dif_pos (Nat.lt_trans hiN (Nat.lt_succ_self numWords)), dif_pos hiS]
    exact hstep
  obtain ⟨lo, hlo, htel⟩ := chain_telescope f k hchain
  refine ⟨lo, hlo, ?_⟩
  dsimp [f] at htel
  simpa only [dif_pos (Nat.succ_pos numWords), dif_pos (Nat.lt_succ_of_le hk)] using htel

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD) in
/-- The suffix of a running-sum chain telescopes: from word `k`, `z_k` splits into
`K·(numWords-k)` low bits and `2^(K·(numWords-k))·z_{numWords}`; with full decomposition
(`z_{numWords} = 0`) this bounds `z_k < 2^(K·(numWords-k))`. -/
private theorem suffix {numWords : ℕ} {element : Fp} {zs : fields (numWords + 1) Fp}
    {data : ProverData Fp} (h : Spec numWords element zs data)
    (htop : zs[numWords]'(Nat.lt_succ_self _) = 0) (k : ℕ) (hk : k ≤ numWords) :
    ∃ lo : ℕ, lo < 2 ^ (K * (numWords - k)) ∧ zs[k]'(Nat.lt_succ_of_le hk) = (lo : Fp) := by
  set g : ℕ → Fp := fun i => if hj : k + i < numWords + 1 then zs[k + i]'hj else 0 with hg
  have hchain : ∀ i, i < numWords - k → ∃ w : ℕ, w < 2 ^ K ∧
      g i = 2 ^ K * g (i + 1) + (w : Fp) := by
    intro i hi
    have hki : k + i < numWords := by omega
    obtain ⟨w, hw, hstep⟩ := h.2 ⟨k + i, hki⟩
    refine ⟨w, hw, ?_⟩
    simp only [hg, dif_pos (show k + i < numWords + 1 by omega),
      dif_pos (show k + (i + 1) < numWords + 1 by omega)]
    exact hstep
  obtain ⟨lo, hlo, htel⟩ := chain_telescope g (numWords - k) hchain
  refine ⟨lo, hlo, ?_⟩
  have hg0 : g 0 = zs[k]'(Nat.lt_succ_of_le hk) := by
    simp only [hg, Nat.add_zero, dif_pos (Nat.lt_succ_of_le hk)]
  have hgn : g (numWords - k) = 0 := by
    simp only [hg, show k + (numWords - k) = numWords by omega, dif_pos (Nat.lt_succ_self numWords)]
    exact htop
  rw [hg0, hgn, mul_zero, _root_.add_zero] at htel
  exact htel

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD) in
/-- A fully-decomposed chain bounds its element below `2^(K·numWords)`. -/
theorem element_lt {numWords : ℕ} (hpow : K * numWords ≤ 254)
    {element : Fp} {zs : fields (numWords + 1) Fp} {data : ProverData Fp}
    (h : Spec numWords element zs data) (htop : zs[numWords]'(Nat.lt_succ_self _) = 0) :
    element.val < 2 ^ (K * numWords) := by
  obtain ⟨lo, hlo, htel⟩ := spec_telescope h numWords le_rfl
  rw [htop, mul_zero, _root_.add_zero] at htel
  have helem : element = (lo : Fp) := by rw [← h.1]; exact htel
  rw [helem, ZMod.val_natCast_of_lt (lt_of_lt_of_le hlo
    (le_trans (Nat.pow_le_pow_right (by norm_num) hpow)
      (le_of_lt (by norm_num [PALLAS_BASE_CARD] : (2 : ℕ) ^ 254 < PALLAS_BASE_CARD))))]
  exact hlo

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD) in
/-- A fully-decomposed chain pins each running sum to the exact shift of `element`:
`(z_k).val = element.val / 2^(K·k)`. -/
theorem read {numWords : ℕ} (hpow : K * numWords ≤ 254)
    {element : Fp} {zs : fields (numWords + 1) Fp} {data : ProverData Fp}
    (h : Spec numWords element zs data) (htop : zs[numWords]'(Nat.lt_succ_self _) = 0)
    (k : ℕ) (hk : k ≤ numWords) :
    (zs[k]'(Nat.lt_succ_of_le hk)).val = element.val / 2 ^ (K * k) := by
  have hcard : ∀ m : ℕ, m ≤ 254 → (2 : ℕ) ^ m < PALLAS_BASE_CARD := fun m hm =>
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hm) (by norm_num [PALLAS_BASE_CARD])
  have hsubpow : K * (numWords - k) ≤ 254 :=
    le_trans (Nat.mul_le_mul_left K (Nat.sub_le numWords k)) hpow
  obtain ⟨lok, hlok, htelk⟩ := spec_telescope h k hk
  obtain ⟨lo', hlo', hzk⟩ := suffix h htop k hk
  have hsum_lt : lok + 2 ^ (K * k) * lo' < 2 ^ (K * numWords) := by
    have hab : 2 ^ (K * k) * 2 ^ (K * (numWords - k)) = 2 ^ (K * numWords) := by
      rw [← pow_add]; congr 1; rw [← Nat.mul_add]; congr 1; omega
    calc lok + 2 ^ (K * k) * lo'
        < 2 ^ (K * k) + 2 ^ (K * k) * lo' := by omega
      _ = 2 ^ (K * k) * (lo' + 1) := by ring
      _ ≤ 2 ^ (K * k) * 2 ^ (K * (numWords - k)) := by gcongr; omega
      _ = 2 ^ (K * numWords) := hab
  have hzkval : (zs[k]'(Nat.lt_succ_of_le hk)).val = lo' := by
    rw [hzk]; exact ZMod.val_natCast_of_lt (lt_trans hlo' (hcard _ hsubpow))
  have helem : element = (((lok + 2 ^ (K * k) * lo' : ℕ)) : Fp) := by
    rw [← h.1, htelk, hzk]; push_cast; ring
  have helemval : element.val = lok + 2 ^ (K * k) * lo' := by
    rw [helem]; exact ZMod.val_natCast_of_lt (lt_trans hsum_lt (hcard _ hpow))
  rw [hzkval, helemval, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ (K * k)),
    Nat.div_eq_of_lt hlok, Nat.zero_add]

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
    refine ⟨_, h, ?_⟩
    rw [ZMod.natCast_zmod_val]
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

namespace Telescoped

structure Output (F : Type) where
  z0 : F
  zLast : F
deriving ProvableStruct

def main (numWords : ℕ) (element : Expression Fp) :
    Circuit Fp (Var Output Fp) := do
  let zs ← CopyCheck.circuit numWords element
  return { z0 := zs[0], zLast := zs[numWords] }

def output (numWords : ℕ) (offset : ℕ) : Var Output Fp :=
  let zs := #v[var (F:=Fp) ⟨offset⟩] ++ varFromOffset (F:=Fp) (fields numWords) (offset + 1)
  { z0 := zs[0], zLast := zs[numWords] }

instance elaborated (numWords : ℕ) :
    ElaboratedCircuit Fp field Output (main numWords) := by
  elaborate_circuit_with {
    output _ offset := output numWords offset
  }

/-- Soundness payoff: `z0 = element` and the (only soundly available) telescoped
decomposition `element = lo + 2^(K·numWords)·zLast` with `lo < 2^(K·numWords)`. -/
def Spec (numWords : ℕ) (element : Fp) (out : Output Fp) (_ : ProverData Fp) : Prop :=
  out.z0 = element ∧
  ∃ lo : ℕ, lo < 2 ^ (K * numWords) ∧
    element = lo + ((2 ^ (K * numWords) : ℕ) : Fp) * out.zLast

/-- Completeness payoff: the *honest* running-sum cells. `zLast = element >> (K·numWords)`
is the exact value (unavailable in `Spec`, since the constraints alone admit non-canonical
decompositions); consumers use it to discharge `b = 1 → zLast = 0` when `element < 2^(K·n)`. -/
def ProverSpec (numWords : ℕ) (element : Fp) (out : Output Fp) (_ : ProverHint Fp) : Prop :=
  out.z0 = element ∧
    out.zLast = ((element.val / 2 ^ (K * numWords) : ℕ) : Fp)

def circuit (numWords : ℕ) : GeneralFormalCircuit Fp field Output where
  main := main numWords
  Spec := Spec numWords
  ProverSpec := ProverSpec numWords
  soundness := by
    circuit_proof_start [CopyCheck.circuit, output]
    obtain ⟨lo, hlo, htel⟩ := CopyCheck.spec_telescope h_holds numWords le_rfl
    refine ⟨?_, lo, hlo, ?_⟩
    · convert h_holds.1 using 1; simp [circuit_norm]
    · rw [← h_holds.1]
      convert htel using 1
      simp [circuit_norm]
  completeness := by
    circuit_proof_start [CopyCheck.circuit, CopyCheck.ProverSpec, output]
    refine ⟨?_, h_env.2 ⟨numWords, by omega⟩⟩
    rw [h_env.2 ⟨0, by omega⟩]
    simp

end Telescoped

/- A *full* 25-word (`K`-bit) decomposition of `element` — the final running sum is asserted
to `0`, so the exposed reads are exact — surfacing the two interior running sums
`z₁ = element ≫ K` and `z₁₃ = element ≫ 13·K` that `y_canonicity` consumes. Like `Telescoped`,
it returns a struct of projections (not a vector) with a hand-written opaque `output`, so
parents read `.z1`/`.z13` without unfolding the `mapRange` term. Tailored for now to the
250-bit low limb of a `y`-coordinate; generalize if a second consumer appears. -/
namespace Decomposed

structure Output (F : Type) where
  z1 : F
  z13 : F
deriving ProvableStruct

def main (element : Expression Fp) : Circuit Fp (Var Output Fp) := do
  let zs ← CopyCheck.circuit 25 element
  assertZero zs[25]
  return { z1 := zs[1], z13 := zs[13] }

def output (offset : ℕ) : Var Output Fp :=
  let zs := #v[var (F:=Fp) ⟨offset⟩] ++ varFromOffset (F:=Fp) (fields 25) (offset + 1)
  { z1 := zs[1], z13 := zs[13] }

instance elaborated : ElaboratedCircuit Fp field Output main := by
  elaborate_circuit_with {
    output _ offset := output offset
  }

def Spec (element : Fp) (out : Output Fp) (_ : ProverData Fp) : Prop :=
  element.val < 2 ^ 250 ∧
    out.z1.val = element.val / 2 ^ 10 ∧
    out.z13.val = element.val / 2 ^ 130

/-- Completeness precondition: the element is a genuine `< 2^250` low limb. Soundness does
*not* assume this — the asserted full decomposition (`z₂₅ = 0`) derives it — but the honest
prover can only satisfy `z₂₅ = 0` when the element actually fits in 250 bits. -/
def ProverAssumptions (element : Fp) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  element.val < 2 ^ 250

def ProverSpec (element : Fp) (out : Output Fp) (_ : ProverHint Fp) : Prop :=
  out.z1.val = element.val / 2 ^ 10 ∧
    out.z13.val = element.val / 2 ^ 130

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD) in
def circuit : GeneralFormalCircuit.WithHint Fp field Output where
  main
  elaborated
  Spec
  ProverAssumptions
  ProverSpec
  soundness := by
    circuit_proof_start [CopyCheck.circuit, output]
    obtain ⟨hcc, hz25⟩ := h_holds
    refine ⟨?_, ?_, ?_⟩
    · simpa only [show K * 25 = 250 from by norm_num [K]] using
        element_lt (by norm_num [K]) hcc
          (by simp only [Vector.getElem_map, Vector.getElem_cast]; exact hz25)
    · simpa only [Vector.getElem_map, Vector.getElem_cast,
        show K * 1 = 10 from by norm_num [K]] using
        read (by norm_num [K]) hcc
          (by simp only [Vector.getElem_map, Vector.getElem_cast]; exact hz25) 1 (by norm_num)
    · simpa only [Vector.getElem_map, Vector.getElem_cast,
        show K * 13 = 130 from by norm_num [K]] using
        read (by norm_num [K]) hcc
          (by simp only [Vector.getElem_map, Vector.getElem_cast]; exact hz25) 13 (by norm_num)
  completeness := by
    circuit_proof_start [CopyCheck.circuit, CopyCheck.ProverSpec, output]
    change Fp at input
    have hlt : ∀ k : ℕ, input.val / 2 ^ k < PALLAS_BASE_CARD := by
      intro k
      have h1 : input.val / 2 ^ k ≤ input.val := Nat.div_le_self _ _
      have h2 : input.val < PALLAS_BASE_CARD :=
        lt_trans h_assumptions (by norm_num [PALLAS_BASE_CARD])
      omega
    refine ⟨?_, ?_, ?_⟩
    · -- z₂₅ = 0 (honest tail vanishes since the limb fits in 250 bits)
      rw [h_env.2 ⟨25, by norm_num⟩, show K * 25 = 250 from by norm_num [K],
        Nat.div_eq_of_lt h_assumptions, Nat.cast_zero]
    · -- z₁ = element ≫ 10
      rw [h_env.2 ⟨1, by norm_num⟩, show K * 1 = 10 from by norm_num [K]]
      exact ZMod.val_natCast_of_lt (hlt 10)
    · -- z₁₃ = element ≫ 130
      rw [h_env.2 ⟨13, by norm_num⟩, show K * 13 = 130 from by norm_num [K]]
      exact ZMod.val_natCast_of_lt (hlt 130)

end Decomposed

end CopyCheck

end LookupRangeCheck

end Utilities
end Orchard
