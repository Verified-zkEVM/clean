import Clean.Halo2
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Tactic.LinearCombination
import Midnight.SHA256.Configure
import Midnight.Chips.Synthesis

/-!
Semantic native arithmetic used by the pinned SHA circuit. This is the four-term,
single-row case of `NativeChip::assign_linear_combination_aux`, followed by the
copies in `linear_combination` (`native_chip.rs:425-519,868-926`). The complete
native gate is retained, including its next-row and multiplication queries.

This module proves a field relation. Byte bounds, packing into bounded words,
the native zero-cache/filter shortcuts, and the rest of SHA are separate layers.
-/
namespace Midnight.SHA256.Semantics.Arithmetic
open Halo2

/-- The four source cells, ordered as the native linear-combination terms. -/
structure Inputs (α : Type) where
  a : α
  b : α
  c : α
  d : α
deriving ProvableStruct

/-- The exact arithmetic gate at the SHA example's canonical columns. -/
def nativeGate : Gate F :=
  let v0 : Expression F Query := queryAdvice ⟨0⟩ 0
  let v1 : Expression F Query := queryAdvice ⟨1⟩ 0
  let v2 : Expression F Query := queryAdvice ⟨2⟩ 0
  let v3 : Expression F Query := queryAdvice ⟨3⟩ 0
  let v4 : Expression F Query := queryAdvice ⟨4⟩ 0
  let next : Expression F Query := queryAdvice ⟨0⟩ 1
  let c0 : Expression F Query := queryFixed ⟨4⟩
  let c1 : Expression F Query := queryFixed ⟨5⟩
  let c2 : Expression F Query := queryFixed ⟨6⟩
  let c3 : Expression F Query := queryFixed ⟨7⟩
  let c4 : Expression F Query := queryFixed ⟨8⟩
  let cn : Expression F Query := queryFixed ⟨0⟩
  let cab : Expression F Query := queryFixed ⟨1⟩
  let cac : Expression F Query := queryFixed ⟨2⟩
  let cc : Expression F Query := queryFixed ⟨3⟩
  Gate.withSelector "arith_gate" ⟨0, true⟩
    [v0, v1, v2, v3, v4, next, c0, c1, c2, c3, c4, cn, cab, cac, cc]
    [("", cc + c0 * v0 + c1 * v1 + c2 * v2 + c3 * v3 + c4 * v4 +
      cn * next + cab * v0 * v1 + cac * v0 * v2)]

/-- Source selector zero activates precisely this gate and no lookup. -/
theorem activation_zero (row : Nat) :
    SHA256.activation 0 row = [.enableGate nativeGate row] := by
  have hg : SHA256.cleanGates.filter (fun g => g.selector.index == 0) = [nativeGate] := by
    decide +kernel
  have hl : SHA256.cleanLookups.filter (fun l => l.masterSelector.index == 0) = [] := by
    decide +kernel
  simp [SHA256.activation, hg, hl]

@[circuit_norm, keygen_norm]
theorem nativeGate_selector : nativeGate.selector = ⟨0, true⟩ := rfl

def linearValue (coeff : Inputs F) (constant : F) (input : Inputs F) : F :=
  constant + coeff.a * input.a + coeff.b * input.b + coeff.c * input.c + coeff.d * input.d

/-- Serializable witness expression: the Rust fold from the constant through
the four coefficient/value products. It reads the original input cells. -/
def linearWitness (coeff : Inputs F) (constant : F)
    (input : Inputs (AssignedCell F)) : WitgenIR F 1 :=
  .ofFExpr (.const constant + .const coeff.a * .expr input.a +
    .const coeff.b * .expr input.b + .const coeff.c * .expr input.c +
    .const coeff.d * .expr input.d)

/-- Native order: output, four terms, selector, five coefficients, next-row
coefficient, multiplication coefficients, constant, then the four copy edges. -/
def synthesize (coeff : Inputs F) (constant : F) (_config : Unit) (offset : Nat)
    (input : Inputs (AssignedCell F)) : RegionCircuit F (AssignedCell F) := do
  let result ← assignAdvice ⟨0⟩ offset (linearWitness coeff constant input)
  let a ← assignAdvice ⟨1⟩ offset (.ofFExpr (.expr input.a))
  let b ← assignAdvice ⟨2⟩ offset (.ofFExpr (.expr input.b))
  let c ← assignAdvice ⟨3⟩ offset (.ofFExpr (.expr input.c))
  let d ← assignAdvice ⟨4⟩ offset (.ofFExpr (.expr input.d))
  nativeGate.enable offset
  let _ ← assignFixed ⟨4⟩ offset (-1)
  let _ ← assignFixed ⟨5⟩ offset coeff.a
  let _ ← assignFixed ⟨6⟩ offset coeff.b
  let _ ← assignFixed ⟨7⟩ offset coeff.c
  let _ ← assignFixed ⟨8⟩ offset coeff.d
  let _ ← assignFixed ⟨0⟩ offset 0
  let _ ← assignFixed ⟨1⟩ offset 0
  let _ ← assignFixed ⟨2⟩ offset 0
  let _ ← assignFixed ⟨3⟩ offset constant
  constrainEqual a input.a
  constrainEqual b input.b
  constrainEqual c input.c
  constrainEqual d input.d
  return result

def synthesisSummary (offset : Nat) : FloorPlanner.RegionSynthesisSummary :=
  .ofColumns [.column .advice 0, .column .advice 1, .column .advice 2,
    .column .advice 3, .column .advice 4, .selector 0,
    .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7,
    .column .fixed 8, .column .fixed 0, .column .fixed 1, .column .fixed 2,
    .column .fixed 3] (offset + 1) 0 (selectorActivations := [(0, offset)])

/-- A genuine Clean semantic region: malicious assignments satisfying the
native equation and copy edges have the stated result, and the actual witness
program satisfies those constraints for arbitrary field-valued inputs. -/
def linearCombination4 (coeff : Inputs F) (constant : F) :
    FormalRegionCircuit F Unit Unit Inputs field where
  name := "Linear combination"
  configure := pure
  synthesize := synthesize coeff constant
  elaborated :=
    { keygenRequirements :=
        { gates _ _ := [nativeGate]
          fixedColumns _ _ := [⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]
          permutationColumns _ _ :=
            [(⟨1⟩ : Column .advice), (⟨2⟩ : Column .advice),
              (⟨3⟩ : Column .advice), (⟨4⟩ : Column .advice)]
          inputCells _ _ input := [input.a.cell, input.b.cell, input.c.cell, input.d.cell] }
      registered := by keygen_registration [synthesize]
      output _ offset _ self := .of self offset ⟨0⟩
      synthesisSummary _ offset _ _ := synthesisSummary offset
      output_eq := by intro _ _ _ _; rfl
      fixedAssignmentsAgree := by
        intro _ _ _ _ _ _ column row left right hleft hright
        simp only [synthesize, circuit_norm, List.mem_cons, List.not_mem_nil,
          or_false, RegionOperation.assignFixed.injEq, reduceCtorEq,
          false_or] at hleft hright
        rcases hleft with h | h | h | h | h | h | h | h | h <;>
          rcases h with ⟨rfl, rfl, rfl⟩ <;> simp_all
      synthesisSummary_eq := by
        intro _ _ _ _
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [synthesisSummary, synthesize, circuit_norm, nativeGate,
            List.flatMap_cons, List.flatMap_nil, FloorPlanner.regionOperationShapeColumns,
            List.append_nil, List.singleton_append]
        · simp only [synthesisSummary, synthesize, circuit_norm, nativeGate]
          omega
        all_goals simp only [synthesisSummary, synthesize, circuit_norm, nativeGate,
          synthesis_summary_norm] }
  Spec input output _ := output = linearValue coeff constant input
  ProverSpec input output _ _ := output = linearValue coeff constant input
  soundness := by
    circuit_proof_start [nativeGate, synthesize, linearValue]
    rcases hc with ⟨hg, h0, h1, h2, h3, h4, hn, hab, hac, hconst, ha, hb, hc, hd⟩
    rw [h0, h1, h2, h3, h4, hn, hab, hac, hconst, ha, hb, hc, hd] at hg
    linear_combination -hg
  completeness := by
    circuit_proof_start [nativeGate, synthesize, linearWitness, linearValue]
    exact ⟨by ring, h_output.symm⟩

/-- Native `blockFromBytes` supplies bytes in reverse order: `a` is the least
significant (fourth) byte and `d` is the most significant (first) byte. -/
def byteCoefficients : Inputs F := ⟨1, 256, 65536, 16777216⟩

def packedNat (input : Inputs F) : Nat :=
  input.a.val + 256 * input.b.val + 65536 * input.c.val + 16777216 * input.d.val

def ByteInputs (input : Inputs F) : Prop :=
  input.a.val < 256 ∧ input.b.val < 256 ∧ input.c.val < 256 ∧ input.d.val < 256

theorem packedNat_lt (input : Inputs F) (h : ByteInputs input) :
    packedNat input < 2 ^ 32 := by
  unfold ByteInputs at h
  unfold packedNat
  omega

theorem linearValue_bytes_eq_nat (input : Inputs F) :
    linearValue byteCoefficients 0 input = (packedNat input : F) := by
  simp [linearValue, byteCoefficients, packedNat]

/-- Range assumptions are local facts about the four input bytes. They imply
the field packing has no wraparound and gives an actual unsigned 32-bit word. -/
theorem packedValue_val (input : Inputs F) (h : ByteInputs input) :
    (linearValue byteCoefficients 0 input).val = packedNat input := by
  rw [linearValue_bytes_eq_nat, ZMod.val_natCast_of_lt]
  exact lt_trans (packedNat_lt input h) (by norm_num [BLS12_381.scalarFieldSize])

end Midnight.SHA256.Semantics.Arithmetic
