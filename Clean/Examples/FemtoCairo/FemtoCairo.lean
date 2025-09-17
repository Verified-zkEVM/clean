import Clean.Table.Inductive
import Clean.Gadgets.Bits
import Clean.Utils.Bits
import Clean.Utils.Field

import Clean.Examples.FemtoCairo.Spec
import Clean.Examples.FemtoCairo.Types

namespace Examples.FemtoCairo
open Gadgets
open Utils.Bits
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
  Construct a table that represents a read-only memory containing all pairs (i, f(i)) for i in [0, length).
  - The **program table** it is OK, as it a fixed and public,
    so the verifier always has access to lookups into its table.
  - For the **memory table**, it is committed by the prover, and no constraints are enforced on it.
    For our formalization, we represent it also as a fixed table. This is without loss of generality,
    since we do not make any assumptions on its content, and its role is just to fix a function.

  To represent, e.g., a read-write memory we will need a more complex construction.
-/
def ReadOnlyTableFromFunction (f : (F p) → (F p)) (length : ℕ) (h : length < p) [NeZero length] : Table (F p) fieldPair := .fromStatic {
  name := "ReadOnlyMemory"
  length := length
  row i := (i, f i)
  index := fun (i, _) => i.val
  Spec := fun (i, v) => v = f i ∧ i.val < length
  contains_iff := by
    intro t
    constructor
    · rintro ⟨ i, h: t = _ ⟩
      simp_all
      sorry
    · intro h
      simp_all
      use Fin.ofNat length t.1.val
      sorry
}


def decodeInstructionCircuit : FormalCircuit (F p) field DecodedInstruction where
  main := fun instruction => do
    let bits ← Gadgets.ToBits.toBits 8 (by linarith [p_large_enough.elim]) instruction
    return {
      instrType := {
        isAdd := (1 : Expression _) - bits[0] - bits[1] + bits[0] * bits[1],
        isMul := bits[0] - bits[0] * bits[1],
        isStoreState := bits[1] - bits[0] * bits[1],
        isLoadState := bits[0] * bits[1]
      },
      addr1 := {
        isDoubleAddressing := (1 : Expression _) - bits[2] - bits[3] + bits[2] * bits[3],
        isApRelative := bits[2] - bits[2] * bits[3],
        isFpRelative := bits[3] - bits[2] * bits[3],
        isImmediate := bits[2] * bits[3]
      },
      addr2 := {
        isDoubleAddressing := (1 : Expression _) - bits[4] - bits[5] + bits[4] * bits[5],
        isApRelative := bits[4] - bits[4] * bits[5],
        isFpRelative := bits[5] - bits[4] * bits[5],
        isImmediate := bits[4] * bits[5]
      },
      addr3 := {
        isDoubleAddressing := (1 : Expression _) - bits[6] - bits[7] + bits[6] * bits[7],
        isApRelative := bits[6] - bits[6] * bits[7],
        isFpRelative := bits[7] - bits[6] * bits[7],
        isImmediate := bits[6] * bits[7]
      }
    }
  localLength _ := 8

  Assumptions | instruction => True

  Spec
  | instruction, output =>
    let (instr_type, addr1, addr2, addr3) := Spec.decodeInstruction instruction
    (output.instrType.isAdd = if instr_type = 0 then 1 else 0) ∧
    (output.instrType.isMul = if instr_type = 1 then 1 else 0) ∧
    (output.instrType.isStoreState = if instr_type = 2 then 1 else 0) ∧
    (output.instrType.isLoadState = if instr_type = 3 then 1 else 0) ∧

    (output.addr1.isDoubleAddressing = if addr1 = 0 then 1 else 0) ∧
    (output.addr1.isApRelative = if addr1 = 1 then 1 else 0) ∧
    (output.addr1.isFpRelative = if addr1 = 2 then 1 else 0) ∧
    (output.addr1.isImmediate = if addr1 = 3 then 1 else 0) ∧

    (output.addr2.isDoubleAddressing = if addr2 = 0 then 1 else 0) ∧
    (output.addr2.isApRelative = if addr2 = 1 then 1 else 0) ∧
    (output.addr2.isFpRelative = if addr2 = 2 then 1 else 0) ∧
    (output.addr2.isImmediate = if addr2 = 3 then 1 else 0) ∧

    (output.addr3.isDoubleAddressing = if addr3 = 0 then 1 else 0) ∧
    (output.addr3.isApRelative = if addr3 = 1 then 1 else 0) ∧
    (output.addr3.isFpRelative = if addr3 = 2 then 1 else 0) ∧
    (output.addr3.isImmediate = if addr3 = 3 then 1 else 0)

  soundness := by
    circuit_proof_start
    simp only [id_eq, Gadgets.toBits, Nat.reducePow] at h_holds
    obtain ⟨ h_range_check, h_eq ⟩ := h_holds

    simp only [id_eq, Gadgets.toBits, Nat.reducePow, Spec.decodeInstruction, Nat.add_eq_zero,
      ZMod.val_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]

    rw [Vector.ext_iff] at h_eq
    simp only [Vector.getElem_map] at h_eq
    have h1 := h_eq 0 (by linarith)
    have h2 := h_eq 1 (by linarith)
    have h3 := h_eq 2 (by linarith)
    have h4 := h_eq 3 (by linarith)
    have h5 := h_eq 4 (by linarith)
    have h6 := h_eq 5 (by linarith)
    have h7 := h_eq 6 (by linarith)
    have h8 := h_eq 7 (by linarith)
    simp only [eval, fromElements, size, toVars, toElements, ↓ProvableType.varFromOffset_fields,
      Vector.mapRange_succ, Vector.mapRange_zero, add_zero, Vector.push_mk, Nat.reduceAdd,
      List.push_toArray, List.nil_append, List.cons_append, Vector.getElem_mk,
      ↓List.getElem_toArray, ↓List.getElem_cons_zero, ↓List.getElem_cons_succ, Vector.map_mk,
      List.map_toArray, List.map_cons, Expression.eval, neg_mul, one_mul, List.map_nil]
    simp only [↓ProvableType.varFromOffset_fields, ↓Vector.getElem_mapRange, add_zero,
      Expression.eval] at h1 h2 h3 h4 h5 h6 h7 h8
    rw [h1, h2, h3, h4, h5, h6, h7, h8]


    have h_bits_are_binary := fieldToBits_bits (x := input) (n := 8)
    have h_bits0 := h_bits_are_binary 0 (by linarith)
    have h_bits1 := h_bits_are_binary 1 (by linarith)
    have h_bits2 := h_bits_are_binary 2 (by linarith)
    have h_bits3 := h_bits_are_binary 3 (by linarith)
    have h_bits4 := h_bits_are_binary 4 (by linarith)
    have h_bits5 := h_bits_are_binary 5 (by linarith)
    have h_bits6 := h_bits_are_binary 6 (by linarith)
    have h_bits7 := h_bits_are_binary 7 (by linarith)

    repeat' constructor
    repeat
      cases' h_bits0 with h0 h0
      · cases' h_bits1 with h1 h1
        repeat simp only [h0, h1, neg_zero, add_zero, zero_add, add_neg_cancel,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, one_ne_zero, zero_ne_one,
          OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, and_self, and_false, Nat.reduceEqDiff, ↓reduceIte]
      · cases' h_bits1 with h1 h1
        repeat simp only [h0, h1, add_zero, zero_add, add_neg_cancel, neg_add_cancel, neg_zero,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, Nat.reduceAdd, Nat.succ_ne_self,
          one_ne_zero, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, and_true, and_self, ↓reduceIte]

    repeat
      cases' h_bits2 with h0 h0
      · cases' h_bits3 with h1 h1
        repeat simp only [h0, h1, neg_zero, add_zero, zero_add, add_neg_cancel,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, one_ne_zero, zero_ne_one,
          OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, and_self, and_false, Nat.reduceEqDiff, ↓reduceIte]
      · cases' h_bits3 with h1 h1
        repeat simp only [h0, h1, add_zero, zero_add, add_neg_cancel, neg_add_cancel, neg_zero,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, Nat.reduceAdd, Nat.succ_ne_self,
          one_ne_zero, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, and_true, and_self, ↓reduceIte]

    repeat
      cases' h_bits4 with h0 h0
      · cases' h_bits5 with h1 h1
        repeat simp only [h0, h1, neg_zero, add_zero, zero_add, add_neg_cancel,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, one_ne_zero, zero_ne_one,
          OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, and_self, and_false, Nat.reduceEqDiff, ↓reduceIte]
      · cases' h_bits5 with h1 h1
        repeat simp only [h0, h1, add_zero, zero_add, add_neg_cancel, neg_add_cancel, neg_zero,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, Nat.reduceAdd, Nat.succ_ne_self,
          one_ne_zero, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, and_true, and_self, ↓reduceIte]

    repeat
      cases' h_bits6 with h0 h0
      · cases' h_bits7 with h1 h1
        repeat simp only [h0, h1, neg_zero, add_zero, zero_add, add_neg_cancel,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, one_ne_zero, zero_ne_one,
          OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, and_self, and_false, Nat.reduceEqDiff, ↓reduceIte]
      · cases' h_bits7 with h1 h1
        repeat simp only [h0, h1, add_zero, zero_add, add_neg_cancel, neg_add_cancel, neg_zero,
          mul_zero, mul_one, ZMod.val_zero, ZMod.val_one, Nat.reduceAdd, Nat.succ_ne_self,
          one_ne_zero, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, and_true, and_self, ↓reduceIte]

  completeness := by
    sorry

def fetchInstruction (program : (F p) → (F p)) (programTable : Table (F p) fieldPair) : FormalCircuit (F p)
    field RawInstruction where
  main := fun pc => do
    let rawInstrType : Expression _ ← witness fun eval => program (eval pc)
    let op1 ← witness fun eval => program (eval pc + 1)
    let op2 ← witness fun eval => program (eval pc + 2)
    let op3 ← witness fun eval => program (eval pc + 3)

    lookup programTable ⟨pc, rawInstrType⟩
    lookup programTable ⟨pc + 1, op1⟩
    lookup programTable ⟨pc + 2, op2⟩
    lookup programTable ⟨pc + 3, op3⟩

    return { rawInstrType, op1, op2, op3 }

  localLength _ := 4
  Assumptions := sorry
  Spec := sorry
  soundness := by
    sorry
  completeness := by
    sorry

def readFromMemory (memory : (F p) → (F p)) (memoryTable : Table (F p) fieldPair) : FormalCircuit (F p)
    MemoryReadInput field where
  main := fun { state, offset, mode } => do
    -- read into memory for all cases of addressing mode
    let v0 : Expression _ ← witness fun eval => (memory ∘ memory ∘ eval) (state.ap + offset)
    let v1 : Expression _ ← witness fun eval => (memory ∘ eval) (state.ap + offset)
    let v2 : Expression _ ← witness fun eval => (memory ∘ eval) (state.fp + offset)
    lookup memoryTable ⟨(state.ap + offset), v0⟩
    lookup memoryTable ⟨(state.ap + offset), v1⟩
    lookup memoryTable ⟨(state.fp + offset), v2⟩

    -- select the correct value based on the addressing mode
    let value <==
      mode.isDoubleAddressing * v0 +
      mode.isApRelative * v1 +
      mode.isFpRelative * v2 +
      mode.isImmediate * offset

    return value

  localLength _ := 4
  Assumptions := sorry
  Spec := sorry
  soundness := by
    sorry
  completeness := by
    sorry


def checkStateTransition : FormalAssertion (F p) StateTransitionInput where
  main := fun { state, nextState, decoded, memoryValues } => do
    assertZero (decoded.instrType.isAdd * (memoryValues[2] - (memoryValues[0] + memoryValues[1])))

    assertZero (decoded.instrType.isMul * (memoryValues[2] - (memoryValues[0] * memoryValues[1])))

    assertZero (decoded.instrType.isStoreState * (memoryValues[0] - state.pc))
    assertZero (decoded.instrType.isStoreState * (memoryValues[1] - state.ap))
    assertZero (decoded.instrType.isStoreState * (memoryValues[2] - state.fp))

    assertZero (decoded.instrType.isLoadState * (nextState.pc - memoryValues[0]))
    assertZero (decoded.instrType.isLoadState * (nextState.ap - memoryValues[1]))
    assertZero (decoded.instrType.isLoadState * (nextState.fp - memoryValues[2]))

    assertZero ((1 - decoded.instrType.isLoadState) * (nextState.pc - (state.pc + 4)))
    assertZero ((1 - decoded.instrType.isLoadState) * (nextState.ap - state.ap))
    assertZero ((1 - decoded.instrType.isLoadState) * (nextState.fp - state.fp))

  localLength _ := 0
  Assumptions := sorry
  Spec := sorry
  soundness := by
    sorry
  completeness := by
    sorry


def femtoCairoStepCircuit
    (program : (F p) → (F p)) (memory : (F p) → (F p))
    (len : ℕ) [NeZero len] (h_len : len < p) (state : Var State (F p)) :
    Circuit (F p) (Var State (F p)) := do
  let programTable := ReadOnlyTableFromFunction program len h_len
  let memoryTable := ReadOnlyTableFromFunction memory len h_len

  -- Fetch instruction
  let { rawInstrType, op1, op2, op3 } ← subcircuit (fetchInstruction program programTable) state.pc

  -- Decode instruction
  let decoded ← subcircuit decodeInstructionCircuit rawInstrType

  -- Perform relevant memory accesses
  let v1 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op1, mode := decoded.addr1 }
  let v2 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op2, mode := decoded.addr2 }
  let v3 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op3, mode := decoded.addr3 }

  -- Witness the claimed next state
  let nextState : State _ ← ProvableType.witness fun eval => {
    pc := if eval decoded.instrType.isLoadState = 1 then eval v1 else eval state.pc + 4
    ap := if eval decoded.instrType.isLoadState = 1 then eval v2 else eval state.ap
    fp := if eval decoded.instrType.isLoadState = 1 then eval v3 else eval state.fp
  }

  -- Check state transition
  assertion checkStateTransition { state, nextState, decoded, memoryValues := #v[v1, v2, v3] }

  return nextState

end Examples.FemtoCairo
