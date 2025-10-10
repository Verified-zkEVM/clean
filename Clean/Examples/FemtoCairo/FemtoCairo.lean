import Clean.Table.Inductive
import Clean.Gadgets.Bits
import Clean.Utils.Bits
import Clean.Utils.Field
import Clean.Table.Inductive

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
def ReadOnlyTableFromFunction
    {n : ℕ} (f : Fin n → (F p)) (h : n < p) [NeZero n] :
    Table (F p) fieldPair
  := .fromStatic {
  name := "ReadOnlyMemory"
  length := n
  row i := (i, f i)
  index := fun (i, _) => i.val
  Spec := fun (i, v) => v = f (Fin.ofNat n i.val) ∧ i.val < n
  contains_iff := by
    rintro ⟨row_index, row_value⟩
    constructor
    · rintro ⟨ i', h' ⟩
      split
      case h_1 i snd h_eq =>
        simp only [Prod.mk.injEq] at h' h_eq
        rw [←h_eq.left, ←h_eq.right, h'.left, h'.right, Fin.ofNat.eq_1]
        have h := Fin.isLt i'
        constructor
        · congr
          rw [←Fin.val_eq_val]
          simp only
          rw [ZMod.val_cast_of_lt (by linarith), Nat.mod_eq_of_lt h]
        · rw [ZMod.val_cast_of_lt (by linarith)]
          assumption
    · intro h
      simp_all only [gt_iff_lt, Fin.ofNat_eq_cast, Prod.mk.injEq]
      use (Fin.ofNat n row_index.val)
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, and_true]
      rw [Nat.mod_eq_of_lt (by linarith)]
      simp only [ZMod.natCast_val]
      apply_fun ZMod.val
      · rw [ZMod.val_cast_eq_val_of_lt (by linarith)]
      · apply ZMod.val_injective
}

def decodeInstructionMain (instruction : Var field (F p)) : Circuit (F p) (Var DecodedInstruction (F p)) := do
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

def decodeInstructionSpec (instruction : field (F p)) (output : DecodedInstruction (F p)) (_ : Set (NamedList (F p))) : Prop :=
    match Spec.decodeInstruction instruction with
    | some (instr_type, addr1, addr2, addr3) =>
      output.instrType.val = instr_type ∧ output.instrType.isEncodedCorrectly ∧
      output.addr1.val = addr1 ∧ output.addr1.isEncodedCorrectly ∧
      output.addr2.val = addr2 ∧ output.addr2.isEncodedCorrectly ∧
      output.addr3.val = addr3 ∧ output.addr3.isEncodedCorrectly
    | none => False -- impossible, constraints ensure that input < 256

def decodeInstructionElaborated : ElaboratedCircuit (F p) field DecodedInstruction where
  main := decodeInstructionMain
  localLength _ := 8
  yields_eq := by intros; simp only [circuit_norm, decodeInstructionMain, Gadgets.ToBits.toBits, Set.empty_union]

/--
  Circuit that decodes a femtoCairo instruction into a one-hot representation.
  It returns a `DecodedInstruction` struct containing the decoded fields.
  This circuit is not satisfiable if the input instruction is not correctly encoded.
-/
def decodeInstructionCircuit : FormalCircuit (F p) field DecodedInstruction where
  elaborated := decodeInstructionElaborated

  Spec := decodeInstructionSpec

  soundness := by
    circuit_proof_start [Gadgets.toBits, decodeInstructionMain, decodeInstructionSpec, decodeInstructionElaborated]
    clear yielded
    simp only [Nat.reducePow] at h_holds
    obtain ⟨ h_range_check, h_eq ⟩ := h_holds
    have h : ¬ 256 ≤ input.val := by linarith
    simp only [Spec.decodeInstruction, ge_iff_le]
    simp [Vector.mapRange, circuit_norm] at h_eq
    simp [circuit_norm, explicit_provable_type]
    rw [Array.ext_iff] at h_eq
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Vector.size_toArray, List.getElem_toArray, Vector.getElem_toArray, true_and] at h_eq
    have h_bits_eval0 := h_eq 0 (by linarith) (by linarith)
    have h_bits_eval1 := h_eq 1 (by linarith) (by linarith)
    have h_bits_eval2 := h_eq 2 (by linarith) (by linarith)
    have h_bits_eval3 := h_eq 3 (by linarith) (by linarith)
    have h_bits_eval4 := h_eq 4 (by linarith) (by linarith)
    have h_bits_eval5 := h_eq 5 (by linarith) (by linarith)
    have h_bits_eval6 := h_eq 6 (by linarith) (by linarith)
    have h_bits_eval7 := h_eq 7 (by linarith) (by linarith)
    clear h_eq
    simp only [List.getElem_cons_zero,
      List.getElem_cons_succ] at h_bits_eval0 h_bits_eval1 h_bits_eval2 h_bits_eval3 h_bits_eval4 h_bits_eval5 h_bits_eval6 h_bits_eval7
    simp only [h_bits_eval0, h_bits_eval1, h_bits_eval2, h_bits_eval3, h_bits_eval4, h_bits_eval5, h_bits_eval6, h_bits_eval7]
    clear h_bits_eval0 h_bits_eval1 h_bits_eval2 h_bits_eval3 h_bits_eval4 h_bits_eval5 h_bits_eval6 h_bits_eval7

    split

    -- the bit decomposition also implies that the input is < 256
    -- therefore, Spec.decodeInstruction never returns none
    case h_2 =>
      rename_i h_eq2
      simp only [not_le, ite_eq_left_iff, reduceCtorEq, imp_false] at h_eq2
      contradiction
    case _ x instr_type addr1 addr2 addr3 h_eq =>
      have h_bits_are_binary := fieldToBits_bits (x := input) (n := 8)
      have h_bits0 := h_bits_are_binary 0 (by linarith)
      have h_bits1 := h_bits_are_binary 1 (by linarith)
      have h_bits2 := h_bits_are_binary 2 (by linarith)
      have h_bits3 := h_bits_are_binary 3 (by linarith)
      have h_bits4 := h_bits_are_binary 4 (by linarith)
      have h_bits5 := h_bits_are_binary 5 (by linarith)
      have h_bits6 := h_bits_are_binary 6 (by linarith)
      have h_bits7 := h_bits_are_binary 7 (by linarith)
      generalize (fieldToBits 8 input)[0] = f0 at *
      generalize (fieldToBits 8 input)[1] = f1 at *
      generalize (fieldToBits 8 input)[2] = f2 at *
      generalize (fieldToBits 8 input)[3] = f3 at *
      generalize (fieldToBits 8 input)[4] = f4 at *
      generalize (fieldToBits 8 input)[5] = f5 at *
      generalize (fieldToBits 8 input)[6] = f6 at *
      generalize (fieldToBits 8 input)[7] = f7 at *

      simp only [gt_iff_lt, id_eq, not_le,
        Option.ite_none_left_eq_some, Option.some.injEq, Prod.mk.injEq] at *
      repeat' apply And.intro
      · clear h_bits2 h_bits3 h_bits4 h_bits5 h_bits6 h_bits7
        simp only [DecodedInstructionType.val]
        cases' h_bits0 with h0 h0
        · subst h0
          cases' h_bits1 with h1 h1
          · subst h1
            simp only [ZMod.val_zero, mul_zero, add_zero] at h_eq
            simp only [neg_zero, add_zero, mul_zero, ↓reduceIte, h_eq]
          · simp only [h1] at h_eq ⊢
            simp only [ZMod.val_zero, ZMod.val_one, mul_one, zero_add] at h_eq
            simp only [neg_zero, add_zero, add_neg_cancel, mul_one, zero_ne_one, ↓reduceIte, h_eq]
        · subst h0
          cases' h_bits1 with h1 h1
          · subst h1
            simp only [ZMod.val_one, ZMod.val_zero, mul_zero, add_zero] at h_eq
            simp only [add_neg_cancel, neg_zero, add_zero, mul_zero, zero_ne_one, ↓reduceIte, h_eq]
          · subst h1
            simp only [ZMod.val_one, mul_one, Nat.reduceAdd] at h_eq
            simp only [add_neg_cancel, zero_add, mul_one, neg_add_cancel, zero_ne_one, ↓reduceIte, h_eq]
      · clear h_bits2 h_bits3 h_bits4 h_bits5 h_bits6 h_bits7
        simp only [DecodedInstructionType.isEncodedCorrectly, mul_eq_zero]
        cases' h_bits0 with h0 h0
        · subst h0
          cases' h_bits1 with h1 h1
          · subst h1
            simp only [neg_zero, add_zero, mul_zero, or_self, and_self, one_ne_zero,
              zero_ne_one, and_true, and_false, or_false]
          · subst h1
            simp only [neg_zero, add_zero, add_neg_cancel, mul_one, zero_ne_one, one_ne_zero,
              or_false, and_true, and_false, and_self, or_true]
        · subst h0
          cases' h_bits1 with h1 h1
          · subst h1
            simp only [add_neg_cancel, neg_zero, add_zero, mul_zero, zero_ne_one, one_ne_zero,
              or_true, and_self, and_true, and_false, or_self, or_false]
          · subst h1
            simp only [add_neg_cancel, zero_add, mul_one, neg_add_cancel, zero_ne_one, one_ne_zero,
              or_self, and_false, and_self, or_true]
      · clear h_bits0 h_bits1 h_bits4 h_bits5 h_bits6 h_bits7
        simp only [DecodedAddressingMode.val]
        cases' h_bits2 with h0 h0
        · subst h0
          cases' h_bits3 with h1 h1
          · subst h1
            simp only [ZMod.val_zero, mul_zero, add_zero] at h_eq
            simp only [neg_zero, add_zero, mul_zero, ↓reduceIte, h_eq]
          · subst h1
            simp only [ZMod.val_zero, zero_add, ZMod.val_one, mul_one] at h_eq
            simp only [neg_zero, add_zero, add_neg_cancel, mul_one, zero_ne_one, ↓reduceIte, h_eq]
        · subst h0
          cases' h_bits3 with h1 h1
          · subst h1
            simp only [ZMod.val_one, ZMod.val_zero, mul_zero, add_zero] at h_eq
            simp only [add_neg_cancel, neg_zero, add_zero, mul_zero, zero_ne_one, ↓reduceIte, h_eq]
          · subst h1
            simp only [ZMod.val_one, mul_one, Nat.reduceAdd] at h_eq
            simp only [add_neg_cancel, zero_add, mul_one, neg_add_cancel, zero_ne_one, ↓reduceIte, h_eq]
      · clear h_bits0 h_bits1 h_bits4 h_bits5 h_bits6 h_bits7
        simp only [DecodedAddressingMode.isEncodedCorrectly, mul_eq_zero]
        cases' h_bits2 with h0 h0
        · subst h0
          cases' h_bits3 with h1 h1
          · subst h1
            simp only [mul_zero,
            add_zero,
            neg_zero, or_self, and_self, one_ne_zero, zero_ne_one, and_true, and_false, or_false]
          · subst h1
            simp only [
            mul_one,
            zero_ne_one, add_neg_cancel, one_ne_zero,
            or_false, false_and, and_false, and_self, false_or, neg_zero,
            add_zero]
        · subst h0
          cases' h_bits3 with h1 h1 <;> subst h1
          · simp only [
            mul_zero, add_zero,
            add_neg_cancel, neg_zero, zero_ne_one, one_ne_zero, or_true, and_self,
            and_true, true_or]
          · simp only [mul_one,
            add_neg_cancel, zero_add, neg_add_cancel, zero_ne_one, one_ne_zero,
            and_self, or_true]
      · clear h_bits0 h_bits1 h_bits2 h_bits3 h_bits6 h_bits7
        simp only [DecodedAddressingMode.val]
        cases' h_bits4 with h0 h0 <;> subst h0
        · cases' h_bits5 with h1 h1
          · subst h1
            simp only [ZMod.val_zero, mul_zero,
            add_zero] at h_eq
            simp only [neg_zero, add_zero, mul_zero, ↓reduceIte, h_eq]
          · subst h1
            simp only [ZMod.val_zero, ZMod.val_one,
            mul_one, zero_add] at h_eq
            simp only [neg_zero, add_zero, add_neg_cancel, mul_one, zero_ne_one, ↓reduceIte, h_eq]
        · cases' h_bits5 with h1 h1 <;> subst h1
          · simp only [ZMod.val_one, ZMod.val_zero,
            mul_zero, add_zero] at h_eq
            simp only [add_neg_cancel, neg_zero, add_zero, mul_zero, zero_ne_one, ↓reduceIte, h_eq]
          · simp only [ZMod.val_one, mul_one,
            Nat.reduceAdd] at h_eq
            simp only [add_neg_cancel, zero_add, mul_one, neg_add_cancel, zero_ne_one, ↓reduceIte,
              h_eq]
      · clear h_bits0 h_bits1 h_bits2 h_bits3 h_bits6 h_bits7
        simp only [DecodedAddressingMode.isEncodedCorrectly, mul_eq_zero]
        cases' h_bits4 with h0 h0 <;> subst h0
        · cases' h_bits5 with h1 h1 <;> subst h1
          · simp only [neg_zero, add_zero, mul_zero, or_self, and_self, one_ne_zero, zero_ne_one,
            and_true, and_false, or_false]
          · simp only [neg_zero, add_zero, add_neg_cancel, mul_one, zero_ne_one, one_ne_zero,
            or_false, and_true, and_false, and_self, or_true]
        · cases' h_bits5 with h1 h1 <;> subst h1
          · simp only [
            mul_zero, add_zero,
            add_neg_cancel, neg_zero, zero_ne_one, one_ne_zero, or_true, and_self,
            and_true, and_false, or_self, or_false]
          · simp only [mul_one,
            add_neg_cancel, zero_add, neg_add_cancel, zero_ne_one, one_ne_zero, false_or,
            and_self, and_false, or_true]
      · clear h_bits0 h_bits1 h_bits2 h_bits3 h_bits4 h_bits5
        simp only [DecodedAddressingMode.val]
        cases' h_bits6 with h0 h0 <;> subst h0
        · cases' h_bits7 with h1 h1 <;> subst h1
          · simp only [ZMod.val_zero, mul_zero, add_zero] at h_eq
            simp only [mul_zero,
            add_zero,
            neg_zero, ↓reduceIte, h_eq]
          · simp only [ZMod.val_zero, zero_add, ZMod.val_one, mul_one] at h_eq
            simp only [neg_zero, add_zero, add_neg_cancel, mul_one, zero_ne_one, ↓reduceIte, h_eq]
        · cases' h_bits7 with h1 h1 <;> subst h1
          · simp only [ZMod.val_zero, mul_zero, add_zero, ZMod.val_one] at h_eq
            simp only [
            mul_zero, add_zero,
            add_neg_cancel, neg_zero, zero_ne_one, ↓reduceIte, h_eq]
          · simp only [ZMod.val_one, mul_one, Nat.reduceAdd] at h_eq
            simp only [add_neg_cancel, zero_add, mul_one, neg_add_cancel, zero_ne_one, ↓reduceIte,
              h_eq]
      · clear h_bits0 h_bits1 h_bits2 h_bits3 h_bits4 h_bits5
        simp only [DecodedAddressingMode.isEncodedCorrectly, mul_eq_zero]
        cases' h_bits6 with h0 h0 <;> subst h0
        · cases' h_bits7 with h1 h1 <;> subst h1
          · simp only [mul_zero,
            add_zero,
            neg_zero, and_self, one_ne_zero, zero_ne_one, and_true, true_or]
          · simp only [
            mul_one,
            neg_zero, add_zero, add_neg_cancel, zero_ne_one, one_ne_zero, true_or,
            and_true, and_self, or_true]
        · cases' h_bits7 with h1 h1 <;> subst h1
          · simp only [
            mul_zero, add_zero,
            add_neg_cancel, neg_zero, zero_ne_one, one_ne_zero, or_true, and_self,
            and_true, true_or]
          · simp only [mul_one,
            add_neg_cancel, zero_add, neg_add_cancel, zero_ne_one, one_ne_zero, or_self,
            and_self, or_true]

  completeness := by
    sorry

/--
  Circuit that fetches a femtoCairo instruction from a read-only program memory,
  given the program counter.
  It returns a `RawInstruction` struct containing the raw instruction and its operands.
  The circuit uses lookups into a read-only table representing the program memory.
  This circuit is not satisfiable if the program counter is out of bounds.
-/
def fetchInstructionCircuit
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p) :
    FormalCircuit (F p) field RawInstruction where
  main := fun pc => do
    let programTable := ReadOnlyTableFromFunction program h_programSize

    let rawInstrType : Expression _ ← witness fun eval => program <| Fin.ofNat _ (eval pc).val
    let op1 ← witness fun eval => program <| Fin.ofNat _ (eval (pc + 1)).val
    let op2 ← witness fun eval => program <| Fin.ofNat _ (eval (pc + 2)).val
    let op3 ← witness fun eval => program <| Fin.ofNat _ (eval (pc + 3)).val

    lookup programTable ⟨pc, rawInstrType⟩
    lookup programTable ⟨pc + 1, op1⟩
    lookup programTable ⟨pc + 2, op2⟩
    lookup programTable ⟨pc + 3, op3⟩

    return { rawInstrType, op1, op2, op3 }

  localLength _ := 4
  yields_eq := by intros; simp only [circuit_norm, Set.empty_union]
  Assumptions | pc, _ => True
  Spec
  | pc, output, _ =>
    match Spec.fetchInstruction program pc with
      | some claimed_output => output = claimed_output
      | none => False -- impossible, lookups ensure that memory accesses are valid
  soundness := by
    circuit_proof_start [ReadOnlyTableFromFunction, Spec.fetchInstruction, Spec.memoryAccess]
    split

    -- the lookups imply that the memory accesses are valid, therefore
    -- here we prove that Spec.memoryAccess never returns none
    case h_2 x h_eq =>
      -- does reading the type return some or none?
      split at h_eq
      · -- does reading op1 return some or none?
        split at h_eq
        · -- does reading op2 return some or none?
          split at h_eq
          · -- does reading op3 return some or none?
            split at h_eq
            · simp_all only [gt_iff_lt, id_eq, Fin.ofNat_eq_cast, and_true, Option.bind_eq_bind,
              Option.bind_some, reduceCtorEq]
            · simp_all only [gt_iff_lt, id_eq, Fin.ofNat_eq_cast, and_false]
          · simp_all only [gt_iff_lt, id_eq, Fin.ofNat_eq_cast, and_false, false_and]
        · simp_all only [gt_iff_lt, id_eq, Fin.ofNat_eq_cast, and_false, false_and]
      · simp_all only [gt_iff_lt, id_eq, Fin.ofNat_eq_cast, and_false, false_and]

    case h_1 rawInstrType claimed_instruction instruction h_eq =>
      simp_all [circuit_norm, explicit_provable_type]
      -- obtain ⟨ h_eq_type, h_eq_op1, h_eq_op2, h_eq_op3 ⟩ := h_eq
      rw [←h_eq]

      simp only [and_assoc] at h_holds
      obtain ⟨ h1, h1', h2, h2', h3, h3', h4, h4' ⟩ := h_holds

      congr <;>
      · rw [←Fin.val_eq_val]
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt h1',
          Nat.mod_eq_of_lt h2', Nat.mod_eq_of_lt h3', Nat.mod_eq_of_lt h4']
  completeness := by
    sorry

/--
  Circuit that reads a value from a read-only memory, given a state, an offset,
  and an addressing mode.
  It returns the value read from memory, according to the addressing mode.
  - If the addressing is a double addressing, it reads the value at `memory[memory[ap + offset]]`.
  - If the addressing is ap-relative, it reads the value at `memory[ap + offset]`.
  - If the addressing is fp-relative, it reads the value at `memory[fp + offset]`.
  - If the addressing is immediate, it returns the offset itself.
  The circuit uses lookups into a read-only table representing the memory.
  This circuit is not satisfiable if any memory access is out of bounds.
-/
def readFromMemoryCircuit
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalCircuit (F p) MemoryReadInput field where
  main := fun { state, offset, mode } => do
    let memoryTable := ReadOnlyTableFromFunction memory h_memorySize

    -- read into memory for all cases of addressing mode
    let v1_tmp : Expression _ ← witness fun eval => memory <| Fin.ofNat _ (eval (state.ap + offset)).val
    let v1 : Expression _ ← witness fun eval => memory <| Fin.ofNat _ (eval v1_tmp).val
    let v2 : Expression _ ← witness fun eval =>  memory <| Fin.ofNat _ (eval (state.ap + offset)).val
    let v3 : Expression _ ← witness fun eval =>  memory <| Fin.ofNat _ (eval (state.fp + offset)).val
    lookup memoryTable ⟨(state.ap + offset), v1_tmp⟩
    lookup memoryTable ⟨v1_tmp, v1⟩
    lookup memoryTable ⟨(state.ap + offset), v2⟩
    lookup memoryTable ⟨(state.fp + offset), v3⟩

    -- select the correct value based on the addressing mode
    let value <==
      mode.isDoubleAddressing * v1 +
      mode.isApRelative * v2 +
      mode.isFpRelative * v3 +
      mode.isImmediate * offset

    return value

  localLength _ := 5
  yields_eq _ _ _ := by simp [circuit_norm]
  Assumptions | {state, mode, offset}, _ => DecodedAddressingMode.isEncodedCorrectly mode
  Spec
  | {state, offset, mode}, output, _ =>
    match Spec.dataMemoryAccess memory offset (DecodedAddressingMode.val mode) state.ap state.fp with
      | some value => output = value
      | none => False -- impossible, constraints ensure that memory accesses are valid
  soundness := by
    circuit_proof_start [ReadOnlyTableFromFunction, Spec.dataMemoryAccess,
      Spec.memoryAccess, DecodedAddressingMode.val, DecodedAddressingMode.isEncodedCorrectly]

    -- circuit_proof_start did not unpack those, so we manually unpack here
    obtain ⟨isDoubleAddressing, isApRelative, isFpRelative, isImmediate⟩ := input_mode
    obtain ⟨_pc, ap, fp⟩ := input_state

    simp only [Fin.ofNat_eq_cast, id_eq, eval, fromElements, size, toVars, toElements,
      Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
      ↓List.getElem_toArray, ↓List.getElem_cons_zero, ↓List.getElem_cons_succ, State.mk.injEq,
      DecodedAddressingMode.mk.injEq] at h_holds h_input
    simp only [h_input] at h_holds
    simp only [Option.bind_eq_bind, id_eq]

    -- does the memory accesses return some or none?
    split

    -- the lookups imply that the memory accesses are valid, therefore
    -- here we prove that Spec.memoryAccess never returns none
    case h_2 x h_eq =>
      simp only [and_assoc] at h_holds
      obtain ⟨ h1, h1', h2, h2', h3, h3', h4, h4', h_final_constraint ⟩ := h_holds

      split at h_eq
      · have h1'' := h1'
        simp_all only [gt_iff_lt, ite_eq_left_iff, ↓reduceDIte, Option.bind_some, dite_eq_right_iff,
          reduceCtorEq, imp_false, not_lt]
        have contradiction := Nat.not_le_of_lt h2'
        rw [←Fin.mk_val (@Nat.cast (Fin memorySize) (Fin.NatCast.instNatCast memorySize) (ZMod.val (ap + input_offset)))] at contradiction
        simp_all only [Fin.val_natCast, Nat.mod_eq_of_lt h1'', not_true_eq_false]
      · simp_all only [gt_iff_lt, ↓reduceDIte, reduceCtorEq]
      · simp_all only [gt_iff_lt, ↓reduceDIte, reduceCtorEq]
      · simp_all only [gt_iff_lt, reduceCtorEq]

    -- handle the case where all memory accesses are valid
    case h_1 rawInstrType _ _ value h_eq =>
      simp only [and_assoc] at h_holds
      obtain ⟨ h1, h1', h2, h2', h3, h3', h4, h4', h_final_constraint ⟩ := h_holds

      -- by cases on the addressing mode, the proof for each case is pretty simple
      rcases h_assumptions with isDoubleAddressing_cases | isApRelative_cases | isFpRelative_cases | isImmediate_cases
      · simp_all [gt_iff_lt, ↓reduceDIte, Option.bind_some, one_mul, zero_mul, add_zero,
        ↓reduceIte, Option.dite_none_right_eq_some, Option.some.injEq]
        obtain ⟨h, h_eq⟩ := h_eq
        rw [← h_eq]
        -- first addressing
        congr
        rw [←Fin.val_eq_val]
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt h2']
        -- second addressing
        congr
        rw [←Fin.val_eq_val]
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt h1']
      · simp_all only [gt_iff_lt, ↓reduceDIte, Option.bind_some, zero_mul, one_mul, zero_add,
        add_zero, zero_ne_one, ↓reduceIte, Option.some.injEq]
        rw [← h_eq]
        congr
        rw [←Fin.val_eq_val]
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt h3']
      · simp_all only [gt_iff_lt, ↓reduceDIte, Option.bind_some, zero_mul, add_zero, one_mul,
        zero_add, zero_ne_one, ↓reduceIte, Option.some.injEq]
        rw [← h_eq]
        congr
        rw [←Fin.val_eq_val]
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt h4']
      · simp_all only [gt_iff_lt, ↓reduceDIte, Option.bind_some, zero_mul, add_zero, one_mul,
        zero_add, zero_ne_one, ↓reduceIte, Option.some.injEq]

  completeness := by
    sorry

/--
  Circuit that computes the next state of the femtoCairo VM, given the current state,
  a decoded instruction, and the values of the three operands.
  The circuit enforces constraints based on the current instruction type to ensure that
  the state transition is valid, therefore this circuit is not satisfiable
  if the claimed state transition is invalid.
  Returns the next state.
-/
def nextStateCircuit : FormalCircuit (F p) StateTransitionInput State where
  main := fun { state, decoded, v1, v2, v3 } => do
    -- Witness the claimed next state
    let nextState : State _ ← ProvableType.witness fun eval => {
      pc := if eval decoded.instrType.isLoadState = 1 then eval v1 else eval state.pc + 4
      ap := if eval decoded.instrType.isLoadState = 1 then eval v2 else eval state.ap
      fp := if eval decoded.instrType.isLoadState = 1 then eval v3 else eval state.fp
    }

    assertZero (decoded.instrType.isAdd * (v3 - (v1 + v2)))

    assertZero (decoded.instrType.isMul * (v3 - (v1 * v2)))

    assertZero (decoded.instrType.isStoreState * (v1 - state.pc))
    assertZero (decoded.instrType.isStoreState * (v2 - state.ap))
    assertZero (decoded.instrType.isStoreState * (v3 - state.fp))

    assertZero (decoded.instrType.isLoadState * (nextState.pc - v1))
    assertZero (decoded.instrType.isLoadState * (nextState.ap - v2))
    assertZero (decoded.instrType.isLoadState * (nextState.fp - v3))

    assertZero ((1 - decoded.instrType.isLoadState) * (nextState.pc - (state.pc + 4)))
    assertZero ((1 - decoded.instrType.isLoadState) * (nextState.ap - state.ap))
    assertZero ((1 - decoded.instrType.isLoadState) * (nextState.fp - state.fp))

    return nextState

  localLength _ := 3
  Assumptions | {state, decoded, v1, v2, v3}, _ => DecodedInstructionType.isEncodedCorrectly decoded.instrType
  Spec
  | {state, decoded, v1, v2, v3}, output, _ =>
    match Spec.computeNextState (DecodedInstructionType.val decoded.instrType) v1 v2 v3 state with
      | some nextState => output = nextState
      | none => False -- impossible, constraints ensure that the transition is valid
  soundness := by
    circuit_proof_start [DecodedInstructionType.isEncodedCorrectly, Spec.computeNextState, DecodedInstructionType.val]

    -- unpack the decoded instruction type
    obtain ⟨isAdd, isMul, isStoreState, isLoadState⟩ := input_decoded_instrType
    obtain ⟨pc, ap, fp⟩ := input_state

    obtain ⟨h_input_state, h_input_decoded, h_input_memoryValues⟩ := h_input
    simp [circuit_norm, explicit_provable_type] at h_input_decoded h_input_state h_holds ⊢

    obtain ⟨h_input_decoded_isAdd, h_input_decoded_isMul, h_input_decoded_isStoreState, h_input_decoded_isLoadState⟩ := h_input_decoded
    obtain ⟨h_input_state_pc, h_input_state_ap, h_input_state_fp⟩ := h_input_state

    rw [h_input_state_pc, h_input_state_ap, h_input_state_fp] at h_holds

    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := h_holds

    simp_all only [gt_iff_lt]

    -- give names to the next state for readability
    set pc_next := env.get i₀
    set ap_next := env.get (i₀ + 1)
    set fp_next := env.get (i₀ + 2)

    -- case analysis on the instruction type
    rcases h_assumptions with isAdd_cases | isMul_cases | isStoreState_cases | isLoadState_cases

    -- prove the ADD case
    · simp_all only [one_ne_zero, false_or, true_or, neg_zero, add_zero, ↓reduceIte]
      rw [add_eq_zero_iff_eq_neg] at c0 c8 c9 c10
      -- does the transition return some or none for the ADD case?
      split
      case h_1 nextState h_eq =>
        simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h_eq
        simp only [c8, neg_add_rev, neg_neg, c9, c10]
        rw [←h_eq.right]
      case h_2 h_eq =>
        simp_all only [neg_add_rev, neg_neg, ↓reduceIte, reduceCtorEq]

    -- prove the MUL case
    · simp_all only [true_or, one_ne_zero, false_or, neg_zero, add_zero, zero_ne_one, ↓reduceIte]
      rw [add_eq_zero_iff_eq_neg] at c1 c8 c9 c10
      -- does the transition return some or none for the MUL case?
      split
      case h_1 nextState h_eq =>
        simp_all only [neg_neg, neg_add_rev, ↓reduceIte, Option.some.injEq]
      case h_2 h_eq =>
        simp_all only [neg_add_rev, neg_neg, ↓reduceIte, reduceCtorEq]

    -- prove the STORE_STATE case
    · simp_all only [true_or, one_ne_zero, false_or, neg_zero, add_zero, zero_ne_one, ↓reduceIte]
      rw [add_eq_zero_iff_eq_neg] at c2 c3 c4 c8 c9 c10
      -- does the transition return some or none for the STORE_STATE case?
      split
      case h_1 nextState h_eq =>
        simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h_eq
        rw [←h_eq.right]
        simp only [c8, neg_add_rev, neg_neg, c9, c10]
      case h_2 h_eq =>
        simp_all only [neg_neg, neg_add_rev, and_self, ↓reduceIte, reduceCtorEq]

    -- prove the LOAD_STATE case
    · simp_all only [true_or, one_ne_zero, false_or, add_neg_cancel, zero_ne_one, ↓reduceIte,
      State.mk.injEq]
      rw [add_eq_zero_iff_eq_neg, neg_neg] at c5 c6 c7
      rw [c5, c6, c7]
      simp only [and_self]
  completeness := by
    sorry
/--
  The main femtoCairo step circuit, which combines instruction fetch, decode,
  memory accesses, and state transition into a single circuit.
  Given a read-only program memory and a read-only data memory, it takes the current state
  as input and returns the next state as output.
  The circuit is not satisfiable if the state transition is invalid.
-/
def femtoCairoStepElaboratedCircuit
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) State State where
    main := fun state => do
      -- Fetch instruction
      let { rawInstrType, op1, op2, op3 } ← subcircuit (fetchInstructionCircuit program h_programSize) state.pc

      -- Decode instruction
      let decoded ← subcircuit decodeInstructionCircuit rawInstrType

      -- Perform relevant memory accesses
      let v1 ← subcircuit (readFromMemoryCircuit memory h_memorySize) { state, offset := op1, mode := decoded.addr1 }
      let v2 ← subcircuit (readFromMemoryCircuit memory h_memorySize) { state, offset := op2, mode := decoded.addr2 }
      let v3 ← subcircuit (readFromMemoryCircuit memory h_memorySize) { state, offset := op3, mode := decoded.addr3 }

      -- Compute next state
      nextStateCircuit { state, decoded, v1, v2, v3 }
    localLength := 30
    yields_eq := by
      simp only [circuit_norm, readFromMemoryCircuit, fetchInstructionCircuit, nextStateCircuit, decodeInstructionCircuit, decodeInstructionElaborated]
      simp only [Set.union_self, implies_true]

def femtoCairoCircuitSpec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (state : State (F p)) (nextState : State (F p)) (_ : Set (NamedList (F p))) : Prop :=
  match Spec.femtoCairoMachineTransition program memory state with
    | some s => s = nextState
    | none => False -- impossible, constraints ensure that the transition is valid

def femtoCairoAssumptions (_state : State (F p)) (_ : Set (NamedList (F p))) : Prop :=
  True

def femtoCairoStepCircuitSoundness
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    : Soundness (F p) (femtoCairoStepElaboratedCircuit program h_programSize memory h_memorySize) femtoCairoAssumptions (femtoCairoCircuitSpec program memory) := by
  circuit_proof_start [femtoCairoCircuitSpec, femtoCairoAssumptions, femtoCairoStepElaboratedCircuit,
    Spec.femtoCairoMachineTransition, fetchInstructionCircuit, readFromMemoryCircuit, nextStateCircuit, decodeInstructionCircuit]

  obtain ⟨pc_var, ap_var, fp_var⟩ := input_var
  obtain ⟨pc, ap, fp⟩ := input
  simp [circuit_norm, explicit_provable_type] at h_input
  obtain ⟨h_input_pc, h_input_ap, h_input_fp⟩ := h_input

  obtain ⟨ c_fetch, c_decode, c_read1, c_read2, c_read3, c_next ⟩ := h_holds

  split at c_fetch
  case h_2 =>
    -- impossible, fetchInstructionCircuit ensures that
    -- instruction fetch is always successful
    contradiction
  case h_1 raw_instruction h_eq =>
    rw [h_input_pc] at h_eq
    rw [h_eq, ←c_fetch]
    simp [circuit_norm, explicit_provable_type]
    simp only [decodeInstructionSpec] at c_decode

    split at c_decode
    case h_2 =>
      -- impossible, decodeInstructionCircuit ensures that
      -- instruction decode is always successful
      contradiction
    case h_1 instr_type addr1 addr2 addr3 h_eq_decode =>
      rw [h_eq_decode]
      obtain ⟨ h_instr_type_val, h_instr_type_encoded_correctly, h_addr1_val,
        h_addr1_encoded_correctly, h_addr2_val, h_addr2_encoded_correctly,
        h_addr3_val, h_addr3_encoded_correctly ⟩ := c_decode
      simp [circuit_norm, explicit_provable_type]

      -- satisfy assumptions of read1
      specialize c_read1 h_addr1_encoded_correctly
      rw [h_addr1_val] at c_read1

      -- satisfy assumptions of read2
      specialize c_read2 h_addr2_encoded_correctly
      rw [h_addr2_val] at c_read2

      -- satisfy assumptions of read3
      specialize c_read3 h_addr3_encoded_correctly
      rw [h_addr3_val] at c_read3

      -- satisfy assumptions of next
      specialize c_next h_instr_type_encoded_correctly
      rw [h_instr_type_val] at c_next

      split at c_read1
      case h_2 =>
        -- impossible, readFromMemory ensures that
        -- memory access is always successful
        contradiction
      case h_1 v1 h_eq_v1 =>
        rw [h_eq_v1, ←c_read1]
        split at c_read2
        case h_2 =>
          -- impossible, readFromMemory ensures that
          -- memory access is always successful
          contradiction
        case h_1 v2 h_eq_v2 =>
          rw [h_eq_v2, ←c_read2]
          split at c_read3
          case h_2 =>
            -- impossible, readFromMemory ensures that
            -- memory access is always successful
            contradiction
          case h_1 v3 h_eq_v3 =>
            rw [h_eq_v3, ←c_read3]
            simp [circuit_norm, explicit_provable_type]

            split at c_next
            case h_2 =>
              -- impossible, nextState ensures that
              -- state transition is always successful
              contradiction
            case h_1 next_state h_eq_next =>
              simp only [decodeInstructionElaborated] at c_next ⊢ h_eq_next
              simp only [h_eq_next]
              rw [←c_next]
              simp [explicit_provable_type, circuit_norm]

def femtoCairoStepCircuit
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    : FormalCircuit (F p) State State := {
      femtoCairoStepElaboratedCircuit program h_programSize memory h_memorySize with
      Assumptions := femtoCairoAssumptions,
      Spec := femtoCairoCircuitSpec program memory,
      soundness := femtoCairoStepCircuitSoundness program h_programSize memory h_memorySize,
      completeness := by sorry
    }

/--
  The femtoCairo table, which defines the step relation for the femtoCairo VM.
  Given a read-only program memory and a read-only data memory, it defines
  the step relation on states of the femtoCairo VM.

  Proving knowledge of a table of length `n` proves the following statement:
  the prover knows a memory function such that the bounded execution of the femtoCairo VM
  for `n` steps from the given initial state, using the given program memory, does not
  return `none`.
-/
def femtoCairoTable
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    : InductiveTable (F p) State unit where
  step state _ := do
    femtoCairoStepCircuit program h_programSize memory h_memorySize state

  Spec initial_state _ i _ state : Prop := match
      Spec.femtoCairoMachineBoundedExecution program memory (some initial_state) i with
    | some reachedState => state = reachedState
    | none => False -- impossible, constraints ensure that every transition is valid

  soundness := by
    intros initial_state i env yielded state_var input_var state input h1 h2 h_inputs h_hold
    simp [Spec.femtoCairoMachineBoundedExecution, femtoCairoStepCircuit,
      femtoCairoCircuitSpec, femtoCairoAssumptions, circuit_norm] at ⊢ h_hold
    split at h_hold
    case h_2 =>
      contradiction
    case h_1 next_state h_eq =>
      rw [h_inputs.left] at h_eq
      split
      case h_2 =>
        intros
        contradiction
      case h_1 reached_state h_eq_reached =>
        intro ih
        rw [ih] at h_eq
        rw [h_eq_reached]
        simp only [Option.bind_some]
        rw [h_eq]
        simp only [h_hold]

  completeness := by sorry


/--
  The formal table for the femtoCairo VM, which ensures that the execution starts with
  the default initial state (pc=0, ap=0, fp=0)
-/
def femtoCairoFormalTable
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (output : State (F p)) := (femtoCairoTable program h_programSize memory h_memorySize).toFormal {
  pc := 0,
  ap := 0,
  fp := 0
} output

/--
  The table's statement implies that the state at each row is exactly the state reached by the
  femtoCairo machine after executing that many steps from the initial state.
  In particular, the bounded execution does not return `none`, which means that
  the execution is successful for that many steps.
-/
theorem femtoCairoTableStatement
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
  (state : State (F p)) : ∀ n > 0, ∀ trace,
  (femtoCairoFormalTable program h_programSize memory h_memorySize state).statement n trace →
    match
      Spec.femtoCairoMachineBoundedExecution program memory (some {pc:=0, ap:=0, fp:=0}) (n - 1) with
    | some reachedState => state = reachedState
    | none => False -- impossible, constraints ensure that every transition is valid
  := by
  intro n hn trace Spec
  simp only [FormalTable.statement, femtoCairoFormalTable,
    InductiveTable.toFormal, femtoCairoTable, FemtoCairo.Spec.femtoCairoMachineBoundedExecution] at Spec
  simp_all only [gt_iff_lt, and_self, forall_const]

end Examples.FemtoCairo
