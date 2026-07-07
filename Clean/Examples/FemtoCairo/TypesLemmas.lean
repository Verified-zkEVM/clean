import Clean.Examples.FemtoCairo.Types

/-!
# Helper lemmas for FemtoCairo types

This file contains lemmas about the FemtoCairo types that are used
in circuit proofs.
-/

namespace Examples.FemtoCairo.Types

@[ext]
lemma State.ext {F : Type} {s1 s2 : State F} (h1 : s1.pc = s2.pc) (h2 : s1.ap = s2.ap) (h3 : s1.fp = s2.fp) : s1 = s2 := by
  cases s1; cases s2; simp_all only

section StateEval
variable {F : Type} [FiniteField F]

/-- Evaluating a State variable and extracting pc equals evaluating the pc expression -/
@[circuit_norm]
lemma State.eval_pc (env : Environment F) (s : Var State F) :
    (eval env s).pc = Expression.eval env s.pc := by
  obtain ⟨pc, ap, fp⟩ := s
  simp [circuit_norm, explicit_provable_type]

/-- Evaluating a State variable and extracting ap equals evaluating the ap expression -/
@[circuit_norm]
lemma State.eval_ap (env : Environment F) (s : Var State F) :
    (eval env s).ap = Expression.eval env s.ap := by
  obtain ⟨pc, ap, fp⟩ := s
  simp [circuit_norm, explicit_provable_type]

/-- Evaluating a State variable and extracting fp equals evaluating the fp expression -/
@[circuit_norm]
lemma State.eval_fp (env : Environment F) (s : Var State F) :
    (eval env s).fp = Expression.eval env s.fp := by
  obtain ⟨pc, ap, fp⟩ := s
  simp [circuit_norm, explicit_provable_type]

end StateEval

section RawInstructionEval
variable {F : Type} [FiniteField F]

/-- Evaluating a RawInstruction variable and extracting rawInstrType equals evaluating the rawInstrType expression -/
@[circuit_norm]
lemma RawInstruction.eval_rawInstrType (env : Environment F) (r : Var RawInstruction F) :
    (eval env r).rawInstrType = Expression.eval env r.rawInstrType := by
  obtain ⟨rawInstrType, op1, op2, op3⟩ := r
  simp [circuit_norm, explicit_provable_type]

/-- Evaluating a RawInstruction variable and extracting op1 equals evaluating the op1 expression -/
@[circuit_norm]
lemma RawInstruction.eval_op1 (env : Environment F) (r : Var RawInstruction F) :
    (eval env r).op1 = Expression.eval env r.op1 := by
  obtain ⟨rawInstrType, op1, op2, op3⟩ := r
  simp [circuit_norm, explicit_provable_type]

/-- Evaluating a RawInstruction variable and extracting op2 equals evaluating the op2 expression -/
@[circuit_norm]
lemma RawInstruction.eval_op2 (env : Environment F) (r : Var RawInstruction F) :
    (eval env r).op2 = Expression.eval env r.op2 := by
  obtain ⟨rawInstrType, op1, op2, op3⟩ := r
  simp [circuit_norm, explicit_provable_type]

/-- Evaluating a RawInstruction variable and extracting op3 equals evaluating the op3 expression -/
@[circuit_norm]
lemma RawInstruction.eval_op3 (env : Environment F) (r : Var RawInstruction F) :
    (eval env r).op3 = Expression.eval env r.op3 := by
  obtain ⟨rawInstrType, op1, op2, op3⟩ := r
  simp [circuit_norm, explicit_provable_type]

end RawInstructionEval

section DecodedEval
variable {F : Type} [FiniteField F]

/-! `eval`-projection lemmas for the decoded-instruction structs, so hypotheses that mention
per-field evaluations and hypotheses that mention the whole-struct evaluation normalize to the
same form. -/

@[circuit_norm]
lemma DecodedInstruction.eval_instrType (env : Environment F) (d : Var DecodedInstruction F) :
    (eval env d).instrType = eval env d.instrType := by
  obtain ⟨instrType, mode1, mode2, mode3⟩ := d
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedInstruction.eval_mode1 (env : Environment F) (d : Var DecodedInstruction F) :
    (eval env d).mode1 = eval env d.mode1 := by
  obtain ⟨instrType, mode1, mode2, mode3⟩ := d
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedInstruction.eval_mode2 (env : Environment F) (d : Var DecodedInstruction F) :
    (eval env d).mode2 = eval env d.mode2 := by
  obtain ⟨instrType, mode1, mode2, mode3⟩ := d
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedInstruction.eval_mode3 (env : Environment F) (d : Var DecodedInstruction F) :
    (eval env d).mode3 = eval env d.mode3 := by
  obtain ⟨instrType, mode1, mode2, mode3⟩ := d
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedAddressingMode.eval_isDoubleAddressing (env : Environment F) (m : Var DecodedAddressingMode F) :
    (eval env m).isDoubleAddressing = eval env m.isDoubleAddressing := by
  obtain ⟨a, b, c, d⟩ := m
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedAddressingMode.eval_isApRelative (env : Environment F) (m : Var DecodedAddressingMode F) :
    (eval env m).isApRelative = eval env m.isApRelative := by
  obtain ⟨a, b, c, d⟩ := m
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedAddressingMode.eval_isFpRelative (env : Environment F) (m : Var DecodedAddressingMode F) :
    (eval env m).isFpRelative = eval env m.isFpRelative := by
  obtain ⟨a, b, c, d⟩ := m
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedAddressingMode.eval_isImmediate (env : Environment F) (m : Var DecodedAddressingMode F) :
    (eval env m).isImmediate = eval env m.isImmediate := by
  obtain ⟨a, b, c, d⟩ := m
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedInstructionType.eval_isAdd (env : Environment F) (t : Var DecodedInstructionType F) :
    (eval env t).isAdd = eval env t.isAdd := by
  obtain ⟨a, b, c, d⟩ := t
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedInstructionType.eval_isMul (env : Environment F) (t : Var DecodedInstructionType F) :
    (eval env t).isMul = eval env t.isMul := by
  obtain ⟨a, b, c, d⟩ := t
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedInstructionType.eval_isStoreState (env : Environment F) (t : Var DecodedInstructionType F) :
    (eval env t).isStoreState = eval env t.isStoreState := by
  obtain ⟨a, b, c, d⟩ := t
  simp [circuit_norm, explicit_provable_type]

@[circuit_norm]
lemma DecodedInstructionType.eval_isLoadState (env : Environment F) (t : Var DecodedInstructionType F) :
    (eval env t).isLoadState = eval env t.isLoadState := by
  obtain ⟨a, b, c, d⟩ := t
  simp [circuit_norm, explicit_provable_type]

end DecodedEval

end Examples.FemtoCairo.Types
