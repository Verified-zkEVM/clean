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
variable {F : Type} [Field F]

/-- Evaluating a State variable and extracting pc equals evaluating the pc expression -/
@[circuit_norm]
lemma State.eval_pc (env : Environment F) (s : Var State F) :
    (ProvableType.eval env s).pc = Expression.eval env s.pc := rfl

/-- Evaluating a State variable and extracting ap equals evaluating the ap expression -/
@[circuit_norm]
lemma State.eval_ap (env : Environment F) (s : Var State F) :
    (ProvableType.eval env s).ap = Expression.eval env s.ap := rfl

/-- Evaluating a State variable and extracting fp equals evaluating the fp expression -/
@[circuit_norm]
lemma State.eval_fp (env : Environment F) (s : Var State F) :
    (ProvableType.eval env s).fp = Expression.eval env s.fp := rfl

end StateEval

section RawInstructionEval
variable {F : Type} [Field F]

/-- Evaluating a RawInstruction variable and extracting rawInstrType equals evaluating the rawInstrType expression -/
@[circuit_norm]
lemma RawInstruction.eval_rawInstrType (env : Environment F) (r : Var RawInstruction F) :
    (ProvableType.eval env r).rawInstrType = Expression.eval env r.rawInstrType := rfl

/-- Evaluating a RawInstruction variable and extracting op1 equals evaluating the op1 expression -/
@[circuit_norm]
lemma RawInstruction.eval_op1 (env : Environment F) (r : Var RawInstruction F) :
    (ProvableType.eval env r).op1 = Expression.eval env r.op1 := rfl

/-- Evaluating a RawInstruction variable and extracting op2 equals evaluating the op2 expression -/
@[circuit_norm]
lemma RawInstruction.eval_op2 (env : Environment F) (r : Var RawInstruction F) :
    (ProvableType.eval env r).op2 = Expression.eval env r.op2 := rfl

/-- Evaluating a RawInstruction variable and extracting op3 equals evaluating the op3 expression -/
@[circuit_norm]
lemma RawInstruction.eval_op3 (env : Environment F) (r : Var RawInstruction F) :
    (ProvableType.eval env r).op3 = Expression.eval env r.op3 := rfl

end RawInstructionEval

end Examples.FemtoCairo.Types
