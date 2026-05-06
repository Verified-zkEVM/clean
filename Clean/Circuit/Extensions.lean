/- This file contains experimental additions to the Circuit DSL -/
import Clean.Circuit.Subcircuit

variable {F : Type} [Field F] {α : TypeMap} [ProvableType α]

instance {α : TypeMap} [ProvableType α] : Inhabited (Circuit F (Var α F)) where
  default := witness default

def copyToVar (x : Expression F) : Circuit F (Variable F) := do
  let x' ← witnessVar x.eval
  assertZero (x - (var x'))
  return x'

def toVar : Expression F → Circuit F (Variable F)
  | var v => pure v
  | x => copyToVar x

-- these could be used if you want to witness _any_ value and don't care which
-- (typically useless, because in completeness proofs you will often have to prove some assumption about the value)

@[circuit_norm]
def getOffset : Circuit F ℕ := fun n => (n, [])

def valueFromOffset (α : TypeMap) [ProvableType α] (offset : ℕ) (env : Environment F) : α F :=
  fromElements <| .mapRange _ fun i => env.get (offset + i)

theorem eval_varFromOffset_valueFromOffset (α : TypeMap) [ProvableType α] (offset : ℕ) (env : Environment F) :
    Eval.eval env (varFromOffset (F:=F) α offset) = valueFromOffset α offset env := by
  rw [ProvableType.eval_varFromOffset, valueFromOffset]

def witnessAny (α: TypeMap) [ProvableType α] : Circuit F (Var α F) := do
  let offset ← getOffset
  witness fun env => valueFromOffset α offset env

theorem witnessAny_localWitnesses (n : ℕ) (env : ProverEnvironment F) :
    env.UsesLocalWitnessesCompleteness n (witnessAny α |>.operations n) ↔ True := by
  simp only [circuit_norm, getOffset, witnessAny, valueFromOffset,
    ProvableType.toElements_fromElements]

@[circuit_norm]
theorem witnessAny_output {n : ℕ} :
    (witnessAny (F:=F) α |>.output n) = varFromOffset α n  := by
  simp only [circuit_norm, getOffset, witnessAny, valueFromOffset,
    ProvableType.toElements_fromElements]
