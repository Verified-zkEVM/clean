/- This file contains miscellaneous additions and helpers on top of the Circuit DSL -/
import Clean.Circuit.Subcircuit

variable {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]

instance {M : TypeMap} [ProvableType M] : Inhabited (Circuit F (Var M F)) where
  default := witnessIR M (.ofFExprs default)

def copyToVar (x : Expression F) : Circuit F (Variable F) := do
  let x' ← witnessVar (.ofFExpr (.expr x))
  assertZero (x - (var x'))
  return x'

def toVar : Expression F → Circuit F (Variable F)
  | var v => pure v
  | x => copyToVar x

-- these could be used if you want to witness _any_ value and don't care which
-- (typically useless, because in completeness proofs you will often have to prove some assumption about the value)

@[circuit_norm]
def getOffset : Circuit F ℕ := fun n => (n, [])

def valueFromOffset (M : TypeMap) [ProvableType M] (offset : ℕ) (env : Environment F) : M F :=
  fromElements <| .mapRange _ fun i => env.get (offset + i)

theorem eval_varFromOffset_valueFromOffset (M : TypeMap) [ProvableType M] (offset : ℕ) (env : Environment F) :
    Eval.eval env (varFromOffset (F:=F) M offset) = valueFromOffset M offset env := by
  rw [ProvableType.eval_varFromOffset, valueFromOffset]

def witnessAny (M: TypeMap) [ProvableType M] : Circuit F (Var M F) := do
  let offset ← getOffset
  witnessIR M (.ir [] (.range (size M) fun i => .envGet (offset + i)))

theorem witnessAny_localWitnesses (n : ℕ) (env : ProverEnvironment F) :
    env.UsesLocalWitnessesCompleteness n (witnessAny M |>.operations n) ↔ True := by
  simp only [circuit_norm, getOffset, witnessAny]

@[circuit_norm]
theorem witnessAny_output {n : ℕ} :
    (witnessAny (F:=F) M |>.output n) = varFromOffset M n  := by
  simp only [circuit_norm, getOffset, witnessAny]

@[circuit_norm]
theorem witnessAny_interactionsWith {n : ℕ} {channel : RawChannel F} :
    (witnessAny M |>.operations n).interactionsWith channel = [] := by
  simp [circuit_norm, witnessAny, Operations.interactionsWith]
