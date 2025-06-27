/- This file contains experimental additions to the Circuit DSL -/
import Clean.Circuit.Constant

variable {F : Type} [Field F] {α: TypeMap} [ProvableType α]

instance {α: TypeMap} [ProvableType α] : Inhabited (Circuit F (Var α F)) where
  default := witness default

def copyToVar (x: Expression F) : Circuit F (Variable F) := do
  let x' ← witnessVar x.eval
  assertZero (x - (var x'))
  return x'

def toVar : Expression F → Circuit F (Variable F)
  | var v => pure v
  | x => copyToVar x

-- these could be used if you want to witness _any_ value and don't care which
-- (typically useless, because in completeness proofs you will often have to prove some assumption about the value)

def getOffset : Circuit F ℕ := fun n => (n, [])

def computeValueFromOffset (α : TypeMap) [ProvableType α] (offset : ℕ) (env : Environment F) : α F :=
  fromElements <| .mapRange _ fun i => env.get (offset + i)

def ProvableType.witnessAny (α: TypeMap) [ProvableType α] : Circuit F (Var α F) := do
  let offset ← getOffset
  witness (computeValueFromOffset α offset)

theorem ProvableType.witnessAny.localWitnesses (n : ℕ) (env : Environment F) :
    env.UsesLocalWitnessesCompleteness n (ProvableType.witnessAny α |>.operations n) ↔ True := by
  simp only [circuit_norm, getOffset, ProvableType.witnessAny, computeValueFromOffset,
    ProvableType.toElements_fromElements]
