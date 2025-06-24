/- This file contains experimental additions to the Circuit DSL -/
import Clean.Circuit.Constant

variable {F : Type} [Field F] {α: TypeMap} [ProvableType α]

instance {α: TypeMap} [ProvableType α] : Inhabited (Circuit F (Var α F)) where
  default := ProvableType.witness default

def copy_to_var (x: Expression F) : Circuit F (Variable F) := do
  let x' ← witnessVar x.eval
  assertZero (x - (var x'))
  return x'

def to_var : Expression F → Circuit F (Variable F)
  | var v => pure v
  | x => copy_to_var x

-- these could be used if you want to witness _any_ value and don't care which
-- (typically useless, because in completeness proofs you will often have to prove some assumption about the value)

def getOffset : Circuit F ℕ := fun n => (n, [])

def compute_value_from_offset (α : TypeMap) [ProvableType α] (offset : ℕ) (env : Environment F) : α F :=
  from_elements <| .mapRange _ fun i => env.get (offset + i)

def ProvableType.witnessAny (α: TypeMap) [ProvableType α] : Circuit F (Var α F) := do
  let offset ← getOffset
  ProvableType.witness (compute_value_from_offset α offset)

theorem ProvableType.witnessAny.local_witnesses (n : ℕ) (env : Environment F) :
    env.UsesLocalWitnessesCompleteness n (ProvableType.witnessAny α |>.operations n) ↔ True := by
  simp only [circuit_norm, getOffset, ProvableType.witnessAny, compute_value_from_offset,
    ProvableType.to_elements_from_elements]
