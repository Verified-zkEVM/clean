/- This file contains experimental additions to the Circuit DSL -/
import Clean.Circuit.Constant

variable {F : Type} [Field F]

instance {α: TypeMap} [ProvableType α] : Inhabited (Circuit F (Var α F)) where
  default := ProvableType.witness default

def copy_to_var (x: Expression F) : Circuit F (Variable F) := do
  let x' ← witness_var x.eval
  assert_zero (x - (var x'))
  return x'

def to_var : Expression F → Circuit F (Variable F)
  | var v => pure v
  | x => copy_to_var x

@[circuit_norm]
def getOffset : Circuit F ℕ := fun n => (n, [])

@[circuit_norm]
def undetermined (α: TypeMap) [ProvableType α] : Circuit F ((Environment F) → α F) := do
  let offset ← getOffset
  return fun env => from_elements <| .mapRange _ fun i => env.get (offset + i)

@[circuit_norm]
def ProvableType.witnessAny (α: TypeMap) [ProvableType α] : Circuit F (Var α F) := do
  let compute ← undetermined α
  ProvableType.witness compute

@[circuit_norm]
def ProvableVector.witnessAny (α: TypeMap) [NonEmptyProvableType α] (m : ℕ) : Circuit F (Vector (Var α F) m) :=
  ProvableType.witnessAny (ProvableVector α m)
