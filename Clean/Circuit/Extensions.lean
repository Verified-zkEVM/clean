/- This file contains experimental additions to the Circuit DSL -/
import Clean.Circuit.Constant

variable {F : Type} [Field F] {α: TypeMap} [ProvableType α]

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

def compute_value_from_offset (α : TypeMap) [ProvableType α] (offset : ℕ) (env : Environment F) : α F :=
  from_elements <| .mapRange _ fun i => env.get (offset + i)

-- @[circuit_norm]
def ProvableType.witnessAny (α: TypeMap) [ProvableType α] : Circuit F (Var α F) := do
  let offset ← getOffset
  ProvableType.witness (compute_value_from_offset α offset)

@[circuit_norm]
def ProvableVector.witnessAny (α: TypeMap) [NonEmptyProvableType α] (m : ℕ) : Circuit F (Vector (Var α F) m) :=
  ProvableType.witnessAny (ProvableVector α m)

@[circuit_norm]
theorem ProvableType.witnessAny_local_witnesses (offset : ℕ) (env : Environment F) :
  env.uses_local_witnesses_completeness offset (ProvableType.witnessAny α offset).2 ↔ True := by
  simp only [circuit_norm, ProvableType.witnessAny, compute_value_from_offset,
    ProvableType.to_elements_from_elements]
