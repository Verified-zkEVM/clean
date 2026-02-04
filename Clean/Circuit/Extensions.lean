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

def getOffset : Circuit F ℕ := fun n => (n, [])

def valueFromOffset (α : TypeMap) [ProvableType α] (offset : ℕ) (env : Environment F) : α F :=
  fromElements <| .mapRange _ fun i => env.get (offset + i)

theorem eval_varFromOffset_valueFromOffset (α : TypeMap) [ProvableType α] (offset : ℕ) (env : Environment F) :
    eval env (varFromOffset α offset) = valueFromOffset α offset env := by
  simp only [varFromOffset, valueFromOffset, fromVars, ProvableType.eval_fromElements, Vector.map_mapRange]
  rfl

def witnessAny (α: TypeMap) [ProvableType α] : Circuit F (Var α F) := do
  let offset ← getOffset
  witness (valueFromOffset α offset)

theorem witnessAny_localWitnesses (n : ℕ) (env : Environment F) :
    env.UsesLocalWitnessesCompleteness n (witnessAny α |>.operations n) ↔ True := by
  simp only [circuit_norm, getOffset, witnessAny, valueFromOffset,
    ProvableType.toElements_fromElements]

@[circuit_norm]
theorem witnessAny_interactionsWithChannel {n : ℕ} {channel : RawChannel F} {env : Environment F} :
    (witnessAny α |>.operations n).interactionsWithChannel channel env = [] := by
  simp only [circuit_norm, getOffset, witnessAny, valueFromOffset,
    ProvableType.toElements_fromElements]

@[circuit_norm]
theorem witnessAny_output {n : ℕ} :
    (witnessAny (F:=F) α |>.output n) = varFromOffset α n  := by
  simp only [circuit_norm, getOffset, witnessAny, valueFromOffset,
    ProvableType.toElements_fromElements]
