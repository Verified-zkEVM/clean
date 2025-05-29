import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Operations
-- import Clean.Circuit.Append
import Clean.Circuit.SimpGadget
import Mathlib.Control.Monad.Writer

variable {F: Type} [Field F] {α : Type} {n : ℕ}

/--
The monad to write circuits. Lets you use `do` notation while in the background
it builds up a list of `Operation`s that represent the circuit at a low level.

Concretely, a `Circuit` is a function `(offset : ℕ) → α × List (Operation F) × offset'` for some
return type `α`, and the monad is a state monad that keeps the `offset` around, paired with a
writer monad that accumulates the operations.

```
def circuit : Circuit F Unit := do
  -- witness a new variable
  let x ← witness (fun _ => 1)

  -- add a constraint
  assert_zero (x - 1) * x

  -- or add a lookup
  lookup { table := MyTable, entry := [x], ... }
```
-/
def Circuit (F : Type) [Field F] := WriterT (List (Operation F)) (StateM ℕ)

-- instance Circuit.lift : MonadLift (StateM ℕ) (Circuit F) where
--   monadLift {α} (m : StateM ℕ α) : StateM ℕ (α × List (Operation F)) :=
--     fun (n : ℕ) => let (a, n') := m n; ((a, []), n')

instance : Monad (Circuit F) where
  map {α β} (f : α → β) (circuit : Circuit F α) := fun (n : ℕ) =>
    let ((a, ops), n') := circuit n
    ((f a, ops), n')
  pure {α} (a : α) := fun (n : ℕ) => ((a, []), n)
  bind {α β} (f : Circuit F α) (g : α → Circuit F β) := fun (n : ℕ) =>
    let ((a, ops), n') := f n
    let ((b, ops'), n'') := g a n'
    ((b, ops ++ ops'), n'')

namespace Circuit
@[reducible, circuit_norm]
def final_offset (circuit: Circuit F α) (offset: ℕ) : ℕ :=
  circuit offset |>.snd

@[reducible, circuit_norm]
def operations (circuit: Circuit F α) (offset := 0) : Operations F :=
  circuit offset |>.fst.snd

@[reducible, circuit_norm]
def output (circuit: Circuit F α) (offset := 0) : α :=
  circuit offset |>.fst.fst

@[reducible, circuit_norm]
def local_length (circuit: Circuit F α) (offset := 0) : ℕ :=
  Operations.local_length (circuit offset |>.fst.snd)

-- core operations we can do in a circuit

/-- Create a new variable -/
@[circuit_norm]
def witness_var (compute : Environment F → F) : Circuit F (Variable F) :=
  fun (offset : ℕ) =>
    let var : Variable F := ⟨ offset ⟩
    ((var, [.witness 1 fun env => #v[compute env]]), offset + 1)

/-- Create a new variable, as an `Expression`. -/
@[circuit_norm]
def witness (compute : Environment F → F) := do
  let v ← witness_var compute
  return var v

@[circuit_norm]
def witness_vars (m: ℕ) (compute : Environment F → Vector F m) : Circuit F (Vector (Variable F) m) :=
  fun (offset : ℕ) =>
    let vars := .mapRange m fun i => ⟨offset + i⟩
    ((vars, [.witness m compute]), offset + m)

@[circuit_norm]
def witness_vector (m: ℕ) (compute : Environment F → Vector F m) : Circuit F (Vector (Expression F) m) :=
  fun (offset : ℕ) =>
    let vars := var_from_offset (fields m) offset
    ((vars, [.witness m compute]), offset + m)

/-- Add a constraint. -/
@[circuit_norm]
def assert_zero (e: Expression F) : Circuit F Unit := fun (offset : ℕ) =>
  (((), [.assert e]), offset)

/-- Add a lookup. -/
@[circuit_norm]
def lookup (l: Lookup F) : Circuit F Unit := fun (offset : ℕ) =>
  (((), [.lookup l]), offset)

end Circuit

@[circuit_norm]
def ProvableType.witness {α: TypeMap} [ProvableType α] (compute : Environment F → α F) : Circuit F (α (Expression F)) :=
  fun (offset : ℕ) =>
    let var := var_from_offset α offset
    ⟨(var, [.witness (size α) (fun env => compute env |> to_elements)]), offset + size α⟩

/--
If an environment "uses local witnesses" it means that the environment's evaluation
matches the output of the witness generator passed along with a `witness` declaration,
for all variables declared locally within the circuit.

This is the condition needed to prove completeness of a circuit.
-/
def Environment.uses_local_witnesses (env: Environment F) (offset : ℕ) : List (Operation F) → Prop
  | [] => True
  | .witness m c :: ops => env.extends_vector (c env) offset ∧ env.uses_local_witnesses (m + offset) ops
  | .assert _ :: ops => env.uses_local_witnesses offset ops
  | .lookup _ :: ops => env.uses_local_witnesses offset ops
  | .subcircuit s :: ops => env.extends_vector (s.witnesses env) offset ∧ env.uses_local_witnesses (s.local_length + offset) ops

/--
Modification of `uses_local_witnesses` where subcircuits replace the condition with a custom statement.
-/
@[circuit_norm]
def Environment.uses_local_witnesses_completeness (env: Environment F) (offset : ℕ) : List (Operation F) → Prop
  | [] => True
  | .witness m c :: ops => env.extends_vector (c env) offset ∧ env.uses_local_witnesses_completeness (m + offset) ops
  | .assert _ :: ops => env.uses_local_witnesses_completeness offset ops
  | .lookup _ :: ops => env.uses_local_witnesses_completeness offset ops
  | .subcircuit s :: ops => s.uses_local_witnesses env ∧ env.uses_local_witnesses_completeness (s.local_length + offset) ops

namespace Circuit
-- formal concepts of soundness and completeness of a circuit

/--
What it means that "constraints hold" on a sequence of operations.
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
- For subcircuits, the constraints must hold on the subcircuit's flat operations
-/
@[circuit_norm]
def constraints_hold (eval : Environment F) : List (Operation F) → Prop
  | [] => True
  | .witness _ _ :: ops => constraints_hold eval ops
  | .assert e :: ops => eval e = 0 ∧ constraints_hold eval ops
  | .lookup { table, entry, .. } :: ops =>
    table.contains (entry.map eval) ∧ constraints_hold eval ops
  | .subcircuit s :: ops =>
    constraints_hold_flat eval s.ops ∧ constraints_hold eval ops

/--
Version of `constraints_hold` that replaces the statement of subcircuits with their `soundness`.
-/
@[circuit_norm]
def constraints_hold.soundness (eval : Environment F) : List (Operation F) → Prop
  | [] => True
  | .witness _ _ :: ops => constraints_hold.soundness eval ops
  | .assert e :: ops => eval e = 0 ∧ constraints_hold.soundness eval ops
  | .lookup { table, entry, .. } :: ops =>
    table.contains (entry.map eval) ∧ constraints_hold.soundness eval ops
  | .subcircuit s :: ops =>
    s.soundness eval ∧ constraints_hold.soundness eval ops

/--
Version of `constraints_hold` that replaces the statement of subcircuits with their `completeness`.
-/
@[circuit_norm]
def constraints_hold.completeness (eval : Environment F) : List (Operation F) → Prop
  | [] => True
  | .witness _ _ :: ops => constraints_hold.completeness eval ops
  | .assert e :: ops => eval e = 0 ∧ constraints_hold.completeness eval ops
  | .lookup { table, entry, .. } :: ops =>
    table.contains (entry.map eval) ∧ constraints_hold.completeness eval ops
  | .subcircuit s :: ops =>
    s.completeness eval ∧ constraints_hold.completeness eval ops
end Circuit

section
open Circuit (constraints_hold)
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

/-
Common base type for circuits that are to be used in formal proofs.

It contains the main circuit plus some of its properties in elaborated form, to make it
faster to reason about them in proofs.
-/
class ElaboratedCircuit (F: Type) [Field F] (β α: TypeMap) [ProvableType β] [ProvableType α] where
  main: Var β F → Circuit F (Var α F)

  /-- how many local witnesses this circuit introduces -/
  local_length: Var β F → ℕ

  /-- the local length must not depend on the offset. usually automatically proved by `rfl` -/
  local_length_eq : ∀ var offset, (main var).local_length offset = local_length var
    := by intros; rfl

  /-- a direct way of computing the output of this circuit (i.e. without having to unfold `main`) -/
  output : Var β F → ℕ → Var α F

  /-- correctness of `output` -/
  output_eq : ∀ var offset, (main var).output offset = output var offset
    := by intros; rfl

  -- TODO this doesn't seem to make sense now?
  -- /--
  --   technical condition needed for subcircuit consistency: the circuit must not change its initial offset.
  --   usually automatically proved by `rfl`.
  -- -/
  -- initial_offset_eq: ∀ var, ∀ n, (main var |>.operations n).initial_offset = n
  --   := by intros; rfl

attribute [circuit_norm] ElaboratedCircuit.main ElaboratedCircuit.local_length ElaboratedCircuit.output

def Soundness (F: Type) [Field F] (circuit : ElaboratedCircuit F β α)
    (assumptions: β F → Prop) (spec: β F → α F → Prop) :=
  -- for all environments that determine witness generation
  ∀ offset : ℕ, ∀ env,
  -- for all inputs that satisfy the assumptions
  ∀ b_var : Var β F, ∀ b : β F, eval env b_var = b →
  assumptions b →
  -- if the constraints hold
  constraints_hold.soundness env (circuit.main b_var |>.operations offset) →
  -- the spec holds on the input and output
  let a := eval env (circuit.output b_var offset)
  spec b a

def Completeness (F: Type) [Field F] (circuit : ElaboratedCircuit F β α)
    (assumptions: β F → Prop) :=
  -- for all environments which _use the default witness generators for local variables_
  ∀ offset : ℕ, ∀ env, ∀ b_var : Var β F,
  env.uses_local_witnesses_completeness offset (circuit.main b_var |>.operations offset) →
  -- for all inputs that satisfy the assumptions
  ∀ b : β F, eval env b_var = b →
  assumptions b →
  -- the constraints hold
  constraints_hold.completeness env (circuit.main b_var |>.operations offset)

structure FormalCircuit (F: Type) (β α: TypeMap) [Field F] [ProvableType α] [ProvableType β]
  extends elaborated : ElaboratedCircuit F β α where
  -- β = inputs, α = outputs
  assumptions: β F → Prop
  spec: β F → α F → Prop
  soundness: Soundness F elaborated assumptions spec
  completeness: Completeness F elaborated assumptions

namespace Circuit
@[circuit_norm]
def subcircuit_soundness (circuit: FormalCircuit F β α) (b_var : Var β F) (offset: ℕ) (env : Environment F) :=
  let b := eval env b_var
  let a_var := circuit.output b_var offset
  let a := eval env a_var
  circuit.assumptions b → circuit.spec b a

@[circuit_norm]
def subcircuit_completeness (circuit: FormalCircuit F β α) (b_var : Var β F) (env : Environment F) :=
  let b := eval env b_var
  circuit.assumptions b
end Circuit

/--
`FormalAssertion` models a subcircuit that is "assertion-like":
- it doesn't return anything
- by design, it is not complete: it further constrains its inputs

The notion of _soundness_ is the same as for `FormalCircuit`: some `assumptions` + constraints imply a `spec`.

However, the _completeness_ statement is weaker:
If both the assumptions AND the spec are true, then the constraints hold.

In other words, for `FormalAssertion`s the spec must be an equivalent reformulation of the constraints.
(In the case of `FormalCircuit`, the spec can be strictly weaker than the constraints.)
-/
structure FormalAssertion (F: Type) (β: TypeMap) [Field F] [ProvableType β]
  extends ElaboratedCircuit F β unit where
  assumptions: β F → Prop
  spec: β F → Prop

  soundness:
    -- for all environments that determine witness generation
    ∀ offset, ∀ env,
    -- for all inputs that satisfy the assumptions
    ∀ b_var : Var β F, ∀ b : β F, eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold.soundness env (main b_var |>.operations offset) →
    -- the spec holds
    spec b

  completeness:
    -- for all environments which _use the default witness generators for local variables_
    ∀ offset, ∀ env, ∀ b_var : Var β F,
    env.uses_local_witnesses_completeness offset (main b_var |>.operations offset) →
    -- for all inputs that satisfy the assumptions AND the spec
    ∀ b : β F, eval env b_var = b →
    assumptions b → spec b →
    -- the constraints hold
    constraints_hold.completeness env (main b_var |>.operations offset)

  -- assertions commonly don't introduce internal witnesses, so this is a convenient default
  local_length := fun _ => 0

  output := fun _ _ => ()

namespace Circuit
@[circuit_norm]
def subassertion_soundness (circuit: FormalAssertion F β) (b_var : Var β F) (env: Environment F) :=
  let b := eval env b_var
  circuit.assumptions b → circuit.spec b

@[circuit_norm]
def subassertion_completeness (circuit: FormalAssertion F β) (b_var : Var β F) (env: Environment F) :=
  let b := eval env b_var
  circuit.assumptions b ∧ circuit.spec b
end Circuit
end

export Circuit (witness_var witness witness_vars witness_vector assert_zero lookup)

-- witness generation

def WitnessGenerators (F: Type) (n: ℕ) := Vector (Environment F → F) n

def FlatOperation.witness_generators : (l: List (FlatOperation F)) → Vector (Environment F → F) (witness_length l)
  | [] => #v[]
  | op :: ops =>
    let ws := witness_generators ops
    match op with
    | witness m compute =>
      ⟨ (Vector.mapFinRange m (fun i env => (compute env).get i)).toArray ++ ws.toArray, by
        simp only [Array.size_append, Vector.size_toArray, witness_length]; ac_rfl⟩
    | assert _ | lookup _ =>
      ⟨ ws.toArray, by simp only [ws.size_toArray, witness_length]⟩

def Operations.witness_generators : (ops: Operations F) → Vector (Environment F → F) ops.local_length
  | [] => #v[]
  | .witness m c :: ops => Vector.mapFinRange m (fun i env => (c env).get i) ++ witness_generators ops
  | .assert _ :: ops => witness_generators ops
  | .lookup _ :: ops => witness_generators ops
  | .subcircuit s :: ops => (s.local_length_eq ▸ FlatOperation.witness_generators s.ops) ++ witness_generators ops

-- TODO this is inefficient, Array should be mutable and env should be defined once at the beginning
def Circuit.witnesses (circuit: Circuit F α) (offset := 0) : Array F :=
  let generators := (circuit.operations offset).witness_generators
  generators.foldl (fun acc compute =>
    let env i := acc.getD i 0
    acc.push (compute ⟨ env ⟩))
  #[]

-- `circuit_norm` attributes

-- `circuit_norm` has to expand monad operations, so we need to add them to the simp set
attribute [circuit_norm] bind StateT.bind
attribute [circuit_norm] modify modifyGet MonadStateOf.modifyGet StateT.modifyGet
attribute [circuit_norm] pure StateT.pure
attribute [circuit_norm] StateT.run
-- attribute [circuit_norm] monadLift MonadLift.monadLift
--   tell WriterT.mk WriterT.monad WriterT.liftTell
--   EmptyCollection.emptyCollection
--   Functor.map StateT.map

-- basic logical simplifcations
attribute [circuit_norm] true_and and_true true_implies forall_const

/-
when simplifying lookup constraints, `circuit_norm` has to deal with expressions of the form
`(Vector.map (fun x ↦ Expression.eval env x) v#[x, y])`
that we want simplified to
`v#[x.eval env, y.eval env]`
-/
attribute [circuit_norm] Vector.map_mk List.map_toArray List.map_cons List.map_nil

-- we often need to simplify concatenated vectors, e.g. for resolving `local_witnesses`
attribute [circuit_norm] Vector.append_singleton Vector.mk_append_mk Vector.push_mk
  Array.append_singleton Array.append_empty List.push_toArray
  List.nil_append List.cons_append List.append_toArray
  Vector.toArray_push Array.push_toList List.append_assoc
  Vector.eq_mk Vector.mk_eq

-- `getElem` lemmas should be tried before expanding Vectors/Lists
attribute [circuit_norm ↓] Fin.getElem_fin
  Vector.getElem_map Vector.getElem_mapFinRange Vector.getElem_mapRange Vector.getElem_finRange
  Vector.getElem_push Vector.getElem_set Vector.getElem_cast
  Vector.getElem_mk Vector.getElem_toArray
  List.getElem_cons_zero List.getElem_cons_succ List.getElem_toArray

/-
lemmas that would expand `Vector.{mapRange, mapFinRange}` are not added to the simp set,
because they would sometimes be applied too eagerly where using the corresponding `getElem` lemma is much better
-/
-- attribute [circuit_norm] Vector.mapRange_zero Vector.mapRange_succ Vector.mapFinRange_succ Vector.mapFinRange_zero

-- simplify Vector.mapFinRange
attribute [circuit_norm]
    Nat.cast_zero Nat.cast_one Nat.cast_ofNat Fin.coe_eq_castSucc Fin.reduceCastSucc

-- simplify stuff like (3 : Fin 8).val = 3 % 8
attribute [circuit_norm] Fin.coe_ofNat_eq_mod

-- simplify `vector.get i` (which occurs in ProvableType definitions) and similar
attribute [circuit_norm] Vector.get Fin.val_eq_zero
  Fin.cast_eq_self Fin.coe_cast Fin.isValue

-- simplify constraint expressions and +0 indices
attribute [circuit_norm] neg_mul one_mul add_zero
