import Clean.Circuit.Operations
import Mathlib.Control.Monad.Writer

variable {F: Type} [Field F] {α : Type} {n : ℕ}

/--
The monad to write circuits. Lets you use `do` notation while in the background
it builds up a list of `Operation`s that represent the circuit at a low level.

Concretely, a `Circuit` is a function `(offset : ℕ) → α × List (Operation F)` for some
return type `α`. The monad is a mix of
- a writer monad that accumulates the list of operations
- a state monad that keeps track of the offset,
  where the next offset is computed from the operations added in the previous step.

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
def Circuit (F : Type) [Field F] (α : Type) := ℕ → α × List (Operation F)

namespace Circuit
-- definition of the circuit monad

def bind {α β} (f : Circuit F α) (g : α → Circuit F β) : Circuit F β := fun (n : ℕ) =>
  -- note: empirically, not unpacking the results of `f` here makes the monad scale to much more operations
  let (b, ops') := g (f n).1 (n + Operations.local_length (f n).2)
  (b, (f n).2 ++ ops')

instance : Monad (Circuit F) where
  map {α β} (f : α → β) (circuit : Circuit F α) := fun (n : ℕ) =>
    let (a, ops) := circuit n
    (f a, ops)
  pure {α} (a : α) := fun _ => (a, [])
  bind := bind

/--
in proofs, we rewrite `bind` into a definition that is more efficient to
reason about (because it avoids the duplicated `f n` term).
 -/
@[circuit_norm]
theorem bind_def {α β} (f : Circuit F α) (g : α → Circuit F β) :
  f >>= g = fun n =>
    let (a, ops) := f n
    let (b, ops') := g a (n + Operations.local_length ops)
    (b, ops ++ ops') := rfl

-- normalize `bind` to `>>=`
@[circuit_norm]
theorem bind_normalize {α β} (f : Circuit F α) (g : α → Circuit F β) : f.bind g = f >>= g := rfl

-- the results of a circuit: operations, output value and local length (which determines the next offset)

@[reducible, circuit_norm]
def operations (circuit: Circuit F α) (offset := 0) : Operations F :=
  (circuit offset).2

@[reducible, circuit_norm]
def output (circuit: Circuit F α) (offset := 0) : α :=
  (circuit offset).1

@[reducible, circuit_norm]
def local_length (circuit: Circuit F α) (offset := 0) : ℕ :=
  Operations.local_length (circuit offset).2

-- core operations we can do in a circuit

/-- Create a new variable. -/
@[circuit_norm]
def witness_var (compute : Environment F → F) : Circuit F (Variable F) :=
  fun (offset : ℕ) =>
    let var : Variable F := ⟨ offset ⟩
    (var, [.witness 1 fun env => #v[compute env]])

/-- Create a new variable, as an `Expression`. -/
@[circuit_norm]
def witness (compute : Environment F → F) := do
  let v ← witness_var compute
  return var v

/-- Create a vector of variables. -/
@[circuit_norm]
def witness_vars (m: ℕ) (compute : Environment F → Vector F m) : Circuit F (Vector (Variable F) m) :=
  fun (offset : ℕ) =>
    let vars := .mapRange m fun i => ⟨offset + i⟩
    (vars, [.witness m compute])

/-- Create a vector of expressions. -/
@[circuit_norm]
def witness_vector (m: ℕ) (compute : Environment F → Vector F m) : Circuit F (Vector (Expression F) m) :=
  fun (offset : ℕ) =>
    let vars := var_from_offset (fields m) offset
    (vars, [.witness m compute])

/-- Add a constraint. -/
@[circuit_norm]
def assert_zero (e: Expression F) : Circuit F Unit := fun _ =>
  ((), [.assert e])

/-- Add a lookup. -/
@[circuit_norm]
def lookup (l: Lookup F) : Circuit F Unit := fun _ =>
  ((), [.lookup l])

end Circuit

/-- Create a new variable of an arbitrary "provable type". -/
@[circuit_norm]
def ProvableType.witness {α: TypeMap} [ProvableType α] (compute : Environment F → α F) : Circuit F (α (Expression F)) :=
  fun (offset : ℕ) =>
    let var := var_from_offset α offset
    (var, [.witness (size α) (fun env => compute env |> to_elements)])

@[circuit_norm]
def ProvableVector.witness {α: TypeMap} [NonEmptyProvableType α] (m: ℕ)
    (compute : Environment F → Vector (α F) m) : Circuit F (Vector (α (Expression F)) m) :=
  ProvableType.witness (α := ProvableVector α m) compute

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
  | .lookup { table, entry } :: ops =>
    table.soundness (entry.map eval) ∧ constraints_hold.soundness eval ops
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
  | .lookup { table, entry } :: ops =>
    table.completeness (entry.map eval) ∧ constraints_hold.completeness eval ops
  | .subcircuit s :: ops =>
    s.completeness eval ∧ constraints_hold.completeness eval ops
end Circuit

/--
If an environment "uses local witnesses", it means that the environment's evaluation
matches the output of the witness generator passed along with a `witness` declaration,
for all variables declared locally within the circuit.

This is the condition needed to prove completeness of a circuit.
-/
def Environment.uses_local_witnesses (env: Environment F) (offset : ℕ) (ops : Operations F) : Prop :=
  ops.forAllFlat offset { witness n _ compute := env.extends_vector (compute env) n }

/--
Modification of `uses_local_witnesses` where subcircuits replace the condition with a custom statement.
-/
@[circuit_norm]
def Environment.uses_local_witnesses_completeness (env: Environment F) (offset : ℕ) : List (Operation F) → Prop
  | [] => True
  | .witness m c :: ops => env.extends_vector (c env) offset ∧ env.uses_local_witnesses_completeness (offset + m) ops
  | .assert _ :: ops => env.uses_local_witnesses_completeness offset ops
  | .lookup _ :: ops => env.uses_local_witnesses_completeness offset ops
  | .subcircuit s :: ops => s.uses_local_witnesses env ∧ env.uses_local_witnesses_completeness (offset + s.local_length) ops

/-- Same as `uses_local_witnesses`, but on flat operations -/
def Environment.uses_local_witnesses_flat (env : Environment F) (n : ℕ) (ops : List (FlatOperation F)) : Prop :=
  FlatOperation.forAll n { witness n _ compute := env.extends_vector (compute env) n } ops

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
  local_length_eq : ∀ input offset, (main input).local_length offset = local_length input
    := by intros; rfl

  /-- a direct way of computing the output of this circuit (i.e. without having to unfold `main`) -/
  output : Var β F → ℕ → Var α F := fun input offset => (main input).output offset

  /-- correctness of `output` -/
  output_eq : ∀ input offset, (main input).output offset = output input offset
    := by intros; rfl

  /-- technical condition: all subcircuits must be consistent with the current offset -/
  subcircuits_consistent : ∀ input offset, ((main input).operations offset).subcircuits_consistent offset
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

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

/--
`FormalCircuit` is the main object that encapsulates correctness of a circuit.

It requires you to provide
- a spec, which is a relationship between inputs and outputs
- assumptions, which are the conditions that must hold for the circuit to make sense
- a proof of _soundness_: assumptions ∧ constraints → spec, for any witnesses
- a proof of _completeness_: assumptions → constraints, when using the correct witnesses

Note that soundness and completeness, taken together, show that the spec will hold for _all_ inputs.
This means that, when viewed as a black box, the circuit acts similar to a function.
-/
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

The notion of _soundness_ is the same as for `FormalCircuit`: assumptions ∧ constraints → spec.

However, the _completeness_ statement is weaker: assumptions ∧ spec → constraints.

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
-- TODO unify these names

def Environment.fromList (witnesses: List F) : Environment F :=
  .mk fun i => witnesses[i]?.getD 0

def FlatOperation.dynamic_witnesses (op : FlatOperation F) (acc : List F) : List F := match op with
  | .witness _ compute => (compute (.fromList acc)).toList
  | .assert _ => []
  | .lookup _ => []

def FlatOperation.dynamic_witnesses_list (ops: List (FlatOperation F)) (init : List F) : List F :=
  ops.foldl (fun (acc : List F) (op : FlatOperation F) =>
    acc ++ op.dynamic_witnesses acc
  ) init

def Environment.fromFlatOperations (ops : List (FlatOperation F)) (init : List F) : Environment F :=
  .fromList (FlatOperation.dynamic_witnesses_list ops init)

def Operation.witnesses (op : Operation F) (acc : List F) : List F := match op with
  | .witness _ compute => (compute (.fromList acc)).toList
  | .assert _ => []
  | .lookup _ => []
  | .subcircuit s => (s.witnesses (.fromFlatOperations s.ops acc)).toList

def Operations.witnesses (ops: Operations F) (init : List F) : List F :=
  FlatOperation.dynamic_witnesses_list (to_flat_operations ops) init

def Environment.same_below (n : ℕ) (env env' : Environment F) :=
  ∀ i < n, env.get i = env'.get i

lemma Environment.same_below_of_le {F} {n m : ℕ} {env env' : Environment F} :
    env.same_below n env' → m ≤ n → env.same_below m env' :=
  fun h_same hi i hi' => h_same i (Nat.lt_of_lt_of_le hi' hi)

def Environment.only_accessed_below (n : ℕ) (f : Environment F → α) :=
  ∀ env env', (∀ i < n, env.get i = env'.get i) → f env = f env'

def Environment.only_accessed_below' (n : ℕ) (f : Environment F → α) (env env' : Environment F) :=
  (∀ i < n, env.get i = env'.get i) → f env = f env'

/--
A circuit has _computable witnesses_ when witness generators only depend on the environment at indices smaller than the current offset.
This allows us to compute a concrete environment from witnesses, by successively extending an array with new witnesses.
-/
def Operations.computable_witnesses (ops: Operations F) (n : ℕ) (env env' : Environment F) : Prop :=
   ops.forAllFlat n {
    witness n _ compute := (∀ i < n, env.get i = env'.get i) → compute env = compute env',
  }

def Circuit.computable_witnesses (circuit: Circuit F α) (n : ℕ) :=
  ∀ (env env' : Environment F), (circuit.operations n).computable_witnesses n env env'

def Circuit.computable_witnesses' (circuit: Circuit F α) (n : ℕ) (env env' : Environment F) :=
  (circuit.operations n).computable_witnesses n env env'

/--
If a circuit satisfies `computable_witnesses`, we can construct a concrete environment
that satisfies `uses_local_witnesses`. (Proof in `Theorems`.)
-/
def Circuit.proverEnvironment (circuit : Circuit F α) (init : List F := []) : Environment F :=
  .fromList ((circuit.operations init.length).witnesses init)

-- witness generators used for AIR trace export
-- TODO unify with the definitions above

def FlatOperation.witness_generators : (l: List (FlatOperation F)) → Vector (Environment F → F) (local_length l)
  | [] => #v[]
  | .witness m c :: ops => Vector.mapFinRange m (fun i env => (c env).get i) ++ witness_generators ops
  | .assert _ :: ops => witness_generators ops
  | .lookup _ :: ops => witness_generators ops

def Operations.witness_generators : (ops: Operations F) → Vector (Environment F → F) ops.local_length
  | [] => #v[]
  | .witness m c :: ops => Vector.mapFinRange m (fun i env => (c env).get i) ++ witness_generators ops
  | .assert _ :: ops => witness_generators ops
  | .lookup _ :: ops => witness_generators ops
  | .subcircuit s :: ops => (s.local_length_eq ▸ FlatOperation.witness_generators s.ops) ++ witness_generators ops

-- `circuit_norm` attributes

-- `circuit_norm` has to expand monad operations, so we need to add them to the simp set
attribute [circuit_norm] modify modifyGet MonadStateOf.modifyGet StateT.modifyGet
attribute [circuit_norm] pure StateT.pure
attribute [circuit_norm] StateT.run
  Functor.map StateT.map

-- basic logical simplifcations
attribute [circuit_norm] true_and and_true true_implies implies_true forall_const

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
