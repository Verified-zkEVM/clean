import Clean.Circuit.Operations
import Mathlib.Control.Monad.Writer

variable {F : Type} [Field F] {α β : Type} {n : ℕ}

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
  assertZero (x - 1) * x

  -- or add a lookup
  lookup { table := MyTable, entry := [x], ... }
```
-/
def Circuit (sentences : PropertySet F) (α : Type) := ℕ → α × List (Operation sentences)

namespace Circuit
-- definition of the circuit monad

def bind {sentences : PropertySet F} {α β} (f : Circuit sentences α) (g : α → Circuit sentences β) : Circuit sentences β := fun (n : ℕ) =>
  -- note: empirically, not unpacking the results of `f` here makes the monad scale to much more operations
  let (b, ops') := g (f n).1 (n + Operations.localLength (f n).2)
  (b, (f n).2 ++ ops')

instance {sentences : PropertySet F} : Monad (Circuit sentences) where
  map {α β} (f : α → β) (circuit : Circuit sentences α) := fun (n : ℕ) =>
    let (a, ops) := circuit n
    (f a, ops)
  pure {α} (a : α) := fun _ => (a, [])
  bind := bind

/--
In proofs, we rewrite `bind` into a definition that is more efficient to
reason about (because it avoids the duplicated `f n` term).
 -/
@[circuit_norm]
theorem bind_def {sentences : PropertySet F} {α β} (f : Circuit sentences α) (g : α → Circuit sentences β) :
  f >>= g = fun n =>
    let (a, ops) := f n
    let (b, ops') := g a (n + Operations.localLength ops)
    (b, ops ++ ops') := rfl

@[circuit_norm]
theorem pure_def {sentences : PropertySet F} {α} (a : α) : (pure a : Circuit sentences α) = fun _ => (a, []) := rfl

@[circuit_norm]
theorem map_def {sentences : PropertySet F} {α β} (f : α → β) (circuit : Circuit sentences α) :
  f <$> circuit = fun n => let (a, ops) := circuit n; (f a, ops) := rfl

-- normalize `bind` to `>>=`
@[circuit_norm]
theorem bind_normalize {sentences : PropertySet F} {α β} (f : Circuit sentences α) (g : α → Circuit sentences β) : f.bind g = f >>= g := rfl

-- the results of a circuit: operations, output value and local length (which determines the next offset)

@[reducible, circuit_norm]
def operations {sentences : PropertySet F} (circuit : Circuit sentences α) (offset : ℕ) : Operations sentences :=
  (circuit offset).2

@[reducible, circuit_norm]
def output {sentences : PropertySet F} (circuit : Circuit sentences α) (offset : ℕ) : α :=
  (circuit offset).1

@[reducible, circuit_norm]
def localLength {sentences : PropertySet F} (circuit : Circuit sentences α) (offset := 0) : ℕ :=
  Operations.localLength (circuit offset).2

-- core operations we can do in a circuit

/-- Create a new variable. -/
@[circuit_norm]
def witnessVar {sentences : PropertySet F} (compute : Environment F → F) : Circuit sentences (Variable F) :=
  fun (offset : ℕ) =>
    let var : Variable F := ⟨ offset ⟩
    (var, [.witness 1 fun env => #v[compute env]])

/-- Create a new variable, as an `Expression`. -/
@[circuit_norm]
def witnessField {sentences : PropertySet F} (compute : Environment F → F) : Circuit sentences (Expression F) := do
  let v ← witnessVar compute
  return var v

/-- Create a vector of variables. -/
@[circuit_norm]
def witnessVars {sentences : PropertySet F} (m : ℕ) (compute : Environment F → Vector F m) : Circuit sentences (Vector (Variable F) m) :=
  fun (offset : ℕ) =>
    let vars := .mapRange m fun i => ⟨offset + i⟩
    (vars, [.witness m fun env => compute env])

/-- Create a vector of expressions. -/
@[circuit_norm]
def witnessVector {sentences : PropertySet F} (m : ℕ) (compute : Environment F → Vector F m) : Circuit sentences (Vector (Expression F) m) :=
  fun (offset : ℕ) =>
    let vars := varFromOffset (fields m) offset
    (vars, [.witness m fun env => compute env])

/-- Add a constraint. -/
@[circuit_norm]
def assertZero {sentences : PropertySet F} (e : Expression F) : Circuit sentences Unit := fun _ =>
  ((), [.assert e])

/-- Add a lookup. -/
@[circuit_norm]
def lookup {sentences : PropertySet F} {Row : TypeMap} [ProvableType Row] (table : Table F Row)  (entry : Row (Expression F)) : Circuit sentences Unit := fun _ =>
  ((), [.lookup { table := table.toRaw, entry := toElements entry }])

end Circuit

/-- Create a new variable of an arbitrary "provable type". -/
@[circuit_norm]
def ProvableType.witness {sentences : PropertySet F} {α : TypeMap} [ProvableType α] (compute : Environment F → α F) : Circuit sentences (α (Expression F)) :=
  fun (offset : ℕ) =>
    let var := varFromOffset α offset
    (var, [.witness (size α) (fun env => compute env |> toElements)])

@[circuit_norm]
def ProvableVector.witness {sentences : PropertySet F} {α : TypeMap} [NonEmptyProvableType α] (m : ℕ)
    (compute : Environment F → Vector (α F) m) : Circuit sentences (Vector (α (Expression F)) m) :=
  ProvableType.witness (α:=ProvableVector α m) compute

namespace Circuit

-- formal concepts of soundness and completeness of a circuit

/--
What it means that "constraints hold" on a sequence of operations.
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
- For subcircuits, the constraints must hold on the subcircuit's flat operations
-/
@[circuit_norm]
def ConstraintsHold {sentences : PropertySet F} (eval : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences) : List (Operation sentences) → Prop
  | [] => True
  | .witness _ _ :: ops => ConstraintsHold eval yields checked ops
  | .assert e :: ops => eval e = 0 ∧ ConstraintsHold eval yields checked ops
  | .lookup { table, entry, .. } :: ops =>
    table.Contains (entry.map eval) ∧ ConstraintsHold eval yields checked ops
  | .yield _ :: ops => ConstraintsHold eval yields checked ops
  | .subcircuit s :: ops =>
    ConstraintsHoldFlat eval yields checked s.ops ∧ ConstraintsHold eval yields checked ops

/--
Version of `ConstraintsHold` that replaces the statement of subcircuits with their `Soundness`.
-/
@[circuit_norm]
def ConstraintsHold.Soundness {sentences : PropertySet F} (eval : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences) : List (Operation sentences) → Prop
  | [] => True
  | .witness _ _ :: ops => ConstraintsHold.Soundness eval yields checked ops
  | .assert e :: ops => eval e = 0 ∧ ConstraintsHold.Soundness eval yields checked ops
  | .lookup { table, entry } :: ops =>
    table.Soundness (entry.map eval) ∧ ConstraintsHold.Soundness eval yields checked ops
  | .yield _ :: ops => ConstraintsHold.Soundness eval yields checked ops
  | .subcircuit s :: ops =>
    s.Soundness eval yields checked ∧ ConstraintsHold.Soundness eval yields checked ops

/--
Version of `ConstraintsHold` that replaces the statement of subcircuits with their `Completeness`.
-/
@[circuit_norm]
def ConstraintsHold.Completeness {sentences : PropertySet F} (eval : Environment F) (yields : YieldContext sentences) : List (Operation sentences) → Prop
  | [] => True
  | .witness _ _ :: ops => ConstraintsHold.Completeness eval yields ops
  | .assert e :: ops => eval e = 0 ∧ ConstraintsHold.Completeness eval yields ops
  | .lookup { table, entry } :: ops =>
    table.Completeness (entry.map eval) ∧ ConstraintsHold.Completeness eval yields ops
  | .yield _ :: ops => ConstraintsHold.Completeness eval yields ops
  | .subcircuit s :: ops =>
    s.Completeness eval yields ∧ ConstraintsHold.Completeness eval yields ops
end Circuit

/--
If an environment "uses local witnesses and yields", it means that the environment's evaluation
matches the output of the witness generator passed along with a `witness` declaration,
for all variables declared locally within the circuit, and all yielded sentences are in the yield context.

This is the condition needed to prove completeness of a circuit.
-/
def Environment.UsesLocalWitnessesAndYields {sentences : PropertySet F} (env : Environment F) (yields : YieldContext sentences) (offset : ℕ) (ops : Operations sentences) : Prop :=
  ops.forAllFlat offset {
    witness n _ compute := env.ExtendsVector (compute env) n,
    yield _ s := s.eval env ∈ yields.yielded
  }

/--
Modification of `UsesLocalWitnessesAndYields` where subcircuits replace the condition with a custom statement.
-/
@[circuit_norm]
def Environment.UsesLocalWitnessesAndYieldsCompleteness {sentences : PropertySet F} (env : Environment F) (yields : YieldContext sentences) (offset : ℕ) : List (Operation sentences) → Prop
  | [] => True
  | .witness m c :: ops => env.ExtendsVector (c env) offset ∧ env.UsesLocalWitnessesAndYieldsCompleteness yields (offset + m) ops
  | .assert _ :: ops => env.UsesLocalWitnessesAndYieldsCompleteness yields offset ops
  | .lookup _ :: ops => env.UsesLocalWitnessesAndYieldsCompleteness yields offset ops
  | .yield s :: ops => s.eval env ∈ yields.yielded ∧ env.UsesLocalWitnessesAndYieldsCompleteness yields offset ops
  | .subcircuit s :: ops => s.UsesLocalWitnessesAndYields env yields ∧ env.UsesLocalWitnessesAndYieldsCompleteness yields (offset + s.localLength) ops

/-- Environment uses local witnesses for flat operations (witness checking only) -/
def Environment.UsesLocalWitnessesFlat {sentences : PropertySet F} (env : Environment F) (n : ℕ) (ops : List (FlatOperation sentences)) : Prop :=
  FlatOperation.forAll n {
    witness n _ compute := env.ExtendsVector (compute env) n
  } ops

/-- Environment uses local yields for flat operations (yield checking only) -/
def Environment.UsesLocalYieldsFlat {sentences : PropertySet F} (env : Environment F) (yields : YieldContext sentences) (n : ℕ) (ops : List (FlatOperation sentences)) : Prop :=
  FlatOperation.forAll n {
    yield _ s := s.eval env ∈ yields.yielded
  } ops

/-- Environment uses local witnesses and yields for flat operations (both witness and yield checking) -/
def Environment.UsesLocalWitnessesAndYieldsFlat {sentences : PropertySet F} (env : Environment F) (yields : YieldContext sentences) (n : ℕ) (ops : List (FlatOperation sentences)) : Prop :=
  FlatOperation.forAll n {
    witness n _ compute := env.ExtendsVector (compute env) n,
    yield _ s := s.eval env ∈ yields.yielded
  } ops

section
open Circuit (ConstraintsHold)
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-
Common base type for circuits that are to be used in formal proofs.

It contains the main circuit plus some of its properties in elaborated form, to make it
faster to reason about them in proofs.
-/
class ElaboratedCircuit (F : Type) (sentences : PropertySet F) (Input Output : TypeMap) [Field F] [ProvableType Input] [ProvableType Output] where
  main : Var Input F → Circuit sentences (Var Output F)

  /-- how many local witnesses this circuit introduces -/
  localLength : Var Input F → ℕ

  /-- the local length must not depend on the offset. usually automatically proved by `rfl` -/
  localLength_eq : ∀ input offset, (main input).localLength offset = localLength input
    := by intros; rfl

  /-- a direct way of computing the output of this circuit (i.e. without having to unfold `main`) -/
  output : Var Input F → ℕ → Var Output F := fun input offset => (main input).output offset

  /-- correctness of `output` -/
  output_eq : ∀ input offset, (main input).output offset = output input offset
    := by intros; rfl

  /-- technical condition: all subcircuits must be consistent with the current offset -/
  subcircuitsConsistent : ∀ input offset, ((main input).operations offset).SubcircuitsConsistent offset
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

attribute [circuit_norm] ElaboratedCircuit.main ElaboratedCircuit.localLength ElaboratedCircuit.output

/-
`checked` is an argument because there will be an induction involving all circuits and all tables
with respect to the growing `checked` set.
-/
@[circuit_norm]
def Soundness (F : Type) [Field F] {sentences : PropertySet F}
    (circuit : ElaboratedCircuit F sentences Input Output) (order : SentenceOrder sentences)
    (Assumptions : Input F → Prop) (Spec : CheckedYields sentences → Input F → Output F → Prop) :=
  -- for all environments that determine witness generation
  ∀ offset : ℕ, ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
  -- for all inputs that satisfy the assumptions
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- if the constraints hold
  ConstraintsHold.Soundness env yields checked (circuit.main input_var |>.operations offset) →
  -- the spec holds on the input and output
  let output := eval env (circuit.output input_var offset)
  -- TODO: prove `yield`ed properties hold, when their dependencies are already checked
  Spec checked input output

@[circuit_norm]
def Completeness (F : Type) [Field F] (sentences : PropertySet F) (circuit : ElaboratedCircuit F sentences Input Output)
    (Assumptions : Input F → Prop) :=
  -- for all environments which _use the default witness generators for local variables_
  ∀ offset : ℕ, ∀ env, ∀ (yields : YieldContext sentences), ∀ input_var : Var Input F,
  env.UsesLocalWitnessesAndYieldsCompleteness yields offset (circuit.main input_var |>.operations offset) →
  -- for all inputs that satisfy the assumptions
  ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- the constraints hold
  ConstraintsHold.Completeness env yields (circuit.main input_var |>.operations offset)

/--
`FormalCircuit` is the main object that encapsulates correctness of a circuit.

It requires you to provide
- a spec, which is a relationship between inputs and outputs
- assumptions, which are the conditions that must hold for the circuit to make sense
- a proof of _soundness_: assumptions ∧ constraints → spec, for any witnesses
- a proof of _completeness_: assumptions → constraints, using some witnesses that exist

Note that soundness and completeness, taken together, show that the spec will hold for _all_ inputs.
This means that, when viewed as a black box, the circuit acts similar to a function. The assumptions act as
preconditions, and the spec acts as the postcondition.
-/
structure FormalCircuit {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    (Input Output : TypeMap) [ProvableType Input] [ProvableType Output]
    extends elaborated : ElaboratedCircuit F sentences Input Output where
  Assumptions (_ : Input F) : Prop := True
  Spec : CheckedYields sentences → Input F → Output F → Prop
  soundness : Soundness F elaborated order Assumptions Spec
  completeness : Completeness F sentences elaborated Assumptions

/--
`DeterministicFormalCircuit` extends `FormalCircuit` with an explicit uniqueness constraint.
This ensures that for any input satisfying the assumptions, the specification uniquely determines the output.
Use this class when you want to formally guarantee that constraints uniquely determine the output,
preventing ambiguity in deterministic circuits.
-/
structure DeterministicFormalCircuit {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    (checked : CheckedYields sentences) (Input Output : TypeMap) [ProvableType Input] [ProvableType Output]
    extends circuit : FormalCircuit order Input Output where
  uniqueness : ∀ (input : Input F) (out1 out2 : Output F),
    circuit.Assumptions input → circuit.Spec checked input out1 → circuit.Spec checked input out2 → out1 = out2

@[circuit_norm]
def FormalAssertion.Soundness (F : Type) [Field F] (sentences : PropertySet F) (order : SentenceOrder sentences)
    (circuit : ElaboratedCircuit F sentences Input unit)
    (Assumptions : Input F → Prop) (Spec : CheckedYields sentences → Input F → Prop) :=
  -- for all environments that determine witness generation
  ∀ offset : ℕ, ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
  -- for all inputs that satisfy the assumptions
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- if the constraints hold
  ConstraintsHold.Soundness env yields checked (circuit.main input_var |>.operations offset) →
  -- the spec holds on the input
  -- TODO: prove `yield`ed properties hold, when their dependencies are already checked
  Spec checked input

@[circuit_norm]
def FormalAssertion.Completeness (F : Type) [Field F] (sentences : PropertySet F) (circuit : ElaboratedCircuit F sentences Input unit)
    (Assumptions : Input F → Prop) (Spec : Input F → Prop) :=
  -- for all environments which _use the default witness generators for local variables_
  ∀ offset, ∀ env, ∀ (yields : YieldContext sentences), ∀ input_var : Var Input F,
  env.UsesLocalWitnessesAndYieldsCompleteness yields offset (circuit.main input_var |>.operations offset) →
  -- for all inputs that satisfy the assumptions AND the spec
  ∀ input : Input F, eval env input_var = input →
  Assumptions input → Spec input →
  -- the constraints hold
  ConstraintsHold.Completeness env yields (circuit.main input_var |>.operations offset)

/--
`FormalAssertion` models a subcircuit that is "assertion-like":
- it doesn't return anything
- by design, it does not have `FormalCircuit`'s completeness. `FormalAssertion` further constrains its inputs.

The notion of _soundness_ is the same as for `FormalCircuit`: assumptions ∧ constraints → spec.

However, the _completeness_ statement is weaker: assumptions ∧ spec → constraints.

Given assumptions, the constraints might not be satisfiable and the spec must be an equivalent reformulation
of the constraints.
(In the case of `FormalCircuit`, given assumptions, the constraints are always satisfiable and the spec can be
strictly weaker than the constraints.)
-/
structure FormalAssertion {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    (Input : TypeMap) [ProvableType Input]
    extends elaborated : ElaboratedCircuit F sentences Input unit where
  Assumptions : Input F → Prop
  Spec : CheckedYields sentences → Input F → Prop
  soundness : FormalAssertion.Soundness F sentences order elaborated Assumptions Spec
  completeness : FormalAssertion.Completeness F sentences elaborated Assumptions (Spec Set.univ)

  -- assertions commonly don't introduce internal witnesses, so this is a convenient default
  localLength _ := 0
  -- the output has to be unit
  output _ _ := ()

@[circuit_norm]
def GeneralFormalCircuit.Soundness (F : Type) [Field F] (sentences : PropertySet F) (order : SentenceOrder sentences)
    (circuit : ElaboratedCircuit F sentences Input Output)
    (Spec : CheckedYields sentences → Input F → Output F → Prop) :=
  -- for all environments that determine witness generation
  ∀ offset : ℕ, ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
  -- for all inputs
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  -- if the constraints hold
  ConstraintsHold.Soundness env yields checked (circuit.main input_var |>.operations offset) →
  -- the spec holds on the input and output
  let output := eval env (circuit.output input_var offset)
  -- TODO: prove `yield`ed properties hold, when their dependencies are already checked
  Spec checked input output

@[circuit_norm]
def GeneralFormalCircuit.Completeness (F : Type) [Field F] (sentences : PropertySet F) (circuit : ElaboratedCircuit F sentences Input Output) (Assumptions : Input F → Prop) :=
  -- for all environments which _use the default witness generators for local variables_
  ∀ offset : ℕ, ∀ env, ∀ (yields : YieldContext sentences), ∀ input_var : Var Input F,
  env.UsesLocalWitnessesAndYieldsCompleteness yields offset (circuit.main input_var |>.operations offset) →
  -- for all inputs that satisfy the "honest prover" assumptions
  ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- the constraints hold
  ConstraintsHold.Completeness env yields (circuit.main input_var |>.operations offset)

/--
`GeneralFormalCircuit` is the most general model of formal circuits, needed in cases where the circuit is a
_mix_ of "assertion-like" and "function-like". It allows you flexibility in specifying separate statements
to be proved in the soundness and completeness proofs, by
- only using the `Spec` in the soundness statement
- only using the `Assumptions` in the completeness statement
i.e. the two statements are not "coupled".

For example, take the `toBits n` circuit, which outputs the `n`-bit decomposition of the input.
To do so, the circuit, as a side effect, constrains the input to be representable in `n` bits.
Consequently, the input being `n` bits is a necessary assumption _for completeness_. However, _for soundness_,
this assumption is not needed as the circuit adds that constraint itself. Using `FormalCircuit` would unnecessarily
add the range assumption to the soundness statement, thus making the circuit hard to use
(in particular, not usable as a bit range check, because it already _requires_ the bit range assumption).
-/
structure GeneralFormalCircuit {F : Type} [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    (Input Output : TypeMap) [ProvableType Input] [ProvableType Output]
    extends elaborated : ElaboratedCircuit F sentences Input Output where
  Assumptions : Input F → Prop -- the statement to be assumed for completeness
  Spec : CheckedYields sentences → Input F → Output F → Prop -- the statement to be proved for soundness. (Might have to include `Assumptions` on the inputs, as a hypothesis.)
  soundness : GeneralFormalCircuit.Soundness F sentences order elaborated Spec
  completeness : GeneralFormalCircuit.Completeness F sentences elaborated Assumptions
end

export Circuit (witnessVar witnessField witnessVars witnessVector assertZero lookup)

-- general `witness` method

class Witnessable (F : Type) [Field F] (sentences : PropertySet F) (value : outParam TypeMap) (var : TypeMap) [ProvableType value] where
  witness : ((Environment F → value F) → Circuit sentences (var F))
  var_eq : var F = value (Expression F) := by rfl
  witness_eq (compute : Environment F → value F) :
    witness compute = var_eq ▸ ProvableType.witness compute := by intros; rfl

export Witnessable (witness)

instance {sentences : PropertySet F} : Witnessable F sentences field Expression where
  witness := witnessField

instance {sentences : PropertySet F} {m : ℕ} : Witnessable F sentences (Vector · m) (fun F => Vector (Expression F) m) where
  witness := witnessVector m

instance {sentences : PropertySet F} (α : TypeMap) [ProvableType α] : Witnessable F sentences α (Var α) where
  witness := ProvableType.witness

instance {sentences : PropertySet F} {m : ℕ} (α : TypeMap) [NonEmptyProvableType α] :
    Witnessable F sentences (ProvableVector α m) (Var (ProvableVector α m)) where
  witness := ProvableVector.witness m

-- witness generation

def Environment.fromList (witnesses : List F) : Environment F :=
  .mk fun i => witnesses[i]?.getD 0

def FlatOperation.dynamicWitness {sentences : PropertySet F} (op : FlatOperation sentences) (acc : List F) : List F := match op with
  | .witness _ compute => (compute (Environment.fromList acc)).toList
  | .assert _ => []
  | .lookup _ => []
  | .yield _ => []

def FlatOperation.dynamicWitnesses {sentences : PropertySet F} (ops : List (FlatOperation sentences)) (init : List F) : List F :=
  ops.foldl (fun (acc : List F) (op : FlatOperation sentences) =>
    acc ++ op.dynamicWitness acc
  ) init

def FlatOperation.proverEnvironment {sentences : PropertySet F} (ops : List (FlatOperation sentences)) (init : List F) : Environment F :=
  Environment.fromList (FlatOperation.dynamicWitnesses ops init)

/--
Computes the set of yielded sentences from the prover environment.
-/
def FlatOperation.proverYields {sentences : PropertySet F} (ops : List (FlatOperation sentences)) (init : List F) : YieldContext sentences :=
  { yielded := FlatOperation.localYields (FlatOperation.proverEnvironment ops init) ops }

def Environment.AgreesBelow (n : ℕ) (env env' : Environment F) :=
  ∀ i < n, env.get i = env'.get i

def Environment.OnlyAccessedBelow (n : ℕ) (f : Environment F → α) :=
  ∀ env env', Environment.AgreesBelow n env env' → f env = f env'

/--
A circuit has _computable witnesses_ when witness generators only depend on the environment at indices smaller than the current offset.
This allows us to compute a concrete environment from witnesses, by successively extending an array with new witnesses.
-/
def Operations.ComputableWitnesses {sentences : PropertySet F} (ops : Operations sentences) (n : ℕ) (env env' : Environment F) : Prop :=
  ops.forAllFlat n { witness n _ compute := env.AgreesBelow n env' → compute env = compute env' }

def Circuit.ComputableWitnesses {sentences : PropertySet F} (circuit : Circuit sentences α) (n : ℕ) :=
  ∀ env env', (circuit.operations n).ComputableWitnesses n env env'

/--
If a circuit satisfies `computableWitnesses`, we can construct a concrete environment
that satisfies `UsesLocalWitnessesAndYields`. (Proof in `Theorems`.)
-/
def Circuit.proverEnvironment {sentences : PropertySet F} (circuit : Circuit sentences α) (init : List F := []) : Environment F :=
  Environment.fromList (FlatOperation.dynamicWitnesses (circuit.operations init.length).toFlat init)

/--
Computes the set of yielded sentences from the prover environment for a circuit.
-/
def Circuit.proverYields {sentences : PropertySet F} (circuit : Circuit sentences α) (init : List F := []) : YieldContext sentences :=
  FlatOperation.proverYields (circuit.operations init.length).toFlat init

-- witness generators used for AIR trace export
-- TODO unify with the definitions above

def FlatOperation.witnessGenerators {sentences : PropertySet F} : (l : List (FlatOperation sentences)) → Vector (Environment F → F) (localLength l)
  | [] => #v[]
  | .witness m c :: ops => Vector.mapFinRange m (fun i env => (c env)[i.val]) ++ witnessGenerators ops
  | .assert _ :: ops => witnessGenerators ops
  | .lookup _ :: ops => witnessGenerators ops
  | .yield _ :: ops => witnessGenerators ops

def Operations.witnessGenerators {sentences : PropertySet F} : (ops : Operations sentences) → Vector (Environment F → F) ops.localLength
  | [] => #v[]
  | .witness m c :: ops => Vector.mapFinRange m (fun i env => (c env)[i.val]) ++ witnessGenerators ops
  | .assert _ :: ops => witnessGenerators ops
  | .lookup _ :: ops => witnessGenerators ops
  | .yield _ :: ops => witnessGenerators ops
  | .subcircuit s :: ops => (s.localLength_eq ▸ FlatOperation.witnessGenerators s.ops) ++ witnessGenerators ops

-- statements about constant length or output

namespace Circuit
/--
The given family of circuits all share the same `localLength`, for all inputs.

This is a bit stronger than the assumption on local length implicit in `ElaboratedCircuit`,
but still the typical case.
-/
class ConstantLength {sentences : PropertySet F} (circuit : α → Circuit sentences β) where
  localLength : ℕ
  localLength_eq : ∀ (a : α) (n : ℕ), (circuit a).localLength n = localLength

def ConstantLength.fromConstantLength {sentences : PropertySet F} {circuit : α → Circuit sentences β} [Inhabited α]
    (h : ∀ (a : α) n, (circuit a).localLength n = (circuit default).localLength 0) : ConstantLength circuit where
  localLength := (circuit default).localLength 0
  localLength_eq a n := h a n

/-- The output of this circuit does not depend on the input. -/
@[circuit_norm]
def ConstantOutput {sentences : PropertySet F} (circuit : α → Circuit sentences β) [Inhabited α] :=
  ∀ (x : α) (n : ℕ), (circuit x).output n = (circuit default).output n

syntax "infer_constant_length" : tactic

macro_rules
  | `(tactic|infer_constant_length) => `(tactic|(
    apply ConstantLength.fromConstantLength
    try simp only [circuit_norm]
    try intros
    try ac_rfl))

example {sentences : PropertySet F} :
  let add (x : Expression F) : Circuit sentences (Expression F) := do
    let y : Expression F ← witness fun _ => 1
    let z ← witness fun eval => eval (x + y)
    assertZero (x + y - z)
    pure z
  ConstantLength add := by infer_constant_length
end Circuit

-- `circuit_norm` attributes

-- basic logical simplifcations
attribute [circuit_norm] true_and and_true true_implies implies_true forall_const

/-
when simplifying lookup constraints, `circuit_norm` has to deal with expressions of the form
`(Vector.map (fun x ↦ Expression.eval env x) v#[x, y])`
that we want simplified to
`v#[x.eval env, y.eval env]`
-/
attribute [circuit_norm] Vector.map_mk List.map_toArray List.map_cons List.map_nil

-- we often need to simplify concatenated vectors, e.g. for resolving `localWitnesses`
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

-- simplify `vector[i]` (which occurs in ProvableType definitions) and similar
attribute [circuit_norm] Fin.val_eq_zero Fin.cast_eq_self Fin.coe_cast Fin.isValue

-- simplify constraint expressions and +0 indices
attribute [circuit_norm] neg_mul one_mul add_zero
