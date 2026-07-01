import Clean.Circuit.Operations
import Mathlib.Control.Monad.Writer

variable {F : Type} [FiniteField F] {α β : Type} {n : ℕ}

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
def Circuit (F : Type) [FiniteField F] (α : Type) := ℕ → α × List (Operation F)

namespace Circuit
-- definition of the circuit monad

def bind {α β} (f : Circuit F α) (g : α → Circuit F β) : Circuit F β := fun (n : ℕ) =>
  -- note: empirically, not unpacking the results of `f` here makes the monad scale to much more operations
  let (b, ops') := g (f n).1 (n + Operations.localLength (f n).2)
  (b, (f n).2 ++ ops')

instance : Monad (Circuit F) where
  map {α β} (f : α → β) (circuit : Circuit F α) := fun (n : ℕ) =>
    let (a, ops) := circuit n
    (f a, ops)
  pure {α} (a : α) := fun _ => (a, [])
  bind := bind

/--
In proofs, we rewrite `bind` into a definition that is more efficient to
reason about (because it avoids the duplicated `f n` term).
 -/
@[circuit_norm]
theorem bind_def {α β} (f : Circuit F α) (g : α → Circuit F β) :
  f >>= g = fun n =>
    let (a, ops) := f n
    let (b, ops') := g a (n + Operations.localLength ops)
    (b, ops ++ ops') := rfl

@[circuit_norm]
theorem pure_def {α} (a : α) : (pure a : Circuit F α) = fun _ => (a, []) := rfl

@[circuit_norm]
theorem map_def {α β} (f : α → β) (circuit : Circuit F α) :
  f <$> circuit = fun n => let (a, ops) := circuit n; (f a, ops) := rfl

@[circuit_norm]
theorem seqRight_def {α β} (f : Circuit F α) (g : Circuit F β) :
  f *> g = fun n =>
    let (_, ops) := f n
    let (b, ops') := g (n + Operations.localLength ops)
    (b, ops ++ ops') := rfl

-- normalize `bind` to `>>=`
@[circuit_norm]
theorem bind_normalize {α β} (f : Circuit F α) (g : α → Circuit F β) : f.bind g = f >>= g := rfl

-- the results of a circuit: operations, output value and local length (which determines the next offset)

@[reducible, circuit_norm]
def operations (circuit : Circuit F α) (offset : ℕ) : Operations F :=
  (circuit offset).2

@[reducible, circuit_norm]
def output (circuit : Circuit F α) (offset : ℕ) : α :=
  (circuit offset).1

@[reducible, circuit_norm]
def localLength (circuit : Circuit F α) (offset := 0) : ℕ :=
  Operations.localLength (circuit offset).2

-- core operations we can do in a circuit

/-- Create a new variable. -/
@[circuit_norm]
def witnessVarNative (compute : ProverEnvironment F → F) : Circuit F (Variable F) :=
  fun (offset : ℕ) =>
    let var : Variable F := ⟨ offset ⟩
    (var, [.witness 1 (.native fun env => #v[compute env])])

/-- Create a new variable, as an `Expression`. -/
@[circuit_norm]
def witnessFieldNative (compute : ProverEnvironment F → F) := do
  let v ← witnessVarNative compute
  return var v

/-- Create a vector of variables. -/
@[circuit_norm]
def witnessVarsNative (m : ℕ) (compute : ProverEnvironment F → Vector F m) : Circuit F (Vector (Variable F) m) :=
  fun (offset : ℕ) =>
    let vars := .mapRange m fun i => ⟨offset + i⟩
    (vars, [.witness m (.native compute)])

/-- Create a vector of expressions. -/
@[circuit_norm]
def witnessVectorNative (m : ℕ) (compute : ProverEnvironment F → Vector F m) : Circuit F (Vector (Expression F) m) :=
  fun (offset : ℕ) =>
    let vars := varFromOffset (fields m) offset
    (vars, [.witness m (.native compute)])

/-- Witness a single field element computed by the given witness-IR program,
returning the raw `Variable`. -/
@[circuit_norm]
def witnessVar (ir : WitgenIR F 1) : Circuit F (Variable F) :=
  fun (offset : ℕ) =>
    (⟨offset⟩, [.witness 1 ir])

/-- Witness a single field element computed by the given witness-IR program.
Prefer the generic `witness` entry point; an `FExpr` coerces into `WitgenIR F 1`. -/
@[circuit_norm]
def witnessField (ir : WitgenIR F 1) : Circuit F (Expression F) :=
  fun (offset : ℕ) =>
    (var ⟨offset⟩, [.witness 1 ir])

/-- Witness `m` field elements computed by a vector-shaped witness-IR expression.
Use `witnessIR` for programs with `let`-steps. -/
@[circuit_norm]
def witnessVector (m : ℕ) (out : Witgen.VExpr F m) :
    Circuit F (Vector (Expression F) m) :=
  fun (offset : ℕ) =>
    (varFromOffset (fields m) offset, [.witness m (.ir [] out)])

/-- Add a constraint. -/
@[circuit_norm]
def assertZero (e : Expression F) : Circuit F Unit := fun _ =>
  ((), [.assert e])

/-- Add a lookup. -/
@[circuit_norm]
def lookup {Row : TypeMap} [ProvableType Row] (table : Table F Row)  (entry : Row (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.lookup { table := table.toRaw, entry := toElements entry }])

end Circuit

/-- Emit an interaction to the channel -/
@[circuit_norm]
def Channel.emit {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (mult : Expression F) (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  let interaction : ChannelInteraction channel := ⟨ mult, msg, false ⟩
  ((), [.interact interaction.toRaw])

@[circuit_norm]
def Channel.pull {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  let interaction : ChannelInteraction channel := ⟨ -1, msg, true ⟩
  ((), [.interact interaction.toRaw])

@[circuit_norm]
def Channel.pullIf {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (enabled : Expression F) (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  let interaction : ChannelInteraction channel := ⟨ -enabled, msg, true ⟩
  ((), [.interact interaction.toRaw])

@[circuit_norm]
def Channel.push {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  let interaction : ChannelInteraction channel := ⟨ 1, msg, false ⟩
  ((), [.interact interaction.toRaw])

@[circuit_norm]
def Channel.pushIf {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (enabled : Expression F) (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  let interaction : ChannelInteraction channel := ⟨ enabled, msg, false ⟩
  ((), [.interact interaction.toRaw])

/-- Witness a value of a provable type computed by the given witness-IR program
(producing its `size α` field elements in `toElements` order).
IR-based counterpart of `ProvableType.witnessNative`. -/
@[circuit_norm]
def ProvableType.witness {α : TypeMap} [ProvableType α] (ir : WitgenIR F (size α)) :
    Circuit F (α (Expression F)) :=
  fun (offset : ℕ) =>
    (varFromOffset α offset, [.witness (size α) ir])

/-- Shape-exact evaluation for expression-copying struct witnesses (`<==`):
produces the same normal form as the closure it replaced. -/
@[circuit_norm]
theorem Witgen.WitgenIR.eval_ofExprs_toElements {α : TypeMap} [ProvableType α]
    (x : α (Expression F)) (env : ProverEnvironment F) :
    (Witgen.WitgenIR.ofExprs (toElements x)).eval env
      = toElements (Eval.eval env.toEnvironment x) := by
  rw [Witgen.WitgenIR.eval_ofExprs, ProvableType.toElements_eval]

/-- Create a new variable of an arbitrary "provable type". -/
@[circuit_norm]
def ProvableType.witnessNative {α : TypeMap} [ProvableType α] (compute : ProverEnvironment F → α F) :
    Circuit F (α (Expression F)) :=
  fun (offset : ℕ) =>
    let var := varFromOffset α offset
    (var, [.witness (size α) (.native fun env => compute env |> toElements)])

@[circuit_norm]
def ProvableVector.witnessNative {α : TypeMap} [NonEmptyProvableType α] (m : ℕ)
    (compute : ProverEnvironment F → Vector (α F) m) : Circuit F (Vector (α (Expression F)) m) :=
  ProvableType.witnessNative (α:=ProvableVector α m) compute

/--
If an environment "uses local witnesses", it means that the environment's evaluation
matches the output of the witness generator passed along with a `witness` declaration,
for all variables declared locally within the circuit.

This is the condition needed to prove completeness of a circuit.
-/
def ProverEnvironment.UsesLocalWitnesses (env : ProverEnvironment F) (offset : ℕ) (ops : Operations F) : Prop :=
  ops.forAllFlat offset { witness n _ compute := env.ExtendsVector (compute.eval env) n }

/--
Modification of `UsesLocalWitnesses` where subcircuits replace the condition with a custom statement.
-/
@[circuit_norm]
def ProverEnvironment.UsesLocalWitnessesCompleteness (env : ProverEnvironment F) (offset : ℕ) : List (Operation F) → Prop
  | [] => True
  | .witness m c :: ops => env.ExtendsVector (c.eval env) offset ∧ env.UsesLocalWitnessesCompleteness (offset + m) ops
  | .assert _ :: ops => env.UsesLocalWitnessesCompleteness offset ops
  | .lookup _ :: ops => env.UsesLocalWitnessesCompleteness offset ops
  | .interact _ :: ops => env.UsesLocalWitnessesCompleteness offset ops
  | .subcircuit s :: ops => s.ProverSpec env ∧ env.UsesLocalWitnessesCompleteness (offset + s.localLength) ops

/-- Same as `UsesLocalWitnesses`, but on flat operations -/
def ProverEnvironment.UsesLocalWitnessesFlat (env : ProverEnvironment F) (n : ℕ) (ops : List (FlatOperation F)) : Prop :=
  FlatOperation.forAll n { witness n _ compute := env.ExtendsVector (compute.eval env) n } ops

section
variable {Input Output : TypeMap}

/--
Channel lawfulness for an elaborated circuit.

This bundles the structural facts that connect the circuit's actual operations to its
declared channel interface.
-/
@[circuit_norm]
def ElaboratedCircuit.ChannelsLawful [CircuitType Input] [CircuitType Output]
    (main : Var Input F → Circuit F (Var Output F))
    (channelsWithGuarantees : List (RawChannel F)) : Prop :=
  ∀ input_var offset,
    ((main input_var).operations offset).ChannelsLawful
      channelsWithGuarantees

/-
Common base type for circuits that are to be used in formal proofs.

It contains the main circuit plus some of its properties in elaborated form, to make it
faster to reason about them in proofs.
-/
class ElaboratedCircuit (F : Type) (Input Output : TypeMap) [FiniteField F] [CircuitType Input] [CircuitType Output]
    (main : Var Input F → Circuit F (Var Output F)) where
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

  /-- expose the channel guarantees for end-to-end proofs -/
  channelsWithGuarantees : List (RawChannel F) := []

  channelsLawful : ElaboratedCircuit.ChannelsLawful main
      channelsWithGuarantees := by
    -- TODO this tactic would be more effective if it would unfold all channel declarations/uses.
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    try dsimp only [main]
    simp only [circuit_norm, seval]
    try first | ac_rfl | trivial | tauto

attribute [circuit_norm] ElaboratedCircuit.localLength ElaboratedCircuit.output
  ElaboratedCircuit.channelsWithGuarantees

end

export Circuit (witnessVar witnessField witnessVector
  witnessVarNative witnessFieldNative witnessVarsNative witnessVectorNative assertZero lookup)

-- general `witness` method

class Witnessable (F : Type) [FiniteField F] (value : outParam TypeMap) (var : TypeMap) [ProvableType value] where
  /-- Witness a value given per-element witness-IR expressions, in the shape of the
  value type itself (so the type is inferred from the argument, as with the old
  closure-based API). The main entry point. -/
  witness : value (Witgen.FExpr F) → Circuit F (var F)
  /-- Witness a value computed by a general witness-IR program (with `let`-steps and
  loops, which the per-element form cannot express). The first argument gives the
  result type, since a program's output length alone does not determine it. -/
  witnessIR : WitgenIR F (size value) → Circuit F (var F)
  /-- Witness a value computed by an arbitrary Lean closure (not exportable;
  the migration escape hatch). -/
  witnessNative : (ProverEnvironment F → value F) → Circuit F (var F)
  var_eq : var F = value (Expression F) := by rfl
  witness_def (xs : value (Witgen.FExpr F)) :
    witness xs = var_eq ▸ ProvableType.witness (.ofFExprs (toElements xs)) := by intros; rfl
  witnessIR_def (code : WitgenIR F (size value)) :
    witnessIR code = var_eq ▸ ProvableType.witness code := by intros; rfl
  witnessNative_eq (compute : ProverEnvironment F → value F) :
    witnessNative compute = var_eq ▸ ProvableType.witnessNative compute := by intros; rfl

export Witnessable (witness witnessNative)

/-- Witness a value computed by a general witness-IR program.
The value type is explicit because a program's output length alone does not determine it. -/
@[circuit_norm]
def witnessIR (value : TypeMap) [ProvableType value] {var : TypeMap}
    [inst : Witnessable F value var] (code : WitgenIR F (size value)) :
    Circuit F (var F) :=
  inst.witnessIR code

/-- Witness `m` field elements computed by a monadic witness-IR program.
Use this when the vector witness has shared `letF`/`letN` computations or compact loops. -/
@[circuit_norm]
def witnessVectorProgram (m : ℕ) (program : Witgen.M F (Witgen.VExpr F m)) :
    Circuit F (Vector (Expression F) m) :=
  ProvableType.witness (α := fields m) (Witgen.WitgenIR.build program)

/-- Witness a provable value computed by a monadic witness-IR program.
This is `witness`, but with shared `letF`/`letN` computations. -/
@[circuit_norm]
def witnessProgram {value : TypeMap} [ProvableType value] {var : TypeMap}
    [Witnessable F value var] (program : Witgen.M F (value (Witgen.FExpr F))) :
    Circuit F (var F) :=
  witnessIR value (Witgen.M.toIR program)

instance : Witnessable F field Expression where
  witness e := witnessField (.ofFExpr e)
  witnessIR := witnessField
  witnessNative := witnessFieldNative

instance {m : ℕ} : Witnessable F (Vector · m) (fun F => Vector (Expression F) m) where
  witness v := witnessVector m (.lit v)
  witnessIR := ProvableType.witness
  witnessNative := witnessVectorNative m

instance (α : TypeMap) [ProvableType α] : Witnessable F α (Var α) where
  witness xs := ProvableType.witness (.ofFExprs (toElements xs))
  witnessIR := ProvableType.witness
  witnessNative := ProvableType.witnessNative

instance {m : ℕ} (α : TypeMap) [NonEmptyProvableType α] :
    Witnessable F (ProvableVector α m) (Var (ProvableVector α m)) where
  witness xs := ProvableType.witness (.ofFExprs (toElements xs))
  witnessIR := ProvableType.witness
  witnessNative := ProvableVector.witnessNative m

-- witness generation

/-- Build a `ProverEnvironment` from a witness list and a specific prover hint. -/
def ProverEnvironment.fromList (witnesses : List F) (hint : ProverHint F) : ProverEnvironment F where
  get i := witnesses[i]?.getD 0
  data _ _ := #[]
  hint

def FlatOperation.dynamicWitness (hint : ProverHint F) (op : FlatOperation F) (acc : List F) : List F := match op with
  | .witness _ compute => (compute.eval (.fromList acc hint)).toList
  | .assert _ => []
  | .lookup _ => []
  | .interact _ => []

def FlatOperation.dynamicWitnesses (ops : List (FlatOperation F)) (hint : ProverHint F) (init : List F) : List F :=
  ops.foldl (fun acc op => acc ++ op.dynamicWitness hint acc) init

def FlatOperation.proverEnvironment (ops : List (FlatOperation F)) (hint : ProverHint F) (init : List F) :=
  ProverEnvironment.fromList (FlatOperation.dynamicWitnesses ops hint init) hint

def ProverEnvironment.AgreesBelow (n : ℕ) (env env' : ProverEnvironment F) :=
  ∀ i < n, env.get i = env'.get i

def ProverEnvironment.OnlyAccessedBelow (n : ℕ) (f : ProverEnvironment F → α) :=
  ∀ env env', env.AgreesBelow n env' → f env = f env'

/--
A circuit has _computable witnesses_ when witness generators only depend on the environment at indices smaller than the current offset.
This allows us to compute a concrete environment from witnesses, by successively extending an array with new witnesses.
-/
def Operations.ComputableWitnesses (ops : Operations F) (n : ℕ) (env env' : ProverEnvironment F) : Prop :=
  ops.forAllFlat n { witness n _ compute := env.AgreesBelow n env' → compute.eval env = compute.eval env' }

def Circuit.ComputableWitnesses (circuit : Circuit F α) (n : ℕ) :=
  ∀ env env', (circuit.operations n).ComputableWitnesses n env env'

/--
If a circuit satisfies `computableWitnesses`, we can construct a concrete environment
that satisfies `UsesLocalWitnesses`. (Proof in `Theorems`.)
-/
def Circuit.proverEnvironment (circuit : Circuit F α) (hint : ProverHint F) (init : List F := []) : ProverEnvironment F :=
  .fromList (FlatOperation.dynamicWitnesses (circuit.operations init.length).toFlat hint init) hint

-- witness generators used for AIR trace export
-- TODO unify with the definitions above

def FlatOperation.witnessGenerators : (l : List (FlatOperation F)) → Vector (ProverEnvironment F → F) (localLength l)
  | [] => #v[]
  | .witness m c :: ops => Vector.mapFinRange m (fun i env => (c.eval env)[i.val]) ++ witnessGenerators ops
  | .assert _ :: ops => witnessGenerators ops
  | .lookup _ :: ops => witnessGenerators ops
  | .interact _ :: ops => witnessGenerators ops

def Operations.witnessGenerators : (ops : Operations F) → Vector (ProverEnvironment F → F) ops.localLength
  | [] => #v[]
  | .witness m c :: ops => Vector.mapFinRange m (fun i env => (c.eval env)[i.val]) ++ witnessGenerators ops
  | .assert _ :: ops => witnessGenerators ops
  | .lookup _ :: ops => witnessGenerators ops
  | .interact _ :: ops => witnessGenerators ops
  | .subcircuit s :: ops => (s.localLength_eq ▸ FlatOperation.witnessGenerators s.ops.toFlat) ++ witnessGenerators ops

-- statements about constant length or output

namespace Circuit
/--
The given family of circuits all share the same `localLength`, for all inputs.

This is a bit stronger than the assumption on local length implicit in `ElaboratedCircuit`,
but still the typical case.
-/
class ConstantLength (circuit : α → Circuit F β) where
  localLength : ℕ
  localLength_eq : ∀ (a : α) (n : ℕ), (circuit a).localLength n = localLength

@[circuit_norm]
def ConstantLength.fromConstantLength {circuit : α → Circuit F β} [Inhabited α]
    (h : ∀ (a : α) n, (circuit a).localLength n = (circuit default).localLength 0) : ConstantLength circuit where
  localLength := (circuit default).localLength 0
  localLength_eq a n := h a n

/-- The output of this circuit does not depend on the input. -/
@[circuit_norm]
def ConstantOutput (circuit : α → Circuit F β) [Inhabited α] :=
  ∀ (x : α) (n : ℕ), (circuit x).output n = (circuit default).output n

syntax "infer_constant_length" : tactic

macro_rules
  | `(tactic|infer_constant_length) => `(tactic|(
    apply ConstantLength.fromConstantLength
    try simp only [circuit_norm]
    try intros
    try trivial
    try ac_rfl))

example :
  let add (x : Expression F) := do
    let y : Expression F ← witnessNative fun _ => 1
    let z ← witnessNative fun eval => eval (x + y)
    assertZero (x + y - z)
    pure z
  ConstantLength add := by infer_constant_length

-- basic simp lemmas

theorem pure_operations_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).operations n = [] := rfl

theorem bind_operations_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl

theorem map_operations_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).operations n = f.operations n := rfl

theorem pure_localLength_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).localLength n = 0 := rfl

theorem bind_localLength_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
    (f >>= g).localLength n = f.localLength n + (g (f.output n)).localLength (n + f.localLength n) := by
  show (f.operations n ++ (g _).operations _).localLength = _
  rw [Operations.append_localLength]

theorem map_localLength_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).localLength n = f.localLength n := rfl

theorem pure_output_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).output n = a := rfl

theorem bind_output_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).output n = (g (f.output n)).output (n + f.localLength n) := rfl

theorem map_output_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).output n = g (f.output n) := rfl

@[circuit_norm]
theorem bind_forAll {f : Circuit F α} {g : α → Circuit F β} {prop : Condition F} :
  ((f >>= g).operations n).forAll n prop ↔
    (f.operations n).forAll n prop ∧ (((g (f.output n)).operations (n + f.localLength n)).forAll (n + f.localLength n)) prop := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl
  rw [h_ops, Operations.forAll_append, add_comm n]

end Circuit

-- `circuit_norm` attributes

-- basic logical simplifcations
attribute [circuit_norm] true_and and_true true_implies implies_true forall_const gt_iff_lt
  not_true_eq_false ne_eq false_implies and_false false_and
  and_self or_self or_true or_false true_or false_or
  Bool.false_eq_true Bool.true_eq_false

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
  Vector.toArray_push Array.toList_push List.append_assoc
  Vector.eq_mk Vector.mk_eq

-- `getElem` lemmas should be tried before expanding Vectors/Lists
attribute [circuit_norm ↓] Fin.getElem_fin
  Vector.getElem_map Vector.getElem_mapFinRange Vector.getElem_mapRange Vector.getElem_finRange
  Vector.getElem_push Vector.getElem_set Vector.getElem_cast
  Vector.getElem_mk Vector.getElem_toArray Vector.getElem_ofFn
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
attribute [circuit_norm] neg_mul one_mul add_zero zero_add neg_zero neg_eq_zero one_ne_zero zero_ne_one
  Nat.reduceAdd

attribute [circuit_norm] List.append_nil

-- simp lemmas useful to unfold subcircuit channels

attribute [circuit_norm] List.nil_subset List.subset_cons_of_subset List.Subset.refl
attribute [circuit_norm] List.Forall List.flatten_cons List.flatten_nil List.Sublist.refl
attribute [circuit_norm] List.mem_cons List.mem_nil_iff List.mem_append List.mem_ofFn

@[circuit_norm]
lemma List.ofFn_singleton_flatten {α : Type} {m : ℕ} (f : Fin m → α) :
    (List.ofFn fun i : Fin m => [f i]).flatten = List.ofFn f := by
  induction m <;> simp_all

@[circuit_norm]
lemma List.ofFn_nil_flatten {α : Type} {m : ℕ} :
    (List.ofFn fun _ : Fin m => ([] : List α)).flatten = [] := by
  simp

attribute [circuit_norm] forall_eq reduceIte String.reduceEq decide_false
