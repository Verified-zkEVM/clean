/-
This file introduces `ExplicitCircuit`, a variant of `ElaboratedCircuit` that can be auto-derived
using the `infer_explicit_circuit(s)` tactic.

This could be useful to simplify circuit statements with less user intervention.
-/
import Clean.Utils.Misc
import Clean.Circuit.Subcircuit
variable {n : ℕ} {F : Type} [Field F] {sentences : PropertySet F} {α β : Type}

class ExplicitCircuit (circuit : Circuit sentences α) where
  /-- an "explicit" circuit is encapsulated by three functions of the input offset -/
  output : ℕ → α
  localLength : ℕ → ℕ
  operations : ℕ → Operations sentences

  /-- the functions have to match the circuit -/
  output_eq : ∀ n : ℕ, circuit.output n = output n := by intro _; rfl
  localLength_eq : ∀ n : ℕ, circuit.localLength n = localLength n := by intro _; rfl
  operations_eq : ∀ n : ℕ, circuit.operations n = operations n := by intro _; rfl

  /-- same condition as in `ElaboratedCircuit`: subcircuits must be consistent with the current offset -/
  subcircuitsConsistent : ∀ n : ℕ, (circuit.operations n).SubcircuitsConsistent n := by
    intro _; and_intros <;> try first | ac_rfl | trivial

/-- family of explicit circuits -/
class ExplicitCircuits (circuit : α → Circuit sentences β) where
  output : α → ℕ → β
  localLength : α → ℕ → ℕ
  operations : α → ℕ → Operations sentences
  output_eq : ∀ (a : α) (n : ℕ), (circuit a).output n = output a n := by intro _ _; rfl
  localLength_eq : ∀ (a : α) (n : ℕ), (circuit a).localLength n = localLength a n := by intro _ _; rfl
  operations_eq : ∀ (a : α) (n : ℕ), (circuit a).operations n = operations a n := by intro _ _; rfl
  subcircuitsConsistent : ∀ (a : α) (n : ℕ), ((circuit a).operations n).SubcircuitsConsistent n := by
    intro _ _; and_intros <;> try first | ac_rfl | trivial

-- move between family and single explicit circuit

instance ExplicitCircuits.from_single {circuit : α → Circuit sentences β}
    (explicit : ∀ a, ExplicitCircuit (circuit a)) : ExplicitCircuits circuit where
  output a n := (explicit a).output n
  localLength a n := (explicit a).localLength n
  operations a n := (explicit a).operations n
  output_eq a n := (explicit a).output_eq n
  localLength_eq a n := (explicit a).localLength_eq n
  operations_eq a n := (explicit a).operations_eq n
  subcircuitsConsistent a n := (explicit a).subcircuitsConsistent n

instance ExplicitCircuits.to_single (circuit : α → Circuit sentences β) (a : α)
    [explicit : ExplicitCircuits circuit] : ExplicitCircuit (circuit a) where
  output n := output circuit a n
  localLength n := explicit.localLength a n
  operations n := operations circuit a n
  output_eq n := output_eq a n
  localLength_eq n := localLength_eq a n
  operations_eq n := operations_eq a n
  subcircuitsConsistent n := subcircuitsConsistent a n

-- `pure` is an explicit circuit
instance ExplicitCircuit.from_pure {a : α} : ExplicitCircuit (pure a : Circuit sentences α) where
  output _ := a
  localLength _ := 0
  operations _ := []

instance ExplicitCircuits.from_pure {f : α → β} : ExplicitCircuits (fun a => pure (f a) : α → Circuit sentences β) where
  output a _ := f a
  localLength _ _ := 0
  operations _ _ := []

-- `bind` of two explicit circuits yields an explicit circuit
instance ExplicitCircuit.from_bind {f : Circuit sentences α} {g : α → Circuit sentences β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) : ExplicitCircuit (f >>= g) where
  output n :=
    let a := output f n
    output (g a) (n + localLength f n)

  localLength n :=
    let a := output f n
    localLength f n + localLength (g a) (n + localLength f n)

  operations n :=
    let a := output f n
    operations f n ++ operations (g a) (n + localLength f n)

  output_eq n := by rw [Circuit.bind_output_eq, output_eq, output_eq, localLength_eq]
  localLength_eq n := by rw [Circuit.bind_localLength_eq, localLength_eq, output_eq, localLength_eq]
  operations_eq n := by rw [Circuit.bind_operations_eq, operations_eq, output_eq, localLength_eq, operations_eq]
  subcircuitsConsistent n := by
    rw [Operations.SubcircuitsConsistent, Circuit.bind_forAll]
    exact ⟨ f_explicit.subcircuitsConsistent .., (g_explicit _).subcircuitsConsistent .. ⟩

-- `map` of an explicit circuit yields an explicit circuit
instance ExplicitCircuit.from_map {f : α → β} {g : Circuit sentences α}
    (g_explicit : ExplicitCircuit g) : ExplicitCircuit (f <$> g) where
  output n := output g n |> f
  localLength n := localLength g n
  operations n := operations g n

  output_eq n := by rw [Circuit.map_output_eq, output_eq]
  localLength_eq n := by rw [Circuit.map_localLength_eq, localLength_eq]
  operations_eq n := by rw [Circuit.map_operations_eq, operations_eq]
  subcircuitsConsistent n := by
    rw [Circuit.map_operations_eq]
    exact g_explicit.subcircuitsConsistent n

-- basic operations are explicit circuits

instance : ExplicitCircuits (F:=F) (sentences:=sentences) witnessVar where
  output _ n := ⟨ n ⟩
  localLength _ _ := 1
  operations c n := [.witness 1 fun env => #v[c env]]

instance {k : ℕ} {c : Environment F → Vector F k} : ExplicitCircuit (sentences:=sentences) (witnessVars k c) where
  output n := .mapRange k fun i => ⟨n + i⟩
  localLength _ := k
  operations n := [.witness k c]

instance {α : TypeMap} [ProvableType α] : ExplicitCircuits (sentences:=sentences) (ProvableType.witness (α:=α) (F:=F)) where
  output _ n := varFromOffset α n
  localLength _ _ := size α
  operations c n := [.witness (size α) (toElements ∘ c)]

instance {value var : TypeMap} [ProvableType value] [inst : Witnessable F sentences value var] :
    ExplicitCircuits (witness (F:=F) (sentences:=sentences) (value:=value) (var:=var)) where
  output _ n := inst.var_eq ▸ varFromOffset value n
  output_eq c n := by
    rw [inst.witness_eq]
    show _ = inst.var_eq ▸ (ProvableType.witness (sentences:=sentences) c).output n
    rw [Circuit.output, Circuit.output, eqRec_eq_cast, eqRec_eq_cast,
      cast_fst, cast_apply (by rw [inst.var_eq])]

  localLength _ _ := size value
  localLength_eq c n := by
    rw [inst.witness_eq, Circuit.localLength, eqRec_eq_cast,
      cast_apply (by rw [inst.var_eq]), snd_cast (by rw [inst.var_eq])]
    rfl

  operations c n := [.witness (size value) (toElements ∘ c)]
  operations_eq c n := by
    rw [inst.witness_eq, Circuit.operations, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    rfl

  subcircuitsConsistent c n := by
    simp only [circuit_norm]
    rw [inst.witness_eq, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    reduce
    trivial

instance : ExplicitCircuits (F:=F) (sentences:=sentences) assertZero where
  output _ _ := ()
  localLength _ _ := 0
  operations e n := [.assert e]

instance {α : TypeMap} [ProvableType α] {table : Table F α} : ExplicitCircuits (F:=F) (sentences:=sentences) (lookup table) where
  output _ _ := ()
  localLength _ _ := 0
  operations entry n := [.lookup { table := table.toRaw, entry := toElements entry }]

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {sentences : PropertySet F} {order : SentenceOrder sentences} {circuit : FormalCircuit F sentences order β α} {input} :
    ExplicitCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]

instance {β : TypeMap} [ProvableType β] {sentences : PropertySet F} {order : SentenceOrder sentences} {circuit : FormalAssertion F sentences order β} {input} :
    ExplicitCircuit (assertion circuit input) where
  output n := ()
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]

syntax "infer_explicit_circuit" : tactic

macro_rules
  | `(tactic|infer_explicit_circuit) => `(tactic|(
    try intros
    try repeat infer_instance
    repeat (
      try intros
      first
        | apply ExplicitCircuit.from_bind
        | apply ExplicitCircuit.from_map
      repeat infer_instance
    )))

syntax "infer_explicit_circuits" : tactic

macro_rules
  | `(tactic|infer_explicit_circuits) => `(tactic|(
    apply ExplicitCircuits.from_single (by infer_explicit_circuit)))

-- this tactic is pretty good at inferring explicit circuits!
section

-- single
example {sentences : PropertySet F} : ExplicitCircuit (witness fun _ => (0 : F) : Circuit sentences (Expression F)) := by infer_explicit_circuit

example {sentences : PropertySet F} :
  let add : Circuit sentences (Expression F) := do
    let x : Expression F ← witness fun _ => 0
    let y ← witness fun _ => 1
    let z ← witness fun eval => eval (x + y)
    assertZero (x + y - z)
    return z

  ExplicitCircuit add := by infer_explicit_circuit

-- family
example {sentences : PropertySet F} : ExplicitCircuits (sentences:=sentences) (witnessField (F:=F)) := by infer_explicit_circuits

example {sentences : PropertySet F} :
  let add (x : Expression F) : Circuit sentences (Expression F) := do
    let y : Expression F ← witness fun _ => 1
    let z ← witness fun eval => eval (x + y)
    assertZero (x + y - z)
    return z

  ExplicitCircuits add := by infer_explicit_circuits
end

attribute [explicit_circuit_norm] ExplicitCircuit.localLength ExplicitCircuit.operations ExplicitCircuit.output
attribute [explicit_circuit_norm] ExplicitCircuits.localLength ExplicitCircuits.operations ExplicitCircuits.output
attribute [explicit_circuit_norm] ExplicitCircuits.to_single ExplicitCircuits.from_single
attribute [explicit_circuit_norm] ElaboratedCircuit.localLength ElaboratedCircuit.output
attribute [explicit_circuit_norm] size
