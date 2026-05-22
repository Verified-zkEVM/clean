/-
This file introduces `ExplicitCircuit`, a variant of `ElaboratedCircuit` that can be auto-derived
using the `infer_explicit_circuit(s)` tactic.

This could be useful to simplify circuit statements with less user intervention.
-/
import Clean.Utils.Misc
import Clean.Circuit.Basic
variable {n : ℕ} {F : Type} [Field F] {α β : Type}

class ExplicitCircuit (circuit : Circuit F α) where
  /-- an "explicit" circuit is encapsulated by three functions of the input offset -/
  output : ℕ → α
  localLength : ℕ → ℕ
  operations : ℕ → Operations F

  /-- the functions have to match the circuit -/
  output_eq : ∀ n : ℕ, circuit.output n = output n := by intro _; rfl
  localLength_eq : ∀ n : ℕ, circuit.localLength n = localLength n := by intro _; rfl
  operations_eq : ∀ n : ℕ, circuit.operations n = operations n := by intro _; rfl

  /-- same condition as in `ElaboratedCircuit`: subcircuits must be consistent with the current offset -/
  subcircuitsConsistent : ∀ n : ℕ, (circuit.operations n).SubcircuitsConsistent n := by
    intro _; and_intros <;> try first | ac_rfl | trivial
  /-- channel metadata explicitly collected from the circuit structure -/
  channelsWithGuarantees : ℕ → List (RawChannel F)
  channelsWithRequirements : ℕ → List (RawChannel F)
  channelsLawful : ∀ n : ℕ, (circuit.operations n).ChannelsLawful
      (channelsWithGuarantees n) (channelsWithRequirements n) [] := by
    intro n
    try rw [operations_eq n]
    try dsimp only [channelsWithGuarantees, channelsWithRequirements, operations]
    simp [circuit_norm]
    all_goals try first | ac_rfl | trivial | tauto

/-- family of explicit circuits -/
class ExplicitCircuits (circuit : α → Circuit F β) where
  output : α → ℕ → β
  localLength : α → ℕ → ℕ
  operations : α → ℕ → Operations F
  output_eq : ∀ (a : α) (n : ℕ), (circuit a).output n = output a n := by intro _ _; rfl
  localLength_eq : ∀ (a : α) (n : ℕ), (circuit a).localLength n = localLength a n := by intro _ _; rfl
  operations_eq : ∀ (a : α) (n : ℕ), (circuit a).operations n = operations a n := by intro _ _; rfl
  subcircuitsConsistent : ∀ (a : α) (n : ℕ), ((circuit a).operations n).SubcircuitsConsistent n := by
    intro _ _; and_intros <;> try first | ac_rfl | trivial
  /-- channel metadata explicitly collected from the circuit structure -/
  channelsWithGuarantees : α → ℕ → List (RawChannel F)
  channelsWithRequirements : α → ℕ → List (RawChannel F)
  channelsLawful : ∀ (a : α) (n : ℕ), ((circuit a).operations n).ChannelsLawful
      (channelsWithGuarantees a n) (channelsWithRequirements a n) [] := by
    intro a n
    try rw [operations_eq a n]
    try dsimp only [channelsWithGuarantees, channelsWithRequirements, operations]
    simp [Operations.ChannelsLawful, circuit_norm]
    all_goals try first | ac_rfl | trivial | tauto

/-- From an `ExplicitCircuit`, we can usually derive an `ElaboratedCircuit` -/
class ExplicitCircuits.IsElaborated (circuit : α → Circuit F β) (explicit : ExplicitCircuits circuit) where
  localLength_eq : ∀ (a : α) (n m : ℕ),
    explicit.localLength a n = explicit.localLength a m := by intros; rfl
  channelsWithGuarantees_eq : ∀ (a a' : α) (n m : ℕ),
    explicit.channelsWithGuarantees a n = explicit.channelsWithGuarantees a' m := by intros; rfl
  channelsWithRequirements_eq : ∀ (a a' : α) (n m : ℕ),
    explicit.channelsWithRequirements a n = explicit.channelsWithRequirements a' m := by intros; rfl

@[circuit_norm, explicit_circuit_norm]
def ExplicitCircuits.toElaborated {Input Output : TypeMap}
  [CircuitType Input] [CircuitType Output] [Inhabited (Var Input F)]
  (circuit : Var Input F → Circuit F (Var Output F))
  (explicit : ExplicitCircuits circuit)
  (explicit_elaborated : ExplicitCircuits.IsElaborated circuit explicit) :
    ElaboratedCircuit F Input Output circuit where
  localLength a := explicit.localLength a 0
  output a n := explicit.output a n
  localLength_eq a n := by
    rw [explicit.localLength_eq, explicit_elaborated.localLength_eq a n 0]
  output_eq a n := explicit.output_eq a n
  subcircuitsConsistent a n := explicit.subcircuitsConsistent a n
  channelsWithGuarantees := explicit.channelsWithGuarantees default 0
  channelsWithRequirements := explicit.channelsWithRequirements default 0
  channelsLawful a n := by
    convert explicit.channelsLawful a n using 1
    rw [explicit_elaborated.channelsWithGuarantees_eq]
    rw [explicit_elaborated.channelsWithRequirements_eq]

@[circuit_norm, explicit_circuit_norm]
def ElaboratedCircuit.fromExplicit {Input Output : TypeMap}
  [CircuitType Input] [CircuitType Output] [Inhabited (Var Input F)]
  {circuit : Var Input F → Circuit F (Var Output F)}
  (explicit : ExplicitCircuits circuit)
  (explicit_elaborated : ExplicitCircuits.IsElaborated circuit explicit) :
    ElaboratedCircuit F Input Output circuit := explicit.toElaborated _ explicit_elaborated

structure ElaboratedCircuit.Data {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : Var Input F → Circuit F (Var Output F)} (elaborated : ElaboratedCircuit F Input Output circuit) where
  localLength : Var Input F → ℕ := elaborated.localLength
  output : Var Input F → ℕ → Var Output F := elaborated.output
  channelsWithGuarantees : List (RawChannel F) := elaborated.channelsWithGuarantees

@[circuit_norm, explicit_circuit_norm]
def ElaboratedCircuit.withData {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
  {circuit : Var Input F → Circuit F (Var Output F)}
  (derived : ElaboratedCircuit F Input Output circuit)
  (data : ElaboratedCircuit.Data derived)
  (data_eq :
    (∀ a, derived.localLength a = data.localLength a) ∧
    (∀ a n, derived.output a n = data.output a n) ∧
    (derived.channelsWithGuarantees ⊆ data.channelsWithGuarantees) := by
      and_intros
      · intro a; ac_rfl
      · intro a n; rfl
      · try simp only [circuit_norm]; try grind; done) :
    ElaboratedCircuit F Input Output circuit where
  localLength := data.localLength
  output := data.output
  localLength_eq a n := by
    rw [derived.localLength_eq, data_eq.1]
  output_eq a n := by
    rw [derived.output_eq, data_eq.2.1]
  subcircuitsConsistent := derived.subcircuitsConsistent
  channelsWithGuarantees := data.channelsWithGuarantees
  channelsWithRequirements := derived.channelsWithRequirements
  exposedChannels := derived.exposedChannels
  channelsLawful a n := by
    have h_lawful := derived.channelsLawful a n
    have channelsWithGuarantees_subset := data_eq.2.2
    dsimp only [Operations.ChannelsLawful] at h_lawful ⊢
    obtain ⟨h_g_sub, h_g, h_r_sub, h_r, h_shallow, h_exposed, h_sub⟩ := h_lawful
    and_intros
    · exact List.Subset.trans h_g_sub channelsWithGuarantees_subset
    · intro env
      exact (h_g env).mono channelsWithGuarantees_subset
    · exact h_r_sub
    · exact h_r
    · intro channel h_mem
      rcases h_shallow channel h_mem with h_channel | h_channel
      · exact Or.inl (channelsWithGuarantees_subset h_channel)
      · exact Or.inr h_channel
    · exact h_exposed
    · exact h_sub

-- move between family and single explicit circuit

def ExplicitCircuits.fromSingle {circuit : α → Circuit F β}
    (explicit : ∀ a, ExplicitCircuit (circuit a)) : ExplicitCircuits circuit where
  output a n := (explicit a).output n
  localLength a n := (explicit a).localLength n
  operations a n := (explicit a).operations n
  output_eq a n := (explicit a).output_eq n
  localLength_eq a n := (explicit a).localLength_eq n
  operations_eq a n := (explicit a).operations_eq n
  subcircuitsConsistent a n := (explicit a).subcircuitsConsistent n
  channelsWithGuarantees a n := (explicit a).channelsWithGuarantees n
  channelsWithRequirements a n := (explicit a).channelsWithRequirements n
  channelsLawful a n := (explicit a).channelsLawful n

instance ExplicitCircuits.toSingle (circuit : α → Circuit F β) (a : α)
    [explicit : ExplicitCircuits circuit] : ExplicitCircuit (circuit a) where
  output n := output circuit a n
  localLength n := explicit.localLength a n
  operations n := operations circuit a n
  output_eq n := output_eq a n
  localLength_eq n := localLength_eq a n
  operations_eq n := operations_eq a n
  subcircuitsConsistent n := subcircuitsConsistent a n
  channelsWithGuarantees n := channelsWithGuarantees circuit a n
  channelsWithRequirements n := channelsWithRequirements circuit a n
  channelsLawful n := channelsLawful a n

instance ExplicitCircuits.fromProvableInputOutput {α β : TypeMap} [ProvableType α] [ProvableType β]
  {circuit : Var α F → Circuit F (Var β F)} [explicit : ExplicitCircuits circuit] :
  ExplicitCircuits (circuit : α (Expression F) → Circuit F (β (Expression F))) := explicit

-- `pure` is an explicit circuit
instance ExplicitCircuit.from_pure {a : α} : ExplicitCircuit (pure a : Circuit F α) where
  output _ := a
  localLength _ := 0
  operations _ := []
  channelsWithGuarantees _ := []
  channelsWithRequirements _ := []

instance ExplicitCircuits.from_pure {f : α → β} : ExplicitCircuits (fun a => pure (f a) : α → Circuit F β) where
  output a _ := f a
  localLength _ _ := 0
  operations _ _ := []
  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := []

-- `bind` of two explicit circuits yields an explicit circuit
instance ExplicitCircuit.from_bind {f : Circuit F α} {g : α → Circuit F β}
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

  channelsWithGuarantees n :=
    let a := output f n
    channelsWithGuarantees f n ++ channelsWithGuarantees (g a) (n + localLength f n)

  channelsWithRequirements n :=
    let a := output f n
    channelsWithRequirements f n ++ channelsWithRequirements (g a) (n + localLength f n)

  output_eq n := by rw [Circuit.bind_output_eq, output_eq, output_eq, localLength_eq]
  localLength_eq n := by rw [Circuit.bind_localLength_eq, localLength_eq, output_eq, localLength_eq]
  operations_eq n := by rw [Circuit.bind_operations_eq, operations_eq, output_eq, localLength_eq, operations_eq]
  subcircuitsConsistent n := by
    rw [Operations.SubcircuitsConsistent, Circuit.bind_forAll]
    exact ⟨ f_explicit.subcircuitsConsistent .., (g_explicit _).subcircuitsConsistent .. ⟩
  channelsLawful n := by
    rw [Circuit.bind_operations_eq, output_eq, localLength_eq]
    apply Operations.channelsLawful_append_of_channelsLawful
    · exact f_explicit.channelsLawful n
    · exact (g_explicit (output f n)).channelsLawful (n + localLength f n)

instance ExplicitCircuit.from_bind_tc {f : Circuit F α} {g : α → Circuit F β}
    [f_explicit : ExplicitCircuit f] [g_explicit : ∀ a : α, ExplicitCircuit (g a)] :
    ExplicitCircuit (f >>= g) :=
  ExplicitCircuit.from_bind f_explicit g_explicit

-- `map` of an explicit circuit yields an explicit circuit
instance ExplicitCircuit.from_map {f : α → β} {g : Circuit F α}
    (g_explicit : ExplicitCircuit g) : ExplicitCircuit (f <$> g) where
  output n := output g n |> f
  localLength n := localLength g n
  operations n := operations g n
  channelsWithGuarantees n := channelsWithGuarantees g n
  channelsWithRequirements n := channelsWithRequirements g n

  output_eq n := by rw [Circuit.map_output_eq, output_eq]
  localLength_eq n := by rw [Circuit.map_localLength_eq, localLength_eq]
  operations_eq n := by rw [Circuit.map_operations_eq, operations_eq]
  subcircuitsConsistent n := by
    rw [Circuit.map_operations_eq]
    exact g_explicit.subcircuitsConsistent n
  channelsLawful n := by
    rw [Circuit.map_operations_eq]
    exact g_explicit.channelsLawful n

-- basic operations are explicit circuits

instance : ExplicitCircuits (F:=F) witnessVar where
  output _ n := ⟨ n ⟩
  localLength _ _ := 1
  operations c n := [.witness 1 fun env => #v[c env]]
  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := []

instance {k : ℕ} {c : ProverEnvironment F → Vector F k} : ExplicitCircuit (witnessVars k c) where
  output n := .mapRange k fun i => ⟨n + i⟩
  localLength _ := k
  operations n := [.witness k c]
  channelsWithGuarantees _ := []
  channelsWithRequirements _ := []

instance {k : ℕ} {c : ProverEnvironment F → Vector F k} : ExplicitCircuit (witnessVector k c) where
  output n := varFromOffset (fields k) n
  localLength _ := k
  operations n := [.witness k c]
  channelsWithGuarantees _ := []
  channelsWithRequirements _ := []

instance {α : TypeMap} [ProvableType α] : ExplicitCircuits (ProvableType.witness (α:=α) (F:=F)) where
  output _ n := varFromOffset α n
  localLength _ _ := size α
  operations c n := [.witness (size α) (toElements ∘ c)]
  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := []

instance {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var] :
    ExplicitCircuits (witness (F:=F) (value:=value) (var:=var)) where
  output _ n := inst.var_eq ▸ varFromOffset value n
  output_eq c n := by
    rw [inst.witness_eq]
    show _ = inst.var_eq ▸ (ProvableType.witness c).output n
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

  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := []

  subcircuitsConsistent c n := by
    simp only [circuit_norm]
    rw [inst.witness_eq, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    reduce
    trivial
  channelsLawful c n := by
    simp only [circuit_norm]
    rw [inst.witness_eq, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    simp [circuit_norm]

instance : ExplicitCircuits (F:=F) assertZero where
  output _ _ := ()
  localLength _ _ := 0
  operations e n := [.assert e]
  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := []

instance {α : TypeMap} [ProvableType α] {table : Table F α} : ExplicitCircuits (F:=F) (lookup table) where
  output _ _ := ()
  localLength _ _ := 0
  operations entry n := [.lookup { table := table.toRaw, entry := toElements entry }]
  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := []

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message}
    {mult : Expression F} :
    ExplicitCircuits (F:=F) (channel.emit mult) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.emitted mult msg).toRaw]
  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := [channel.toRaw]

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message} :
    ExplicitCircuits (F:=F) (channel.pull) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pulled msg).toRaw]
  channelsWithGuarantees _ _ := [channel.toRaw]
  channelsWithRequirements _ _ := []

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message} :
    ExplicitCircuits (F:=F) (channel.push) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pushed msg).toRaw]
  channelsWithGuarantees _ _ := []
  channelsWithRequirements _ _ := [channel.toRaw]

attribute [explicit_circuit_norm, circuit_norm] ExplicitCircuit.localLength ExplicitCircuit.operations ExplicitCircuit.output
  ExplicitCircuit.channelsWithGuarantees ExplicitCircuit.channelsWithRequirements
attribute [explicit_circuit_norm, circuit_norm] ExplicitCircuits.localLength ExplicitCircuits.operations ExplicitCircuits.output
  ExplicitCircuits.channelsWithGuarantees ExplicitCircuits.channelsWithRequirements
attribute [explicit_circuit_norm, circuit_norm] ExplicitCircuits.toSingle ExplicitCircuits.fromSingle
attribute [explicit_circuit_norm] ElaboratedCircuit.localLength ElaboratedCircuit.output
attribute [explicit_circuit_norm] size

syntax "infer_explicit_circuit" : tactic

macro_rules
  | `(tactic|infer_explicit_circuit) => `(tactic|(
    try intros
    try repeat infer_instance
    repeat (
      try intros
      first
        | infer_instance
        | apply ExplicitCircuit.from_bind
        | apply ExplicitCircuit.from_map
      repeat infer_instance
    )
    done))

syntax "infer_explicit_circuits" : tactic

macro_rules
  | `(tactic|infer_explicit_circuits) => `(tactic|(
    -- unfold head. TODO is there a better way?
    try conv => congr; whnf
    apply ExplicitCircuits.fromSingle
    intro a
    infer_explicit_circuit
    ))

-- TODO this is needed because `conv => congr; whnf` creates terms involving `Eq.mpr`
attribute [explicit_circuit_norm, circuit_norm] eq_mpr_eq_cast cast_eq

syntax "infer_elaborated_circuit" : tactic
syntax "infer_elaborated_circuit_with" term : tactic
syntax "infer_elaborated_circuit_with" term " using " term : tactic

macro_rules
  | `(tactic|infer_elaborated_circuit) => `(tactic|(
    refine ExplicitCircuits.toElaborated _ ?explicit ?elaborated
    · infer_explicit_circuits
    · exact ExplicitCircuits.IsElaborated.mk
  ))

macro_rules
  | `(tactic|infer_elaborated_circuit_with $data:term using $data_eq:term) => `(tactic|(
    exact ElaboratedCircuit.withData (by infer_elaborated_circuit) $data $data_eq
  ))
  | `(tactic|infer_elaborated_circuit_with $data:term) => `(tactic|(
    exact ElaboratedCircuit.withData (by infer_elaborated_circuit) $data
  ))

-- this tactic is pretty good at inferring explicit circuits!
section

-- single
example : ExplicitCircuit (witness fun _ => (0 : F) : Circuit F (Expression F)) := by infer_explicit_circuit

example :
  let add := do
    let x : Expression F ← witness fun _ => 0
    let y ← witness fun _ => 1
    let z ← witness fun eval => eval (x + y)
    assertZero (x + y - z)
    return z

  ExplicitCircuit add := by infer_explicit_circuit

-- family
example : ExplicitCircuits (witnessField (F:=F)) := by infer_explicit_circuits

example :
  let add (x : Expression F) := do
    let y : Expression F ← witness fun _ => 1
    let z ← witness fun eval => eval (x + y)
    assertZero (x + y - z)
    return z

  ExplicitCircuits add := by infer_explicit_circuits

-- elaborated
example :
  let add (x : Expression F) := do
    let y : Expression F ← witness fun _ => 1
    let z ← witness fun eval => eval (x + y)
    assertZero (x + y - z)
    return z

  ElaboratedCircuit F field field add := by infer_elaborated_circuit

-- needed for the output type
instance : ExplicitCircuits (F:=F) (β := Var unit F) assertZero :=
  inferInstanceAs (ExplicitCircuits (F:=F) assertZero)

example : ElaboratedCircuit F field unit (fun x ↦ assertZero (x * (x - 1))) := by
  infer_elaborated_circuit

-- works with circuits hidden behind definitions
private def assertBool (x : Expression F) := do
  assertZero (x * (x - 1))

example : ElaboratedCircuit F field unit assertBool := by infer_elaborated_circuit

end
