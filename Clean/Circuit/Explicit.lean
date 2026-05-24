/-
This file introduces `ExplicitCircuit`, a variant of `ElaboratedCircuit` that can be auto-derived
using the `infer_explicit_circuit(s)` tactic.

This could be useful to simplify circuit statements with less user intervention.
-/
import Clean.Utils.Misc
import Clean.Circuit.Basic
import Lean.Elab.Tactic
import Mathlib.Lean.Meta.Simp

open Lean Meta Elab Tactic

register_option debug.explicitCircuitReduced : Bool := {
  defValue := false
  descr := "trace generated dsimp unfold sets used by infer_elaborated_circuit_reduced"
}

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

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_output {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.output F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.output (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_localLength {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.localLength F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.localLength f n +
        ExplicitCircuit.localLength (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_operations {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.operations F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.operations f n ++
        ExplicitCircuit.operations (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_channelsWithGuarantees {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.channelsWithGuarantees F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.channelsWithGuarantees f n ++
        ExplicitCircuit.channelsWithGuarantees (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_channelsWithRequirements {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.channelsWithRequirements F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.channelsWithRequirements f n ++
        ExplicitCircuit.channelsWithRequirements (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

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

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_output {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.output F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = f (ExplicitCircuit.output g n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_localLength {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.localLength F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = ExplicitCircuit.localLength g n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_operations {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.operations F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = ExplicitCircuit.operations g n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_channelsWithGuarantees {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.channelsWithGuarantees F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = ExplicitCircuit.channelsWithGuarantees g n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_channelsWithRequirements {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.channelsWithRequirements F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = ExplicitCircuit.channelsWithRequirements g n := rfl

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

/--
Experimental elaboration tactic that stores reduced `localLength` and `output` directly.

This follows the same explicit-circuit derivation path as `infer_elaborated_circuit`, but simplifies
open metadata projections at tactic elaboration time before constructing the `ElaboratedCircuit`
record.  The result is cheap metadata for parent circuits: e.g. a loop-derived `localLength` can be
stored as `fun _ => 16` instead of a large tree of `ExplicitCircuit.from_*` projections.

The normalization uses the `explicit_circuit_norm` simp set instead of broad kernel reduction.
This keeps it targeted to projection lemmas and other explicit-circuit metadata rules.

This prototype currently delegates consistency/channel proofs to the inferred `ExplicitCircuits`
proof and is best suited to circuits whose channel metadata is definitionally empty.
-/
elab "infer_elaborated_circuit_reduced" : tactic => withMainContext do
  -- We are going to build an `ElaboratedCircuit` record directly.  First inspect the
  -- current goal and pull the important arguments out of
  --   ElaboratedCircuit F Input Output main
  -- so later code can construct the record fields explicitly.
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  unless target.getAppFn.isConstOf ``ElaboratedCircuit do
    throwError "target is not an ElaboratedCircuit: {target}"
  let args := target.getAppArgs
  if args.size < 7 then
    throwError "unexpected ElaboratedCircuit target: {target}"
  let F := args[0]!
  let Input := args[1]!
  let Output := args[2]!
  let main := args[6]!

  -- Step 1: infer the explicit circuit metadata for `main`, exactly like the
  -- ordinary `infer_elaborated_circuit` tactic does.  The difference is that we
  -- keep this proof term around and read its projections below instead of
  -- returning `ExplicitCircuits.toElaborated` unchanged.
  let explicitType ← mkAppM ``ExplicitCircuits #[main]
  let explicit ← Lean.Elab.Term.elabTerm (← `(by infer_explicit_circuits)) (some explicitType)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let explicit ← instantiateMVars explicit
  if (← getOptions).getBool `debug.explicitCircuitReduced false then
    logInfo m!"infer_elaborated_circuit_reduced explicit proof term:
  {explicit}"

  -- Useful object-language types for the lambdas we need to create.
  let varInputType ← mkAppM ``Var #[Input, F]
  let natType := mkConst ``Nat

  -- Read the simp theorem database tagged with `[explicit_circuit_norm]`.  These
  -- are mostly projection lemmas for `ExplicitCircuit.from_*` constructors, for
  -- example rewriting `(from_bind ...).localLength` to the corresponding explicit
  -- expression.  We use this as a targeted replacement for expensive `Meta.reduce`.
  let explicitThms ← do
    let some ext ← getSimpExtension? `explicit_circuit_norm
      | throwError "unknown simp attribute explicit_circuit_norm"
    ext.getTheorems
  let congrThms ← getSimpCongrTheorems

  -- Syntactic search used by the unfold heuristic below.
  let rec containsConst (declName : Name) (e : Expr) : Bool :=
    match e with
    | .const n _ => n == declName
    | .app f a => containsConst declName f || containsConst declName a
    | .lam _ t b _ | .forallE _ t b _ => containsConst declName t || containsConst declName b
    | .letE _ t v b _ => containsConst declName t || containsConst declName v || containsConst declName b
    | .mdata _ b => containsConst declName b
    | .proj _ _ b => containsConst declName b
    | _ => false

  -- Some circuit-like declarations are not literally named `Circuit`; this helper
  -- catches local project definitions such as `FormalCircuit` by suffix.
  let containsConstSuffix (suffix : String) (e : Expr) : Bool := Id.run do
    let rec go (e : Expr) : Bool :=
      match e with
      | .const n _ => n.getString! == suffix
      | .app f a => go f || go a
      | .lam _ t b _ | .forallE _ t b _ => go t || go b
      | .letE _ t v b _ => go t || go v || go b
      | .mdata _ b => go b
      | .proj _ _ b => go b
      | _ => false
    go e

  -- Decide whether a declaration's *type* mentions circuit infrastructure.  This
  -- identifies user-level circuit definitions such as `ThetaC.main` or
  -- `Xor64.circuit`, which often must be unfolded once before projection lemmas
  -- can fire.
  let hasCircuitType (type : Expr) : Bool :=
    containsConst ``Circuit type || containsConstSuffix "FormalCircuit" type ||
      containsConstSuffix "FormalAssertion" type || containsConstSuffix "GeneralFormalCircuit" type

  -- Do not unfold the core library constructors/projections themselves here.
  -- Those are handled by `[explicit_circuit_norm]`; unfolding them blindly would
  -- recreate the large terms that this tactic is trying to avoid.
  let isCoreCircuitInfra (declName : Name) : Bool :=
    let s := declName.toString
    s.startsWith "Circuit." || s.startsWith "ExplicitCircuit." || s.startsWith "ExplicitCircuits." ||
      s.startsWith "Operations." || s.startsWith "FormalCircuit" || s == "subcircuit"

  -- A declaration is eligible for `dsimp only` if it is a user-facing definition
  -- whose type looks circuit-like.  We deliberately exclude input-offset helpers:
  -- unfolding them expands variables rather than circuit structure.
  let isUnfoldable (declName : Name) : MetaM Bool := do
    if declName == ``ProvableType.varFromOffset || declName == ``ProvableStruct.varFromOffset ||
        isCoreCircuitInfra declName then
      return false
    match (← getEnv).find? declName with
    | some (.defnInfo info) => return hasCircuitType info.type
    | some (.opaqueInfo info) => return hasCircuitType info.type
    | _ => return false

  -- Collect the user circuit definitions that occur in an expression.  The list is
  -- fed to `dsimp only`; after each simplification pass we scan again, because
  -- unfolding one definition may reveal another circuit definition inside it.
  let rec collectUnfoldable (e : Expr) (decls : Array Name) : MetaM (Array Name) := do
    match e with
    | .const declName _ =>
        if decls.contains declName || !(← isUnfoldable declName) then
          return decls
        else
          return decls.push declName
    | .app f a => collectUnfoldable a (← collectUnfoldable f decls)
    | .lam _ t b _ | .forallE _ t b _ => collectUnfoldable b (← collectUnfoldable t decls)
    | .letE _ t v b _ => collectUnfoldable b (← collectUnfoldable v (← collectUnfoldable t decls))
    | .mdata _ b => collectUnfoldable b decls
    | .proj _ _ b => collectUnfoldable b decls
    | _ => return decls

  -- Build a `dsimp` context from `[explicit_circuit_norm]` plus the particular
  -- user declarations found in the expression currently being normalized.
  let mkDsimpCtx (decls : Array Name) : MetaM Simp.Context := do
    let mut thms := explicitThms
    for decl in decls do
      thms ← thms.addDeclToUnfold decl
    Simp.mkContext { zeta := true, beta := true, proj := true, iota := true }
      (simpTheorems := #[thms]) congrThms

  -- Normalize an explicit metadata expression, but only by the targeted rules
  -- described above.  This is intentionally a small fixed-point loop rather than
  -- full reduction.  The debug output is copyable Lean syntax, e.g.
  --   dsimp only [explicit_circuit_norm, Foo.main, Bar.circuit]
  -- so a failing or slow normalization step can be replayed in a source file.
  let normalizeExplicit (label : String) (e : Expr) : MetaM Expr := do
    let debug := (← getOptions).getBool `debug.explicitCircuitReduced false
    let mut current := e
    let mut decls ← collectUnfoldable e #[]
    for i in [:8] do
      if debug then
        let declNames := String.intercalate ", " (decls.toList.map fun decl => toString decl)
        let simpArgs := if declNames.isEmpty then "explicit_circuit_norm" else s!"explicit_circuit_norm, {declNames}"
        logInfo m!"infer_elaborated_circuit_reduced {label} pass {i}:
  dsimp only [{simpArgs}]"
      let ctx ← mkDsimpCtx decls
      let next := (← dsimp current ctx).1
      let decls' ← collectUnfoldable next decls
      if next == current && decls'.size == decls.size then
        return next
      current := next
      decls := decls'
    return current

  -- Store a simplified elaborated `localLength`.  We start from
  --   explicit.localLength input 0
  -- because an `ElaboratedCircuit` local length should not depend on the offset.
  let localLengthFun ← withLocalDeclD `input varInputType fun input => do
    let zero := mkNatLit 0
    let ll ← mkAppOptM ``ExplicitCircuits.localLength #[none, none, none, none, main, explicit, input, zero]
    let ll ← normalizeExplicit "localLength" ll
    mkLambdaFVars #[input] ll

  -- Store a simplified elaborated `output`.  Unlike `localLength`, output is a
  -- function of both the input variables and the current offset.
  let outputFun ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let out ← mkAppOptM ``ExplicitCircuits.output #[none, none, none, none, main, explicit, input, offset]
      let out ← normalizeExplicit "output" out
      mkLambdaFVars #[input, offset] out

  -- Prove the elaborated local-length equation by composing:
  --   circuit.localLength offset = explicit.localLength input offset
  -- with the definitional equality between the normalized stored field and the
  -- explicit expression at offset 0.  The latter proof is just `rfl`; if the
  -- normalization changed the expression in a non-definitional way, this assignment
  -- would fail, which is exactly the safety check we want.
  let localLengthEq ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p1 ← mkAppOptM ``ExplicitCircuits.localLength_eq #[none, none, none, none, main, explicit, input, offset]
      let p1Type ← whnf (← inferType p1)
      let some (_, _, mid) := p1Type.eq?
        | throwError "unexpected localLength_eq type: {p1Type}"
      let rhs := mkApp localLengthFun input
      let p2Type ← mkEq mid rhs
      let p2MVar ← mkFreshExprMVar p2Type
      p2MVar.mvarId!.assign (← mkEqRefl mid)
      let p ← mkAppM ``Eq.trans #[p1, p2MVar]
      mkLambdaFVars #[input, offset] p

  -- Same proof pattern for output:
  --   circuit.output offset = explicit.output input offset = storedOutput input offset.
  let outputEq ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p1 ← mkAppOptM ``ExplicitCircuits.output_eq #[none, none, none, none, main, explicit, input, offset]
      let p1Type ← whnf (← inferType p1)
      let some (_, _, mid) := p1Type.eq?
        | throwError "unexpected output_eq type: {p1Type}"
      let rhs := mkApp2 outputFun input offset
      let p2Type ← mkEq mid rhs
      let p2MVar ← mkFreshExprMVar p2Type
      p2MVar.mvarId!.assign (← mkEqRefl mid)
      let p ← mkAppM ``Eq.trans #[p1, p2MVar]
      mkLambdaFVars #[input, offset] p

  -- Consistency proofs are not recomputed.  They are taken directly from the
  -- inferred explicit metadata, whose operations still match the real circuit.
  let subProof ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p ← mkAppOptM ``ExplicitCircuits.subcircuitsConsistent #[none, none, none, none, main, explicit, input, offset]
      mkLambdaFVars #[input, offset] p

  -- Store simplified top-level channel metadata too.  The explicit metadata APIs
  -- expose channel lists as functions of input/offset, but these lists are intended
  -- to be circuit-level metadata.  As in `ExplicitCircuits.toElaborated`, read them
  -- at a default input and offset 0, then normalize the resulting projection tree.
  let defaultInput ← mkAppOptM ``default #[varInputType, none]
  let zero := mkNatLit 0
  let channelsWithGuarantees ← do
    let ch ← mkAppOptM ``ExplicitCircuits.channelsWithGuarantees
      #[none, none, none, none, main, explicit, defaultInput, zero]
    normalizeExplicit "channelsWithGuarantees" ch
  let channelsWithRequirements ← do
    let ch ← mkAppOptM ``ExplicitCircuits.channelsWithRequirements
      #[none, none, none, none, main, explicit, defaultInput, zero]
    normalizeExplicit "channelsWithRequirements" ch
  let exposedChannelType ← mkAppOptM ``ExposedChannel #[F, none]
  let exposed ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let nil := mkApp (mkConst ``List.nil [levelZero]) exposedChannelType
      mkLambdaFVars #[input, offset] nil

  -- Channel lawfulness is delegated to the inferred explicit circuit proof.  This
  -- type-checks when the normalized stored channel metadata is definitionally equal
  -- to the explicit metadata at the current input/offset; for static channel lists,
  -- the targeted normalization above makes that true without broad reduction.
  let channelsLawful ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p ← mkAppOptM ``ExplicitCircuits.channelsLawful #[none, none, none, none, main, explicit, input, offset]
      mkLambdaFVars #[input, offset] p

  -- Assemble the final `ElaboratedCircuit` record using the normalized fields and
  -- the delegated proofs, then close the user's goal.
  let val ← mkAppOptM ``ElaboratedCircuit.mk #[F, Input, Output, none, none, none, main,
    localLengthFun, localLengthEq, outputFun, outputEq, subProof, channelsWithGuarantees,
    channelsWithRequirements, exposed, channelsLawful]
  goal.assign val
  replaceMainGoal []
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
