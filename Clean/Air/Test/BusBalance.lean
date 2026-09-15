import Clean.Air.BalanceModel
import Clean.Circuit.Json
import Mathlib.Tactic.NormNum.Prime

/-!
# Bus balance acceptance tests

The compatibility baseline of the bus-balance roadmap (A11, A13), the directed tag
representation (A1), and the Layer 0 prototype: one typed message, a provider, a receive
with an assumption, a receive without an assumption, a gated event, and one ensemble whose
statement takes an explicit balance model (A14).

Two kinds of fixture are kept apart. An `example` whose type is `Prop` only checks that the
new API elaborates with explicit parameters; it proves nothing about satisfiability. Every
semantic claim in this file (what the legacy relation admits over `F 2`, what the local
contract rejects, what a model accepts, what a nested circuit collects) is a proved statement
or a `#guard`.
-/

namespace BusBalanceTests
open Air.Flat

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ## Legacy compatibility fixtures (A11, A13) -/
section Legacy
variable {p : ℕ} [Fact p.Prime]

/-- A legacy channel with a nontrivial guarantee. -/
def LegacyChannel : Channel (F p) field where
  name := "legacy"
  Guarantees x _ := x = 7

/-- A legacy channel whose guarantee can never be established. -/
def NeverChannel : Channel (F p) field where
  name := "never"
  Guarantees _ _ := False

/-- A11: legacy `emit (-1)` neither assumes nor owes the guarantee, even a `False` one. -/
example (env : Environment (F p)) (msg : Expression (F p)) :
    ((NeverChannel (p := p)).emitted (-1) msg).Guarantees env ∧
    ((NeverChannel (p := p)).emitted (-1) msg).Requirements env := by
  simp [circuit_norm]

/-- A13: the two-premise requirement proof shape used downstream still typechecks. -/
example (env : Environment (F p)) (m msg : Expression (F p))
    (h : (LegacyChannel (p := p)).Guarantees (eval env msg) env.data) :
    ((LegacyChannel (p := p)).emitted m msg).Requirements env :=
  fun _ _ => h

/-- A13: `exists_push_of_pull` keeps its name and statement. -/
example {F : Type} [FiniteField F] [DecidableEq F] (interactions : List (Interaction F))
    (balance : BalancedInteractions interactions) :
    ∀ a ∈ interactions, a.mult = -1 →
      ∃ b ∈ interactions, b.msg = a.msg ∧ b.mult ≠ 0 ∧ b.mult ≠ -1 :=
  exists_push_of_pull interactions balance

/-- A13: `one_ne_neg_one` keeps its name and statement. -/
example {F : Type} [FiniteField F] [Fact (ringChar F ≠ 2)] : (1 : F) ≠ -1 := one_ne_neg_one

/-- A13: the legacy VM theorem keeps its name, binders and characteristic assumption. -/
example {F : Type} [FiniteField F] [DecidableEq F] [Fact (ringChar F ≠ 2)]
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
    (n : ℕ) (len_pulls : pulls.length = n) (len_pushes : pushes.length = n)
    (pulls_channel : ∀ a ∈ pulls, a.channel = channel)
    (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
    (pulls_mult : ∀ a ∈ pulls, a.mult = -1) (pushes_mult : ∀ b ∈ pushes, b.mult = 1) :
    (∀ (i : ℕ) (hi : i < n), pulls[i].Guarantees data → pushes[i].Requirements data) →
    ∀ (i : ℕ) (hi: i < n), pushes[i].Requirements data → pulls[i].Guarantees data :=
  guarantees_of_requirements_of_requirements_of_guarantees channel pulls pushes balance data n
    len_pulls len_pushes pulls_channel pushes_channel pulls_mult pushes_mult

-- A13: the JSON of a legacy interaction is unchanged: channel, multiplicity, message, no tag.
#guard (Lean.toJson ((LegacyChannel (p := 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"legacy\",\"message\":[{\"type\":\"const\",\"value\":3}]," ++
  "\"multiplicity\":{\"type\":\"const\",\"value\":1}}"

/-- What the legacy relation excludes over `F 2`: more than one interaction on a channel,
since its no-wrap guard is `length < ringChar F = 2`. A matching provide/receive pair is
already too many. It says nothing about a channel without interactions; see
`legacyProto_satisfiable`. -/
theorem legacy_length_le_one_over_F2 (l : List (Interaction (F 2))) :
    BalancedInteractions l → l.length ≤ 1 := by
  intro ⟨guard, _⟩
  rw [ZMod.ringChar_zmod_n] at guard
  omega
end Legacy

/-! ## The directed tag representation (A1) -/
section Directed
variable {K : Type} [FiniteField K] [DecidableEq K]

/-- A directed channel whose guarantee is that the message equals `1`. -/
def OneChannel (F : Type) [FiniteField F] : DirectedChannel F field where
  name := "one"
  Guarantees x _ := x = 1

/-- A directed channel whose guarantee can never be established. -/
def NeverDirected (F : Type) [FiniteField F] : DirectedChannel F field where
  name := "never-directed"
  Guarantees _ _ := False

/-- A1: the sign carries no direction over `F 2`; the tag does, over every field. -/
example : (-1 : F 2) = 1 := by decide
example : (Direction.provide.tag : F 2) ≠ Direction.receive.tag := by decide
example : (Direction.provide.tag : K) ≠ Direction.receive.tag := by simp [circuit_norm]

/-- A raw interaction on a directed channel whose last element is neither tag fails the local
contract whatever its gate, so it cannot occur in a sound row. The typed constructors always
emit a well-formed tag (`DirectedInteraction.toRaw_requirements`). -/
example (mult : F 5) (data : ProverData (F 5)) :
    ¬ (NeverDirected (F 5)).toRaw.Requirements mult #v[0, 2] data := by
  have h : (2 : F 5) ≠ 0 ∧ (2 : F 5) ≠ 1 := by decide
  simp [NeverDirected, DirectedChannel.toRaw, Direction.tag, h.1, h.2]

/-- A legacy channel with a two-element payload on the same wire name as `OneChannel`. -/
def LegacyTwo : Channel (F 5) (fields 2) where
  name := "one"
  Guarantees _ _ := True

-- Serialization shape only: the raw JSON of a directed interaction is the legacy
-- channel/message/multiplicity object with the tag as one more message element. It does not
-- identify the directed interpretation: a legacy interaction with a two-element payload
-- serializes to the same bytes. The opt-in directed export protocol is roadmap Layer 5 work and
-- does not exist yet.
#guard (Lean.toJson ((OneChannel (F 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"one\",\"message\":[{\"type\":\"const\",\"value\":3}," ++
  "{\"type\":\"const\",\"value\":0}],\"multiplicity\":{\"type\":\"const\",\"value\":1}}"
#guard (Lean.toJson ((OneChannel (F 5)).pushed 0).toRaw).compress ==
  (Lean.toJson (LegacyTwo.pushed #v[0, 0]).toRaw).compress
end Directed

/-! ## Explicit models (A14) -/
section Models

/-- A14, typechecking test: the model-aware statement is stated over any field with an
explicit model; there is no default instance to fall back to. The `Prop` is not proved. -/
example {F : Type} [FiniteField F] [DecidableEq F] {PublicIO : TypeMap} [ProvableType PublicIO]
    (model : BalanceModel F) (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ens.StatementWith model publicInput

/-- `BalanceModel` is an abstract count/support interface: a model that reads every
interaction as an inactive event satisfies every field. Nothing in the structure relates
`view` to the raw channel contract. -/
def blindModel (F : Type) [FiniteField F] [DecidableEq F] : BalanceModel F where
  Verified _ := True
  SideCondition _ := True
  view _ := { payload := #[], direction := .provide, active := false }
  UnitEvent _ := True
  verified_of_perm _ _ := trivial
  sideCondition_of_perm _ _ := trivial
  pullsSupported := by intro l _ _; simp [PullsSupported]
  countBalanced := by intro l _ _ _; simp [CountBalanced, activeCount]

/-- So the interface alone does not reject a lone active receive that no provider supports,
although its raw guarantee (`message = 1`, for payload `0`) is false. Ruling this out is the
job of the correspondence law of the reading a model uses: it ties the view to the evaluated
interactions of the channel and transports the requirement of the supporting provider to the
guarantee of the receive. That law is roadmap Layer 1 work and lives outside the structure. -/
example : (blindModel (F 2)).Balanced [(OneChannel (F 2)).emittedValue .receive 1 0 true] :=
  ⟨trivial, trivial⟩

example (data : ProverData (F 2)) :
    ¬ ((OneChannel (F 2)).emittedValue .receive 1 0 true).Guarantees data := by
  simp [OneChannel, Interaction.Guarantees, Interaction.msgVector, DirectedChannel.emittedValue,
    DirectedChannel.toRaw, Direction.tag, fromElements, field, ProvableType.fromElements,
    toElements, ProvableType.toElements]
  decide
end Models

/-! ## The Layer 0 prototype -/
section Prototype

structure ProtoInput (F : Type) where
  enabled : F
  x : F
deriving ProvableStruct

/-- One typed message on a directed channel: a receive with an assumption, a provider that
owes what the receive assumed, a gated receive without an assumption, and a gated provider. -/
def proto (F : Type) [FiniteField F] : GeneralFormalCircuit F ProtoInput unit where
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    (OneChannel F).pull input.x
    (OneChannel F).push input.x
    (OneChannel F).emit .receive input.enabled input.x
    (OneChannel F).pushIf input.enabled 1
  Spec input _ _ := input.x = 1
  ProverAssumptions input _ _ := (input.enabled = 0 ∨ input.enabled = 1) ∧ input.x = 1
  channelsWithRequirements := [(OneChannel F).toRaw]
  soundness := by
    circuit_proof_start [OneChannel]
    -- `h_holds` carries the boolean constraint and the guarantee assumed by the receive
    obtain ⟨h_bool, h_pull⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    simp_all
  completeness := by
    circuit_proof_start [OneChannel]
    obtain ⟨h_enabled, hx⟩ := h_assumptions
    refine ⟨?_, fun _ => hx⟩
    rcases h_enabled with h | h <;> simp [h]

example {F : Type} [FiniteField F] (input : Var ProtoInput F) :
    ExplicitCircuit ((proto F).main input) := by
  infer_explicit_circuit

/-- The prototype called as a subcircuit of another circuit. -/
def nestedProto (F : Type) [FiniteField F] (input : Var ProtoInput F) : Circuit F Unit :=
  proto F input

/-- The tag survives subcircuit composition, flattening and evaluation: the interactions
collected from the nested prototype are its four directed events, payload and tag intact and
in circuit order. -/
example {F : Type} [FiniteField F] (env : Environment F) (input : Var ProtoInput F) :
    ((nestedProto F input).operations 0).interactionValues env =
      [ (OneChannel F).emittedValue .receive 1 (env input.x) true,
        (OneChannel F).emittedValue .provide 1 (env input.x) false,
        (OneChannel F).emittedValue .receive (env input.enabled) (env input.x) false,
        (OneChannel F).emittedValue .provide (env input.enabled) 1 false ] := by
  simp [circuit_norm, nestedProto, proto, Operations.interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, DirectedChannel.eval_toRaw]

/-- The prototype ensemble: one table on one directed channel, no verifier. -/
def protoEnsemble (F : Type) [FiniteField F] : Ensemble F unit where
  tables := [⟨ proto F ⟩]
  channels := [(OneChannel F).toRaw]

/-- A14, typechecking tests: the model-aware statement of the prototype ensemble elaborates
over any field with an explicit model, and over `F 2`. Neither `Prop` is proved here; the
directed statement with a nonempty witness is A9 (roadmap Layer 4). -/
example {F : Type} [FiniteField F] [DecidableEq F] (model : BalanceModel F) : Prop :=
  (protoEnsemble F).StatementWith model ()
example (model : BalanceModel (F 2)) : Prop := (protoEnsemble (F 2)).StatementWith model ()

/-- The empty prototype table over `F 2`: no rows, hence no interactions. -/
def emptyProtoTable : Table (F 2) where
  component := ⟨ proto (F 2) ⟩
  width := 2
  table := []
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The empty witness of the prototype ensemble over `F 2`. -/
def emptyProtoWitness : EnsembleWitness (protoEnsemble (F 2)) where
  tables := [emptyProtoTable]
  data := fun _ _ => #[]
  publicInput := ()
  same_length := rfl
  same_circuits := by
    intro i hi
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    rfl
  same_data := by
    intro table ht
    simp only [List.mem_singleton] at ht
    subst ht
    rfl

/-- The legacy statement of the prototype ensemble is satisfiable over `F 2`: the empty trace
has no interactions, so every channel is balanced. The legacy limitation is
`legacy_length_le_one_over_F2`, not unsatisfiability of the statement. -/
theorem legacyProto_satisfiable : (protoEnsemble (F 2)).Statement () := by
  refine ⟨emptyProtoWitness, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    exact ⟨EnsembleWitness.verifierTable_constraints_of_verifier_empty rfl,
      by simp [emptyProtoWitness, emptyProtoTable, Table.Constraints]⟩
  · intro channel _
    have h : emptyProtoWitness.allTablesWitness.interactionsWith channel = [] := by
      rw [EnsembleWitness.interactionsWith_allTablesWitness,
        EnsembleWitness.interactionsWith_of_verifier_empty rfl]
      simp [emptyProtoWitness, emptyProtoTable, Table.interactionsWith]
    change BalancedInteractions (emptyProtoWitness.allTablesWitness.interactionsWith channel)
    rw [h]
    simp [BalancedInteractions, balanceOf, ZMod.ringChar_zmod_n]

/-- And it is satisfied only by empty prototype tables: every row puts four interactions on
the channel, where `legacy_length_le_one_over_F2` allows at most one. This is the precise form
of the legacy limitation for this ensemble. -/
theorem legacyProto_only_empty (witness : EnsembleWitness (protoEnsemble (F 2)))
    (balanced : witness.BalancedChannels) : ∀ table ∈ witness.tables, table.table = [] := by
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp witness.same_length.symm
  have h_component : t.component = ⟨ proto (F 2) ⟩ := by
    have h := witness.same_circuits 0 (by simp [protoEnsemble])
    simp only [protoEnsemble, ht, List.getElem_cons_zero] at h
    exact h.symm
  have h_row (row : Array (F 2)) :
      (t.component.operations.interactionValuesWith (OneChannel (F 2)).toRaw
        (t.environment row)).length = 4 := by
    rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq, h_component]
    simp [circuit_norm, proto]
  have h_len := legacy_length_le_one_over_F2 _
    (balanced (OneChannel (F 2)).toRaw (by simp [protoEnsemble]))
  rw [EnsembleWitness.interactionsWith_allTablesWitness,
    EnsembleWitness.interactionsWith_of_verifier_empty rfl, ht] at h_len
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Table.interactionsWith,
    List.length_flatMap, h_row, List.map_const', List.sum_replicate, smul_eq_mul] at h_len
  intro table h_table
  rw [ht, List.mem_singleton] at h_table
  subst h_table
  exact List.eq_nil_of_length_eq_zero (by omega)
end Prototype

end BusBalanceTests
