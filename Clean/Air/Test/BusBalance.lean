import Clean.Air.BalanceModel
import Clean.Circuit.Json
import Mathlib.Tactic.NormNum.Prime

/-!
# Bus balance acceptance tests

The compatibility baseline of the bus-balance roadmap (A11, A13), the directed tag
representation (A1), and the Layer 0 prototype: one typed message, a provider, a receive
with an assumption, a receive without an assumption, a gated event, and one ensemble whose
statement takes an explicit balance model (A14).
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
    ∀ a ∈ interactions, a.mult = -1 → ∃ b ∈ interactions, b.msg = a.msg ∧ b.mult ≠ 0 ∧ b.mult ≠ -1 :=
  exists_push_of_pull interactions balance

/-- A13: `one_ne_neg_one` keeps its name and statement. -/
example {F : Type} [FiniteField F] [Fact (ringChar F ≠ 2)] : (1 : F) ≠ -1 := one_ne_neg_one

/-- A13: the legacy VM theorem keeps its name, binders and characteristic assumption. -/
example {F : Type} [FiniteField F] [DecidableEq F] [Fact (ringChar F ≠ 2)]
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
    (n : ℕ) (len_pulls : pulls.length = n) (len_pushes : pushes.length = n)
    (pulls_channel : ∀ a ∈ pulls, a.channel = channel) (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
    (pulls_mult : ∀ a ∈ pulls, a.mult = -1) (pushes_mult : ∀ b ∈ pushes, b.mult = 1) :
    (∀ (i : ℕ) (hi : i < n), pulls[i].Guarantees data → pushes[i].Requirements data) →
    ∀ (i : ℕ) (hi: i < n), pushes[i].Requirements data → pulls[i].Guarantees data :=
  guarantees_of_requirements_of_requirements_of_guarantees channel pulls pushes balance data n
    len_pulls len_pushes pulls_channel pushes_channel pulls_mult pushes_mult

-- A13: the JSON of a legacy interaction is unchanged: channel, multiplicity, message, no tag.
#guard (Lean.toJson ((LegacyChannel (p := 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"legacy\",\"message\":[{\"type\":\"const\",\"value\":3}],\"multiplicity\":{\"type\":\"const\",\"value\":1}}"
end Legacy

/-! ## The directed tag representation (A1) -/
section Directed
variable {K : Type} [FiniteField K] [DecidableEq K]

/-- A directed channel whose guarantee is that the message equals `1`. -/
def OneChannel (F : Type) [FiniteField F] : DirectedChannel F field where
  name := "one"
  Guarantees x _ := x = 1

/-- A1: the sign carries no direction over `F 2`; the tag does, over every field. -/
example : (-1 : F 2) = 1 := by decide
example : (Direction.provide.tag : F 2) ≠ Direction.receive.tag := by decide
example : (Direction.provide.tag : K) ≠ Direction.receive.tag := by simp [circuit_norm]

-- The raw export of a directed interaction: the payload followed by the direction tag, in the
-- existing channel/message/multiplicity shape. The opt-in directed export protocol is specified
-- separately.
#guard (Lean.toJson ((OneChannel (F 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"one\",\"message\":[{\"type\":\"const\",\"value\":3},{\"type\":\"const\",\"value\":0}],\"multiplicity\":{\"type\":\"const\",\"value\":1}}"
end Directed

/-! ## Explicit models (A14) -/
section Models

/-- A14: the model-aware statement is stated over any field with an explicit model; there is
no default instance to fall back to. -/
example {F : Type} [FiniteField F] [DecidableEq F] {PublicIO : TypeMap} [ProvableType PublicIO]
    (model : BalanceModel F) (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ens.StatementWith model publicInput
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

/-- The prototype ensemble: one table on one directed channel, no verifier. -/
def protoEnsemble (F : Type) [FiniteField F] : Ensemble F unit where
  tables := [⟨ proto F ⟩]
  channels := [(OneChannel F).toRaw]

/-- Layer 0: the model-aware statement of the prototype ensemble typechecks over any field
with an explicit model ... -/
example {F : Type} [FiniteField F] [DecidableEq F] (model : BalanceModel F) : Prop :=
  (protoEnsemble F).StatementWith model ()

/-- ... and over `F 2`, where the legacy statement would be unsatisfiable. -/
example (model : BalanceModel (F 2)) : Prop := (protoEnsemble (F 2)).StatementWith model ()
end Prototype

end BusBalanceTests
