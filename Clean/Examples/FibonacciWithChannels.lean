/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table
-/
import Clean.Circuit
import Clean.Circuit.Extensions
import Clean.Gadgets.Addition8.Theorems
open ByteUtils (mod256 floorDiv256)
open Gadgets.Addition8 (Theorems.soundness Theorems.completeness_bool Theorems.completeness_add)

/-- Lookup-like channels expose a predicate via both requirements and guarantees. -/
structure StaticLookupChannel (F : Type) [Field F] [DecidableEq F] (Message : TypeMap) [ProvableType Message] where
  name : String
  table : List (Message F)
  Guarantees : Message F → Prop
  guarantees_iff : ∀ msg, Guarantees msg ↔ msg ∈ table

section
variable {F : Type} [Field F] [DecidableEq F] {Message : TypeMap} [ProvableType Message]

@[circuit_norm]
def Channel.fromStatic (F : Type) [Field F] [DecidableEq F]
    (Message : TypeMap) [ProvableType Message]
    (slc : StaticLookupChannel F Message) : Channel F Message where
  name := slc.name
  Guarantees mult msg _ _ := if mult = -1 then slc.Guarantees msg else True
  Requirements mult msg _ _ := if ¬ mult = -1 then slc.Guarantees msg else True

def StaticLookupChannel.channel (slc : StaticLookupChannel F Message) :=
  Channel.fromStatic F Message slc
end

variable {p : ℕ} [Fact p.Prime] [pGt: Fact (p > 512)]

def BytesTable : StaticLookupChannel (F p) field where
  name := "bytes"
  table := List.finRange 256 |>.map ByteUtils.fromByte
  Guarantees msg := msg.val < 256

  guarantees_iff := by
    intro (msg : F p)
    simp only [id_eq, List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h_lt
      exact ⟨⟨ msg.val, h_lt ⟩, ByteUtils.fromByte_eq ..⟩
    · intro ⟨ ⟨ b, hb ⟩, h_eq ⟩
      rw [← h_eq]
      apply ByteUtils.fromByte_lt

def BytesChannel := Channel.fromStatic (F p) field BytesTable

-- bytes "circuit" that just pushes all bytes
-- probably shouldn't be a "circuit" at all
def pushBytes : FormalCircuitWithInteractions (F p) (fields (BytesTable (p:=p)).table.length) unit where
  main multiplicities := do
    let tableVector : Vector (F p) BytesTable.table.length := ⟨ .mk BytesTable.table, rfl ⟩
    .forEach (multiplicities.zip tableVector)
      fun (m, i) => BytesChannel.emit m (const i)

  localLength _ := 0
  localLength_eq := by simp +arith only [circuit_norm]
  output _ _ := ()

  localAdds
  | multiplicities, _, _ =>
    let tableVector : Vector (F p) BytesTable.table.length := ⟨ .mk BytesTable.table, rfl ⟩
    (multiplicities.zip tableVector).map (fun (m, i) => BytesChannel.emitted m i)
    |>.toList.flatten

  Assumptions | multiplicities, _ => True
  Spec _ _ _ := True

  -- TODO need better tools for finite range foreach, but probably this shouldn't be a circuit anyway
  localAdds_eq := by sorry
  soundness := by sorry
  completeness := by sorry

def Add8Channel : Channel (F p) fieldTriple where
  name := "add8"
  Guarantees
  | mult, (x, y, z), _, _ =>
    if mult = -1 then x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256
    else True
  Requirements
  | mult, (x, y, z), _, _ =>
    if ¬ mult = -1 then x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256
    else True

structure Add8Inputs F where
  x : F
  y : F
  z : F
  m : F -- multiplicity
deriving ProvableStruct

def add8 : FormalCircuitWithInteractions (F p) Add8Inputs unit where
  main | { x, y, z, m } => do
    -- range-check z using the bytes channel
    -- (x and y are guaranteed to be range-checked from earlier interactions)
    BytesChannel.pull z

    -- witness the output carry
    let carry ← witness fun eval => floorDiv256 (eval (x + y))
    assertBool carry

    -- assert correctness
    x + y - z - carry * 256 === 0

    -- emit to the add8 channel with multiplicity `m`
    Add8Channel.emit m (x, y, z)

  localLength _ := 1
  output _ _ := ()

  localAdds
  | { x, y, z, m }, _, _ =>
    BytesChannel.pulled z + Add8Channel.emitted m (x, y, z)

  -- TODO feels weird to put the entire spec in the completeness assumptions
  -- can we get something from the channel interactions??
  Assumptions
  | { x, y, z, m }, _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [BytesChannel, Add8Channel, reduceIte, not_true_eq_false]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq, _ ⟩ := h_holds
    split_ifs
    intro hx hy
    have add_soundness := Theorems.soundness input_x input_y input_z 0 carry hx hy hz (by left; trivial) hcarry
    simp_all

  -- TODO: we didn't need to prove z < 256, but we could have
  -- for completeness, it would make sense to require proving the Guarantees as well
  -- what about the Requirements?
  completeness := by
    circuit_proof_start
    set carry := env.get i₀
    simp_all only
    rcases h_assumptions with ⟨ hx, hy, hz, heq ⟩
    have add_completeness_bool := Theorems.completeness_bool input_x input_y 0 hx hy (by simp)
    have add_completeness_add := Theorems.completeness_add input_x input_y 0 hx hy (by simp)
    simp only [add_zero] at add_completeness_bool add_completeness_add
    use add_completeness_bool
    convert add_completeness_add
    apply FieldUtils.ext
    rw [heq, mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
    linarith [‹Fact (p > 512)›.elim]

-- define valid Fibonacci state transitions

def fibonacciStep : ℕ × ℕ → ℕ × ℕ
  | (x, y) => (y, (x + y) % 256)

def fibonacci : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | 0, state => state
  | n + 1, state => fibonacciStep (fibonacci n state)

/-- helper lemma: fibonacci states are bytes -/
lemma fibonacci_bytes {n x y : ℕ} : (x, y) = fibonacci n (0, 1) → x < 256 ∧ y < 256 := by
  induction n generalizing x y with
  | zero => simp_all [fibonacci]
  | succ n ih =>
    specialize ih rfl
    have : 0 < 256 := by norm_num
    simp_all [fibonacci, fibonacciStep, Nat.mod_lt]

instance FibonacciChannel : Channel (F p) fieldTriple where
  name := "fibonacci"

  -- when pulling, we want the guarantee that the previous interactions pushed
  -- some tuple equal to ours which represents a valid Fibonacci step
  Guarantees
  | m, (n, x, y), interactions, _ =>
    if (m = -1)
    then
      -- (x, y) is a valid Fibonacci state
      (∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val) ∧
      -- and was pushed in a previous interaction
      (1, (n, x, y)) ∈ interactions
    else True

  Requirements
  | m, (n, x, y), interactions, _ =>
    if (m = 1)
    then
      -- (x, y) is a valid Fibonacci state
      (∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val) ∧
      -- and is pushed (in this interaction! this is tautological)
      (1, (n, x, y)) ∈ interactions
    else True

def fib8 : FormalCircuitWithInteractions (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- pull the current Fibonacci state
    FibonacciChannel.pull (n, x, y)

    -- witness the next Fibonacci value
    let z ← witness fun eval => mod256 (eval (x + y))

    -- pull from the Add8 channel to check addition
    Add8Channel.pull (x, y, z)

    -- push the next Fibonacci state
    FibonacciChannel.push (n + 1, y, z)

  localLength _ := 1
  output _ _ := ()

  localAdds
  | (n, x, y), i₀, env =>
    let z := env.get i₀;
    FibonacciChannel.pulled (n, x, y) +
    Add8Channel.pulled (x, y, z) +
    FibonacciChannel.pushed (n + 1, y, z)

  Assumptions | (n, x, y), _ => True
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [reduceIte, seval, and_false, not_true_eq_false]
    rcases input with ⟨ n, x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [Prod.mk.injEq] at h_input
    -- why are these not simped?? maybe because fieldPair is not well-recognized
    rw [RawChannel.filter_eq] at h_holds ⊢
    rw [Channel.interactionFromRaw_eq, Channel.interactionFromRaw_eq, Channel.interactionFromRaw_eq]
    simp_all only [circuit_norm]
    set fibInteractions := FibonacciChannel.filter interactions
    set add8Interactions := Add8Channel.filter interactions
    set z := env.get i₀
    simp only [circuit_norm, FibonacciChannel, Add8Channel, reduceIte, not_true_eq_false] at h_holds ⊢
    simp only [List.mem_cons, true_or, and_true]
    obtain ⟨ ⟨ ⟨k, fiby, hk⟩, hfib_push ⟩, hadd ⟩ := h_holds
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    use k + 1
    simp only [fibonacci, fibonacciStep, ← fiby]
    rw [ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start

-- additional circuits that pull/push remaining channel interactions
-- these really wouldn't have to be circuits, need to find a better place for tying together channels

-- completing Fibonacci channel with input and output
def fibonacciVerifier : FormalCircuitWithInteractions (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- push initial state, pull the final state
    FibonacciChannel.push (0, 0, 1)
    FibonacciChannel.pull (n, x, y)

  localLength _ := 0
  output _ _ := ()
  localAdds
  | (n, x, y), _, _ =>
    FibonacciChannel.pushed (0, 0, 1) +
    FibonacciChannel.pulled (n, x, y)

  Assumptions _ _ := True
  Spec
  | (n, x, y), _, _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

  soundness := by
    circuit_proof_start [reduceIte, seval, and_false, not_true_eq_false]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    rw [RawChannel.filter_eq] at h_holds ⊢
    rw [Channel.interactionFromRaw_eq, Channel.interactionFromRaw_eq] at ⊢
    rw [Channel.interactionFromRaw_eq] at h_holds
    set fibInteractions := FibonacciChannel.filter interactions
    simp_all only [circuit_norm, FibonacciChannel, reduceIte,
      List.mem_cons, true_or, and_true, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩

  completeness := by
    circuit_proof_start

section
-- define what global soundness means for an ensemble of circuits/tables and channels

-- table contains the concrete values on which we expect constraints to hold
-- which also defines what concrete interactions are contained in each channel

variable {F : Type} [Field F] [DecidableEq F]
variable {Input Output Message : TypeMap} [ProvableType Input] [ProvableType Output] [ProvableType Message]

-- tables need to be instantiated with a concrete circuit, not a family of circuits
-- this is achieved for any FormalCircuit* by witnessing the inputs and plugging them in

def FormalCircuitWithInteractions.instantiate (circuit : FormalCircuitWithInteractions F Input Output) : Circuit F Unit := do
  let input ← witnessAny Input
  let _ ← circuit input -- we don't care about the output in this context

def FormalCircuitWithInteractions.size (circuit : FormalCircuitWithInteractions F Input Output) : ℕ :=
  circuit.instantiate.localLength 0

structure AbstractTable (F : Type) [Field F] [DecidableEq F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : FormalCircuitWithInteractions F Input Output

instance (t: AbstractTable F) : ProvableType t.Input := t.provableInput
instance (t: AbstractTable F) : ProvableType t.Output := t.provableOutput

namespace AbstractTable
def operations (table : AbstractTable F) : Operations F :=
  table.circuit.instantiate.operations 0

def width (table : AbstractTable F) : ℕ := table.circuit.size
end AbstractTable

structure TableWitness (F : Type) [Field F] [DecidableEq F] where
  abstract : AbstractTable F
  table : List (Vector F abstract.circuit.size)
  data : ProverData F

def ConstraintsHold (env : Environment F) (ops : Operations F) : Prop :=
  ops.forAll 0 {
    assert _ e := env e = 0
    lookup _ l := l.Contains env
    subcircuit _ _ s := ConstraintsHoldFlat env s.ops.toFlat
  }

namespace TableWitness
def width (t : TableWitness F) : ℕ := t.abstract.width

def environment (witness : TableWitness F) (row : Vector F witness.width) : Environment F where
  get j := row[j]?.getD 0
  data := witness.data
  interactions := [] -- I think we can remove this field??

def Constraints (witness : TableWitness F) : Prop :=
  witness.table.Forall fun row =>
    ConstraintsHold (witness.environment row) witness.abstract.operations

def interactions (witness : TableWitness F) (channel : RawChannel F) : List (F × Vector F channel.arity) :=
  witness.table.flatMap fun row =>
    let env := witness.environment row
    witness.abstract.operations.localAdds env
  |> channel.filter
end TableWitness

structure Ensemble (F : Type) [Field F] [DecidableEq F] where
  tables : List (AbstractTable F)
  channels : List (RawChannel F)

  PublicIO : TypeMap
  [provablePublicIO : ProvableType PublicIO]
  verifier : FormalCircuitWithInteractions F PublicIO unit
  verifier_length_zero : ∀ pi, (verifier (const pi)).localLength 0 = 0

  Spec : PublicIO F → Prop

structure EnsembleWitness (ens : Ensemble F) where
  tables : List (TableWitness F)
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length), ens.tables[i] = tables[i].abstract

def emptyEnvironment (F : Type) [Field F] [DecidableEq F] : Environment F := { get _ := 0, data _ _ := #[], interactions := [] }

instance (ens : Ensemble F) : ProvableType ens.PublicIO := ens.provablePublicIO

def BalancedInteractions (channel : RawChannel F) (interactions : List (F × Vector F channel.arity)) : Prop :=
  ∀ msg : Vector F channel.arity,
    let is := (interactions.filter (·.2 = msg))
    is.length < ringChar F ∧ (is.map Prod.fst).sum = 0

namespace Ensemble
def verifierInteractions (ens : Ensemble F) (channel : RawChannel F) (publicInput : ens.PublicIO F) : List (F × Vector F channel.arity) :=
  let circuit := ens.verifier.main (const publicInput)
  (circuit.operations 0).localAdds (emptyEnvironment F)
  |> channel.filter

def Constraints (ens : Ensemble F) (witness : EnsembleWitness ens) : Prop :=
  witness.tables.Forall fun table => table.Constraints

def interactions (ens : Ensemble F) (publicInput : ens.PublicIO F) (witness : EnsembleWitness ens) (channel : RawChannel F) : List (F × Vector F channel.arity) :=
  witness.tables.flatMap (fun table => table.interactions channel)
  ++ ens.verifierInteractions channel publicInput

abbrev BalancedChannel (ens : Ensemble F) (publicInput : ens.PublicIO F) (witness : EnsembleWitness ens) (channel : RawChannel F) : Prop :=
  BalancedInteractions channel (ens.interactions publicInput witness channel)

def BalancedChannels (ens : Ensemble F) (publicInput : ens.PublicIO F) (witness : EnsembleWitness ens) : Prop :=
  ens.channels.Forall fun channel =>
    BalancedInteractions channel (ens.interactions publicInput witness channel)

def VerifierAccepts (ens : Ensemble F) (publicInput : ens.PublicIO F) : Prop :=
  let circuit := ens.verifier.main (const publicInput)
  ConstraintsHold (emptyEnvironment F) (circuit.operations 0)

/--
Soundness for an ensemble states that if
- constraints hold on all tables and
- and interactions sum to zero
- and constraints hold on the verifier circuit, when given the public inputs (as constants)
then the spec holds
-/
def Soundness (F : Type) [Field F] [DecidableEq F] (ens : Ensemble F) : Prop :=
  ∀ witness publicInput,
    ens.Constraints witness →
    ens.BalancedChannels publicInput witness →
    ens.VerifierAccepts publicInput →
    ens.Spec publicInput

/--
Completeness for an ensemble states that for any public input satisfying the spec,
the verifier accepts and there exists a witness such that constraints hold and the channels are balanced
-/
def Completeness (ens : Ensemble F) : Prop :=
  ∀ publicInput,
    ens.Spec publicInput →
    ens.VerifierAccepts publicInput ∧
    ∃ witness, ens.Constraints witness ∧ ens.BalancedChannels publicInput witness

end Ensemble

/-!
## Global helpers for lifting constraints and per-message balance
-/

/-- The interaction guarantees for a list of operations, threaded through `is`.
    This extracts ONLY the guarantee conditions, with everything else set to True. -/
def InteractionGuarantees (env : Environment F) (is : RawInteractions F)
    (ops : Operations F) : Prop :=
  ops.forAllWithInteractions env 0 is {
    interact _ is i := i.Guarantees env is
    subcircuit _ _ _ s := ConstraintsHoldFlat env s.ops.toFlat
  }

omit [DecidableEq F] in
/-- Raw constraints + interaction guarantees ⇒ full constraints with interactions. -/
lemma lift_constraints_with_guarantees (env : Environment F) (is : RawInteractions F)
    (ops : Operations F)
    (h_raw : ops.forAll 0 {
      assert _ e := env e = 0
      lookup _ l := l.Contains env
      subcircuit _ _ s := ConstraintsHoldFlat env s.ops.toFlat
    })
    (h_guarantees : InteractionGuarantees env is ops) :
    ConstraintsHoldWithInteractions.Soundness env is ops := by
  -- prove a general offset version by induction on ops
  suffices h_gen : ∀ (offset : ℕ) (is : RawInteractions F) (ops : Operations F),
      ops.forAll offset {
        assert _ e := env e = 0
        lookup _ l := l.Contains env
        subcircuit _ _ s := ConstraintsHoldFlat env s.ops.toFlat
      } →
      ops.forAllWithInteractions env offset is {
        interact _ is i := i.Guarantees env is
        subcircuit _ _ _ s := ConstraintsHoldFlat env s.ops.toFlat
      } →
      ops.forAllWithInteractions env offset is {
        assert _ _ e := env e = 0
        lookup _ _ l := l.Soundness env
        interact _ is i := i.Guarantees env is
        subcircuit _ _ _ s := s.Soundness env
      } by
    exact h_gen 0 is ops h_raw h_guarantees
  intro offset is' ops'
  induction ops' generalizing offset is' with
  | nil =>
    intro _ _
    trivial
  | cons op ops ih =>
    intro h_raw' h_guar'
    cases op with
    | witness m c =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨h_guar'.1, ih _ _ h_raw'.2 h_guar'.2⟩
    | assert e =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨h_raw'.1, ih _ _ h_raw'.2 h_guar'.2⟩
    | lookup l =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨l.table.imply_soundness _ _ h_raw'.1, ih _ _ h_raw'.2 h_guar'.2⟩
    | interact i =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨h_guar'.1, ih _ _ h_raw'.2 h_guar'.2⟩
    | subcircuit s =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      constructor
      · exact s.imply_soundness _ h_raw'.1
      · exact ih _ _ h_raw'.2 h_guar'.2

omit [DecidableEq F] in
/-- Sum of a list where every element is -1 equals -(length) as a field element. -/
lemma sum_neg_ones (l : List F) (h : ∀ x ∈ l, x = (-1 : F)) :
    l.sum = -(l.length : F) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have h_hd : hd = (-1 : F) := h hd (by simp)
    have h_tl : ∀ x ∈ tl, x = (-1 : F) := by
      intro x hx
      exact h x (by simp [hx])
    simp [List.sum_cons, List.length_cons, h_hd, ih h_tl]
end

omit [Fact (p > 512)] in
/-- If a pull (-1, msg) appears and the per-message sum is 0 with length < p,
    then there is a non-pull interaction with the same msg. -/
lemma exists_non_pull_of_pull {n : ℕ}
    (interactions : List (F p × Vector (F p) n)) (msg : Vector (F p) n)
    (h_balance : ((interactions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0)
    (h_bound : (interactions.filter (fun x => x.2 = msg)).length < ringChar (F p))
    (h_pull : (-1, msg) ∈ interactions) :
    ∃ mult, mult ≠ (-1 : F p) ∧ (mult, msg) ∈ interactions := by
  set is := interactions.filter (fun x => x.2 = msg) with h_is
  have h_pull_in_is : (-1, msg) ∈ is := by
    apply List.mem_filter.2
    exact ⟨h_pull, by simp⟩
  by_contra h_no
  have h_all_neg : ∀ m ∈ (is.map Prod.fst), m = (-1 : F p) := by
    intro m h_mem
    rcases List.mem_map.1 h_mem with ⟨pair, h_pair, rfl⟩
    rcases pair with ⟨mult, msg'⟩
    have h_msg : msg' = msg := by
      exact of_decide_eq_true (List.mem_filter.1 h_pair).2
    have h_mem_inter : (mult, msg) ∈ interactions := by
      simpa [h_msg] using (List.mem_filter.1 h_pair).1
    have h_mult : mult = (-1 : F p) := by
      by_contra h_ne
      exact h_no ⟨mult, h_ne, h_mem_inter⟩
    simpa [h_msg] using h_mult
  have h_sum_neg : (is.map Prod.fst).sum = -((is.map Prod.fst).length : F p) :=
    sum_neg_ones _ h_all_neg
  have h_sum_neg' : (is.map Prod.fst).sum = -(is.length : F p) := by
    simpa [List.length_map] using h_sum_neg
  have h_balance' : (is.map Prod.fst).sum = 0 := by
    simpa [h_is] using h_balance
  have h_len_cast : (is.length : F p) = 0 := by
    have h_eq : -(is.length : F p) = 0 := by simpa [h_balance'] using h_sum_neg'
    exact (neg_eq_zero.mp h_eq)
  have h_len_pos : 0 < is.length := List.length_pos_of_mem h_pull_in_is
  have h_ringChar : ringChar (F p) = p := by
    simpa [F] using ZMod.ringChar_zmod_n p
  have h_len_lt : is.length < p := by
    simpa [h_is, h_ringChar] using h_bound
  have _ : CharP (F p) p := by
    simpa [F] using (ZMod.charP p)
  have h_div : p ∣ is.length :=
    (CharP.cast_eq_zero_iff (R := F p) (p := p) is.length).1 h_len_cast
  exact (Nat.not_dvd_of_pos_of_lt h_len_pos h_len_lt) h_div

omit [Fact (p > 512)] in
/-- Generic per-message balance: a pull gets the same property as a non-pull interaction. -/
lemma guarantee_of_balance {n : ℕ} (interactions : List (F p × Vector (F p) n))
    (msg : Vector (F p) n) (P : Vector (F p) n → Prop)
    (h_balance : ((interactions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0)
    (h_bound : (interactions.filter (fun x => x.2 = msg)).length < ringChar (F p))
    (h_req : ∀ mult, (mult, msg) ∈ interactions → mult ≠ (-1 : F p) → P msg)
    (h_pull : (-1, msg) ∈ interactions) :
    P msg := by
  obtain ⟨mult, h_ne, h_mem⟩ :=
    exists_non_pull_of_pull interactions msg h_balance h_bound h_pull
  exact h_req mult h_mem h_ne

omit [Fact (p > 512)] [Fact (Nat.Prime p)] in
/-- `fromElements` for a byte message equals the first element. -/
lemma fromElements_eq_getElem (msg : Vector (F p) 1) :
    fromElements (M:=field) msg = msg[0]'(by decide) := by
  cases msg using Vector.elimAsArray with
  | mk arr hsize =>
    rcases (Array.size_eq_one_iff.mp hsize) with ⟨a, h_arr⟩
    subst h_arr
    simp [explicit_provable_type]

omit [Fact (p > 512)] [Fact (Nat.Prime p)] in
lemma fromElements_eq_getElem' (msg : Vector (F p) 1) (h : 0 < 1) :
    fromElements (M:=field) msg = msg[0]'h := by
  simpa using (fromElements_eq_getElem msg)

omit [Fact (p > 512)] in
/-- Balance + non-pull predicate ⇒ pull guarantees for lookup-like channels. -/
lemma lookup_channel_guarantee_of_balance {Message : TypeMap} [ProvableType Message]
    {lc : StaticLookupChannel (F p) Message}
    {interactions : List (F p × Vector (F p) lc.channel.toRaw.arity)}
    (msg : Vector (F p) lc.channel.toRaw.arity)
    (h_balance : BalancedInteractions lc.channel.toRaw interactions)
    (h_req : ∀ mult, (mult, msg) ∈ interactions → mult ≠ (-1 : F p) → lc.Guarantees (fromElements msg))
    (h_pull : (-1, msg) ∈ interactions) :
    lc.channel.Guarantees (-1) (fromElements msg)
      (interactions.map Channel.interactionFromRaw) (fun _ _ => #[]) := by
  rcases h_balance msg with ⟨ h_bound, h_balance ⟩
  have h_val : lc.Guarantees (fromElements msg) :=
    guarantee_of_balance interactions msg (fun v => lc.Guarantees (fromElements v))
      h_balance h_bound h_req h_pull
  have h_guar : (-1 : F p) = -1 → lc.Guarantees (fromElements msg) := by
    intro _
    exact h_val
  simp only [StaticLookupChannel.channel, Channel.fromStatic, reduceIte]
  exact h_guar rfl

-- let's try to prove soundness and completeness of the Fibonacci with channels example
def fibonacciEnsemble : Ensemble (F p) where
  tables := [ ⟨pushBytes⟩, ⟨add8⟩, ⟨fib8⟩ ]
  channels := [ BytesChannel.toRaw, Add8Channel.toRaw, FibonacciChannel.toRaw ]
  PublicIO := fieldTriple
  verifier := fibonacciVerifier
  verifier_length_zero := by simp only [fibonacciVerifier, circuit_norm]

  Spec | (n, x, y) => ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

lemma bytes_guarantee_of_balance_tables
    (witness : EnsembleWitness fibonacciEnsemble) (n x y : F p)
    (h_balanced_bytes : fibonacciEnsemble.BalancedChannel (n, x, y) witness BytesChannel.toRaw) :
    -- TODO generalize to any mult, not just -1 (the others are trivial)
    ∀ msg, (-1, msg) ∈ fibonacciEnsemble.interactions (n, x, y) witness BytesChannel.toRaw →
      BytesChannel.Guarantees (-1) (fromElements (M:=field) msg)
        ((fibonacciEnsemble.interactions (n, x, y) witness BytesChannel.toRaw).map
          Channel.interactionFromRaw)
        (fun _ _ => #[]) := by
  set bytesInteractions :=
    fibonacciEnsemble.interactions (n, x, y) witness BytesChannel.toRaw
  have h_const : const (α:=fieldTriple) (n, x, y) = (.const n, .const x, .const y) := by
    simp [circuit_norm, ProvableType.const, explicit_provable_type]
  intro msg h_pull
  have h_channel : BytesChannel (p:=p) = StaticLookupChannel.channel _ := rfl

  apply lookup_channel_guarantee_of_balance _ h_balanced_bytes ?_ h_pull
  clear h_balanced_bytes
  have h_witness_len : witness.tables.length = 3 := witness.same_length.symm
  intro mult h_mem h_ne

  -- this is the part that should be guaranteed by the relationship of pushBytes to BytesChannel
  -- should be a generic theorem about static lookup channels and their auto-generated circuits
  rw [BytesTable.guarantees_iff]
  let pushBytesTable := witness.tables[0]
  suffices h_mem : (mult, msg) ∈ pushBytesTable.interactions BytesChannel.toRaw by
    have : ⟨ pushBytes ⟩ = pushBytesTable.abstract := by
      convert witness.same_circuits 0 (by simp [fibonacciEnsemble])
    simp only [TableWitness.interactions, ←this] at h_mem
    simp only [AbstractTable.operations, FormalCircuitWithInteractions.instantiate,
      circuit_norm, witnessAny, pushBytes, getOffset] at h_mem
    simp only [id_eq, List.mem_flatMap] at h_mem
    obtain ⟨ row, h_row_mem, h_mem ⟩ := h_mem
    set env := pushBytesTable.environment row with h_env
    simp only [Vector.map_mapRange, Expression.eval, Vector.mapRange_zip,
      Vector.map_mapFinRange, RawChannel.filter, List.mem_filterMap] at h_mem
    simp only [Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.mem_flatten,
      Vector.mem_toList_iff, Option.dite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
      Vector.mk_eq, exists_and_left, exists_prop, Prod.exists, ↓existsAndEq, Vector.size_toArray,
      and_true, true_and, exists_eq_right] at h_mem
    simp only [Vector.mapFinRange, Vector.finRange, Vector.mem_map, Vector.mem_ofFn, ↓existsAndEq,
      true_and, exists_exists_eq_and] at h_mem
    rcases h_mem with ⟨ ⟨i, hi⟩, h_mem ⟩
    rw [List.mem_iff_getElem]
    use i, hi
    suffices msg = toElements BytesTable.table[i] by
      rw [this, ProvableType.fromElements_toElements]
    rw [←Vector.toArray_inj]
    simp [Channel.emitted, InteractionDelta.single] at h_mem
    convert h_mem.2.2

  -- this part is just about characterizing which of the tables in the ensemble push to the BytesChannel
  rcases List.mem_append.1 h_mem with h_tables | h_ver
  · rcases List.mem_flatMap.1 h_tables with ⟨table, h_table_mem, h_mem_table⟩
    rcases List.mem_iff_getElem.1 h_table_mem with ⟨i, hi, htable⟩
    have h_len : witness.tables.length = 3 := by
      simpa [fibonacciEnsemble] using witness.same_length.symm
    have hi' : i < 3 := by
      simpa [h_len] using hi
    have h_same : fibonacciEnsemble.tables[i] = table.abstract := by
      simpa [htable] using witness.same_circuits i (by simpa [fibonacciEnsemble, h_len] using hi)
    have h_table_abs : table.abstract = fibonacciEnsemble.tables[i] := by
      simpa using h_same.symm
    cases i with
    | zero => convert h_mem_table
    | succ i1 =>
      cases i1 with
      | zero =>
        simp [fibonacciEnsemble] at h_table_abs
        have h_mem_table' : (mult, msg) ∈ table.interactions BytesChannel.toRaw := h_mem_table
        rcases (by
          simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_mem_table'
        ) with ⟨row, h_row_mem, h_raw_mem⟩
        have h_raw_mem' := h_raw_mem
        rw [h_table_abs] at h_raw_mem'
        simp [witnessAny, getOffset, FormalCircuitWithInteractions.instantiate, add8, circuit_norm,
          BytesChannel, Channel.emitted, InteractionDelta.single] at h_raw_mem'
        rw [InteractionDelta.add_eq_append] at h_raw_mem'
        have h_raw_mem'' := h_raw_mem'
        simp [List.mem_append, List.mem_cons] at h_raw_mem''
        rcases h_raw_mem'' with ⟨_, h_mult, _⟩ | h_mem1 | ⟨h_name, _, _⟩ | h_mem2
        · exact (False.elim (h_ne h_mult))
        · cases h_mem1
        · have h_name' := h_name
          simp [BytesTable, Add8Channel, Channel.toRaw] at h_name'
        · cases h_mem2
      | succ i2 =>
        simp [fibonacciEnsemble] at h_table_abs
        have h_mem_table' : (mult, msg) ∈ table.interactions BytesChannel.toRaw := h_mem_table
        rcases (by
          simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_mem_table'
        ) with ⟨row, h_row_mem, h_raw_mem⟩
        have h_raw_mem' := h_raw_mem
        rw [h_table_abs] at h_raw_mem'
        simp [witnessAny, getOffset, FormalCircuitWithInteractions.instantiate, fib8, circuit_norm,
          BytesChannel, BytesTable, Channel.emitted, InteractionDelta.single] at h_raw_mem'
        rw [InteractionDelta.add_eq_append, InteractionDelta.add_eq_append] at h_raw_mem'
        simp [List.mem_append, List.mem_cons, Channel.toRaw, FibonacciChannel, Add8Channel] at h_raw_mem'
        cases h_raw_mem'
  · have h_verifier_empty :
        fibonacciEnsemble.verifierInteractions BytesChannel.toRaw (n, x, y) = [] := by rfl
    have h_false : False := by
      simp [h_verifier_empty] at h_ver
    exact h_false.elim

theorem fibonacciEnsemble_soundness : Ensemble.Soundness (F p) fibonacciEnsemble := by
  whnf
  intro witness publicInput h_constraints h_balanced h_verifier
  clear h_constraints h_verifier
  rcases publicInput with ⟨ n, x, y ⟩
  simp [Ensemble.BalancedChannels, List.Forall, fibonacciEnsemble] at h_balanced
  -- extract the channel balance hypotheses
  have h_balanced_bytes := h_balanced.1
  have h_balanced_add8 := h_balanced.2.1
  have h_balanced_fib := h_balanced.2.2

  -- define the bytes interactions list for this public input
  set bytesInteractions :=
    fibonacciEnsemble.interactions (n, x, y) witness BytesChannel.toRaw

  have h_bytes_arity_pos : 0 < (BytesChannel (p := p)).toRaw.arity := by
    have h_bytes_arity : (BytesChannel (p := p)).toRaw.arity = 1 := by rfl
    simp [h_bytes_arity]

  have h_bytes_guarantee : ∀ msg, (-1, msg) ∈ bytesInteractions → (fromElements msg).val < 256 := by
    intro msg h_pull
    have h_guar := bytes_guarantee_of_balance_tables witness n x y h_balanced_bytes msg h_pull
    simp only [BytesChannel, BytesTable, Channel.fromStatic, reduceIte] at h_guar
    convert h_guar

  -- define the fibonacci interactions list for this public input
  set fibInteractions :=
    List.flatMap (fun table => table.interactions FibonacciChannel.toRaw) witness.tables ++
      FibonacciChannel.toRaw.filter
        (FibonacciChannel.emitted 1 (0, 0, 1) + FibonacciChannel.emitted (-1) (n, x, y))
  -- message vector for (n, x, y)
  set fibMsg : Vector (F p) 3 := #v[n, x, y]
  have h_const : const (α:=fieldTriple) (n, x, y) = (.const n, .const x, .const y) := by
    simp [circuit_norm, ProvableType.const, explicit_provable_type]
  have h_balanced_msg :
      (List.filter (fun x ↦ decide (x.2 = fibMsg)) fibInteractions).length < ringChar (F p) ∧
        (List.map Prod.fst
            (List.filter (fun x ↦ decide (x.2 = fibMsg)) fibInteractions)).sum = 0 := by
    simpa [Ensemble.BalancedChannel, Ensemble.interactions, Ensemble.verifierInteractions,
      fibonacciEnsemble, fibonacciVerifier, pushBytes, add8, fib8, emptyEnvironment, h_const,
      fibInteractions, circuit_norm] using h_balanced_fib fibMsg

  -- show the verifier pull is in the global fibonacci interactions
  have h_pull_mem : (-1, fibMsg) ∈ fibInteractions := by
    apply (List.mem_append).2
    refine Or.inr ?_
    -- the verifier interactions are exactly [push, pull]
    simp [fibMsg, RawChannel.filter, FibonacciChannel,
      Channel.emitted, InteractionDelta.single]
    constructor
    ·
      right
      change List.Mem ("fibonacci", (-1 : F p), #[n, x, y])
        [("fibonacci", (-1 : F p),
            (toElements (M:=fieldTriple) ((n, x, y) : fieldTriple (F p))).toArray)]
      have h_arr : (toElements (M:=fieldTriple) ((n, x, y) : fieldTriple (F p))).toArray = #[n, x, y] := by
        simp [explicit_provable_type]
      have h_mem : List.Mem ("fibonacci", (-1 : F p), #[n, x, y]) [("fibonacci", (-1 : F p), #[n, x, y])] := by
        exact List.Mem.head []
      simpa [h_arr] using h_mem
    ·
      exact rfl

  -- derive a matching push for the pulled message
  have h_push_mem : (1, fibMsg) ∈ fibInteractions := by
    set is := fibInteractions.filter (·.2 = fibMsg) with h_is
    have h_balanced_msg' : is.length < ringChar (F p) ∧ (is.map Prod.fst).sum = 0 := by
      simpa [h_is] using h_balanced_msg
    have h_pull_in_is : (-1, fibMsg) ∈ is := by
      apply List.mem_filter.2
      exact ⟨h_pull_mem, by simp⟩
    have h_len_pos : 0 < is.length := List.length_pos_of_mem h_pull_in_is
    -- use h_balanced_msg' and the fact that all multiplicities are ±1 to show (1, fibMsg) ∈ is
    have h_mult_pm1 : ∀ mult, (mult, fibMsg) ∈ is → mult = -1 ∨ mult = 1 := by
      intro mult h_mem
      have h_mem_fib : (mult, fibMsg) ∈ fibInteractions := List.mem_of_mem_filter h_mem
      rcases List.mem_append.1 h_mem_fib with h_tables | h_ver
      ·
        rcases List.mem_flatMap.1 h_tables with ⟨table, h_table_mem, h_mem_table⟩
        rcases List.mem_iff_getElem.1 h_table_mem with ⟨i, hi, htable⟩
        have h_len : witness.tables.length = 3 := by
          simpa [fibonacciEnsemble] using witness.same_length.symm
        have hi' : i < 3 := by
          simpa [h_len] using hi
        have h_same : fibonacciEnsemble.tables[i] = table.abstract := by
          simpa [htable] using witness.same_circuits i (by simpa [fibonacciEnsemble, h_len] using hi)
        have h_table_abs : table.abstract = fibonacciEnsemble.tables[i] := by
          simpa using h_same.symm
        -- split on which table it is: pushBytes / add8 / fib8
        cases i with
        | zero =>
          simp [fibonacciEnsemble] at h_table_abs
          -- pushBytes has no fibonacci interactions
          have h_mem_table' : (mult, fibMsg) ∈ table.interactions FibonacciChannel.toRaw := h_mem_table
          rcases (by
            simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_mem_table'
          ) with ⟨row, h_row_mem, h_raw_mem⟩
          -- reduce to membership in pushBytes localAdds
          have h_raw_mem' := h_raw_mem
          rw [h_table_abs] at h_raw_mem'
          simp [witnessAny, getOffset, FormalCircuitWithInteractions.instantiate, pushBytes, circuit_norm] at h_raw_mem'
          rcases h_raw_mem' with ⟨i, h_mem_emitted⟩
          have h_mem_emitted' := h_mem_emitted
          simp [BytesChannel, BytesTable, Channel.emitted, InteractionDelta.single] at h_mem_emitted'
          rcases h_mem_emitted' with ⟨h_name, _, _⟩
          have h_fib_name : (FibonacciChannel (p:=p)).toRaw.name = "fibonacci" := rfl
          have h_ne : (FibonacciChannel (p:=p)).toRaw.name ≠ "bytes" := by simp [h_fib_name]
          -- this is simple/mechanical
          sorry
          -- exact (False.elim (h_ne h_name))
        | succ i1 =>
          cases i1 with
          | zero =>
            simp [fibonacciEnsemble] at h_table_abs
            -- add8 has no fibonacci interactions
            have h_mem_table' : (mult, fibMsg) ∈ table.interactions FibonacciChannel.toRaw := h_mem_table
            rcases (by
              simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_mem_table'
            ) with ⟨row, h_row_mem, h_raw_mem⟩
            -- reduce to membership in add8 localAdds
            have h_raw_mem' := h_raw_mem
            rw [h_table_abs] at h_raw_mem'
            simp [witnessAny, getOffset, FormalCircuitWithInteractions.instantiate, add8, circuit_norm] at h_raw_mem'
            -- localAdds is bytes pull + add8 emit
            rcases List.mem_append.1 h_raw_mem' with h_bytes | h_add8
            ·
              have h_bytes' := h_bytes
              simp [BytesChannel, Channel.emitted, InteractionDelta.single] at h_bytes'
              rcases h_bytes' with ⟨h_name, _, _⟩
              have h_fib_name : (FibonacciChannel (p:=p)).toRaw.name = "fibonacci" := rfl
              have h_ne : (FibonacciChannel (p:=p)).toRaw.name ≠ "bytes" := by
                simp [h_fib_name]
              exact (False.elim (h_ne h_name))
            ·
              have h_add8' := h_add8
              simp [Add8Channel, Channel.emitted, InteractionDelta.single] at h_add8'
              rcases h_add8' with ⟨h_name, _, _⟩
              have h_fib_name : (FibonacciChannel (p:=p)).toRaw.name = "fibonacci" := rfl
              have h_ne : (FibonacciChannel (p:=p)).toRaw.name ≠ "add8" := by
                simp [h_fib_name]
              exact (False.elim (h_ne h_name))
          | succ i2 =>
            cases i2 with
            | zero =>
              simp [fibonacciEnsemble] at h_table_abs
              -- fib8 interactions only emit ±1
              have h_mem_table' : (mult, fibMsg) ∈ table.interactions FibonacciChannel.toRaw := h_mem_table
              rcases (by
                simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_mem_table'
              ) with ⟨row, h_row_mem, h_raw_mem⟩
              have h_raw_mem' := h_raw_mem
              rw [h_table_abs] at h_raw_mem'
              simp [witnessAny, getOffset, FormalCircuitWithInteractions.instantiate, fib8, circuit_norm,
                FibonacciChannel, Add8Channel, Channel.pull, Channel.push, Channel.pulled, Channel.pushed,
                InteractionDelta.single] at h_raw_mem'
              have h_raw_mem'' := h_raw_mem'
              simp [InteractionDelta.add_eq_append] at h_raw_mem''
              rcases h_raw_mem'' with h_left | h_rest
              ·
                exact Or.inl h_left.2.1
              ·
                rcases h_rest with h_mem0 | h_rest
                · cases h_mem0
                ·
                  rcases h_rest with h_add8 | h_rest
                  · exact Or.inl h_add8.2.1
                  ·
                    rcases h_rest with h_mem0 | h_rest
                    · cases h_mem0
                    ·
                      rcases h_rest with h_right | h_mem0
                      · exact Or.inr h_right.2.1
                      · cases h_mem0
            | succ i3 =>
              -- impossible since i < 3
              have hi'' : i3 + 4 < 3 := by
                have hi'' := hi'
                simp [Nat.add_left_comm, Nat.add_comm] at hi''
              have h_ge : 3 ≤ i3 + 4 := by
                have h1 : 4 ≤ i3 + 4 := Nat.le_add_left 4 i3
                have h2 : 3 ≤ 4 := by decide
                exact Nat.le_trans h2 h1
              have : False := (Nat.not_lt_of_ge h_ge) hi''
              exact this.elim
      ·
        -- verifier interactions are exactly one push and one pull
        have h_ver' : (mult, fibMsg) ∈
            FibonacciChannel.toRaw.filter
              (FibonacciChannel.emitted 1 (0, 0, 1) + FibonacciChannel.emitted (-1) (n, x, y)) := h_ver
        rcases List.mem_filterMap.mp h_ver' with ⟨raw, h_raw_mem, h_raw_some⟩
        have h_raw_mem' :
            raw ∈ [("fibonacci", (1 : F p), (toElements (M:=fieldTriple) ((0 : F p), (0 : F p), (1 : F p))).toArray)] ++
              [("fibonacci", (-1 : F p), (toElements (M:=fieldTriple) ((n, x, y) : fieldTriple (F p))).toArray)] := by
          simpa [FibonacciChannel, Channel.emitted, InteractionDelta.single, explicit_provable_type,
            InteractionDelta.add_eq_append] using h_raw_mem
        rcases List.mem_append.1 h_raw_mem' with h_left | h_right
        ·
          rcases List.mem_singleton.1 h_left with h_raw_eq
          subst h_raw_eq
          have h_some' : 1 = mult ∧ 3 = size fieldTriple ∧ #[0, 0, 1] = fibMsg.toArray := by
            simpa [RawChannel.filter, FibonacciChannel, Channel.toRaw, Channel.emitted,
              explicit_provable_type] using h_raw_some
          exact Or.inr h_some'.1.symm
        ·
          rcases List.mem_singleton.1 h_right with h_raw_eq
          subst h_raw_eq
          have h_some' : -1 = mult ∧ 3 = size fieldTriple ∧ #[n, x, y] = fibMsg.toArray := by
            simpa [RawChannel.filter, FibonacciChannel, Channel.toRaw, Channel.emitted,
              explicit_provable_type] using h_raw_some
          exact Or.inl h_some'.1.symm
    have h_one_in_is : (1, fibMsg) ∈ is := by
      classical
      by_contra h_no_one
      have h_all_neg : ∀ mult, (mult, fibMsg) ∈ is → mult = -1 := by
        intro mult h_mem
        rcases h_mult_pm1 mult h_mem with h_neg | h_pos
        · exact h_neg
        · exfalso
          apply h_no_one
          simpa [h_pos] using h_mem
      have h_map_eq' : is.map Prod.fst = List.replicate (is.map Prod.fst).length (-1 : F p) := by
        apply (List.eq_replicate_length (a := (-1 : F p))).2
        intro b h_mem
        rcases List.mem_map.1 h_mem with ⟨pair, h_pair, rfl⟩
        rcases pair with ⟨mult, msg⟩
        have h_msg : msg = fibMsg := by
          exact of_decide_eq_true (List.mem_filter.1 h_pair).2
        have h_neg : mult = -1 := by
          apply h_all_neg
          simpa [h_msg] using h_pair
        simp [h_neg]
      have h_map_eq : is.map Prod.fst = List.replicate is.length (-1 : F p) := by
        simpa [List.length_map] using h_map_eq'
      have h_sum_eq : (is.length : F p) * (-1) = 0 := by
        have h_sum' : (is.map Prod.fst).sum = 0 := h_balanced_msg'.2
        -- sum of a replicate list
        simpa [h_map_eq, nsmul_eq_mul, mul_comm] using h_sum'
      have h_len_cast : (is.length : F p) = 0 := by
        have h_mul := mul_eq_zero.mp h_sum_eq
        rcases h_mul with h_len | h_neg
        · exact h_len
        ·
          have h_neg' : (-1 : F p) ≠ 0 := by
            simp
          cases (h_neg' h_neg)
      have h_ringChar : ringChar (F p) = p := by
        simpa [F] using ZMod.ringChar_zmod_n p
      have h_len_lt : is.length < p := by
        simpa [h_ringChar] using h_balanced_msg'.1
      have _ : CharP (F p) p := by
        simpa [F] using (ZMod.charP p)
      have h_div : p ∣ is.length :=
        (CharP.cast_eq_zero_iff (R := F p) (p := p) is.length).1 h_len_cast
      exact (Nat.not_dvd_of_pos_of_lt h_len_pos h_len_lt) h_div
    exact List.mem_of_mem_filter h_one_in_is

  -- derive Fibonacci requirements for the matching push
  have h_req : FibonacciChannel.toRaw.Requirements 1 fibMsg fibInteractions (fun _ _ => #[]) := by
    -- TODO: derive from constraints + fib8 soundness (or from the fibonacci induction)
    sorry

  have h_req' : (∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val) := by
    -- unfold the raw-channel requirements and simplify the message
    have h_req'' : (∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val) ∧
        (1, ((n, x, y) : fieldTriple (F p))) ∈
          fibInteractions.map (Channel.interactionFromRaw (Message:=fieldTriple)) := by
      simpa [fibMsg, Channel.toRaw, FibonacciChannel, ProvableType.fromElements_toElements] using h_req
    exact h_req''.1
  exact h_req'
