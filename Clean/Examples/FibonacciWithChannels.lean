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

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

instance BytesChannel : Channel (F p) field where
  name := "bytes"
  Guarantees mult x _ _ :=
    if mult = -1 then x.val < 256 else True
  Requirements mult x _ _ :=
    if ¬ mult = -1 then x.val < 256 else True

instance Add8Channel : Channel (F p) fieldTriple where
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

/-- Bytes "circuit" that pushes all byte values (0..255) to BytesChannel.

    The input `multiplicities : fields 256` specifies the multiplicity for each byte value.
    For a balanced ensemble, `multiplicities[i]` should equal the number of times byte `i`
    is pulled elsewhere (e.g., by add8 circuits). This is NOT necessarily ±1 — if byte 42
    is pulled 5 times across different add8 rows, then `multiplicities[42] = 5`.

    The key property is that pushBytes only emits byte values 0..255, regardless of
    the multiplicities. This is used to prove that any non-pull BytesChannel entry
    has value < 256. -/
def pushBytes : FormalCircuitWithInteractions (F p) (fields 256) unit where
  main multiplicities := do
    let _  ← .mapFinRange 256 fun ⟨ i, _ ⟩ =>
      BytesChannel.emit multiplicities[i] (const i)

  localLength _ := 0
  localLength_eq := by simp only [circuit_norm]
  output _ _ := ()

  localAdds
  | multiplicities, _, _ =>
    (List.finRange 256).flatMap fun ⟨ i, _ ⟩ =>
      BytesChannel.emitted multiplicities[i] i

  Assumptions | multiplicities, _ => True
  Spec _ _ _ := True

  -- TODO need better tools for finite range foreach, but probably this shouldn't be a circuit anyway
  localAdds_eq := by sorry
  soundness := by sorry
  completeness := by sorry

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

/-- Per-message balance: for each channel, for each message, the sum of multiplicities is 0.
    This is stronger than just requiring the total sum to be 0, and captures the intuition
    that every pull (-1) must be matched by a push (+1) for the same message.
    Additionally requires that the number of interactions is bounded by the field characteristic
    (needed for exists_push_of_pull which uses natCast). -/
def BalancedChannels (ens : Ensemble F) (publicInput : ens.PublicIO F) (witness : EnsembleWitness ens) : Prop :=
  ens.channels.Forall fun channel =>
    (ens.interactions publicInput witness channel).length < (ringChar F) ∧
    ∀ msg : Vector F channel.arity,
      ((ens.interactions publicInput witness channel).filter (·.2 = msg) |>.map Prod.fst).sum = 0

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
end

-- let's try to prove soundness and completeness of the Fibonacci with channels example
def fibonacciEnsemble : Ensemble (F p) where
  tables := [ ⟨pushBytes⟩, ⟨add8⟩, ⟨fib8⟩ ]
  channels := [ BytesChannel.toRaw, Add8Channel.toRaw, FibonacciChannel.toRaw ]
  PublicIO := fieldTriple
  verifier := fibonacciVerifier
  verifier_length_zero := by simp only [fibonacciVerifier, circuit_norm]

  Spec | (n, x, y) => ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

/-!
## Lifting lemma: from ConstraintsHold to ConstraintsHoldWithInteractions.Soundness

The ensemble-level `ConstraintsHold` checks raw constraints (asserts, lookups, subcircuits)
but ignores channel interactions (they default to `True`). The per-circuit soundness
theorems need `ConstraintsHoldWithInteractions.Soundness`, which additionally requires
channel guarantees to hold for each interaction.

This lemma bridges the gap: given raw constraints hold AND channel guarantees hold
at each interaction point, we can construct the full `ConstraintsHoldWithInteractions.Soundness`.
-/

/-- The interaction guarantees for a list of operations, threaded through `is`.
    This extracts ONLY the guarantee conditions, with everything else set to True. -/
def InteractionGuarantees (env : Environment (F p)) (is : RawInteractions (F p)) (ops : Operations (F p)) : Prop :=
  ops.forAllWithInteractions env 0 is {
    interact _ is i := i.Guarantees env is
    subcircuit _ _ _ s := ConstraintsHoldFlat env s.ops.toFlat -- TODO: should use s.Soundness
  }

omit [Fact (p > 512)] in
/-- Lifting lemma: raw constraints + interaction guarantees → full constraints with interactions.
    Combines the assert/lookup conditions from ConstraintsHold with the interaction
    guarantee conditions from InteractionGuarantees to produce the full
    ConstraintsHoldWithInteractions.Soundness. -/
lemma lift_constraints_with_guarantees (env : Environment (F p)) (is : RawInteractions (F p))
    (ops : Operations (F p))
    (h_raw : ops.forAll 0 {
      assert _ e := env e = 0
      lookup _ l := l.Contains env
      subcircuit _ _ s := ConstraintsHoldFlat env s.ops.toFlat
    })
    (h_guarantees : InteractionGuarantees env is ops) :
    ConstraintsHoldWithInteractions.Soundness env is ops := by
  -- We need a generalized version that works for any offset
  suffices h_gen : ∀ (offset : ℕ) (is : RawInteractions (F p)) (ops : Operations (F p)),
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
  | nil => intros; trivial
  | cons op ops' ih =>
    intro h_raw' h_guar'
    cases op with
    | witness m c =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨ h_guar'.1, ih _ _ h_raw'.2 h_guar'.2 ⟩
    | assert e =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨ h_raw'.1, ih _ _ h_raw'.2 h_guar'.2 ⟩
    | lookup l =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨ l.table.imply_soundness _ _ h_raw'.1, ih _ _ h_raw'.2 h_guar'.2 ⟩
    | interact i =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      exact ⟨ h_guar'.1, ih _ _ h_raw'.2 h_guar'.2 ⟩
    | subcircuit s =>
      simp only [Operations.forAll, Operations.forAllWithInteractions] at *
      -- Need ConstraintsHoldFlat → s.Soundness AND continue with rest of ops
      constructor
      · -- s.Soundness follows from imply_soundness
        exact s.imply_soundness _ h_raw'.1
      · -- Continue with the rest of the operations
        exact ih _ _ h_raw'.2 h_guar'.2

/-!
## Helper lemmas for per-message channel balance
-/

/-- Sum of a list where every element is -1 equals -(length) as a field element -/
lemma sum_neg_ones {F : Type} [Ring F] (l : List F) (h : ∀ x ∈ l, x = (-1 : F)) :
    l.sum = -(l.length : F) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_succ, neg_add_rev]
    rw [h hd (List.mem_cons.mpr (Or.inl rfl)), ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

omit [Fact (p > 512)] in
/-- In a list of interactions where all multiplicities are 1 or -1,
    if the per-message sum is 0 and (-1, msg) appears, then (1, msg) also appears.
    Requires that the characteristic is larger than the list length. -/
lemma exists_push_of_pull {n : ℕ}
    (interactions : List (F p × Vector (F p) n)) (msg : Vector (F p) n)
    (h_mults : ∀ entry ∈ interactions, entry.2 = msg → entry.1 = 1 ∨ entry.1 = -1)
    (h_balance : ((interactions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0)
    (h_pull : (-1, msg) ∈ interactions)
    (h_bound : interactions.length < p) :
    (1, msg) ∈ interactions := by
  by_contra h_no_push
  -- Every entry for msg has mult = -1
  have h_all_neg : ∀ entry ∈ interactions, entry.2 = msg → entry.1 = -1 := by
    intro entry h_mem h_eq
    rcases h_mults entry h_mem h_eq with h | h
    · exact absurd (show (1, msg) ∈ interactions by rwa [← h_eq, ← h]) h_no_push
    · exact h
  -- The filtered list has all multiplicities = -1
  have h_neg_mults : ∀ m ∈ (interactions.filter (fun x => x.2 = msg)).map Prod.fst, m = (-1 : F p) := by
    intro m h_mem
    rw [List.mem_map] at h_mem
    obtain ⟨ ⟨ m', v ⟩, h_mem', rfl ⟩ := h_mem
    simp only [List.mem_filter, decide_eq_true_eq] at h_mem'
    exact h_all_neg _ h_mem'.1 h_mem'.2
  -- The filtered list is non-empty
  have h_nonempty : 0 < (interactions.filter (fun x => x.2 = msg)).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨ h_pull, by simp ⟩)
  -- The sum equals -(filtered_length : F p)
  have h_sum := sum_neg_ones _ h_neg_mults
  rw [h_balance] at h_sum
  -- So (filtered_length : F p) = 0, but 0 < filtered_length < p, contradiction
  set filtered := (interactions.filter (fun x => x.2 = msg)).map Prod.fst with h_filtered_def
  have h_len_lt_p : filtered.length < p := by
    simp only [h_filtered_def, List.length_map]
    exact lt_of_le_of_lt (List.length_filter_le _ _) h_bound
  have h_cast_zero : (filtered.length : F p) = 0 := by
    have := h_sum; -- 0 = -(filtered.length : F p)
    rw [eq_comm, neg_eq_zero] at this; exact this
  rw [ZMod.natCast_eq_zero_iff filtered.length p] at h_cast_zero
  -- p | filtered.length, but 0 < filtered.length < p, contradiction
  have h_pos : filtered.length > 0 := by
    simp only [h_filtered_def, List.length_map]; exact h_nonempty
  exact absurd (Nat.le_of_dvd h_pos h_cast_zero) (not_le.mpr h_len_lt_p)

/-- A valid Fibonacci state: (n, x, y) such that (x.val, y.val) = fibonacci k (0, 1) for some k
    with k % p = n.val -/
def IsValidFibState (n x y : F p) : Prop :=
  ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

omit [Fact (p > 512)] in
/-- The verifier push (0, 0, 1) is a valid fibonacci state -/
lemma verifier_push_valid : IsValidFibState (0 : F p) 0 1 :=
  ⟨ 0, by simp [fibonacci, ZMod.val_zero, ZMod.val_one], by simp ⟩

/-- From fib8 row constraints + valid input state + add8 correctness,
    the output state is also valid -/
lemma fib8_step_valid (n_i x_i y_i z_i carry : F p)
    (h_input_valid : IsValidFibState n_i x_i y_i)
    (h_carry_bool : IsBool carry)
    (h_add_eq : x_i + y_i + -z_i + -(carry * 256) = 0)
    (h_x_range : x_i.val < 256)
    (h_y_range : y_i.val < 256)
    (h_z_range : z_i.val < 256) :
    IsValidFibState (n_i + 1) y_i z_i := by
  obtain ⟨ k, h_fib, h_k ⟩ := h_input_valid
  -- from the constraints, z_i = (x_i + y_i) % 256
  have h_add := Theorems.soundness x_i y_i z_i 0 carry h_x_range h_y_range h_z_range
    (Or.inl rfl) h_carry_bool
  simp only [add_zero, ZMod.val_zero] at h_add
  have h_z_eq := (h_add h_add_eq).1
  refine ⟨ k + 1, ?_, ?_ ⟩
  · simp only [fibonacci, fibonacciStep, ← h_fib]
    simp_all
  · rw [ZMod.val_add, ← h_k, Nat.mod_add_mod, ZMod.val_one]

/-!
## Key inductive lemma: all fibonacci pushes are valid

The Fibonacci channel interactions come from:
- The verifier: push (0, 0, 1), pull (n, x, y)
- Each fib8 row: pull (n_i, x_i, y_i), push (n_i+1, y_i, z_i)

We prove by strong induction on the step counter that every push is a valid
fibonacci state. The well-foundedness relies on each fib8 row incrementing the
step counter by 1 (and p > 512 prevents wraparound for chains up to 512 steps).

**Key design principle**: The hypotheses of this lemma talk about
FibonacciChannel.Requirements (which is the OUTPUT of per-circuit soundness),
NOT about raw circuit constraints. All concrete constraint reasoning
(carry bits, addition equations, etc.) lives inside the per-circuit
soundness proofs and is not repeated here.
-/

/-- All entries pushed (mult = 1) to the fibonacci channel are valid states.

    The key hypothesis `h_fib8_soundness` captures what `fib8.soundness` gives us
    at the channel level: if a push is not the verifier push, then it came from a
    fib8 row, and IF the fib8 row's pull had a valid guarantee (the pulled state
    is a valid fibonacci state), THEN the push also satisfies its requirements
    (the pushed state is a valid fibonacci state).

    This avoids re-deriving any concrete circuit constraints — all of that is
    encapsulated inside `fib8.soundness`. -/
lemma all_fib_pushes_valid
    (fibInteractions : List (F p × Vector (F p) 3))
    -- the verifier pushes (0, 0, 1)
    -- list is shorter than the field characteristic
    (h_bound : fibInteractions.length < p)
    -- per-message balance
    (h_balance : ∀ msg : Vector (F p) 3,
      ((fibInteractions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0)
    -- all multiplicities are 1 or -1
    (h_mults : ∀ entry ∈ fibInteractions, entry.1 = 1 ∨ entry.1 = -1)
    -- For each push that is NOT the verifier push:
    -- there is a corresponding pull, and
    -- IF the pull's state is a valid fibonacci state,
    -- THEN the push's state is also a valid fibonacci state.
    -- (This is the output of fib8.soundness applied to each row.)
    (h_fib8_soundness : ∀ entry ∈ fibInteractions, entry.1 = 1 →
      -- either it's the verifier push
      entry.2 = (#v[0, 0, 1] : Vector (F p) 3) ∨
      -- or it's a fib8 push: there's a pull at step n_i, and
      -- valid input → valid output
      ∃ (n_i x_i y_i : F p),
        -- the fib8 row pulled (n_i, x_i, y_i)
        (-1, (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ fibInteractions ∧
        -- the push's step counter is n_i + 1
        entry.2[0] = n_i + 1 ∧
        -- no wraparound
        n_i.val + 1 < p ∧
        -- if the pulled state is valid, the pushed state is valid
        -- (this is the core of fib8.soundness + add8 guarantees)
        (IsValidFibState n_i x_i y_i → IsValidFibState entry.2[0] entry.2[1] entry.2[2])) :
    -- conclusion: all pushes are valid fibonacci states
    ∀ entry ∈ fibInteractions, entry.1 = 1 →
      IsValidFibState entry.2[0] entry.2[1] entry.2[2] := by
  -- Strong induction on the step counter value
  suffices h : ∀ (n : ℕ), ∀ entry ∈ fibInteractions, entry.1 = 1 → entry.2[0].val = n →
      IsValidFibState entry.2[0] entry.2[1] entry.2[2] by
    intro entry h_mem h_push
    exact h entry.2[0].val entry h_mem h_push rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro entry h_mem h_push h_step
    rcases h_fib8_soundness entry h_mem h_push with h_veq | ⟨ n_i, x_i, y_i, h_pull_mem, h_step_eq, h_no_wrap, h_valid_implies ⟩
    · -- Verifier push: entry.2 = #v[0, 0, 1]
      rw [h_veq]
      simp only [Vector.getElem_mk]
      exact verifier_push_valid
    · -- Fib8 push: valid if input is valid
      -- By per-message balance, the pull (-1, (n_i, x_i, y_i)) has a matching push
      have h_matching := exists_push_of_pull fibInteractions (#v[n_i, x_i, y_i])
        (fun e h_mem _ => h_mults e h_mem) (h_balance _) h_pull_mem h_bound
      -- Apply IH: the matching push (1, (n_i, x_i, y_i)) is valid
      have h_input_valid : IsValidFibState n_i x_i y_i := by
        -- n_i.val < n because entry.2[0] = n_i + 1 and n = entry.2[0].val
        have : Fact (1 < p) := ⟨ by linarith [Fact.elim ‹Fact (p > 512)›] ⟩
        have h_lt : n_i.val < n := by
          rw [← h_step, h_step_eq, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt h_no_wrap]; omega
        have h_push_valid := ih n_i.val h_lt (1, #v[n_i, x_i, y_i]) h_matching rfl rfl
        simp only [Vector.getElem_mk] at h_push_valid
        exact h_push_valid
      exact h_valid_implies h_input_valid

/-!
## Structural lemmas about channel interactions

These lemmas characterize which circuits emit to which channels with what multiplicities.
They are purely mechanical - just unfolding definitions and filtering.

We state them at the level of table witness interactions, which is what the
ensemble soundness proof actually needs.
-/

/-- For any BytesChannel entry with mult ≠ -1 (i.e., not a pull), the value is < 256.

    BytesChannel interactions come from:
    - pushBytes: emits values 0..255 with arbitrary multiplicities (to balance all pulls)
    - add8: pulls (mult = -1) with arbitrary values (the witness z)
    - fib8, verifier: no BytesChannel interactions

    So any entry with mult ≠ -1 must be from pushBytes, hence val ∈ {0..255}. -/
lemma bytes_push_val_lt_256
    (witness : EnsembleWitness (fibonacciEnsemble (p := p)))
    (publicInput : fieldTriple (F p))
    (entry : F p × Vector (F p) 1)
    (h_mem : entry ∈ (fibonacciEnsemble (p := p)).interactions publicInput witness
                      ((BytesChannel (p := p)).toRaw))
    (h_push : entry.1 ≠ -1) :
    entry.2[0].val < 256 := by
  sorry

/-- For any FibonacciChannel interaction from the tables (not verifier),
    the multiplicity is 1 or -1.

    This follows from:
    - pushBytes doesn't emit to FibonacciChannel
    - add8 doesn't emit to FibonacciChannel
    - fib8 only pulls (mult=-1) and pushes (mult=1) to FibonacciChannel -/
lemma fib_table_interaction_mult_pm_one
    (witness : EnsembleWitness (fibonacciEnsemble (p := p)))
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ witness.tables.flatMap
              (fun table => table.interactions ((FibonacciChannel (p := p)).toRaw))) :
    entry.1 = 1 ∨ entry.1 = -1 := by
  sorry

/-- Verifier's Add8Channel interactions are empty (verifier only uses FibonacciChannel) -/
lemma verifier_add8_interactions_empty (publicInput : fieldTriple (F p)) :
    (fibonacciEnsemble (p := p)).verifierInteractions (Add8Channel.toRaw) publicInput = [] := by
  sorry

/-- pushBytes's Add8Channel interactions are empty (pushBytes only uses BytesChannel) -/
lemma pushBytes_add8_interactions_empty
    (table : TableWitness (F p))
    (h_is_pushBytes : table.abstract = ⟨pushBytes (p := p)⟩) :
    table.interactions (Add8Channel.toRaw) = [] := by
  sorry

/-- fib8's Add8Channel interactions all have mult = -1 (fib8 only pulls from Add8Channel) -/
lemma fib8_add8_interactions_mult_neg
    (table : TableWitness (F p))
    (h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ table.interactions (Add8Channel.toRaw)) :
    entry.1 = -1 := by
  sorry

/-- add8's Add8Channel interactions satisfy Requirements when BytesChannel guarantees hold -/
lemma add8_interactions_satisfy_requirements
    (table : TableWitness (F p))
    (h_is_add8 : table.abstract = ⟨add8 (p := p)⟩)
    (h_constraints : table.Constraints)
    (h_bytes_guarantees : ∀ (z : F p),
        (-1, #v[z]) ∈ table.interactions (BytesChannel.toRaw) → z.val < 256)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ table.interactions (Add8Channel.toRaw)) :
    (Add8Channel (p := p)).toRaw.Requirements entry.1 entry.2 [] (fun _ _ => #[]) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- FibonacciChannel structural lemmas
-- ══════════════════════════════════════════════════════════════════════════════

/-- pushBytes's FibonacciChannel interactions are empty -/
lemma pushBytes_fib_interactions_empty
    (table : TableWitness (F p))
    (h_is_pushBytes : table.abstract = ⟨pushBytes (p := p)⟩) :
    table.interactions (FibonacciChannel.toRaw) = [] := by
  sorry

/-- add8's FibonacciChannel interactions are empty -/
lemma add8_fib_interactions_empty
    (table : TableWitness (F p))
    (h_is_add8 : table.abstract = ⟨add8 (p := p)⟩) :
    table.interactions (FibonacciChannel.toRaw) = [] := by
  sorry

/-- fib8 rows emit matching pull and push to FibonacciChannel:
    For each push (1, (n+1, y, z)), the same row has pull (-1, (n, x, y)) -/
lemma fib8_fib_push_has_matching_pull
    (table : TableWitness (F p))
    (h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩)
    (h_constraints : table.Constraints)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ table.interactions (FibonacciChannel.toRaw))
    (h_push : entry.1 = 1) :
    ∃ (n_i x_i y_i : F p),
      (-1, (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ table.interactions (FibonacciChannel.toRaw) ∧
      entry.2[0] = n_i + 1 ∧
      entry.2[1] = y_i := by
  sorry

/-!
## Main ensemble soundness theorem
-/

theorem fibonacciEnsemble_soundness : Ensemble.Soundness (F p) fibonacciEnsemble := by
  whnf
  intro witness publicInput h_constraints h_balanced h_verifier
  clear h_verifier
  -- Selectively unfold: don't unfold h_balanced yet (we'll extract channels later)
  simp only [Ensemble.Constraints] at h_constraints
  simp only [TableWitness.Constraints] at h_constraints
  rcases publicInput with ⟨ n, x, y ⟩

  -- Unfold the concrete ensemble definitions
  -- no need to rewrite h_balanced yet

  -- ═══════════════════════════════════════════════════════════════════
  -- The spec is: ∃ k, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
  -- i.e., IsValidFibState n x y
  --
  -- Strategy:
  -- 1. Extract fibonacci channel interactions from the ensemble
  -- 2. Show the verifier's pull (-1, (n,x,y)) has a matching push by balance
  -- 3. All pushes are valid (by all_fib_pushes_valid)
  -- 4. Therefore (n, x, y) is valid
  -- ═══════════════════════════════════════════════════════════════════

  -- The fibonacci channel interactions from the ensemble
  -- Note: FibonacciChannel.toRaw.arity = 3
  set fibInteractions : List (F p × Vector (F p) 3) :=
    fibonacciEnsemble.interactions (n, x, y) witness (FibonacciChannel (p := p) |>.toRaw)

  -- ── Step 1: The verifier's pull (-1, (n,x,y)) is in the interactions ──
  -- The verifier does FibonacciChannel.push (0,0,1) then FibonacciChannel.pull (n,x,y)
  -- So both (1, encode(0,0,1)) and (-1, encode(n,x,y)) are in the verifier interactions

  -- The verifier interactions for the fibonacci channel come from fibonacciVerifier
  -- which does: FibonacciChannel.push (0,0,1) then FibonacciChannel.pull (n,x,y)
  -- These produce localAdds entries that, after filtering for the fibonacci channel,
  -- give us (1, #v[0,0,1]) and (-1, #v[n,x,y]).
  -- The fibonacci interactions = table contributions ++ verifier contributions
  -- so verifier entries are in the list via List.mem_append_right.

  -- Lemma: const decomposes for triples
  have const_triple :
      (const (n, x, y) : Var fieldTriple (F p)) =
      (Expression.const n, Expression.const x, Expression.const y) := by
    simp [circuit_norm, const, explicit_provable_type]

  -- First prove a direct characterization of the verifier's localAdds
  have verifier_localAdds :
      let circuit := fibonacciVerifier.main (const (n, x, y))
      let env := emptyEnvironment (F p)
      (circuit.operations 0).localAdds env =
        FibonacciChannel.pushed (0, 0, 1) + FibonacciChannel.pulled (n, x, y) := by
    unfold fibonacciVerifier
    simp only [circuit_norm, emptyEnvironment]
    rw [const_triple]
    simp only [Expression.eval]

  have h_verifier_pull : (-1, (#v[n, x, y] : Vector (F p) 3)) ∈ fibInteractions := by
    simp only [fibInteractions, Ensemble.interactions, fibonacciEnsemble]
    apply List.mem_append_right
    simp only [Ensemble.verifierInteractions]
    rw [verifier_localAdds, Channel.pushed_def, Channel.pulled_def,
      Channel.filter_self_add, Channel.filter_self_single]
    simp [toElements]

  have h_verifier_push : (1, (#v[(0 : F p), 0, 1] : Vector (F p) 3)) ∈ fibInteractions := by
    simp only [fibInteractions, Ensemble.interactions, fibonacciEnsemble]
    apply List.mem_append_right
    simp only [Ensemble.verifierInteractions]
    rw [verifier_localAdds, Channel.pushed_def, Channel.pulled_def,
      Channel.filter_self_add, Channel.filter_self_single]
    simp [toElements]

  -- ── Step 2: Extract length bound and per-message balance for fibonacci channel ──
  have h_bal : Ensemble.BalancedChannels fibonacciEnsemble (n, x, y) witness := h_balanced
  unfold Ensemble.BalancedChannels at h_bal
  simp only [fibonacciEnsemble, List.Forall] at h_bal
  -- h_bal now contains length bounds and balances for all 3 channels
  -- FibonacciChannel is the 3rd channel: h_bal.2.2 contains its length bound and balance

  have h_fib_bound : fibInteractions.length < p := by
    have : ringChar (F p) = p := ZMod.ringChar_zmod_n p
    convert h_bal.2.2.1
    exact this.symm

  have h_fib_balanced : ∀ msg : Vector (F p) 3,
      ((fibInteractions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0 := by
    intro msg
    exact h_bal.2.2.2 msg

  -- ── Step 3: All multiplicities are ±1 ──
  -- All fibonacci interactions come from:
  -- - verifier: push (mult=1) and pull (mult=-1)
  -- - fib8 rows: each does pull (mult=-1) and push (mult=1)
  -- So all are ±1 by construction
  have h_fib_mults : ∀ entry ∈ fibInteractions, entry.1 = 1 ∨ entry.1 = -1 := by
    intro entry h_mem
    -- entry is either from tables or verifier
    simp only [fibInteractions, Ensemble.interactions] at h_mem
    rcases List.mem_append.mp h_mem with h_table | h_verifier
    · -- From tables: use the structural lemma
      exact fib_table_interaction_mult_pm_one witness entry h_table
    · -- From verifier: the verifier interactions are exactly the two we proved above
      simp only [fibonacciEnsemble, Ensemble.verifierInteractions] at h_verifier
      rw [verifier_localAdds, Channel.pushed_def, Channel.pulled_def,
          Channel.filter_self_add, Channel.filter_self_single] at h_verifier
      simp only [ProvableType.toElements] at h_verifier
      -- h_verifier : entry ∈ [(1, #v[0,0,1]), (-1, #v[n,x,y])]
      simp only [List.mem_cons] at h_verifier
      -- h_verifier : entry = (1, #v[0,0,1]) ∨ entry = (-1, #v[n,x,y]) ∨ entry ∈ []
      rcases h_verifier with h | h | h
      · left; rw [h]
      · right; rw [h]
      · simp at h

  -- ══════════════════════════════════════════════════════════════════════════
  -- STEP 4: Layered channel guarantee derivation
  -- ══════════════════════════════════════════════════════════════════════════
  --
  -- The channel dependency graph is:
  --   pushBytes → BytesChannel → add8 → Add8Channel → fib8 → FibonacciChannel
  --
  -- We derive guarantees layer by layer:
  -- (a) BytesChannel guarantees: from pushBytes requirements + balance
  -- (b) Add8Channel guarantees: from add8 soundness (using bytes guarantees) + balance
  -- (c) FibonacciChannel: handled by induction in all_fib_pushes_valid

  -- Step 4a: BytesChannel guarantees
  -- Every bytes pull has guarantee: x.val < 256
  -- This follows from: if z.val ≥ 256, all entries for #v[z] are pulls, so sum < 0, contradicting balance
  have h_bytes_guarantees : ∀ (z : F p),
      -- if z is pulled from BytesChannel somewhere in the ensemble
      (-1, #v[z]) ∈ fibonacciEnsemble.interactions (n, x, y) witness (BytesChannel.toRaw) →
      z.val < 256 := by
    intro z h_pull
    -- Extract balance for BytesChannel (first channel)
    have h_bytes_bal := h_bal.1
    set bytesInteractions := fibonacciEnsemble.interactions (n, x, y) witness (BytesChannel.toRaw)

    by_contra h_ge
    push_neg at h_ge  -- z.val ≥ 256

    -- Key fact: any entry with mult ≠ -1 has val < 256 (by bytes_push_val_lt_256)
    -- Contrapositive: if val ≥ 256, then mult = -1
    have h_all_pulls : ∀ entry ∈ bytesInteractions, entry.2 = #v[z] → entry.1 = -1 := by
      intro entry h_mem h_eq
      by_contra h_not_pull
      have h_lt := bytes_push_val_lt_256 witness (n, x, y) entry h_mem h_not_pull
      -- entry.2 = #v[z], so entry.2[0] = z, so entry.2[0].val = z.val
      simp only [h_eq, Vector.getElem_mk] at h_lt
      -- h_lt : z.val < 256, h_ge : z.val ≥ 256
      exact Nat.not_lt.mpr h_ge h_lt

    -- The filtered list for message #v[z] is nonempty (contains our pull)
    have h_nonempty : (bytesInteractions.filter (·.2 = #v[z])).length > 0 :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨h_pull, by simp⟩)

    -- All mults in the filtered list are -1
    have h_all_neg : ∀ m ∈ (bytesInteractions.filter (·.2 = #v[z])).map Prod.fst, m = -1 := by
      intro m hm
      rw [List.mem_map] at hm
      obtain ⟨⟨m', v⟩, hfilt, rfl⟩ := hm
      simp only [List.mem_filter, decide_eq_true_eq] at hfilt
      exact h_all_pulls _ hfilt.1 hfilt.2

    -- Sum of -1s = -(length)
    have h_sum_neg := sum_neg_ones _ h_all_neg

    -- But balance says sum = 0
    have h_sum_zero : ((bytesInteractions.filter (·.2 = #v[z])).map Prod.fst).sum = 0 :=
      h_bytes_bal.2 #v[z]

    -- So -(length) = 0 in F_p, meaning p | length
    rw [h_sum_neg, neg_eq_zero] at h_sum_zero

    -- But 0 < length < p, contradiction
    have h_len_bound : (bytesInteractions.filter (·.2 = #v[z])).length < p := by
      calc _ ≤ bytesInteractions.length := List.length_filter_le _ _
        _ < ringChar (F p) := h_bytes_bal.1
        _ = p := ZMod.ringChar_zmod_n p
    have h_len_zero : (bytesInteractions.filter (·.2 = #v[z])).length = 0 := by
      have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp h_sum_zero
      simp only [List.length_map] at hdvd
      exact Nat.eq_zero_of_dvd_of_lt hdvd h_len_bound
    omega

  -- Step 4b: Add8Channel guarantees
  -- Every add8 pull has guarantee (using generic channel types for reusability)
  -- This follows from: add8 soundness (using bytes guarantees) + balance
  have h_add8_guarantees : ∀ entry ∈ fibonacciEnsemble.interactions (n, x, y) witness (Add8Channel.toRaw),
      (Add8Channel (p := p)).toRaw.Guarantees entry.1 entry.2 [] (fun _ _ => #[]) := by
    intro entry h_entry_mem

    -- Extract balance for Add8Channel (second channel)
    have h_add8_bal := h_bal.2.1
    set add8Interactions := fibonacciEnsemble.interactions (n, x, y) witness (Add8Channel.toRaw)

    -- Key fact: any Add8Channel entry with mult ≠ -1 satisfies the Requirements.
    -- This follows from add8.soundness applied to each add8 row.
    -- Note: For Add8Channel, Requirements for pushes = Guarantees for pulls (same property)
    have h_push_req : ∀ entry ∈ add8Interactions, entry.1 ≠ -1 →
        (Add8Channel (p := p)).toRaw.Requirements entry.1 entry.2 [] (fun _ _ => #[]) := by
      intro entry h_entry_mem h_entry_not_neg
      -- entry is in add8Interactions = tables.flatMap table.interactions + verifier.interactions
      -- verifier doesn't emit to Add8Channel, so entry is from tables
      -- pushBytes (table 0) doesn't emit to Add8Channel
      -- add8 (table 1) emits to Add8Channel with arbitrary mult
      -- fib8 (table 2) only pulls from Add8Channel (mult = -1)
      -- So if mult ≠ -1, entry must be from add8 (table 1)

      -- Step 1: entry is from tables or verifier
      simp only [add8Interactions, Ensemble.interactions, fibonacciEnsemble] at h_entry_mem
      rcases List.mem_append.mp h_entry_mem with h_from_tables | h_from_verifier

      case inr =>
        -- From verifier: but verifier's Add8Channel interactions are empty
        have h_empty := verifier_add8_interactions_empty (p := p) (n, x, y)
        simp only [fibonacciEnsemble] at h_empty
        rw [h_empty] at h_from_verifier
        cases h_from_verifier

      case inl =>
        -- From tables: entry ∈ tables.flatMap table.interactions
        rw [List.mem_flatMap] at h_from_tables
        obtain ⟨table, h_table_mem, h_entry_in_table⟩ := h_from_tables

        -- witness.tables has 3 elements: [pushBytes_table, add8_table, fib8_table]
        -- Use witness.same_circuits to identify which circuit each table corresponds to
        have h_tables_len : witness.tables.length = 3 := by
          rw [← witness.same_length]; rfl

        -- Get the index of table in witness.tables
        obtain ⟨⟨i, hi⟩, h_table_eq⟩ := List.mem_iff_get.mp h_table_mem
        simp only [h_tables_len] at hi

        -- fibonacciEnsemble.tables.length = 3
        have h_ens_len : (fibonacciEnsemble (p := p)).tables.length = 3 := rfl

        -- i ∈ {0, 1, 2} since length = 3
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl

        case inl =>  -- i = 0: pushBytes table
          -- pushBytes's Add8Channel interactions are empty
          have h_is_pushBytes : table.abstract = ⟨pushBytes (p := p)⟩ := by
            have h_same := witness.same_circuits 0 (by rw [h_ens_len]; omega)
            simp only [fibonacciEnsemble, List.getElem_cons_zero] at h_same
            have h_table_abstract := congrArg TableWitness.abstract h_table_eq
            simp only [List.get_eq_getElem] at h_table_abstract
            exact h_table_abstract.symm.trans h_same.symm
          have h_empty := pushBytes_add8_interactions_empty table h_is_pushBytes
          rw [h_empty] at h_entry_in_table
          cases h_entry_in_table

        case inr.inl =>  -- i = 1: add8 table
          -- add8's interactions satisfy Requirements
          have h_is_add8 : table.abstract = ⟨add8 (p := p)⟩ := by
            have h_same := witness.same_circuits 1 (by rw [h_ens_len]; omega)
            simp only [fibonacciEnsemble, List.getElem_cons_succ, List.getElem_cons_zero] at h_same
            have h_table_abstract := congrArg TableWitness.abstract h_table_eq
            simp only [List.get_eq_getElem] at h_table_abstract
            exact h_table_abstract.symm.trans h_same.symm
          -- Get constraints for this table
          have h_table_constraints : table.Constraints := by
            -- h_constraints : List.Forall (fun table => table.Constraints) witness.tables
            -- h_table_mem : table ∈ witness.tables
            rw [List.forall_iff_forall_mem] at h_constraints
            exact h_constraints table h_table_mem
          -- BytesChannel guarantees for entries in this table's interactions
          -- follow from h_bytes_guarantees since table interactions ⊆ ensemble interactions
          have h_table_bytes_guarantees : ∀ (z : F p),
              (-1, #v[z]) ∈ table.interactions (BytesChannel.toRaw) → z.val < 256 := by
            intro z h_z_mem
            apply h_bytes_guarantees
            simp only [Ensemble.interactions, fibonacciEnsemble]
            apply List.mem_append_left
            rw [List.mem_flatMap]
            exact ⟨table, h_table_mem, h_z_mem⟩
          exact add8_interactions_satisfy_requirements table h_is_add8 h_table_constraints
            h_table_bytes_guarantees entry h_entry_in_table

        case inr.inr =>  -- i = 2: fib8 table
          -- fib8's Add8Channel interactions all have mult = -1
          have h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩ := by
            have h_same := witness.same_circuits 2 (by rw [h_ens_len]; omega)
            simp only [fibonacciEnsemble, List.getElem_cons_succ, List.getElem_cons_zero] at h_same
            have h_table_abstract := congrArg TableWitness.abstract h_table_eq
            simp only [List.get_eq_getElem] at h_table_abstract
            exact h_table_abstract.symm.trans h_same.symm
          have h_mult_neg := fib8_add8_interactions_mult_neg table h_is_fib8 entry h_entry_in_table
          exact absurd h_mult_neg h_entry_not_neg

    -- Case split on whether entry is a pull (mult = -1) or not
    by_cases h_is_pull : entry.1 = -1
    case pos =>
      -- entry is a pull: need to show Guarantees hold
      -- By balance, there's a push with the same message
      -- The push satisfies Requirements, which equals Guarantees for this channel

      -- Unfold the Guarantees definition for pulls
      simp only [Channel.toRaw, Add8Channel, reduceIte, h_is_pull]

      -- Need: x < 256 → y < 256 → z = (x+y) % 256 where entry.2 = #v[x, y, z]
      intro hx hy

      -- By balance, sum of mults for this message is 0
      have h_sum_zero := h_add8_bal.2 entry.2

      -- We have a pull, so filtered list is nonempty
      have h_nonempty : (add8Interactions.filter (·.2 = entry.2)).length > 0 :=
        List.length_pos_of_mem (List.mem_filter.mpr ⟨h_entry_mem, by simp⟩)

      -- There must exist an entry with mult ≠ -1 (otherwise sum of -1s ≠ 0)
      have h_exists_push : ∃ entry' ∈ add8Interactions, entry'.2 = entry.2 ∧ entry'.1 ≠ -1 := by
        by_contra h_all_neg
        push_neg at h_all_neg
        have h_all_neg_mults : ∀ m ∈ (add8Interactions.filter (·.2 = entry.2)).map Prod.fst, m = -1 := by
          intro m hm
          rw [List.mem_map] at hm
          obtain ⟨⟨m', v⟩, hfilt, rfl⟩ := hm
          simp only [List.mem_filter, decide_eq_true_eq] at hfilt
          exact h_all_neg _ hfilt.1 hfilt.2
        have h_sum_neg := sum_neg_ones _ h_all_neg_mults
        have h_sum_zero' : ((add8Interactions.filter (·.2 = entry.2)).map Prod.fst).sum = 0 := h_sum_zero
        rw [h_sum_neg, neg_eq_zero] at h_sum_zero'
        have h_len_bound : (add8Interactions.filter (·.2 = entry.2)).length < p := by
          calc _ ≤ add8Interactions.length := List.length_filter_le _ _
            _ < ringChar (F p) := h_add8_bal.1
            _ = p := ZMod.ringChar_zmod_n p
        have h_len_zero : (add8Interactions.filter (·.2 = entry.2)).length = 0 := by
          have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp h_sum_zero'
          simp only [List.length_map] at hdvd
          exact Nat.eq_zero_of_dvd_of_lt hdvd h_len_bound
        omega

      -- Get the push entry and apply h_push_req
      obtain ⟨entry', h_entry'_mem, h_entry'_eq, h_entry'_not_neg⟩ := h_exists_push
      have h_req := h_push_req entry' h_entry'_mem h_entry'_not_neg

      -- Unfold Requirements for the push (same property as Guarantees for pull)
      simp only [Channel.toRaw, Add8Channel, reduceIte, h_entry'_not_neg, not_false_eq_true] at h_req

      -- entry'.2 = entry.2, so the property transfers
      rw [h_entry'_eq] at h_req
      exact h_req hx hy

    case neg =>
      -- entry is not a pull (mult ≠ -1): Guarantees is True
      simp only [Channel.toRaw, Add8Channel, reduceIte, h_is_pull]

  -- ══════════════════════════════════════════════════════════════════════════
  -- STEP 5: h_fib8_soundness - validity transfers through fib8 rows
  -- ══════════════════════════════════════════════════════════════════════════

  have h_fib8_soundness : ∀ entry ∈ fibInteractions, entry.1 = 1 →
      entry.2 = (#v[(0 : F p), 0, 1] : Vector (F p) 3) ∨
      ∃ (n_i x_i y_i : F p),
        (-1, (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ fibInteractions ∧
        entry.2[0] = n_i + 1 ∧
        n_i.val + 1 < p ∧
        (IsValidFibState n_i x_i y_i → IsValidFibState entry.2[0] entry.2[1] entry.2[2]) := by
    intro entry h_mem h_push
    -- Case split: entry from tables or verifier?
    simp only [fibInteractions, Ensemble.interactions] at h_mem
    rcases List.mem_append.mp h_mem with h_table | h_verifier
    · -- From tables: must be from fib8 (pushBytes/add8 don't emit to FibonacciChannel)
      right
      -- Extract: entry came from some table in witness.tables
      rw [List.mem_flatMap] at h_table
      obtain ⟨table, h_table_mem, h_entry_in_table⟩ := h_table

      -- Determine which table this is - only fib8 emits to FibonacciChannel
      -- Use sorry for now; the structural case split follows the same pattern as h_push_req
      have h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩ := by
        sorry -- Structural: table must be fib8 since only fib8 emits to FibonacciChannel
      have h_table_constraints : table.Constraints := by
        rw [List.forall_iff_forall_mem] at h_constraints
        exact h_constraints table h_table_mem
      -- Use fib8_fib_push_has_matching_pull to get the matching pull
      obtain ⟨n_i, x_i, y_i, h_pull_in_table, h_n_eq, h_y_eq⟩ :=
        fib8_fib_push_has_matching_pull table h_is_fib8 h_table_constraints entry h_entry_in_table h_push
      use n_i, x_i, y_i
      refine ⟨?_, h_n_eq, ?_, ?_⟩
      · -- (-1, #v[n_i, x_i, y_i]) ∈ fibInteractions
        simp only [fibInteractions, Ensemble.interactions]
        apply List.mem_append_left
        rw [List.mem_flatMap]
        exact ⟨table, h_table_mem, h_pull_in_table⟩
      · -- n_i.val + 1 < p
        -- This requires an assumption about the fibonacci sequence not overflowing
        sorry
      · -- Validity transfer: IsValidFibState n_i x_i y_i → IsValidFibState entry.2[0] entry.2[1] entry.2[2]
        -- This requires using h_add8_guarantees to get z_i = (x_i + y_i) % 256
        sorry
    · -- From verifier: push is (0, 0, 1)
      left
      simp only [fibonacciEnsemble, Ensemble.verifierInteractions] at h_verifier
      rw [verifier_localAdds, Channel.pushed_def, Channel.pulled_def,
          Channel.filter_self_add, Channel.filter_self_single] at h_verifier
      simp only [toElements, List.mem_cons, List.not_mem_nil, or_false] at h_verifier
      rcases h_verifier with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl  -- push case: entry = (1, #v[0,0,1])
      · -- pull case: entry.1 = -1, contradicts h_push (entry.1 = 1)
        simp only at h_push
        -- h_push : -1 = 1, which is false in F p (since p > 2)
        have hp : p > 2 := by linarith [Fact.elim ‹Fact (p > 512)›]
        have h_ne : (1 : F p) ≠ -1 := by
          have h2ne : (2 : F p) ≠ 0 := by
            rw [ne_eq, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
            intro hdvd
            exact Nat.not_lt.mpr (Nat.le_of_dvd (by omega) hdvd) hp
          intro h
          apply h2ne
          calc (2 : F p) = 1 + 1 := by ring
            _ = 1 + (-1) := by rw [← h]
            _ = 0 := by ring
        exact absurd h_push.symm h_ne

  -- ── Step 6: Apply all_fib_pushes_valid ──
  have h_all_valid := all_fib_pushes_valid fibInteractions
    h_fib_bound h_fib_balanced h_fib_mults h_fib8_soundness

  -- ── Step 7: The verifier's pull has a matching valid push ──
  have h_matching := exists_push_of_pull fibInteractions (#v[n, x, y])
    (fun e h _ => h_fib_mults e h) (h_fib_balanced _) h_verifier_pull h_fib_bound

  have h_valid := h_all_valid (1, #v[n, x, y]) h_matching rfl
  simp only [Vector.getElem_mk, List.getElem_cons_zero, List.getElem_cons_succ] at h_valid
  -- h_valid should now be IsValidFibState n x y, but we might need to match the types
  exact h_valid
