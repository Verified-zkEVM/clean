/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table

Prove e2e soundness and completeness of the table ensemble.
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
  Guarantees mult msg _ := mult = -1 → slc.Guarantees msg
  Requirements mult msg _ := mult ≠ -1 → slc.Guarantees msg

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
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h_lt
      exact ⟨⟨ msg.val, h_lt ⟩, ByteUtils.fromByte_eq ..⟩
    · intro ⟨ ⟨ b, hb ⟩, h_eq ⟩
      rw [← h_eq]
      apply ByteUtils.fromByte_lt

def BytesChannel := Channel.fromStatic (F p) field BytesTable

-- bytes "circuit" that just pushes all bytes
-- probably shouldn't be a "circuit" at all
def pushBytes : FormalCircuitWithInteractions (F p) (fields 256) unit where
  main multiplicities := do
    let _  ← .mapFinRange 256 fun ⟨ i, _ ⟩ =>
      BytesChannel.emit multiplicities[i] (const i)

  localLength _ := 0
  localLength_eq := by simp +arith only [circuit_norm]
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

  channelsWithRequirements := [ BytesChannel.toRaw ]

instance Add8Channel : Channel (F p) fieldTriple where
  name := "add8"
  Guarantees
  | mult, (x, y, z), _ =>
    mult = -1 → x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256
  Requirements
  | mult, (x, y, z), _ =>
    mult ≠ -1 → x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256

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

  -- TODO make coercion work without .toRaw
  channelsWithGuarantees := [ BytesChannel.toRaw ]
  channelsWithRequirements := [ Add8Channel.toRaw ]
  requirements_iff := by
    simp only [circuit_norm, seval, BytesChannel, Add8Channel]

  -- TODO feels weird to put the entire spec in the completeness assumptions
  -- can we get something from the channel interactions??
  Assumptions
  | { x, y, z, m }, _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [BytesChannel, Add8Channel]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hm hx hy
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
    have h_input_z : input_z = mod256 (input_x + input_y) := by
      apply FieldUtils.ext
      rw [heq, mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
      linarith [hx, hy, ‹Fact (p > 512)›.elim]
    have h_bytes_guarantee : BytesChannel.Guarantees (-1) input_z env.data := by
      simpa [BytesChannel, Channel.fromStatic, BytesTable] using hz
    refine ⟨h_bytes_guarantee, ?_⟩
    refine ⟨ ?_, ?_ ⟩
    · simpa [floorDiv256] using add_completeness_bool
    · simpa [h_input_z, floorDiv256] using add_completeness_add

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
  | m, (n, x, y), _ =>
    if (m = -1)
    then
      -- (x, y) is a valid Fibonacci state
      ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
    else True

  Requirements
  | m, (n, x, y), _ =>
    if (m = 1)
    then
      -- (x, y) is a valid Fibonacci state
      ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
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

  channelsWithGuarantees := [ Add8Channel.toRaw, FibonacciChannel.toRaw ]
  channelsWithRequirements := [ FibonacciChannel.toRaw ]

  Assumptions
  | (n, x, y), _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [reduceIte, seval]
    rcases input with ⟨ n, x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [Prod.mk.injEq] at h_input
    -- why are these not simped?? maybe because fieldPair is not well-recognized
    -- rw [RawChannel.filter_eq] at h_holds ⊢
    -- rw [Channel.interactionFromRaw_eq, Channel.interactionFromRaw_eq, Channel.interactionFromRaw_eq]
    simp_all only [circuit_norm]
    set z := env.get i₀
    simp only [circuit_norm, FibonacciChannel, Add8Channel, reduceIte] at h_holds ⊢
    obtain ⟨ ⟨k, fiby, hk⟩, hadd ⟩ := h_holds
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    use k + 1
    simp only [fibonacci, fibonacciStep, ← fiby]
    rw [ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start [reduceIte]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, FibonacciChannel, Add8Channel, reduceIte]
    intro hx hy
    rw [mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
    linarith [hx, hy, ‹Fact (p > 512)›.elim]

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

  channelsWithGuarantees := [ FibonacciChannel.toRaw ]
  channelsWithRequirements := [ FibonacciChannel.toRaw ]

  Assumptions
  | (n, x, y), _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
  Spec
  | (n, x, y), _, _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

  soundness := by
    circuit_proof_start [reduceIte]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, FibonacciChannel, reduceIte,
      and_true, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩

  completeness := by
    circuit_proof_start [reduceIte]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simpa [circuit_norm, FibonacciChannel, reduceIte] using h_assumptions

section
-- define what global soundness means for an ensemble of circuits/tables and channels

-- table contains the concrete values on which we expect constraints to hold
-- which also defines what concrete interactions are contained in each channel

variable {F : Type} [Field F] [DecidableEq F]
variable {Input Output Message : TypeMap} [ProvableType Input] [ProvableType Output] [ProvableType Message]

-- tables need to be instantiated with a concrete circuit, not a family of circuits
-- this is achieved for any FormalCircuit* by witnessing the inputs and plugging them in

@[circuit_norm]
def FormalCircuitWithInteractions.instantiate (circuit : FormalCircuitWithInteractions F Input Output) : Circuit F Unit := do
  let input ← witnessAny Input
  let _ ← circuit input -- we don't care about the output in this context

@[circuit_norm]
def FormalCircuitWithInteractions.instantiatedOutput (circuit : FormalCircuitWithInteractions F Input Output)
    (env : Environment F) : Output F :=
  let outputVar := (circuit (varFromOffset Input 0)).output (size Input)
  eval env outputVar

def FormalCircuitWithInteractions.size (circuit : FormalCircuitWithInteractions F Input Output) : ℕ :=
  circuit.instantiate.localLength 0

omit [DecidableEq F] in
/-- Bridge lemma: ConstraintsHold + channel Guarantees → ConstraintsHoldWithInteractions.Soundness
    This lemma allows us to use circuit soundness proofs by providing the required Guarantees externally. -/
lemma constraintsHold_to_soundness {env : Environment F} {ops : Operations F}
    (h_constraints : Operations.ConstraintsHold env ops)
    -- For each interact operation (including subcircuits), we can prove its Guarantees
    (h_guarantees : ops.FullGuarantees env) :
    ConstraintsHoldWithInteractions.Soundness env ops := by
  have h_constraints' : Circuit.ConstraintsHold env ops := by
    apply (Circuit.constraintsHold_iff_forAll' (env := env) (ops := ops)).2
    simpa [Operations.ConstraintsHold] using h_constraints
  have h_guarantees_flat : FlatOperation.Guarantees env ops.toFlat := by
    exact (FlatOperation.forAll_toFlat_iff
      (condition := { interact i := i.assumeGuarantees → i.Guarantees env })
      (ops := ops)).2 h_guarantees
  exact Circuit.can_replace_soundness h_constraints' h_guarantees_flat

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

def Spec (table : AbstractTable F) (env : Environment F) : Prop :=
  -- first `size Input` elements of the environment are the input
  let input := valueFromOffset table.Input 0 env
  -- output is whatever the circuit computes on the input
  let output := table.circuit.instantiatedOutput env
  -- Spec on input + output
  table.circuit.Spec input output env

lemma constraintsHold_instantiate
    (circuit : FormalCircuitWithInteractions F Input Output)
    (env : Environment F) :
    (circuit.instantiate.operations 0).ConstraintsHold env ↔
    ((circuit.main (varFromOffset Input 0)).operations (size Input)).ConstraintsHold env := by
  simp only [FormalCircuitWithInteractions.instantiate, circuit_norm, witnessAny, getOffset]
  simp only [FormalCircuitWithInteractions.toSubcircuit]
  rw [Operations.toNested_toFlat, Circuit.constraintsHold_toFlat_iff, zero_add, add_zero,
    Circuit.constraintsHold_iff_forAll']

lemma guarantees_instantiate
    (circuit : FormalCircuitWithInteractions F Input Output)
    (env : Environment F) :
    (circuit.instantiate.operations 0).FullGuarantees env ↔
    ((circuit.main (varFromOffset Input 0)).operations (size Input)).FullGuarantees env := by
  simp only [FormalCircuitWithInteractions.instantiate, circuit_norm, witnessAny, getOffset]
  simp only [FormalCircuitWithInteractions.toSubcircuit]
  rw [Operations.toNested_toFlat]
  simpa [Operations.FullGuarantees, FlatOperation.Guarantees]
    using (FlatOperation.forAll_toFlat_iff
      (condition := { interact i := i.assumeGuarantees → i.Guarantees env })
      (ops := ((circuit.main (varFromOffset Input 0)).operations (size Input))))

lemma requirements_instantiate
    (circuit : FormalCircuitWithInteractions F Input Output)
    (env : Environment F) :
    (circuit.instantiate.operations 0).FullRequirements env ↔
    ((circuit.main (varFromOffset Input 0)).operations (size Input)).FullRequirements env := by
  simp only [FormalCircuitWithInteractions.instantiate, circuit_norm, witnessAny, getOffset]
  simp only [FormalCircuitWithInteractions.toSubcircuit]
  rw [Operations.toNested_toFlat]
  simpa [Operations.FullRequirements, FlatOperation.Requirements]
    using (FlatOperation.forAll_toFlat_iff
      (condition := { interact i := i.Requirements env })
      (ops := ((circuit.main (varFromOffset Input 0)).operations (size Input))))

-- this is the circuit's soundness theorem, stated in "instantiated" form
theorem weakSoundness {table : AbstractTable F} {env : Environment F} :
    table.operations.ConstraintsHold env →
    table.operations.FullGuarantees env →
      table.Spec env ∧ table.operations.FullRequirements env := by
  intro h_constraints h_guarantees
  simp only [AbstractTable.operations, AbstractTable.Spec] at *
  simp only [constraintsHold_instantiate] at h_constraints
  simp only [guarantees_instantiate] at h_guarantees
  simp only [requirements_instantiate]
  have h_constraints' :
      Circuit.ConstraintsHold env ((table.circuit.main (varFromOffset table.Input 0)).operations (size table.Input)) := by
    apply (Circuit.constraintsHold_iff_forAll' (env := env)
      (ops := (table.circuit.main (varFromOffset table.Input 0)).operations (size table.Input))).2
    simpa [Operations.ConstraintsHold] using h_constraints
  exact table.circuit.original_full_soundness
    (size table.Input) env (varFromOffset table.Input 0)
    (valueFromOffset table.Input 0 env) (eval_varFromOffset_valueFromOffset ..)
    h_constraints' h_guarantees

end AbstractTable

structure TableWitness (F : Type) [Field F] [DecidableEq F] where
  abstract : AbstractTable F
  table : List (Vector F abstract.circuit.size)
  data : ProverData F

namespace TableWitness
def width (t : TableWitness F) : ℕ := t.abstract.width

def environment (witness : TableWitness F) (row : Vector F witness.width) : Environment F where
  get j := row[j]?.getD 0
  data := witness.data
  interactions := [] -- I think we can remove this field??

def Constraints (witness : TableWitness F) : Prop :=
  witness.table.Forall fun row =>
    witness.abstract.operations.ConstraintsHold (witness.environment row)

def Guarantees (witness : TableWitness F) : Prop :=
  witness.table.Forall fun row =>
    witness.abstract.operations.FullGuarantees (witness.environment row)

def Requirements (witness : TableWitness F) : Prop :=
  witness.table.Forall fun row =>
    witness.abstract.operations.FullRequirements (witness.environment row)

def Spec (witness : TableWitness F) : Prop :=
  witness.table.Forall fun row =>
    witness.abstract.Spec (witness.environment row)

noncomputable def interactions (witness : TableWitness F) (channel : RawChannel F) : List (F × Vector F channel.arity) :=
  witness.table.flatMap fun row =>
    witness.abstract.operations.interactionsWithChannel channel (witness.environment row)
end TableWitness

def FormalCircuitWithInteractions.empty (F : Type) [Field F] [DecidableEq F]
    (Input : TypeMap) [ProvableType Input] : FormalCircuitWithInteractions F Input unit where
  main _ := return
  localLength _ := 0
  output _ _ := ()
  localAdds | _, _, _ => []
  Assumptions | _, _ => True
  Spec _ _ _ := True
  soundness := by circuit_proof_start
  completeness := by circuit_proof_start

structure Ensemble (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  tables : List (AbstractTable F)
  channels : List (RawChannel F)
  verifier : FormalCircuitWithInteractions F PublicIO unit := .empty F PublicIO
  verifier_length_zero : ∀ pi, (verifier (const pi)).localLength 0 = 0 := by
    simp only [FormalCircuitWithInteractions.empty, circuit_norm]
  Spec : PublicIO F → Prop

variable {PublicIO : TypeMap} [ProvableType PublicIO]

structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (TableWitness F)
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length), ens.tables[i] = tables[i].abstract

def emptyEnvironment (F : Type) [Field F] [DecidableEq F] : Environment F := { get _ := 0, data _ _ := #[], interactions := [] }

namespace Ensemble
noncomputable def verifierInteractions (ens : Ensemble F PublicIO) (channel : RawChannel F) (publicInput : PublicIO F) : List (F × Vector F channel.arity) :=
  let circuit := ens.verifier.main (const publicInput)
  (circuit.operations 0).interactionsWithChannel channel (emptyEnvironment F)

def Constraints (ens : Ensemble F PublicIO) (witness : EnsembleWitness ens) : Prop :=
  witness.tables.Forall fun table => table.Constraints

noncomputable def interactions (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (witness : EnsembleWitness ens) (channel : RawChannel F) : List (F × Vector F channel.arity) :=
  witness.tables.flatMap (fun table => table.interactions channel)
  ++ ens.verifierInteractions channel publicInput

/-- Per-message balance for a single channel: for each message, the sum of multiplicities is 0,
    and the filtered list length is bounded by the field characteristic.
    Also requires that the total interaction count is bounded. -/
def BalancedChannel (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (witness : EnsembleWitness ens) (channel : RawChannel F) : Prop :=
  (ens.interactions publicInput witness channel).length < ringChar F ∧
  ∀ msg : Vector F channel.arity,
    let is := (ens.interactions publicInput witness channel).filter (·.2 = msg)
    is.length < ringChar F ∧ (is.map Prod.fst).sum = 0

/-- Per-message balance: for each channel, for each message, the sum of multiplicities is 0.
    This is stronger than just requiring the total sum to be 0, and captures the intuition
    that every pull (-1) must be matched by a push (+1) for the same message.
    Additionally requires that the number of interactions is bounded by the field characteristic
    (needed for exists_push_of_pull which uses natCast). -/
def BalancedChannels (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (witness : EnsembleWitness ens) : Prop :=
  ens.channels.Forall fun channel => ens.BalancedChannel publicInput witness channel

def VerifierAccepts (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  let circuit := ens.verifier.main (const publicInput)
  (circuit.operations 0).ConstraintsHold (emptyEnvironment F)

/--
Soundness for an ensemble states that if
- constraints hold on all tables and
- and interactions sum to zero
- and constraints hold on the verifier circuit, when given the public inputs (as constants)
then the spec holds
-/
def Soundness (F : Type) [Field F] [DecidableEq F] (ens : Ensemble F PublicIO) : Prop :=
  ∀ witness publicInput,
    ens.Constraints witness →
    ens.BalancedChannels publicInput witness →
    ens.VerifierAccepts publicInput →
    ens.Spec publicInput

/--
Completeness for an ensemble states that for any public input satisfying the spec,
the verifier accepts and there exists a witness such that constraints hold and the channels are balanced
-/
def Completeness (ens : Ensemble F PublicIO) : Prop :=
  ∀ publicInput,
    ens.Spec publicInput →
    ens.VerifierAccepts publicInput ∧
    ∃ witness, ens.Constraints witness ∧ ens.BalancedChannels publicInput witness

end Ensemble

-- infrastructure for iteratively adding tables to an ensemble such that we can always fill in
-- the next table's guarantees

namespace Ensemble
def empty (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] : Ensemble F PublicIO where
  tables := []
  channels := []
  Spec _ := True

-- weaker version of BalancedChannel that works with ensembles that aren't fully specified yet,
-- so we don't have information about the _full_ list of interaction but we can assume our interactions are
-- a sublist of some larger list which is balanced
def PartialBalancedChannel (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (witness : EnsembleWitness ens) (channel : RawChannel F) : Prop :=
  ∃ interactions,
    (ens.interactions publicInput witness channel).Sublist interactions ∧
    interactions.length < ringChar F ∧
    ∀ msg : Vector F channel.arity,
      (interactions.filter (·.2 = msg) |>.map Prod.fst).sum = 0

def PartialBalancedChannels (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (witness : EnsembleWitness ens) : Prop :=
  ens.channels.Forall fun channel => ens.PartialBalancedChannel publicInput witness channel

-- sound channels means that we can eliminate the Guarantees from each table, assuming constraints and partial balance
-- this is basically what's needed for Soundness, together with per-table soundness implying global soundness
def SoundChannels (ens : Ensemble F PublicIO) : Prop :=
  ∀ witness publicInput,
  PartialBalancedChannels ens publicInput witness →
  ens.Constraints witness →
  witness.tables.Forall fun table => table.Guarantees

/--
partial balance + sound channels gives you the full soundness statement
on each table without assuming guarantees
-/
lemma soundChannels_imply_soundness (ens : Ensemble F PublicIO) :
  ens.SoundChannels →
  ∀ witness publicInput,
    ens.PartialBalancedChannels publicInput witness →
    -- assuming the constraints hold, the spec and the requirements hold as well
    ens.Constraints witness →
    witness.tables.Forall fun table =>
      table.Spec ∧ table.Requirements
     := by
  simp only [SoundChannels, Constraints]
  intro sound_channels witness publicInput partial_balance constraints
  simp only [List.forall_iff_forall_mem] at *
  intro table h_mem_table
  have guarantees := sound_channels witness publicInput partial_balance constraints table h_mem_table
  clear sound_channels
  specialize constraints table h_mem_table
  simp only [TableWitness.Guarantees, TableWitness.Requirements, TableWitness.Spec, TableWitness.Constraints] at *
  set env := table.environment
  rcases table with ⟨ table, witness, data ⟩
  simp only [List.forall_iff_forall_mem] at *
  suffices (∀ row ∈ witness, table.Spec (env row) ∧ table.operations.FullRequirements (env row)) by
    simp_all
  intro row h_mem_row
  exact AbstractTable.weakSoundness (constraints row h_mem_row) (guarantees row h_mem_row)

end Ensemble
end

-- let's try to prove soundness and completeness of the Fibonacci with channels example
def fibonacciEnsemble : Ensemble (F p) fieldTriple where
  tables := [ ⟨pushBytes⟩, ⟨add8⟩, ⟨fib8⟩ ]
  channels := [ BytesChannel.toRaw, Add8Channel.toRaw, FibonacciChannel.toRaw ]
  verifier := fibonacciVerifier
  verifier_length_zero := by simp only [fibonacciVerifier, circuit_norm]

  Spec | (n, x, y) => ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

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
        have : Fact (1 < p) := ⟨ by linarith [Fact.elim pGt] ⟩
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
  -- Entry is from tables or verifier
  simp only [Ensemble.interactions] at h_mem
  rcases List.mem_append.1 h_mem with h_tables | h_ver
  · -- From tables: case split on which table
    rcases List.mem_flatMap.1 h_tables with ⟨table, h_table_mem, h_mem_table⟩
    rcases List.mem_iff_getElem.1 h_table_mem with ⟨i, hi, htable⟩
    have h_len : witness.tables.length = 3 := by
      simpa [fibonacciEnsemble] using witness.same_length.symm
    have hi' : i < 3 := by simpa [h_len] using hi
    have h_same : fibonacciEnsemble.tables[i] = table.abstract := by
      simpa [htable] using witness.same_circuits i (by simpa [fibonacciEnsemble, h_len] using hi)
    have h_table_abs : table.abstract = fibonacciEnsemble.tables[i] := h_same.symm
    match i with
    | 0 => -- pushBytes: emits byte values 0..255
      simp only [fibonacciEnsemble] at h_table_abs
      simp only [TableWitness.interactions, AbstractTable.operations] at h_mem_table
      rcases List.mem_flatMap.1 h_mem_table with ⟨row, h_row_mem, h_in_filter⟩
      rw [h_table_abs] at h_in_filter
      simp only [RawChannel.filter, pushBytes, witnessAny, getOffset,
        FormalCircuitWithInteractions.instantiate, circuit_norm, BytesChannel, BytesTable,
        Channel.emitted, InteractionDelta.single, Channel.toRaw,
        List.filterMap_flatMap] at h_in_filter
      rcases List.mem_flatMap.1 h_in_filter with ⟨idx, h_idx_mem, h_entry_mem⟩
      -- h_entry_mem says entry is in filterMap applied to singleton list, giving entry = (_, #v[idx])
      simp only [List.filterMap_cons, true_and,
        show (#[(_ : F p)] : Array (F p)).size = 1 by rfl, dite_true,
        show (0 : InteractionDelta (F p)) = [] by rfl, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h_entry_mem
      -- h_entry_mem : entry = (_, #v[↑↑idx]) where idx : Fin 256
      -- idx.val < 256 by definition
      have h_idx_lt : idx.val < 256 := idx.isLt
      have h_idx_lt_p : idx.val < p := by
        have hp : p > 512 := Fact.elim (by infer_instance : Fact (p > 512))
        omega
      have h_val : (idx.val : F p).val = idx.val := ZMod.val_natCast_of_lt h_idx_lt_p
      -- entry.2[0] = idx (as F p), so entry.2[0].val = idx.val < 256
      rw [h_entry_mem]
      -- Goal: ZMod.val ((_, #v[↑↑idx]).2)[0] < 256
      -- #v[↑↑idx][0] = ↑↑idx = (idx.val : F p)
      -- So ZMod.val (↑↑idx) = idx.val < 256
      calc ZMod.val ((_, #v[(idx.val : F p)]).2)[0]
        = ZMod.val (#v[(idx.val : F p)])[0] := rfl
        _ = ZMod.val (idx.val : F p) := by congr 1
        _ = idx.val := h_val
        _ < 256 := h_idx_lt
    | 1 => -- add8: only pulls (mult = -1), contradicts h_push
      simp only [fibonacciEnsemble] at h_table_abs
      simp only [TableWitness.interactions, AbstractTable.operations] at h_mem_table
      rcases List.mem_flatMap.1 h_mem_table with ⟨row, h_row_mem, h_in_filter⟩
      rw [h_table_abs] at h_in_filter
      simp only [RawChannel.filter, add8, witnessAny, getOffset, BytesTable,
        FormalCircuitWithInteractions.instantiate, circuit_norm, BytesChannel, Add8Channel,
        Channel.emitted, Channel.pulled, InteractionDelta.single, Channel.toRaw] at h_in_filter
      rw [InteractionDelta.add_eq_append] at h_in_filter
      simp only [List.filterMap_append, List.filterMap_cons, true_and,
        show ("add8" : String) = "bytes" ↔ False by decide, false_and, dite_false, dite_true,
        show (#[(_ : F p)] : Array (F p)).size = 1 by rfl,
        show (0 : InteractionDelta (F p)) = [] by rfl,
        List.filterMap_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h_in_filter
      -- h_in_filter : entry = (-1, #v[z])
      -- But h_push says entry.1 ≠ -1, contradiction
      rw [h_in_filter] at h_push
      simp only [ne_eq, not_true_eq_false] at h_push
    | 2 => -- fib8: no BytesChannel interactions
      simp only [fibonacciEnsemble] at h_table_abs
      simp only [TableWitness.interactions, AbstractTable.operations] at h_mem_table
      rcases List.mem_flatMap.1 h_mem_table with ⟨row, h_row_mem, h_in_filter⟩
      rw [h_table_abs] at h_in_filter
      simp only [RawChannel.filter, fib8, witnessAny, getOffset, BytesTable,
        FormalCircuitWithInteractions.instantiate, circuit_norm, BytesChannel, Add8Channel,
        FibonacciChannel, Channel.emitted, Channel.pulled, InteractionDelta.single, Channel.toRaw] at h_in_filter
      rw [InteractionDelta.add_eq_append, InteractionDelta.add_eq_append] at h_in_filter
      simp only [List.filterMap_append, List.filterMap_cons,
        show ("fibonacci" : String) = "bytes" ↔ False by decide, false_and, dite_false,
        show ("add8" : String) = "bytes" ↔ False by decide,
        show (0 : InteractionDelta (F p)) = [] by rfl,
        List.filterMap_nil, List.append_nil, List.not_mem_nil] at h_in_filter
  · -- From verifier: verifier has no BytesChannel interactions
    have h_verifier_empty :
        fibonacciEnsemble.verifierInteractions BytesChannel.toRaw publicInput = [] := by
      -- TODO `circuit_norm` alone here should use `Channel.toRaw_ext_iff` but doesn't,
      -- it seems to need `seval` to discharge side conditions? not clear to me why
      simp only [fibonacciEnsemble, Ensemble.verifierInteractions, fibonacciVerifier, circuit_norm, seval]
    simp only [h_verifier_empty, List.not_mem_nil] at h_ver

omit [Fact (p > 512)] in
/-- The step counter of any valid fibonacci state is bounded by the number of interactions.

    The fibonacci sequence forms a chain: 0 → 1 → 2 → ... → n where each step
    contributes at least 2 entries to fibInteractions. Since fibInteractions.length < p,
    any step counter n_i satisfies n_i.val < p/2 < p - 1, hence n_i.val + 1 < p. -/
lemma fib_step_counter_bounded
    (fibInteractions : List (F p × Vector (F p) 3))
    (h_bound : fibInteractions.length < p)
    (h_mults : ∀ e ∈ fibInteractions, e.1 = 1 ∨ e.1 = -1)
    (h_balanced : ∀ msg, (fibInteractions.filter (·.2 = msg) |>.map (·.1)).sum = 0)
    (h_push_pred :
      ∀ entry ∈ fibInteractions, entry.1 = 1 →
        entry.2 = (#v[(0 : F p), 0, 1] : Vector (F p) 3) ∨
        ∃ (n x y : F p), ((-1 : F p), (#v[n, x, y] : Vector (F p) 3)) ∈ fibInteractions ∧
          entry.2[0] = n + 1)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ fibInteractions)
    (h_push : entry.1 = 1)
    (n_i : F p)
    (h_n_eq : entry.2[0] = n_i) :
    n_i.val + 1 < p := by
  -- Prove a stronger statement by induction on Nat counters < p
  suffices h : ∀ n : ℕ, n < p →
      ∀ entry ∈ fibInteractions, entry.1 = 1 → entry.2[0] = (n : F p) → (n + 1 ≤ fibInteractions.length) by
    have h_step : entry.2[0] = (n_i.val : F p) := by
      exact h_n_eq.trans (ZMod.natCast_zmod_val n_i).symm
    have h_le := h n_i.val (ZMod.val_lt n_i) entry h_mem h_push h_step
    exact lt_of_le_of_lt h_le h_bound
  intro n h_n_lt
  suffices h : ∀ entry ∈ fibInteractions,
    entry.1 = 1 → entry.2[0] = (n : F p) → ∀ k ≤ n, ∃ entry' ∈ fibInteractions, entry'.2[0].val = k by
    intro entry h_mem h_push h_step
    -- this is should be very easy: there are n+1 distinct entries in the chain (0..n),
    -- therefore the chain length is at least n+1
    specialize h entry h_mem h_push h_step
    clear h_mem h_push h_step entry h_n_lt h_n_eq
    clear h_mem h_push entry n_i h_push_pred
    -- let's map the list to ℕ counters and use List.map_length
    -- and then talk about Finsets
    let as := fibInteractions.map (fun e => ZMod.val e.2[0])
    suffices h_natList : (∀ k ≤ n, k ∈ as) → n + 1 ≤ as.length by simp_all [as]
    intro hk
    simp only [← List.mem_toFinset] at hk
    suffices n + 1 ≤ as.toFinset.card by
      grw [List.toFinset_card_le] at this
      linarith
    generalize as.toFinset = s at *
    rw [← Finset.card_range (n + 1)]
    apply Finset.card_le_card
    intro k hk'
    simp_all only [Finset.mem_range]
    exact hk k (by linarith)

  induction n with
  | zero =>
    intro entry h_mem h_push h_step k k_le_0
    have hk : k = 0 := by linarith
    subst hk
    use entry, h_mem
    simp only [Nat.cast_zero] at h_step
    simp [h_step, ZMod.val_zero]
  | succ n ih =>
    intro entry h_mem h_push h_step k hk
    have h_pred := h_push_pred entry h_mem h_push
    rcases h_pred with h_base | ⟨n_prev, x, y, h_pull, h_step_prev⟩
    · -- base push contradicts counter n+1
      exfalso
      have h0 : entry.2[0] = 0 := by simp [h_base]
      have h_cast : ((n + 1 : ℕ) : F p) = 0 := by simpa [h_step] using h0
      have hval := ZMod.val_cast_of_lt h_n_lt
      have : (n + 1 : ℕ) = 0 := by simp [h_cast] at hval
      exact Nat.succ_ne_zero _ this
    · -- predecessor pull gives predecessor push
      have h_push_prev : (1, (#v[n_prev, x, y] : Vector (F p) 3)) ∈ fibInteractions :=
        exists_push_of_pull fibInteractions (#v[n_prev, x, y])
          (fun e h _ => h_mults e h) (h_balanced _) h_pull h_bound
      have h_eq : n_prev = (n : F p) := by
        have h' : n_prev + 1 = (n + 1 : F p) := by simpa [h_step_prev] using h_step
        have h'' : n_prev + 1 = (n : F p) + 1 := by simpa [Nat.cast_add] using h'
        exact add_right_cancel h''
      -- if k = n+1, use current entry; otherwise use IH on predecessor
      have hk_cases : k = n + 1 ∨ k ≤ n := by
        exact Nat.lt_or_eq_of_le hk |>.elim (fun hlt => Or.inr (Nat.le_of_lt_succ hlt)) (fun heq => Or.inl heq)
      cases hk_cases with
      | inl hk_eq =>
          subst hk_eq
          use entry, h_mem
          -- counter value is n+1
          have hval := ZMod.val_cast_of_lt h_n_lt
          simpa [h_step] using hval
      | inr hk_le =>
          have h_step_prev' : (#v[n_prev, x, y] : Vector (F p) 3)[0] = (n : F p) := by
            simp [h_eq]
          have := ih (Nat.lt_of_succ_lt h_n_lt)
            (1, (#v[n_prev, x, y] : Vector (F p) 3)) h_push_prev rfl h_step_prev' k hk_le
          exact this

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
  -- Entry is from some table's FibonacciChannel interactions
  rcases List.mem_flatMap.1 h_mem with ⟨table, h_table_mem, h_entry_in_table⟩
  rcases List.mem_iff_getElem.1 h_table_mem with ⟨i, hi, htable⟩
  have h_len : witness.tables.length = 3 := by
    simpa [fibonacciEnsemble] using witness.same_length.symm
  have hi' : i < 3 := by simpa [h_len] using hi
  have h_same : fibonacciEnsemble.tables[i] = table.abstract := by
    simpa [htable] using witness.same_circuits i (by simpa [fibonacciEnsemble, h_len] using hi)
  have h_table_abs : table.abstract = fibonacciEnsemble.tables[i] := h_same.symm
  match i with
  | 0 => -- pushBytes: no FibonacciChannel interactions
    simp only [fibonacciEnsemble] at h_table_abs
    rcases (by
      simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_entry_in_table
    ) with ⟨row, h_row_mem, h_raw_mem⟩
    rw [h_table_abs] at h_raw_mem
    simp [circuit_norm, pushBytes, FibonacciChannel, BytesChannel, Channel.emitted, RawChannel.filter] at h_raw_mem
  | 1 => -- add8: no FibonacciChannel interactions
    simp only [fibonacciEnsemble] at h_table_abs
    rcases (by
      simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_entry_in_table
    ) with ⟨row, h_row_mem, h_raw_mem⟩
    rw [h_table_abs] at h_raw_mem
    simp only [add8, circuit_norm, FibonacciChannel, BytesChannel, Add8Channel, Channel.emitted, RawChannel.filter,
      InteractionDelta.single] at h_raw_mem
    simp [InteractionDelta.zero_eq_nil, InteractionDelta.add_eq_append] at h_raw_mem
  | 2 => -- fib8: pulls and pushes to FibonacciChannel with mult = ±1
    simp only [fibonacciEnsemble] at h_table_abs
    rcases (by
      simpa [TableWitness.interactions, AbstractTable.operations, RawChannel.filter, h_table_abs] using h_entry_in_table
    ) with ⟨row, h_row_mem, h_raw_mem⟩
    set env := table.environment row
    rw [h_table_abs] at h_raw_mem
    simp only [fib8, circuit_norm, FibonacciChannel, Add8Channel, Channel.emitted,
      InteractionDelta.single, RawChannel.filter] at h_raw_mem
    simp [InteractionDelta.zero_eq_nil, InteractionDelta.add_eq_append] at h_raw_mem
    rcases h_raw_mem with rfl | rfl <;> simp

/-- Verifier's Add8Channel interactions are empty (verifier only uses FibonacciChannel) -/
lemma verifier_add8_interactions_empty (publicInput : fieldTriple (F p)) :
    (fibonacciEnsemble (p := p)).verifierInteractions (Add8Channel.toRaw) publicInput = [] := by
  simp [circuit_norm, Ensemble.verifierInteractions, fibonacciEnsemble, fibonacciVerifier,
    FibonacciChannel, Add8Channel]

/-- pushBytes's Add8Channel interactions are empty (pushBytes only uses BytesChannel) -/
lemma pushBytes_add8_interactions_empty
    (table : TableWitness (F p))
    (h_is_pushBytes : table.abstract = ⟨pushBytes (p := p)⟩) :
    table.interactions (Add8Channel.toRaw) = [] := by
  -- pushBytes only emits to BytesChannel (name = "bytes"), not Add8Channel (name = "add8")
  simp only [TableWitness.interactions, AbstractTable.operations]
  rw [List.flatMap_eq_nil_iff]
  intro row h_row_mem
  rw [h_is_pushBytes]
  -- Unfold to get the actual localAdds list for pushBytes
  simp only [RawChannel.filter, pushBytes, witnessAny, getOffset, BytesTable,
    FormalCircuitWithInteractions.instantiate, circuit_norm, BytesChannel, Add8Channel,
    Channel.emitted, InteractionDelta.single, Channel.toRaw, List.filterMap_flatMap,
    List.flatMap_eq_nil_iff]
  intro i _
  -- Each entry has name "bytes" ≠ "add8", so filter removes it
  simp only [List.filterMap_cons]
  simp only [show ("bytes" : String) = "add8" ↔ False by decide, false_and, dite_false]
  rfl

/-- fib8's Add8Channel interactions all have mult = -1 (fib8 only pulls from Add8Channel) -/
lemma fib8_add8_interactions_mult_neg
    (table : TableWitness (F p))
    (h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ table.interactions (Add8Channel.toRaw)) :
    entry.1 = -1 := by
  -- fib8 emits to Add8Channel only with pulled (mult = -1)
  simp only [TableWitness.interactions, AbstractTable.operations] at h_mem
  rcases List.mem_flatMap.1 h_mem with ⟨row, h_row_mem, h_in_filter⟩
  rw [h_is_fib8] at h_in_filter
  simp only [RawChannel.filter, fib8, witnessAny, getOffset, FormalCircuitWithInteractions.instantiate,
    circuit_norm, FibonacciChannel, Add8Channel, Channel.emitted, Channel.pulled,
    InteractionDelta.single, Channel.toRaw] at h_in_filter
  rw [InteractionDelta.add_eq_append, InteractionDelta.add_eq_append] at h_in_filter
  simp only [List.filterMap_append, List.filterMap_cons,
    show ("fibonacci" : String) = "add8" ↔ False by decide, false_and, dite_false,
    true_and, toElements] at h_in_filter
  simp only [show ([_,_,_] : List (F p)).toArray.size = 3 by rfl, dite_true] at h_in_filter
  -- `0` in List context represents InteractionDelta.zero = []
  -- Simplify using the fact that InteractionDelta.zero = []
  simp only [show (0 : InteractionDelta (F p)) = [] by rfl,
    List.filterMap_nil, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at h_in_filter
  -- Now h_in_filter says entry = (-1, ...)
  rw [h_in_filter]

/-- add8's Add8Channel interactions satisfy Requirements when BytesChannel guarantees hold -/
lemma add8_interactions_satisfy_requirements
    (table : TableWitness (F p))
    (h_is_add8 : table.abstract = ⟨add8 (p := p)⟩)
    (h_constraints : table.Constraints)
    (h_bytes_guarantees : ∀ (z : F p),
        (-1, #v[z]) ∈ table.interactions (BytesChannel.toRaw) → z.val < 256)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ table.interactions (Add8Channel.toRaw)) :
    (Add8Channel (p := p)).toRaw.Requirements entry.1 entry.2 (fun _ _ => #[]) := by
  -- Extract the row that generated this entry
  simp only [TableWitness.interactions, AbstractTable.operations] at h_mem
  rw [h_is_add8] at h_mem
  rcases List.mem_flatMap.1 h_mem with ⟨row, h_row_mem, h_in_filter⟩

  -- Simplify h_in_filter to extract entry structure
  simp only [RawChannel.filter, add8, witnessAny, getOffset, FormalCircuitWithInteractions.instantiate,
    circuit_norm, BytesChannel, Add8Channel, Channel.emitted, Channel.pulled, BytesTable,
    InteractionDelta.single, Channel.toRaw] at h_in_filter
  rw [InteractionDelta.add_eq_append] at h_in_filter
  simp only [List.filterMap_append, List.filterMap_cons,
    show ("bytes" : String) = "add8" ↔ False by decide, false_and, dite_false,
    true_and, toElements] at h_in_filter
  simp only [show ([_,_,_] : List (F p)).toArray.size = 3 by rfl, dite_true] at h_in_filter
  simp only [show (0 : InteractionDelta (F p)) = [] by rfl,
    List.filterMap_nil, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at h_in_filter

  -- Now h_in_filter : entry = (row[3], #v[row[0], row[1], row[2]])
  -- entry.1 = row[3] (the multiplicity m)
  -- entry.2 = #v[row[0], row[1], row[2]] = (x, y, z)
  rw [h_in_filter]

  -- The Requirements are: if mult ≠ -1 then x < 256 → y < 256 → z = (x + y) % 256
  simp only [Add8Channel, Channel.toRaw]
  set env := table.environment row with h_env_def
  intro (h_mult : env.get 3 ≠ (-1 : F p)) h_x_range h_y_range

  -- Need to prove: x < 256 → y < 256 → z = (x + y) % 256

  -- Get the constraints for this row
  have h_row_constraints : table.abstract.operations.ConstraintsHold env := by
    simp only [TableWitness.Constraints] at h_constraints
    rw [List.forall_iff_forall_mem] at h_constraints
    exact h_constraints row h_row_mem

  simp only [AbstractTable.operations, AbstractTable.constraintsHold_instantiate] at h_row_constraints
  rw [h_is_add8] at h_row_constraints
  simp only at h_row_constraints

  -- Set up aliases
  set input_var : Var Add8Inputs (F p) := varFromOffset Add8Inputs 0
  set offset := size Add8Inputs
  set ops := (add8.main input_var).operations offset

  -- Build Guarantees for the interactions in add8
  have h_guarantees : ops.FullGuarantees env := by
    simp only [ops, circuit_norm, add8, input_var, BytesChannel, BytesTable]
    refine ⟨ ?_, ?_ ⟩
    · apply h_bytes_guarantees (env.get 2)
      -- Need to show (-1, #v[env.get 2]) ∈ table.interactions BytesChannel.toRaw
      -- This follows because add8 pulls z from BytesChannel
      simp only [TableWitness.interactions, AbstractTable.operations]
      rw [List.mem_flatMap]
      refine ⟨row, h_row_mem, ?_⟩
      rw [h_is_add8]
      simp only [RawChannel.filter, add8, witnessAny, getOffset, FormalCircuitWithInteractions.instantiate,
        circuit_norm, BytesChannel, Channel.pulled, InteractionDelta.single, Channel.toRaw,
        toElements]
      simp [InteractionDelta.add_eq_append, env]
    ·
      let boolInput : Var field (F p) := var { index := offset }
      let eqInput : Var (ProvablePair id id) (F p) :=
        (var { index := 0 } + var { index := 1 } - var { index := 2 } - var { index := offset } * 256, 0)
      let boolSc :=
        (assertBool.toSubcircuit (offset + 1) boolInput)
      let eqSc :=
        ((Gadgets.Equality.circuit id).toSubcircuit (offset + 1) eqInput)
      have h_bool_channels : boolSc.channelsWithGuarantees = [] := by
        simp [boolSc, FormalAssertion.toSubcircuit]
      have h_eq_channels : eqSc.channelsWithGuarantees = [] := by
        simp [eqSc, FormalAssertion.toSubcircuit]
      have h_bool_guarantees : FlatOperation.Guarantees env boolSc.ops.toFlat := by
        refine (boolSc.guarantees_iff env).2 ?_
        simpa [h_bool_channels]
      have h_eq_guarantees : FlatOperation.Guarantees env eqSc.ops.toFlat := by
        refine (eqSc.guarantees_iff env).2 ?_
        simpa [h_eq_channels]
      exact ⟨h_bool_guarantees, h_eq_guarantees⟩

  -- Use bridge lemma to get ConstraintsHoldWithInteractions.Soundness
  have h_soundness : ConstraintsHoldWithInteractions.Soundness env ops := by
    apply constraintsHold_to_soundness h_row_constraints h_guarantees

  -- Apply add8.soundness with the correct offset
  have h_eval_eq : eval env input_var = { x := env.get 0, y := env.get 1, z := env.get 2, m := env.get 3 } := by
    simp only [circuit_norm, input_var]
  have h_add8_result := add8.soundness offset env input_var
      { x := env.get 0, y := env.get 1, z := env.get 2, m := env.get 3 }
      h_eval_eq
      h_soundness

  -- Extract Requirements
  have h_requirements := h_add8_result.2

  -- Simplify to get the concrete requirement
  simp only [circuit_norm, add8, Add8Channel, BytesChannel, BytesTable,
    Expression.eval, input_var] at h_requirements

  -- Simplify goal
  simp only [fromElements] at h_x_range h_y_range ⊢

  -- Reduce the if in h_requirements using h_mult
  simp only [h_mult, not_false_eq_true, true_implies] at h_requirements

  -- Apply the requirement
  exact h_requirements h_x_range h_y_range

-- ══════════════════════════════════════════════════════════════════════════════
-- FibonacciChannel structural lemmas
-- ══════════════════════════════════════════════════════════════════════════════

/-- pushBytes's FibonacciChannel interactions are empty -/
lemma pushBytes_fib_interactions_empty
    (table : TableWitness (F p))
    (h_is_pushBytes : table.abstract = ⟨pushBytes (p := p)⟩) :
    table.interactions (FibonacciChannel.toRaw) = [] := by
  -- pushBytes only emits to BytesChannel (name = "bytes"), not FibonacciChannel (name = "fibonacci")
  simp only [TableWitness.interactions, AbstractTable.operations]
  rw [List.flatMap_eq_nil_iff]
  intro row h_row_mem
  rw [h_is_pushBytes]
  simp only [RawChannel.filter, pushBytes, witnessAny, getOffset, FormalCircuitWithInteractions.instantiate,
    circuit_norm, BytesChannel, BytesTable, FibonacciChannel, Channel.emitted, InteractionDelta.single,
    Channel.toRaw, List.filterMap_flatMap, List.flatMap_eq_nil_iff]
  intro i _
  simp only [List.filterMap_cons]
  simp only [show ("bytes" : String) = "fibonacci" ↔ False by decide, false_and, dite_false]
  rfl

/-- add8's FibonacciChannel interactions are empty -/
lemma add8_fib_interactions_empty
    (table : TableWitness (F p))
    (h_is_add8 : table.abstract = ⟨add8 (p := p)⟩) :
    table.interactions (FibonacciChannel.toRaw) = [] := by
  -- add8 only emits to BytesChannel and Add8Channel, not FibonacciChannel
  simp only [TableWitness.interactions, AbstractTable.operations]
  rw [List.flatMap_eq_nil_iff]
  intro row h_row_mem
  rw [h_is_add8]
  simp only [RawChannel.filter, add8, witnessAny, getOffset, FormalCircuitWithInteractions.instantiate,
    circuit_norm, BytesChannel, BytesTable, Add8Channel, FibonacciChannel, Channel.emitted, Channel.pulled,
    InteractionDelta.single, Channel.toRaw]
  rw [InteractionDelta.add_eq_append]
  simp only [List.filterMap_append, List.filterMap_cons,
    show ("bytes" : String) = "fibonacci" ↔ False by decide, false_and, dite_false,
    show ("add8" : String) = "fibonacci" ↔ False by decide]
  simp only [show (0 : InteractionDelta (F p)) = [] by rfl, List.filterMap_nil, List.append_nil]

/-- fib8 rows emit matching pull and push to FibonacciChannel:
    For each push (1, (n+1, y, z)), the same row has:
    - pull (-1, (n, x, y)) to FibonacciChannel
    - pull (-1, (x, y, z)) to Add8Channel -/
lemma fib8_fib_push_has_matching_pull
    (table : TableWitness (F p))
    (h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ table.interactions (FibonacciChannel.toRaw))
    (h_push : entry.1 = 1) :
    ∃ (n_i x_i y_i : F p),
      ((-1 : F p), (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ table.interactions (FibonacciChannel.toRaw) ∧
      ((-1 : F p), (#v[x_i, y_i, entry.2[2]] : Vector (F p) 3)) ∈ table.interactions (Add8Channel.toRaw) ∧
      entry.2[0] = n_i + 1 ∧
      entry.2[1] = y_i := by
  -- entry is a push (mult=1) from table's FibonacciChannel interactions
  -- fib8 emits: pull (-1, (n,x,y)), pull (-1, (x,y,z)) to Add8, push (1, (n+1,y,z))
  -- So entry must be the push, and we can find the corresponding pulls from the same row
  simp only [TableWitness.interactions, AbstractTable.operations] at h_mem
  rw [h_is_fib8] at h_mem
  rcases List.mem_flatMap.1 h_mem with ⟨row, h_row_mem, h_in_filter⟩
  -- Simplify h_in_filter to extract the structure
  simp only [RawChannel.filter, fib8, witnessAny, getOffset, FormalCircuitWithInteractions.instantiate,
    circuit_norm, FibonacciChannel, Add8Channel, Channel.emitted, Channel.pulled,
    InteractionDelta.single, Channel.toRaw] at h_in_filter
  rw [InteractionDelta.add_eq_append, InteractionDelta.add_eq_append] at h_in_filter
  simp only [List.filterMap_append, List.filterMap_cons, true_and,
    show ("add8" : String) = "fibonacci" ↔ False by decide, false_and, dite_false,
    toElements] at h_in_filter
  simp only [show ([_,_,_] : List (F p)).toArray.size = 3 by rfl, dite_true] at h_in_filter
  simp only [show (0 : InteractionDelta (F p)) = [] by rfl,
    List.filterMap_nil, List.append_nil] at h_in_filter

  -- entry is in [pull] ++ [push]
  have h_in_filter' := h_in_filter
  simp only [List.mem_append, List.mem_singleton] at h_in_filter'
  rcases h_in_filter' with h_pull | h_push_eq
  · -- entry is the pull: contradicts h_push
    have hneg : entry.1 = (-1 : F p) := by simp [h_pull]
    have hneq : (-1 : F p) ≠ (1 : F p) := by
      have : Fact (2 < p) := ⟨by
        have : p > 512 := Fact.out
        linarith⟩
      simpa using (ZMod.neg_one_ne_one (n := p))
    have hcon : False := by
      apply hneq
      simpa [hneg] using h_push
    cases hcon
  · -- entry is the push
    -- set aliases
    set env := table.environment row
    use env.get 0, env.get 1, env.get 2
    -- show fib pull in fibInteractions
    and_intros
    · -- FibonacciChannel pull is in table interactions
      simp [TableWitness.interactions, AbstractTable.operations]
      refine ⟨row, h_row_mem, ?_⟩
      rw [h_is_fib8]
      simp only [RawChannel.filter, fib8, witnessAny, getOffset,
        FormalCircuitWithInteractions.instantiate, circuit_norm, FibonacciChannel, Add8Channel,
        Channel.emitted, Channel.pulled, InteractionDelta.single, Channel.toRaw]
      rw [InteractionDelta.add_eq_append, InteractionDelta.add_eq_append]
      simp only [List.filterMap_append, List.filterMap_cons, true_and,
        show ("add8" : String) = "fibonacci" ↔ False by decide, false_and, dite_false,
        toElements]
      simp only [show ([_,_,_] : List (F p)).toArray.size = 3 by rfl, dite_true]
      simp only [show (0 : InteractionDelta (F p)) = [] by rfl,
        List.filterMap_nil, List.append_nil, List.mem_append, List.mem_singleton]
      left
      simp [env]
    · -- Add8Channel pull is in table interactions
      simp [TableWitness.interactions, AbstractTable.operations]
      refine ⟨row, h_row_mem, ?_⟩
      rw [h_is_fib8]
      simp only [RawChannel.filter, fib8, witnessAny, getOffset,
        FormalCircuitWithInteractions.instantiate, circuit_norm, FibonacciChannel, Add8Channel,
        Channel.emitted, Channel.pulled, InteractionDelta.single, Channel.toRaw]
      rw [InteractionDelta.add_eq_append, InteractionDelta.add_eq_append]
      simp only [List.filterMap_append, List.filterMap_cons, true_and,
        show ("fibonacci" : String) = "add8" ↔ False by decide, false_and, dite_false,
        toElements]
      simp only [show ([_,_,_] : List (F p)).toArray.size = 3 by rfl, dite_true]
      simp only [show (0 : InteractionDelta (F p)) = [] by rfl,
        List.filterMap_nil, List.append_nil, List.mem_append, List.mem_singleton]
      right
      simp [h_push_eq, env]
    · -- entry.2[0] = n_i + 1
      simp [h_push_eq, env]
    · -- entry.2[1] = y_i
      simp [h_push_eq, env]

/-- Push-predecessor characterization for FibonacciChannel interactions. -/
lemma fib_push_pred
    (witness : EnsembleWitness fibonacciEnsemble)
    (n x y : F p)
    (fibInteractions : List (F p × Vector (F p) 3))
    (h_fibInteractions : fibInteractions = fibonacciEnsemble.interactions (n, x, y) witness FibonacciChannel.toRaw)
    (h_verifier_interactions :
      fibonacciEnsemble.verifierInteractions FibonacciChannel.toRaw (n, x, y) =
        [(1, (#v[(0 : F p), 0, 1] : Vector (F p) 3)), (-1, (#v[n, x, y] : Vector (F p) 3))]) :
    ∀ entry ∈ fibInteractions, entry.1 = 1 →
      entry.2 = (#v[(0 : F p), 0, 1] : Vector (F p) 3) ∨
      ∃ (n_i x_i y_i : F p),
        ((-1 : F p), (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ fibInteractions ∧
        entry.2[0] = n_i + 1 := by
  intro entry h_mem h_push
  -- split by table vs verifier interactions
  have h_mem' : entry ∈
      witness.tables.flatMap (fun table => table.interactions FibonacciChannel.toRaw) ++
        fibonacciEnsemble.verifierInteractions FibonacciChannel.toRaw (n, x, y) := by
    simpa [h_fibInteractions, Ensemble.interactions] using h_mem
  rcases List.mem_append.mp h_mem' with h_table | h_verifier
  · -- From tables: must be fib8
    right
    rw [List.mem_flatMap] at h_table
    obtain ⟨table, h_table_mem, h_entry_in_table⟩ := h_table
    -- Determine which table this is - only fib8 emits to FibonacciChannel
    have h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩ := by
      rcases List.mem_iff_getElem.1 h_table_mem with ⟨i, hi, htable⟩
      have h_len : witness.tables.length = 3 := by
        simpa [fibonacciEnsemble] using witness.same_length.symm
      have h_same : fibonacciEnsemble.tables[i] = table.abstract := by
        simpa [htable] using witness.same_circuits i (by simpa [fibonacciEnsemble, h_len] using hi)
      have hi' : i < 3 := by
        simpa [h_len] using hi
      match i with
      | 0 =>
        have h_empty := pushBytes_fib_interactions_empty table (by simp [fibonacciEnsemble] at h_same ⊢; exact h_same.symm)
        simp only [h_empty, List.not_mem_nil] at h_entry_in_table
      | 1 =>
        have h_empty := add8_fib_interactions_empty table (by simp [fibonacciEnsemble] at h_same ⊢; exact h_same.symm)
        simp only [h_empty, List.not_mem_nil] at h_entry_in_table
      | 2 =>
        simp [fibonacciEnsemble] at h_same ⊢
        exact h_same.symm
    obtain ⟨n_i, x_i, y_i, h_pull_in_table, _, h_n_eq, _⟩ :=
      fib8_fib_push_has_matching_pull table h_is_fib8 entry h_entry_in_table h_push
    refine ⟨n_i, x_i, y_i, ?_, h_n_eq⟩
    -- lift pull into fibInteractions
    simp only [h_fibInteractions, Ensemble.interactions]
    apply List.mem_append_left
    rw [List.mem_flatMap]
    exact ⟨table, h_table_mem, h_pull_in_table⟩
  · -- From verifier: only base push has mult=1
    left
    -- verifier interactions are exactly [push (0,0,1), pull (n,x,y)]
    have h_verifier' : entry = (1, (#v[(0 : F p), 0, 1] : Vector (F p) 3)) ∨
        entry = (-1, (#v[n, x, y] : Vector (F p) 3)) := by
      simpa [h_verifier_interactions] using h_verifier
    rcases h_verifier' with h_ver | h_ver
    · simp [h_ver]
    · exfalso
      have hneq : (-1 : F p) ≠ (1 : F p) := by
        have : Fact (2 < p) := ⟨by
          have : p > 512 := Fact.out
          linarith⟩
        simpa using (ZMod.neg_one_ne_one (n := p))
      have h_eq : (-1 : F p) = (1 : F p) := by simpa [h_ver] using h_push
      exact hneq h_eq

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
  have h_verifier_interactions :
    fibonacciEnsemble.verifierInteractions FibonacciChannel.toRaw (n, x, y) =
      [(1, (#v[(0 : F p), 0, 1] : Vector (F p) 3)), (-1, (#v[n, x, y] : Vector (F p) 3))] := by
    simp only [circuit_norm, fibonacciEnsemble, Ensemble.verifierInteractions, fibonacciVerifier, emptyEnvironment]
    rw [const_triple]
    simp [reduceDIte, circuit_norm, explicit_provable_type]

  have h_verifier_pull : (-1, (#v[n, x, y] : Vector (F p) 3)) ∈ fibInteractions := by
    simp [fibInteractions, Ensemble.interactions, h_verifier_interactions]

  have h_verifier_push : (1, (#v[(0 : F p), 0, 1] : Vector (F p) 3)) ∈ fibInteractions := by
    simp [fibInteractions, Ensemble.interactions, h_verifier_interactions]

  -- ── Step 2: Extract length bound and per-message balance for fibonacci channel ──
  have h_bal : Ensemble.BalancedChannels fibonacciEnsemble (n, x, y) witness := h_balanced
  unfold Ensemble.BalancedChannels at h_bal
  simp only [fibonacciEnsemble, List.Forall] at h_bal
  -- h_bal now contains BalancedChannel for all 3 channels
  -- h_bal.1 : BalancedChannel for BytesChannel
  -- h_bal.2.1 : BalancedChannel for Add8Channel
  -- h_bal.2.2 : BalancedChannel for FibonacciChannel

  have h_fib_bal := h_bal.2.2
  simp only [Ensemble.BalancedChannel] at h_fib_bal

  have h_fib_bound : fibInteractions.length < p := by
    have : ringChar (F p) = p := ZMod.ringChar_zmod_n p
    calc fibInteractions.length < ringChar (F p) := h_fib_bal.1
      _ = p := this

  have h_fib_balanced : ∀ msg : Vector (F p) 3,
      ((fibInteractions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0 := by
    intro msg
    exact (h_fib_bal.2 msg).2

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
      simp [h_verifier_interactions, List.mem_cons, List.not_mem_nil, or_false] at h_verifier
      rcases h_verifier with rfl|rfl <;> simp

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
    simp only [Ensemble.BalancedChannel] at h_bytes_bal
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
      (h_bytes_bal.2 #v[z]).2

    -- So -(length) = 0 in F_p, meaning p | length
    rw [h_sum_neg, neg_eq_zero] at h_sum_zero

    -- But 0 < length < p, contradiction
    have h_len_bound : (bytesInteractions.filter (·.2 = #v[z])).length < p := by
      have h := (h_bytes_bal.2 #v[z]).1
      calc _ < ringChar (F p) := h
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
      (Add8Channel (p := p)).toRaw.Guarantees entry.1 entry.2 (fun _ _ => #[]) := by
    intro entry h_entry_mem

    -- Extract balance for Add8Channel (second channel)
    have h_add8_bal := h_bal.2.1
    simp only [Ensemble.BalancedChannel] at h_add8_bal
    set add8Interactions := fibonacciEnsemble.interactions (n, x, y) witness (Add8Channel.toRaw)

    -- Key fact: any Add8Channel entry with mult ≠ -1 satisfies the Requirements.
    -- This follows from add8.soundness applied to each add8 row.
    -- Note: For Add8Channel, Requirements for pushes = Guarantees for pulls (same property)
    have h_push_req : ∀ entry ∈ add8Interactions, entry.1 ≠ -1 →
        (Add8Channel (p := p)).toRaw.Requirements entry.1 entry.2 (fun _ _ => #[]) := by
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
      simp only [Channel.toRaw, Add8Channel, h_is_pull, true_implies]

      -- Need: x < 256 → y < 256 → z = (x+y) % 256 where entry.2 = #v[x, y, z]
      intro hy

      -- By balance, sum of mults for this message is 0
      have h_sum_zero := (h_add8_bal.2 entry.2).2

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
          have h := (h_add8_bal.2 entry.2).1
          calc _ < ringChar (F p) := h
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
      simp only [Channel.toRaw, Add8Channel, ne_eq, true_implies, h_entry'_not_neg, not_false_eq_true] at h_req

      -- entry'.2 = entry.2, so the property transfers
      rw [h_entry'_eq] at h_req
      exact h_req hy

    case neg =>
      -- entry is not a pull (mult ≠ -1): Guarantees is True
      simp only [Channel.toRaw, Add8Channel, ne_eq, false_implies, h_is_pull]

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
      -- The proof follows the same pattern as h_push_req but for FibonacciChannel:
      -- Case split on table index, use pushBytes_fib_interactions_empty and
      -- add8_fib_interactions_empty to eliminate cases 0 and 1.
      have h_is_fib8 : table.abstract = ⟨fib8 (p := p)⟩ := by
        -- Only fib8 emits to FibonacciChannel; pushBytes and add8 have empty interactions
        rcases List.mem_iff_getElem.1 h_table_mem with ⟨i, hi, htable⟩
        have h_len : witness.tables.length = 3 := by
          simpa [fibonacciEnsemble] using witness.same_length.symm
        have hi' : i < 3 := by simpa [h_len] using hi
        have h_same : fibonacciEnsemble.tables[i] = table.abstract := by
          simpa [htable] using witness.same_circuits i (by simpa [fibonacciEnsemble, h_len] using hi)
        match i with
        | 0 =>
          -- pushBytes has empty FibonacciChannel interactions
          have h_empty := pushBytes_fib_interactions_empty table (by simp [fibonacciEnsemble] at h_same ⊢; exact h_same.symm)
          simp only [h_empty, List.not_mem_nil] at h_entry_in_table
        | 1 =>
          -- add8 has empty FibonacciChannel interactions
          have h_empty := add8_fib_interactions_empty table (by simp [fibonacciEnsemble] at h_same ⊢; exact h_same.symm)
          simp only [h_empty, List.not_mem_nil] at h_entry_in_table
        | 2 =>
          -- fib8 is the only one that emits to FibonacciChannel
          simp [fibonacciEnsemble] at h_same ⊢
          exact h_same.symm
      -- Use fib8_fib_push_has_matching_pull to get the matching pull
      obtain ⟨n_i, x_i, y_i, h_fib_pull_in_table, h_add8_pull_in_table, h_n_eq, h_y_eq⟩ :=
        fib8_fib_push_has_matching_pull table h_is_fib8 entry h_entry_in_table h_push
      use n_i, x_i, y_i
      refine ⟨?_, h_n_eq, ?_, ?_⟩
      · -- (-1, #v[n_i, x_i, y_i]) ∈ fibInteractions
        simp only [fibInteractions, Ensemble.interactions]
        apply List.mem_append_left
        rw [List.mem_flatMap]
        exact ⟨table, h_table_mem, h_fib_pull_in_table⟩
      · -- n_i.val + 1 < p
        -- The entry is in fibInteractions (from h_mem via h_table)
        have h_entry_in_fib : entry ∈ fibInteractions := by
          simp only [fibInteractions, Ensemble.interactions]
          apply List.mem_append_left
          rw [List.mem_flatMap]
          exact ⟨table, h_table_mem, h_entry_in_table⟩
        have h_push_pred := fib_push_pred witness n x y fibInteractions rfl h_verifier_interactions
        -- Use predecessor push at counter n_i
        have h_push_at_n : (1, (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ fibInteractions := by
          have h_pull_in_fib : (-1, (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ fibInteractions := by
            simp only [fibInteractions, Ensemble.interactions]
            apply List.mem_append_left
            rw [List.mem_flatMap]
            exact ⟨table, h_table_mem, h_fib_pull_in_table⟩
          exact exists_push_of_pull fibInteractions (#v[n_i, x_i, y_i])
            (fun e h _ => h_fib_mults e h) (h_fib_balanced _) h_pull_in_fib h_fib_bound
        have h_bound_n : n_i.val + 1 < p :=
          fib_step_counter_bounded fibInteractions h_fib_bound h_fib_mults h_fib_balanced
            h_push_pred (1, (#v[n_i, x_i, y_i] : Vector (F p) 3)) h_push_at_n rfl n_i rfl
        exact h_bound_n
      · -- Validity transfer: IsValidFibState n_i x_i y_i → IsValidFibState entry.2[0] entry.2[1] entry.2[2]
        intro h_input_valid
        -- From IsValidFibState, we get the range bounds
        obtain ⟨k, h_fib, h_k⟩ := h_input_valid
        have ⟨h_x_range, h_y_range⟩ := fibonacci_bytes h_fib
        -- Get the Add8Channel guarantee for the pull (x_i, y_i, entry.2[2])
        have h_add8_pull_in_ensemble : ((-1 : F p), #v[x_i, y_i, entry.2[2]]) ∈
            fibonacciEnsemble.interactions (n, x, y) witness (Add8Channel.toRaw) := by
          simp only [Ensemble.interactions]
          apply List.mem_append_left
          rw [List.mem_flatMap]
          exact ⟨table, h_table_mem, h_add8_pull_in_table⟩
        have h_guarantee := h_add8_guarantees _ h_add8_pull_in_ensemble
        -- The guarantee for a pull (mult = -1) is: x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256
        simp only [Channel.toRaw, Add8Channel, ne_eq, true_implies] at h_guarantee
        -- Simplify fromElements for fieldTriple
        simp only [fromElements] at h_guarantee
        have h_z_eq := h_guarantee h_x_range h_y_range
        -- Now construct the new valid state
        rw [h_n_eq, h_y_eq]
        refine ⟨k + 1, ?_, ?_⟩
        · simp only [fibonacci, fibonacciStep, ← h_fib, h_z_eq]
        · rw [ZMod.val_add, ← h_k, Nat.mod_add_mod, ZMod.val_one]
    · -- From verifier: push is (0, 0, 1)
      left
      simp only [h_verifier_interactions, List.mem_cons, List.not_mem_nil, or_false] at h_verifier
      rcases h_verifier with rfl | rfl
      · rfl  -- push case: entry = (1, #v[0,0,1])
      · -- pull case: entry.1 = -1, contradicts h_push (entry.1 = 1)
        simp [circuit_norm] at h_push

  -- ── Step 6: Apply all_fib_pushes_valid ──
  have h_all_valid := all_fib_pushes_valid fibInteractions
    h_fib_bound h_fib_balanced h_fib_mults h_fib8_soundness

  -- ── Step 7: The verifier's pull has a matching valid push ──
  have h_matching := exists_push_of_pull fibInteractions (#v[n, x, y])
    (fun e h _ => h_fib_mults e h) (h_fib_balanced _) h_verifier_pull h_fib_bound

  have h_valid := h_all_valid (1, #v[n, x, y]) h_matching rfl
  simp only [Vector.getElem_mk] at h_valid
  -- h_valid should now be IsValidFibState n x y, but we might need to match the types
  exact h_valid
