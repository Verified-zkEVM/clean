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

-- bytes "circuit" that just pushes all bytes
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
def fibonacciInputOutput : FormalCircuitWithInteractions (F p) fieldTriple unit where
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

structure Table' (F : Type) [Field F] [DecidableEq F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]

  circuit : FormalCircuitWithInteractions F Input Output
  witness : List (Vector F circuit.size)
  data : ProverData F := fun _ _ => #[]

def ConstraintsHold (env : Environment F) (ops : Operations F) : Prop :=
  ops.forAll 0 {
    assert _ e := env e = 0
    lookup _ l := l.Contains env
    subcircuit _ _ s := ConstraintsHoldFlat env s.ops.toFlat
  }

namespace Table'
instance (t: Table' F) : ProvableType t.Input := t.provableInput
instance (t: Table' F) : ProvableType t.Output := t.provableOutput

def length (table : Table' F) : ℕ := table.witness.length
def width (table : Table' F) : ℕ := table.circuit.size
def operations (table : Table' F) : Operations F :=
  table.circuit.instantiate.operations 0

def environment (table : Table' F) (row : Vector F table.width) : Environment F where
  get j := row[j]?.getD 0
  data := table.data
  interactions := [] -- I think we can remove this field??

def Constraints (table : Table' F) : Prop :=
  table.witness.Forall fun row =>
    ConstraintsHold (table.environment row) table.operations

def interactions (table : Table' F) (channel : RawChannel F) : List (F × Vector F channel.arity) :=
  table.witness.flatMap fun row =>
    let env := table.environment row
    table.operations.localAdds env
  |> channel.filter
end Table'

structure Ensemble (F : Type) [Field F] [DecidableEq F] where
  tables : List (Table' F)
  channels : List (RawChannel F)

  PublicIO : TypeMap
  [provablePublicIO : ProvableType PublicIO]
  verifier : FormalCircuitWithInteractions F PublicIO unit
  verifier_length_zero : verifier.size = 0

  Spec : PublicIO F → Prop

namespace Ensemble
instance (ens : Ensemble F) : ProvableType ens.PublicIO := ens.provablePublicIO

def emptyEnvironment (F : Type) [Field F] [DecidableEq F] : Environment F := { get _ := 0, data _ _ := #[], interactions := [] }

def verifierTable (ens : Ensemble F) (data : ProverData F := fun _ _ => #[]) : Table' F where
  circuit := ens.verifier
  witness := [⟨ #[], by simp [ens.verifier_length_zero] ⟩]
  data

def Constraints (ens : Ensemble F) : Prop :=
  ens.tables.Forall fun table => table.Constraints

def interactions (ens : Ensemble F) (channel : RawChannel F) : List (F × Vector F channel.arity) :=
  (ens.tables.flatMap fun table => table.interactions channel)
  ++ ens.verifierTable.interactions channel

def BalancedChannels (ens : Ensemble F) : Prop :=
  ens.channels.Forall fun channel =>
    ((ens.interactions channel).map Prod.fst).sum = 0

def VerifierAccepts (ens : Ensemble F) (publicInput : ens.PublicIO F) : Prop :=
  let circuit := ens.verifier (const publicInput)
  ConstraintsHold (emptyEnvironment F) (circuit.operations 0)

/--
Soundness for an ensemble states that if
- constraints hold on all tables and
- and interactions sum to zero
- and constraints hold on the verifier circuit, when given the public inputs (as constants)
then the spec holds
-/
def Soundness (ens : Ensemble F) (publicInput : ens.PublicIO F) : Prop :=
  ens.Constraints → ens.BalancedChannels → ens.VerifierAccepts publicInput →
  ens.Spec publicInput

end Ensemble
end
