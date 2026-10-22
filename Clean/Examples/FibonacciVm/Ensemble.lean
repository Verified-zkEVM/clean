/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table

Prove e2e soundness and completeness of the table ensemble.
-/
module

public import Clean.Air.Vm
public import Clean.Air.Lookup
public import Clean.Air.WitnessGeneration
public import Clean.Gadgets.Addition8.Theorems

@[expose] public section
open ByteUtils (mod256)
open FieldUtils (mod floorDiv)
open Gadgets.Addition8 (Theorems.soundness Theorems.completeness_bool Theorems.completeness_add)

open Air.Flat

variable {p : ℕ} [Fact p.Prime] [pGt: Fact (p > 512)]

/-- The bytes `0, ..., 255`, for range checks. -/
def bytes : Lookup (F p) field where
  name := "bytes"
  height := 256
  row i := pure i
  Contains value := value.val < 256
  contains_iff value := by
    simp only [circuit_norm, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    constructor
    · intro h
      refine ⟨value.val.toUInt64, ?_, ?_⟩ <;> simp [h]
    · rintro ⟨i, hi, rfl⟩
      rwa [ZMod.val_cast_of_lt (by linarith [pGt.out])]

def add8Channel : Channel (F p) fieldTriple where
  name := "add8"
  Guarantees
  | (x, y, z), _ =>
    x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256

structure Add8Inputs F where
  x : F
  y : F
  z : F
  m : F -- multiplicity
deriving ProvableStruct

/-- Proves x + y = z (mod 256) -/
def add8 : GeneralFormalCircuit (F p) Add8Inputs unit where
  name := "add8"
  main input := do
    -- range-check z using the bytes channel
    -- (x and y are guaranteed to be range-checked from earlier interactions)
    bytes.channel.pull input.z
    -- witness the output carry
    let carry ← witness ((input.x + input.y).val / 256).toField
    assertBool carry
    -- assert correctness
    input.x + input.y === input.z + carry * 256
    -- emit to the add8 channel with multiplicity `m`
    add8Channel.emit input.m (input.x, input.y, input.z)

  ProverAssumptions
  | { x, y, z, m }, _, _ =>
    x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True
  channelsWithRequirements := [ add8Channel.toRaw ]

  soundness := by
    circuit_proof_start [bytes, add8Channel]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hm h0 hx hy
    have add_soundness :=
      Theorems.soundness input_x input_y input_z 0 carry hx hy hz (by left; trivial) hcarry
    simp_all
  completeness := by
    circuit_proof_start [bytes]
    set carry := env.get i₀
    rcases h_assumptions with ⟨ hx, hy, hz, heq ⟩
    have add_completeness_bool := Theorems.completeness_bool input_x input_y 0 hx hy (by simp)
    have add_completeness_add := Theorems.completeness_add input_x input_y 0 hx hy (by simp)
    simp only [add_zero] at add_completeness_bool add_completeness_add
    have h_input_z : input_z = mod256 (input_x + input_y) := by
      apply FieldUtils.ext
      rw [heq, mod256, FieldUtils.mod, ZMod.val_natCast_of_lt, ZMod.val_add_of_lt, PNat.val_ofNat]
      · linarith [hx, hy, ‹Fact (p > 512)›.elim]
      · grw [Nat.mod_lt _ (by norm_num)]
        linarith [‹Fact (p > 512)›.elim]
    -- the witness is computed in `u64` arithmetic, which doesn't wrap here since
    -- `input_x + input_y` is a sum of two bytes
    have h_no_wrap : ZMod.val (input_x + input_y) < 2 ^ 64 := by
      rw [ZMod.val_add_of_lt (by linarith [‹Fact (p > 512)›.elim])]
      omega
    rw [Nat.mod_eq_of_lt h_no_wrap] at h_env
    change carry = floorDiv (input_x + input_y) 256 at h_env
    grind

example (input : Var Add8Inputs (F p)) :
    ExplicitCircuit (add8.main input) := by
  infer_explicit_circuit

/-- The addition chip: one row per distinct message pulled from the addition channel, with the
number of pulls as its multiplicity `m`. -/
abbrev add8Component : Component (F p) where
  circuit := add8
  generation := .demand {
    channel := add8Channel
    surplus := .pull
    aggregation := .byMessage fun { m, .. } => m
    input := [.message 0, .message 1, .message 2]
    padding := #[0, 0, 0, 0]
  }

def fibonacci : ℕ → (ℕ × ℕ)
  | 0 => (0, 1)
  | n + 1 =>
    let (x, y) := fibonacci n
    (y, (x + y) % 256)

/-- helper lemma: fibonacci states are bytes -/
lemma fibonacci_bytes {n x y : ℕ} : (x, y) = fibonacci n → x < 256 ∧ y < 256 := by
  induction n generalizing x y with
  | zero => simp_all [fibonacci]
  | succ n ih =>
    specialize ih rfl
    simp_all [fibonacci, Nat.mod_lt]

def fibonacciChannel : Channel (F p) fieldTriple where
  name := "fibonacci"
  -- when pulling, we want the guarantee that the input is a valid Fibonacci step
  Guarantees
  | (n, x, y), _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val

structure Fib8Input F where
  enabled : F
  n : F
  x : F
  y : F
deriving ProvableStruct

def fib8 : GeneralFormalCircuit (F p) Fib8Input unit where
  name := "fibonacci"
  main input := do
    -- boolean constraint for `enabled`
    -- has to be inline, channels with requirements proof doesn't handle subcircuits
    assertZero (input.enabled * (input.enabled - 1))
    -- pull the current Fibonacci state
    fibonacciChannel.pullIf input.enabled (input.n, input.x, input.y)
    -- witness the next Fibonacci value
    let z ← witness ((input.x + input.y).val % 256).toField
    -- pull from the Add8 channel to check addition
    add8Channel.pullIf input.enabled (input.x, input.y, z)
    -- push the next Fibonacci state
    fibonacciChannel.pushIf input.enabled (input.n + 1, input.y, z)

  -- expose interactions
  exposedChannels
  | { enabled, n, x, y }, i₀ =>
    let z := var ⟨ i₀ ⟩
    expose fibonacciChannel [ pulledIf enabled (n, x, y), pushedIf enabled (n + 1, y, z) ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, n, x, y⟩ := input
    simp only [circuit_norm, fibonacciChannel, add8Channel]

  ProverAssumptions
  | { enabled, n, x, y }, _, _ =>
    enabled = 0 ∨ (enabled = 1 ∧ ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val)
  Spec _ _ _ := True

  channelsWithRequirements := [ fibonacciChannel.toRaw ]
  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, n, x, y⟩ := input_var
    simp only [circuit_norm, fibonacciChannel, add8Channel]
    grind

  soundness := by
    circuit_proof_start [fibonacciChannel, add8Channel]
    set z := env.get i₀
    obtain ⟨ h_bool, h_fib, h_add ⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    rcases h_bool with rfl | rfl
    · grind
    simp_all only [circuit_norm]
    obtain ⟨k, fiby, hk⟩ := h_fib
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    use k + 1
    simp only [fibonacci, ← fiby]
    rw [ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start [fibonacciChannel, add8Channel]
    rcases h_assumptions with rfl | ⟨ rfl, h_fib ⟩
    · simp
    simp_all
    intro hx hy
    rw [Nat.mod_eq_of_lt (by grind), ZMod.val_add_of_lt]
    linarith [hx, hy, ‹Fact (p > 512)›.elim]

/-- The Fibonacci VM: one row per state pushed to the Fibonacci channel. Padding rows are
disabled. -/
abbrev fib8Component : Component (F p) where
  circuit := fib8
  generation := .demand {
    channel := fibonacciChannel
    surplus := .push
    aggregation := .perOccurrence
    input := [.const 1, .message 0, .message 1, .message 2]
    padding := #[0, 0, 0, 0]
  }

-- completing Fibonacci channel with input and output
def fibonacciVerifier : Verifier.Program (F p) fieldTriple where
  main | (n, x, y) => do
    -- push initial state, pull the final state
    Verifier.pull fibonacciChannel (n, x, y)
    Verifier.push fibonacciChannel (0, 0, 1)
  Spec
  | (n, x, y), _ => ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val
  soundness := by simp_all [circuit_norm, fibonacciChannel]

def fibonacciVm : VmTables (F p) fieldTriple where
  channel := fibonacciChannel
  tables := [fib8Component]
  unique_names := by simp
  verifier := fibonacciVerifier
  tables_channel := by simp [circuit_norm, fib8, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, fibonacciVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, fibonacciVerifier, fibonacciChannel, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩

def fibonacciEnsemble := SoundEnsemble.empty (F p) fieldTriple
  |>.addLookup bytes
  |>.addTable add8Component
    (by simp [circuit_norm, add8])
    (by simp [circuit_norm, add8])
    (by simp [circuit_norm, add8, bytes])
  |>.addFinishedChannel add8Channel.toRaw
  |>.addVm fibonacciVm
    (by simp +instances [circuit_norm, fibonacciVm, add8, bytes,
      add8Channel, fibonacciChannel])
    (by simp +instances [circuit_norm, fibonacciVm, fib8, fibonacciVerifier])
    (by simp [circuit_norm, fibonacciVm, fib8, fibonacciVerifier,
      add8Channel, fibonacciChannel])
    (by simp [circuit_norm, fibonacciVm, fib8, add8, bytes])
  |>.toFormal (fun _ => True)
    (fun (n, x, y) => ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val)
    (by simp [circuit_norm, fibonacciVm, bytes])
    (by simp [circuit_norm, fibonacciVm, fibonacciVerifier])

namespace FibonacciWitness

/-- Generate a complete ensemble witness from the claimed public final state. -/
def generate (publicInput : fieldTriple (F p)) (fuel : ℕ) :
    Except WitnessGeneration.GenerationError
      (EnsembleWitness (fibonacciEnsemble (p := p)).ensemble) :=
  WitnessGeneration.generate fibonacciEnsemble.ensemble fuel publicInput ()

end FibonacciWitness

/--
Fibonacci soundness, concretely: if someone gives you a proof of the ensemble statement,
then you know that the public input is a Fibonacci number.

TODO: find a generic strategy to show that k < p, so the statement simplifies to
`(x.val, y.val) = fibonacci n.val`
The problem is that the row-transition circuit currently can't prove this: it receives any field
elements n and
pushes n+1, so a priori it can overflow.

It would make sense to provide a guarantee that mentions the total interaction length "before"
running the row circuit,
and prove a requirement about the total interaction length after:
pre: 2*n ≤ total_length_before
post: 2*(n + 1) ≤ total_length_after = total_length_before + 2 :check_mark:
But that massively complicates the guarantees/requirements system, since they now need access to
global information.

And idea could be to define a "global state" per channel, and define how every interaction
transforms that state.
Then let the guarantees/requirements access that state (the guarantees _before_ and the requiremtns
_after_ the interaction).
-/
theorem fibonacci_soundness : ∀ (n x y : F p),
  fibonacciEnsemble.ensemble.Statement (n, x, y) →
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val := by
  intro n x y statement
  exact fibonacciEnsemble.soundness (n, x, y) trivial statement

/-
Fun fact! We can prove end-to-end soundness of a component that proves `False`.
This only works because we don't add a component that pushes to the channel;
requiring a completeness proof would make it impossible.
-/
def falseChannel : Channel (F p) unit where
  name := "false"
  Guarantees _ _ := False

def falseCircuit : GeneralFormalCircuit (F p) unit unit where
  name := "false"
  main _ := do
    falseChannel.pull ()
    return
  Spec _ _ _ := False
  ProverAssumptions _ _ _ := False
  soundness := by circuit_proof_start [falseChannel]
  completeness := by circuit_proof_start [falseChannel]

/-- Rows that answer pushes on the false channel, of which there are none. -/
abbrev falseComponent : Component (F p) where
  circuit := falseCircuit
  generation := .demand {
    channel := falseChannel
    surplus := .push
    aggregation := .perOccurrence
    input := []
    padding := #[]
  }

def falseEnsemble := SoundEnsemble.empty (F p) unit
  |>.addFinishedChannel falseChannel.toRaw
  |>.addTable falseComponent
    (by simp [circuit_norm, falseCircuit]) (by simp [circuit_norm, falseCircuit])
