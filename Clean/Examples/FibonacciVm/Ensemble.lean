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
  rowOf value := value.val
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
    intro h0 hx hy
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

/-- The addition chip: one row per distinct message pulled from the addition channel, with the
number of pulls as its multiplicity `m`. -/
abbrev add8Component : Component (F p) where
  circuit := add8
  /- witness generation: whenever someone ... -/
  generation := .demand {
    trigger := .pull -- pulls ...
    channel := add8Channel --- from the addition channel ...
    --- this circuit is run with the channel message (x, y, z) and its current multiplicity as input.
    input | (x, y, z) => pure { x, y, z, m := .multiplicity }
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

/-- The Fibonacci state `(n, x, y)` reached after `k` steps, which counts them with `n`. -/
def FibonacciReached (k : ℕ) : fieldTriple (F p) → Prop
  | (n, x, y) => (x.val, y.val) = fibonacci k ∧ n = k

/-- The Fibonacci states, which `FibonacciReached` describes. -/
def fibonacciChannel : Channel (F p) fieldTriple where
  name := "fibonacci"
  Guarantees _ _ := True

structure Fib8Input F where
  enabled : F
  n : F
  x : F
  y : F
deriving ProvableStruct

def fib8 : GeneralFormalCircuit (F p) Fib8Input field where
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
    return z

  -- expose interactions
  exposedChannels
  | { enabled, n, x, y }, i₀ =>
    let z := var ⟨ i₀ ⟩
    expose fibonacciChannel [ pulledIf enabled (n, x, y), pushedIf enabled (n + 1, y, z) ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, n, x, y⟩ := input
    simp only [circuit_norm, fibonacciChannel, add8Channel]

  ProverAssumptions
  | { enabled, n, x, y }, _, _ => enabled = 0 ∨ (enabled = 1 ∧ ∃ k, FibonacciReached k (n, x, y))
  -- an enabled step takes the state after `k` steps to the state after `k + 1` steps
  Spec
  | { enabled, n, x, y }, z, _ =>
    enabled = 1 → ∀ k, FibonacciReached k (n, x, y) → FibonacciReached (k + 1) (n + 1, y, z)

  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, n, x, y⟩ := input_var
    simp only [circuit_norm, fibonacciChannel, add8Channel]
    grind

  soundness := by
    circuit_proof_start [fibonacciChannel, add8Channel, FibonacciReached]
    set z := env.get i₀
    obtain ⟨ h_bool, h_add ⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    refine ⟨ ?_, h_bool ⟩
    rintro rfl k ⟨ fiby, rfl ⟩
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    simp only [fibonacci, ← fiby]
    simp_all

  completeness := by
    circuit_proof_start [fibonacciChannel, add8Channel, FibonacciReached]
    rcases h_assumptions with rfl | ⟨ rfl, k, h_fib, rfl ⟩
    · simp
    have ⟨ hx, hy ⟩ := fibonacci_bytes h_fib
    simp_all
    rw [Nat.mod_eq_of_lt (by grind), ZMod.val_add_of_lt]
    linarith [hx, hy, ‹Fact (p > 512)›.elim]

/-- The Fibonacci VM: one row per state pushed to the Fibonacci channel. Padding rows are
disabled. -/
abbrev fib8Component : Component (F p) where
  circuit := fib8
  generation := .demand {
    trigger := .push
    channel := fibonacciChannel
    input | (n, x, y) => pure { enabled := 1, n, x, y }
  }

-- completing Fibonacci channel with input and output
def fibonacciVerifier : Verifier.Program (F p) fieldTriple where
  main | (n, x, y) => do
    -- push initial state, pull the final state
    Verifier.pull fibonacciChannel (n, x, y)
    Verifier.push fibonacciChannel (0, 0, 1)

def fibonacciVm : VmTables (F p) fieldTriple where
  channel := fibonacciChannel
  Reached k state _ := FibonacciReached k state
  guarantees_of_reached := by simp [fibonacciChannel]
  tables := [fib8Component]
  unique_names := by simp
  verifier := fibonacciVerifier
  final := id
  tables_channel := by simp [circuit_norm, explicit_provable_type, fib8, sub_eq_zero]
  verifier_channel := by
    simp [circuit_norm, fibonacciVerifier, FibonacciReached, fibonacci, ZMod.val_one,
      ProverData.getPublicInput_eq_eval]

def fibonacciEnsemble := SoundEnsemble.empty (F p) fieldTriple .logUp
  |>.addLookup bytes
  |>.addChannel add8Channel.toRaw (by simp [circuit_norm, add8Channel, bytes])
  |>.addTable add8Component
    (by simp [circuit_norm, add8])
    (by simp [circuit_norm, add8, add8Channel, bytes])
    (by simp [circuit_norm, add8, bytes])
  |>.markFinished add8Channel.toRaw
  |>.addVm fibonacciVm
    (by simp +instances [circuit_norm, fibonacciVm, bytes, add8Channel, fibonacciChannel])
    (by simp +instances [circuit_norm, fibonacciVm, fib8, fibonacciVerifier])
    (by simp +instances [circuit_norm, fibonacciVm, fib8, fibonacciVerifier,
      add8Channel, fibonacciChannel])
    (by simp [circuit_norm, fibonacciVm, fib8, add8, bytes])
  |>.toFormal (fun _ _ => True) (fun (n, x, y) => (x.val, y.val) = fibonacci n.val)
    (by simp [circuit_norm, fibonacciVm, bytes])
    (by
      -- the number of steps `k` is less than `p`, so the step counter is `k`
      rintro witness - - ⟨ k, count, count_lt, k_lt, reached ⟩
      generalize witness.publicInput = publicInput at reached ⊢
      obtain ⟨ n, x, y ⟩ := publicInput
      obtain ⟨ fib, rfl ⟩ := reached
      simp only [Balance.logUp, ZMod.ringChar_zmod_n] at count_lt
      simp only [ZMod.val_cast_of_lt (show k < p by omega), fib])

/-- Generate a complete ensemble witness from the claimed public final state. -/
def fibonacciGenerate (publicInput : fieldTriple (F p)) (fuel : ℕ) :
    Except WitnessGeneration.GenerationError
      (EnsembleWitness (fibonacciEnsemble (p := p)).ensemble) :=
  WitnessGeneration.generate fibonacciEnsemble.ensemble fuel publicInput ()

/--
Fibonacci soundness, concretely: if someone gives you a proof of the ensemble statement,
then you know that the public input is a Fibonacci state, whose step counter `n` is the number of
steps.
-/
theorem fibonacci_soundness : ∀ (n x y : F p) heights,
    fibonacciEnsemble.ensemble.Statement .logUp (n, x, y) heights →
      (x.val, y.val) = fibonacci n.val :=
  fun n x y heights => fibonacciEnsemble.soundness (n, x, y) heights trivial

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
    trigger := .push
    input _ := pure ()
  }

def falseEnsemble := SoundEnsemble.empty (F p) unit .logUp
  |>.addFinishedChannel falseChannel.toRaw
  |>.addTable falseComponent
    (by simp [circuit_norm, falseCircuit]) (by simp [circuit_norm, falseCircuit])
