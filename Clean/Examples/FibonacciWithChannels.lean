/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table

Prove e2e soundness and completeness of the table ensemble.
-/
import Clean.Air.Vm
import Clean.Gadgets.Addition8.Theorems
open ByteUtils (mod256)
open FieldUtils (mod floorDiv)
open Gadgets.Addition8 (Theorems.soundness Theorems.completeness_bool Theorems.completeness_add)

open Air.Flat

instance (p : ℕ) [pGt : Fact (p > 512)] : Fact (ringChar (F p) ≠ 2) := .mk <| by
  simp [F, ZMod.ringChar_zmod_n]
  linarith [pGt.out]

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

abbrev BytesChannel : Channel (F p) field := .fromStatic _ _ BytesTable

-- bytes "circuit" that just pushes all bytes
-- probably shouldn't be a "circuit" at all
def pushBytes : GeneralFormalCircuit (F p) (fields 256) unit where
  main multiplicities := do
    let _  ← .mapFinRange 256 fun ⟨ i, _ ⟩ =>
      BytesChannel.emit multiplicities[i] (const i)

  elaborated := by elaborate_circuit_with {
    channelsWithRequirements := [ BytesChannel.toRaw ] }
  Spec _ _ _ := True
  soundness := by circuit_proof_start [BytesTable]
  completeness := by circuit_proof_start

instance Add8Channel : Channel (F p) fieldTriple where
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
  main | { x, y, z, m } => do
    -- range-check z using the bytes channel
    -- (x and y are guaranteed to be range-checked from earlier interactions)
    BytesChannel.pull z
    -- witness the output carry
    let carry ← witness fun env => floorDiv (env (x + y)) 256
    assertBool carry
    -- assert correctness
    x + y === z + carry * 256
    -- emit to the add8 channel with multiplicity `m`
    Add8Channel.emit m (x, y, z)

  ProverAssumptions
  | { x, y, z, m }, _, _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [BytesTable, Add8Channel]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hm hm0 hx hy
    have add_soundness := Theorems.soundness input_x input_y input_z 0 carry hx hy hz (by left; trivial) hcarry
    simp_all
  completeness := by
    circuit_proof_start [BytesTable]
    set carry := env.get i₀
    rcases h_assumptions with ⟨ hx, hy, hz, heq ⟩
    have add_completeness_bool := Theorems.completeness_bool input_x input_y 0 hx hy (by simp)
    have add_completeness_add := Theorems.completeness_add input_x input_y 0 hx hy (by simp)
    simp only [add_zero] at add_completeness_bool add_completeness_add
    have h_input_z : input_z = mod256 (input_x + input_y) := by
      apply FieldUtils.ext
      rw [heq, mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
      linarith [hx, hy, ‹Fact (p > 512)›.elim]
    grind

example (input : Var Add8Inputs (F p)) :
    ExplicitCircuit (add8.main input) := by
  infer_explicit_circuit

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

instance FibonacciChannel : Channel (F p) fieldTriple where
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
  main | { enabled, n, x, y } => do
    assertZero (enabled * (enabled - 1))
    -- pull the current Fibonacci state
    FibonacciChannel.pullIf enabled (n, x, y)
    -- witness the next Fibonacci value
    let z ← witness fun eval => mod256 (eval (x + y))
    -- pull from the Add8 channel to check addition
    Add8Channel.pullIf enabled (x, y, z)
    -- push the next Fibonacci state
    FibonacciChannel.pushIf enabled (n + 1, y, z)

  -- expose interactions
  exposedChannels
  | input, i₀ =>
    let z := var ⟨ i₀ ⟩
    expose FibonacciChannel [
      pullIf input.enabled (input.n, input.x, input.y),
      pushIf input.enabled (input.n + 1, input.y, z) ]
  exposedChannels_eq := by simp [circuit_norm, Add8Channel, FibonacciChannel]

  ProverAssumptions
  | { enabled, n, x, y }, _, _ =>
    enabled = 0 ∨ (enabled = 1 ∧ ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val)
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm, FibonacciChannel, Add8Channel]
    rcases h_holds with ⟨ h_bool, h_fib, h_add ⟩
    have h_enabled_bool : input_enabled = 0 ∨ input_enabled = 1 := by
      rcases mul_eq_zero.mp h_bool with h_zero | h_one
      · exact .inl h_zero
      · right
        rw [← sub_eq_add_neg] at h_one
        exact sub_eq_zero.mp h_one
    intro h_not_neg h_nonzero
    rcases h_enabled_bool with h_zero | h_one
    · contradiction
    have ⟨ k, fiby, hk ⟩ := h_fib (by simp [h_one])
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    have hz := h_add (by simp [h_one]) hx hy
    use k + 1
    simp only [fibonacci, ← fiby]
    rw [hz, ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm, FibonacciChannel, Add8Channel]
    rcases h_assumptions with h_disabled | ⟨ h_enabled, h_fib ⟩
    · simp [h_disabled]
    constructor
    · simp [h_enabled]
    constructor
    · intro h_active
      exact h_fib
    · intro h_active hx hy
      rw [mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
      linarith [hx, hy, ‹Fact (p > 512)›.elim]

def fib8Step : VmStep fieldTriple (F p) :=
  let input := varFromOffset (F:=F p) Fib8Input 0
  { enabled := input.enabled
    pull := (input.n, input.x, input.y)
    push := (input.n + 1, input.y, var ⟨ size Fib8Input ⟩) }

@[circuit_norm]
lemma fib8Step_enabled_boolean (env : Environment (F p)) :
    Operations.ConstraintsHold env (⟨ fib8 ⟩ : Component (F p)).operations →
      env fib8Step.enabled = 0 ∨ env fib8Step.enabled = 1 := by
  intro h_constraints
  let input := varFromOffset (F:=F p) Fib8Input 0
  rw [Component.constraintsHold_iff] at h_constraints
  simp only [Operations.ConstraintsHold, Component.rowOperations, Circuit.operations, fib8] at h_constraints
  have h_bool : env (input.enabled * (input.enabled - 1)) = 0 := h_constraints.1 _ (by
    simp [circuit_norm, input])
  simp [circuit_norm] at h_bool
  rcases h_bool with h_zero | h_one
  · exact Or.inl h_zero
  · right
    rw [← sub_eq_add_neg] at h_one
    simpa [fib8Step, input] using sub_eq_zero.mp h_one

@[circuit_norm]
lemma fib8Step_table_enabled_boolean :
    ∀ env,
      (⟨ fib8 ⟩ : Component (F p)).Assumptions env →
      Operations.ConstraintsHold env (⟨ fib8 ⟩ : Component (F p)).operations →
        env fib8Step.enabled = 0 ∨ env fib8Step.enabled = 1 := by
  intro env _ h_constraints
  exact fib8Step_enabled_boolean env h_constraints

example (input : Var Fib8Input (F p)) :
    ExplicitCircuit (fib8.main input) := by
  infer_explicit_circuit

-- completing Fibonacci channel with input and output
def fibonacciVerifier : GeneralFormalCircuit (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- push initial state, pull the final state
    FibonacciChannel.pull (n, x, y)
    FibonacciChannel.push (0, 0, 1)

  exposedChannels
  | (n, x, y), _ =>
    expose FibonacciChannel [ pulled (n, x, y), pushed (0, 0, 1) ]

  ProverAssumptions
  | (n, x, y), _, _ => ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val
  Spec
  | (n, x, y), _, _ => ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val
  soundness := by
    circuit_proof_start [FibonacciChannel]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩
  completeness := by
    circuit_proof_start [FibonacciChannel]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simpa [circuit_norm, reduceIte] using h_assumptions

example (input : Var fieldTriple (F p)) :
    ExplicitCircuit (fibonacciVerifier.main input) := by
  infer_explicit_circuit

def fibonacciVm : VmTables (F p) fieldTriple where
  channel := FibonacciChannel
  tables := [⟨ fib8 ⟩]
  verifier := fibonacciVerifier
  verifier_length_zero := by simp [circuit_norm, fibonacciVerifier]
  tables_channel := by
    intro table table_mem
    simp only [List.mem_singleton] at table_mem
    subst table
    refine ⟨ fib8Step, ?_, fib8Step_table_enabled_boolean ⟩
    simp [circuit_norm, fib8, fib8Step, Component.exposedChannels, Component.rowOffset]
  verifier_channel := by
    simp [circuit_norm, fibonacciVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, fibonacciVerifier, FibonacciChannel, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩

def fibonacciEnsemble := SoundEnsemble.empty (F p) fieldTriple
  |>.addTable ⟨ pushBytes ⟩
    (by simp [circuit_norm, pushBytes]) (by simp [circuit_norm, pushBytes])
  |>.addFinishedChannel BytesChannel.toRaw
  |>.addTable ⟨ add8 ⟩
    (by simp [circuit_norm, add8]) (by simp [circuit_norm, add8])
  |>.addFinishedChannel Add8Channel.toRaw
  |>.addVm fibonacciVm
    (by simp [circuit_norm, fibonacciVm, add8, pushBytes, Add8Channel, FibonacciChannel])
    (by simp [circuit_norm, fibonacciVm, fib8, fibonacciVerifier])
    (by simp [circuit_norm, fibonacciVm, fib8, fibonacciVerifier, Add8Channel, FibonacciChannel])
  |>.toFormal _ (fun _ _ => True)
    (by simp [circuit_norm, fibonacciVm, add8, pushBytes, fib8])

/--
Fibonacci soundness, concretely: if someone gives you a proof of the ensemble statement,
then you know that the public input is a Fibonacci number.

TODO: find a generic strategy to show that k < p, so the statement simplifies to
`(x.val, y.val) = fibonacci n.val`
The problem is that the row-transition circuit currently can't prove this: it receives any field elements n and
pushes n+1, so a priori it can overflow.

It would make sense to provide a guarantee that mentions the total interaction length "before" running the row circuit,
and prove a requirement about the total interaction length after:
pre: 2*n ≤ total_length_before
post: 2*(n + 1) ≤ total_length_after = total_length_before + 2 :check_mark:
But that massively complicates the guarantees/requirements system, since they now need access to global information.

And idea could be to define a "global state" per channel, and define how every interaction transforms that state.
Then let the guarantees/requirements access that state (the guarantees _before_ and the requiremtns _after_ the interaction).
-/
theorem fibonacci_soundness : ∀ (n x y : F p),
  fibonacciEnsemble.ensemble.Statement (n, x, y) →
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val := by
  intro n x y statement
  convert fibonacciEnsemble.soundness (n, x, y) ?assumptions statement
  · simp only [circuit_norm, fibonacciEnsemble, fibonacciVm, fibonacciVerifier]
    tauto
  · simp only [circuit_norm, fibonacciEnsemble, fibonacciVm, fibonacciVerifier]

/-
Fun fact! We can prove end-to-end soundness of a component that proves `False`
-/
def FalseChannel : Channel (F p) unit where
  name := "false"
  Guarantees _ _ := False

def falseCircuit : GeneralFormalCircuit (F p) unit unit where
  main _ := do
    FalseChannel.pull ()
    return
  Spec _ _ _ := False
  ProverAssumptions _ _ _ := False
  soundness := by circuit_proof_start [FalseChannel]
  completeness := by circuit_proof_start [FalseChannel]

def falseEnsemble := SoundEnsemble.empty (F p) unit
  |>.addFinishedChannel FalseChannel.toRaw
  |>.addTable ⟨ falseCircuit ⟩
    (by simp [circuit_norm, falseCircuit]) (by simp [circuit_norm, falseCircuit])

/--
Zero multiplicity disables both sides of an interaction. This circuit uses a channel whose
guarantee is `False`, so it would be impossible to prove if either disabled interaction still
created an obligation or assumption.
-/
def disabledFalseCircuit : GeneralFormalCircuit (F p) unit unit where
  main _ := do
    FalseChannel.pullIf 0 ()
    FalseChannel.pushIf 0 ()
    return
  elaborated := by elaborate_circuit_with {
    channelsWithGuarantees := [FalseChannel.toRaw]
    channelsWithRequirements := [FalseChannel.toRaw] }
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  soundness := by circuit_proof_start [FalseChannel]
  completeness := by circuit_proof_start [FalseChannel]

example : ExplicitCircuit ((disabledFalseCircuit (p:=p)).main ()) := by
  infer_explicit_circuit
