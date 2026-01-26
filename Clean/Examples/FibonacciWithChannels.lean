/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table
-/
import Clean.Circuit
import Clean.Gadgets.Addition8.Theorems
open ByteUtils (mod256 floorDiv256)
open Gadgets.Addition8 (Theorems.soundness Theorems.completeness_bool Theorems.completeness_add)

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

instance BytesChannel : Channel (F p) field where
  name := "bytes"
  Guarantees mult x _ _ :=
    if mult = -1 then x.val < 256 else True
  Requirements mult x _ _ :=
    if mult = 1 then x.val < 256 else True

instance Add8Channel : Channel (F p) fieldTriple where
  name := "add8"
  Guarantees
  | mult, (x, y, z), _, _ =>
    if mult = -1 then x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256
    else True
  Requirements
  | mult, (x, y, z), _, _ =>
    if mult = 1 then x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256
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
    circuit_proof_start [BytesChannel, Add8Channel, reduceIte]
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
    circuit_proof_start [reduceIte, seval, and_false]
    rcases input with ⟨ n, x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [Prod.mk.injEq] at h_input
    -- why are these not simped?? maybe because fieldPair is not well-recognized
    rw [RawChannel.filter_eq] at h_holds ⊢
    rw [Channel.interactionFromRaw_eq, Channel.interactionFromRaw_eq, Channel.interactionFromRaw_eq]
    simp_all only [circuit_norm]
    set fibInteractions := FibonacciChannel.filter interactions
    set add8Interactions := Add8Channel.filter interactions
    set z := env.get i₀
    simp only [circuit_norm, FibonacciChannel, Add8Channel, reduceIte] at h_holds ⊢
    simp only [List.mem_cons, true_or, and_true]
    obtain ⟨ ⟨ ⟨k, fiby, hk⟩, hfib_push ⟩, hadd ⟩ := h_holds
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    use k + 1
    simp only [fibonacci, fibonacciStep, ← fiby]
    rw [ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start

-- define what global soundness means for the ensemble of circuits (tables) and channels
