/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table

Prove e2e soundness and completeness of the table ensemble.
-/
import Clean.Air.Vm
import Clean.Air.WitnessGeneration
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

structure BytesInput F where
  value : F
  multiplicity : F
deriving ProvableStruct

/-- One byte-channel row. Its byte value is supplied by an indexed fixed column. -/
def pushBytes : GeneralFormalCircuit (F p) BytesInput unit where
  name := "bytes"
  main | { value, multiplicity } => do
    BytesChannel.emit multiplicity value

  channelsWithRequirements := [ BytesChannel.toRaw ]
  Assumptions
  | { value, .. }, _ => ∃ i : Fin 256, value = ByteUtils.fromByte i
  ProverAssumptions
  | { value, .. }, _, _ => ∃ i : Fin 256, value = ByteUtils.fromByte i
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [BytesTable]
    obtain ⟨byteIndex, hvalue⟩ := h_assumptions
    rw [hvalue]
    intro _ _
    exact ByteUtils.fromByte_lt byteIndex
  completeness := by circuit_proof_start

def bytesFixedColumns : FixedColumns (F p) where
  width := 1
  rows := List.finRange 256 |>.map fun i => #[ByteUtils.fromByte i]
  uniform_width := by simp

def bytesComponent : Component (F p) where
  dataColumns := [0]
  data_columns_lt_input := by change ∀ column ∈ [0], column < 2; simp
  circuit := pushBytes
  fixedColumns := some bytesFixedColumns
  fixed_width_le_input := by change 1 ≤ 2; omega
  Assumptions := fun _ _ => True
  assumptions_imply_circuit := by
    intro i row data hfixed _ _
    rcases hfixed with ⟨hi, hrow⟩
    simp only [pushBytes]
    let byteIndex : Fin 256 := ⟨i, by simpa [bytesFixedColumns] using hi⟩
    refine ⟨byteIndex, ?_⟩
    simp [bytesFixedColumns] at hrow
    change row[0]?.getD 0 = ByteUtils.fromByte byteIndex
    have hextractSize : (row.extract 0 1).size = 1 := by
      simpa using congrArg Array.size hrow
    have hrowSize : 0 < row.size := by
      rw [Array.size_extract] at hextractSize
      omega
    have hextract : 0 < (row.extract 0 1).size := by omega
    calc
      row[0]?.getD 0 = (row.extract 0 1)[0]?.getD 0 := by
        rw [Array.getElem?_eq_getElem hrowSize, Array.getElem?_eq_getElem hextract]
        simp only [Array.getElem_extract, Nat.zero_add]
      _ = ByteUtils.fromByte byteIndex := by rw [hrow]; rfl

def Add8Channel : Channel (F p) fieldTriple where
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
  main | { x, y, z, m } => do
    -- range-check z using the bytes channel
    -- (x and y are guaranteed to be range-checked from earlier interactions)
    BytesChannel.pull z
    -- witness the output carry
    let carry ← witness ((x + y).val / 256).toField
    assertBool carry
    -- assert correctness
    x + y === z + carry * 256
    -- emit to the add8 channel with multiplicity `m`
    Add8Channel.emit m (x, y, z)

  ProverAssumptions
  | { x, y, z, m }, _, _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True
  channelsWithRequirements := [ Add8Channel.toRaw ]

  soundness := by
    circuit_proof_start [BytesTable, Add8Channel]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hm h0 hx hy
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

def add8Component : Component (F p) where
  circuit := add8

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

def FibonacciChannel : Channel (F p) fieldTriple where
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
  main | { enabled, n, x, y } => do
    -- boolean constraint for `enabled`
    -- has to be inline, channels with requirements proof doesn't handle subcircuits
    assertZero (enabled * (enabled - 1))
    -- pull the current Fibonacci state
    FibonacciChannel.pullIf enabled (n, x, y)
    -- witness the next Fibonacci value
    let z ← witness ((x + y).val % 256).toField
    -- pull from the Add8 channel to check addition
    Add8Channel.pullIf enabled (x, y, z)
    -- push the next Fibonacci state
    FibonacciChannel.pushIf enabled (n + 1, y, z)

  -- expose interactions
  exposedChannels
  | { enabled, n, x, y }, i₀ =>
    let z := var ⟨ i₀ ⟩
    expose FibonacciChannel [ pulledIf enabled (n, x, y), pushedIf enabled (n + 1, y, z) ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, n, x, y⟩ := input
    simp only [circuit_norm, FibonacciChannel, Add8Channel]

  ProverAssumptions
  | { enabled, n, x, y }, _, _ =>
    enabled = 0 ∨ (enabled = 1 ∧ ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val)
  Spec _ _ _ := True

  channelsWithRequirements := [ FibonacciChannel.toRaw ]
  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, n, x, y⟩ := input_var
    simp only [circuit_norm, FibonacciChannel, Add8Channel]
    grind

  soundness := by
    circuit_proof_start [FibonacciChannel, Add8Channel]
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
    circuit_proof_start [FibonacciChannel, Add8Channel]
    rcases h_assumptions with rfl | ⟨ rfl, h_fib ⟩
    · simp
    simp_all
    intro hx hy
    rw [Nat.mod_eq_of_lt (by grind), ZMod.val_add_of_lt]
    linarith [hx, hy, ‹Fact (p > 512)›.elim]

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
  channelsWithRequirements := [ FibonacciChannel.toRaw ]
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

def fib8Component : Component (F p) where
  circuit := fib8

def fibonacciVm : VmTables (F p) fieldTriple where
  channel := FibonacciChannel
  tables := [fib8Component]
  unique_names := by simp [fib8Component]
  verifier := fibonacciVerifier
  verifier_length_zero := by simp [circuit_norm, fibonacciVerifier]
  tables_channel := by
    simp [circuit_norm, fib8Component, fib8, Component.rowInputVar, Component.rowOperations]
    intro env h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  verifier_channel := by simp [circuit_norm, fibonacciVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, fibonacciVerifier, FibonacciChannel, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩

def fibonacciEnsemble := SoundEnsemble.empty (F p) fieldTriple
  |>.addTable bytesComponent
    (List.Subset.refl _)
    (by simp [circuit_norm, bytesComponent, pushBytes])
  |>.addFinishedChannel BytesChannel.toRaw
  |>.addTable add8Component
    (by simp +instances [circuit_norm, add8Component, add8])
    (by simp [circuit_norm, add8Component, add8])
    (by
      simp only [SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable_tables,
        SoundEnsemble.empty_tables, List.map_cons, List.map_nil, List.mem_singleton]
      simp [add8Component, add8, bytesComponent, pushBytes])
  |>.addFinishedChannel Add8Channel.toRaw
  |>.addVm fibonacciVm
    (by simp +instances [circuit_norm, fibonacciVm, add8Component, add8, bytesComponent, pushBytes,
      Add8Channel, FibonacciChannel])
    (by simp +instances [circuit_norm, fibonacciVm, fib8Component, fib8, fibonacciVerifier])
    (by simp [circuit_norm, fibonacciVm, fib8Component, fib8, fibonacciVerifier,
      Add8Channel, FibonacciChannel])
    (by
      simp only [SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable_tables,
        SoundEnsemble.empty_tables, List.map_append, List.map_cons, List.map_nil]
      simp [fibonacciVm, fib8Component, fib8, add8Component, add8,
        bytesComponent, pushBytes])
  |>.toFormal _ (fun _ _ => True)
    (by simp [circuit_norm, fibonacciVm, fib8Component, add8Component, add8,
      bytesComponent, pushBytes, fib8])

namespace FibonacciWitness

open Air.Flat.WitnessGeneration

/-- Generic push-driven generation metadata for the Fibonacci VM component. -/
def fibMode : Mode (F p) := .demand {
  channel := (FibonacciChannel (p := p)).name
  direction := .push
  aggregation := .perOccurrence
  input := { cells := [.const 1, .message 0, .message 1, .message 2] }
}

/-- Generic pull-driven, message-coalescing generation metadata for the addition chip. -/
def add8Mode : Mode (F p) := .demand {
  channel := (Add8Channel (p := p)).name
  direction := .pull
  aggregation := .byMessage
  input := { cells := [.message 0, .message 1, .message 2, .multiplicity] }
}

/-- The byte provider has one fixed-value row and one multiplicity cell per byte. -/
def bytesMode : Mode (F p) := .fixed
  (bytesFixedColumns.rows.map fun fixed => fixed ++ #[0])
  (bytesFixedColumns.rows.zipIdx.map fun (fixed, row) => {
    channel := (BytesChannel (p := p)).name
    direction := .pull
    message := fixed
    row
    column := 1
  })

/--
Channel-driven witness-generation metadata, aligned with
`fibonacciEnsemble.ensemble.tables = [fib8, add8, pushBytes]`.
-/
def config (fuel : ℕ) : Config (F p) where
  modes := [fibMode (p := p), add8Mode (p := p), bytesMode (p := p)]
  padding := [
    { input := #[0, 0, 0, 0], minimumRows := 32 },
    { input := #[0, 0, 0, 0], minimumRows := 32 },
    { input := #[0, 0], minimumRows := 256 }
  ]
  fuel := fuel

/-- Generate a complete ensemble witness from the claimed public final state. -/
def generate (publicInput : fieldTriple (F p)) (fuel : ℕ) :
    Except String (EnsembleWitness (fibonacciEnsemble (p := p)).ensemble) :=
  Air.Flat.WitnessGeneration.generate (fibonacciEnsemble (p := p)).ensemble
    (config (p := p) fuel) publicInput

end FibonacciWitness

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
  name := "false"
  main _ := do
    FalseChannel.pull ()
    return
  Spec _ _ _ := False
  ProverAssumptions _ _ _ := False
  soundness := by circuit_proof_start [FalseChannel]
  completeness := by circuit_proof_start [FalseChannel]

def falseEnsemble := SoundEnsemble.empty (F p) unit
  |>.addFinishedChannel FalseChannel.toRaw
  |>.addTable { circuit := falseCircuit }
    (by simp [circuit_norm, falseCircuit]) (by simp [circuit_norm, falseCircuit])
