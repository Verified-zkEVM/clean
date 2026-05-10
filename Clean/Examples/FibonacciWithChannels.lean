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
open ByteUtils (mod256 floorDiv256)
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

abbrev BytesChannel := Channel.fromStatic (F p) field BytesTable

-- bytes "circuit" that just pushes all bytes
-- probably shouldn't be a "circuit" at all
def pushBytes : GeneralFormalCircuit (F p) (fields 256) unit where
  main multiplicities := do
    let _  ← .mapFinRange 256 fun ⟨ i, _ ⟩ =>
      BytesChannel.emit multiplicities[i] (const i)

  localLength _ := 0
  localLength_eq := by simp +arith only [circuit_norm]
  output _ _ := ()
  ProverAssumptions _ _ _ := True
  Spec _ _ _ := True
  soundness := by circuit_proof_start [BytesTable]
  completeness := by circuit_proof_start
  channelsWithRequirements := [ BytesChannel.toRaw ]

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

def add8 : GeneralFormalCircuit (F p) Add8Inputs unit where
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
  -- TODO make coercion work without .toRaw
  channelsWithGuarantees := [ BytesChannel.toRaw ]
  channelsWithRequirements := [ Add8Channel.toRaw ]
  -- TODO feels weird to put the entire spec in the completeness assumptions
  -- can we get something from the channel interactions??
  ProverAssumptions
  | { x, y, z, m }, _, _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [BytesTable, Add8Channel]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hm hx hy
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
    refine ⟨ hz, ?_⟩
    refine ⟨ ?_, ?_ ⟩
    · simpa [floorDiv256, h_env] using add_completeness_bool
    · simpa [h_input_z, floorDiv256, h_env] using add_completeness_add

example (input : Var Add8Inputs (F p)) :
    ExplicitCircuit (add8.main input) := by
  infer_explicit_circuit

-- define valid Fibonacci state transitions

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

def fib8 : GeneralFormalCircuit (F p) fieldTriple unit where
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
  channelsWithGuarantees := [ Add8Channel.toRaw, FibonacciChannel.toRaw ]
  channelsWithRequirements := [ FibonacciChannel.toRaw ]
  exposedChannels
  | (n, x, y), i₀ =>
    let z := var ⟨ i₀ ⟩
    expose FibonacciChannel [ pulled (n, x, y), pushed (n + 1, y, z) ]
  channelsLawful := by
    simp only [circuit_norm, Add8Channel, FibonacciChannel]

  ProverAssumptions
  | (n, x, y), _, _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start
    rcases input with ⟨ n, x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm]
    set z := env.get i₀
    simp only [circuit_norm, FibonacciChannel, Add8Channel] at h_holds ⊢
    obtain ⟨ ⟨k, fiby, hk⟩, hadd ⟩ := h_holds
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    use k + 1
    simp only [fibonacci, ← fiby]
    rw [ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, FibonacciChannel, Add8Channel]
    intro hx hy
    rw [mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
    linarith [hx, hy, ‹Fact (p > 512)›.elim]

example (input : Var fieldTriple (F p)) :
    ExplicitCircuit (fib8.main input) := by
  infer_explicit_circuit

-- completing Fibonacci channel with input and output
def fibonacciVerifier : GeneralFormalCircuit (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- push initial state, pull the final state
    FibonacciChannel.pull (n, x, y)
    FibonacciChannel.push (0, 0, 1)

  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ FibonacciChannel.toRaw ]
  channelsWithRequirements := [ FibonacciChannel.toRaw ]
  exposedChannels
  | (n, x, y), _ =>
    expose FibonacciChannel [ pulled (n, x, y), pushed (0, 0, 1) ]
  channelsLawful := by simp only [circuit_norm, FibonacciChannel]
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
  tables_channel := by simp [circuit_norm, fib8]
  verifier_channel := by simp [circuit_norm, fibonacciVerifier]
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

abbrev fibonacciFormalEnsemble := fibonacciEnsemble.toFormal (F p) (fun _ _ => True) (by
  simp [circuit_norm, fibonacciEnsemble, fibonacciVm, add8, pushBytes, fib8])

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
  fibonacciEnsemble.Statement (n, x, y) →
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val := by
  intro n x y statement
  convert fibonacciFormalEnsemble.soundness (n, x, y) ?assumptions statement
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
  main _ := FalseChannel.pull ()
  Spec _ _ _ := False
  ProverAssumptions _ _ _ := False
  localLength _ := 0
  channelsWithGuarantees := [ FalseChannel.toRaw ]
  soundness := by circuit_proof_start [FalseChannel]
  completeness := by circuit_proof_start [FalseChannel]

def falseEnsemble := SoundEnsemble.empty (F p) unit
  |>.addFinishedChannel FalseChannel.toRaw
  |>.addTable ⟨ falseCircuit ⟩
    (by simp [circuit_norm, falseCircuit]) (by simp [circuit_norm, falseCircuit])

-- everything below is a remainder of the original AI slop proof of fibonacci soundness
-- TODO port non-overflow proof to the general case and remove

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
lemma exists_push_of_pull' {n : ℕ}
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
        exists_push_of_pull' fibInteractions (#v[n_prev, x, y])
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
