module

public import Clean.Air.Vm
public import Clean.Air.Memory
public import Clean.Utils.BinaryField

@[expose] public section

/-!
# A program in read-only memory, over GF(2^64)

A VM over the binary field `BF64` runs a program of coefficients: step `k` takes the state `x` to
`x * x + program[k]`. The program lives in a read-only memory, which the VM reads by offline memory
checking, since binary fields have no lookups by field sums. The ensemble is sound under multiset
balance.

There is no integer counter in characteristic 2, so the state carries the step's power of the
primitive element `X`, which also addresses the program: the memory holds `(X ^ k, program[k])`.
-/

namespace BinaryProgram

open Air.Flat

/-- The element whose powers count the steps and address the program. -/
abbrev g : BF64 := BF64.X

/-- Running the first steps of a program on the state `x`. -/
def run (program : List BF64) (x : BF64) : BF64 :=
  program.foldl (fun x coefficient => x * x + coefficient) x

variable (program : List BF64)

/-- The program in memory: the entry `(X ^ k, program[k])` for every step `k`. -/
def programMemory (h_length : program.length < 2 ^ 63) : Memory BF64 fieldPair where
  name := "program"
  height := program.length.toUInt64
  entry i :=
    let addresses := ((List.range program.length).map (g ^ ·)).toArray
    pure (addresses[i], program.toArray[i])
  Contains
  | (address, coefficient) => ∃ k < program.length, address = g ^ k ∧ program[k]? = some coefficient
  contains_iff value := by
    obtain ⟨address, coefficient⟩ := value
    simp only [circuit_norm, Witgen.M.evalRow, Witgen.eval]
    have h_toNat (k : ℕ) (hk : k < program.length) : k.toUInt64.toNat = k :=
      Nat.mod_eq_of_lt (by omega)
    constructor
    · rintro ⟨k, hk, rfl, h_coefficient⟩
      rw [List.getElem?_eq_getElem hk, Option.some_inj] at h_coefficient
      exact ⟨k.toUInt64, by simp [h_toNat k hk, hk, h_coefficient]⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      refine ⟨i.toNat, hi, by simp [hi], ?_⟩
      simp [List.getElem?_eq_getElem hi]
  generator := g
  orderOf_generator := BF64.orderOf_X

/-- Powers of `X` below its order are distinct. -/
lemma pow_inj {k i : ℕ} (hk : k < 2 ^ 63) (hi : i < 2 ^ 63) (h : g ^ k = g ^ i) : k = i := by
  have h_order : orderOf g = 2 ^ 64 - 1 := BF64.orderOf_X
  exact pow_injOn_Iio_orderOf (by simp [h_order]; omega) (by simp [h_order]; omega) h

/-- One more step of a program. -/
lemma run_take_succ {k : ℕ} (hk : k < program.length) (initial : BF64) :
    run (program.take (k + 1)) initial =
      run (program.take k) initial * run (program.take k) initial + program[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, run, run,
    List.foldl_append]
  rfl

/-- The state after `k` steps: the counter `X ^ k`, and the result of running the first `k` steps
on the initial state. -/
def stateChannel (initial : BF64) : Channel BF64 fieldPair where
  name := "state"
  Guarantees state _ :=
    ∃ k ≤ program.length, state.1 = g ^ k ∧ state.2 = run (program.take k) initial

structure StepInput (F : Type) where
  enabled : F
  counter : F
  x : F
  coefficient : F
deriving ProvableStruct

/-- The coefficient of the step whose counter is `counter`, as the prover computes it. -/
def coefficientAt (counter : Expression BF64) : Witgen.FExpr BF64 :=
  program.zipIdx.foldr (fun (coefficient, k) rest =>
    .ite (.feq (.expr counter) (.const (g ^ k))) (.const coefficient) rest) (.const 0)

/-- One step: pull a state, read the step's coefficient from the program in memory, and push the
next state. -/
def step (h_length : program.length < 2 ^ 63) (initial : BF64) :
    GeneralFormalCircuit BF64 StepInput unit where
  name := "step"
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    (stateChannel program initial).pullIf input.enabled (input.counter, input.x)
    (programMemory program h_length).channel.pullIf input.enabled
      (input.counter, input.coefficient)
    (stateChannel program initial).pushIf input.enabled
      (input.counter * .const g, input.x * input.x + input.coefficient)

  exposedChannels
  | { enabled, counter, x, coefficient }, _ =>
    expose (stateChannel program initial) [pulledIf enabled (counter, x),
      pushedIf enabled (counter * .const g, x * x + coefficient)]
  exposedChannels_eq input _ := by
    obtain ⟨enabled, counter, x, coefficient⟩ := input
    simp [circuit_norm, stateChannel, programMemory]

  ProverAssumptions
  | { enabled, counter, x, coefficient }, data, _ =>
    enabled = 0 ∨ enabled = 1 ∧ (stateChannel program initial).Guarantees (counter, x) data ∧
      (programMemory program h_length).Contains (counter, coefficient)
  Spec _ _ _ := True

  channelsWithRequirements := [(stateChannel program initial).toRaw]
  requirementsChannelsLawful input_var _ := by
    obtain ⟨enabled, counter, x, coefficient⟩ := input_var
    simp only [circuit_norm, stateChannel, programMemory]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]

  soundness := by
    circuit_proof_start [stateChannel, programMemory]
    obtain ⟨h_bool, h_state, h_read⟩ := h_holds
    rcases mul_eq_zero.mp h_bool with h_zero | h_one
    · simp [h_zero]
    rw [sub_eq_zero] at h_one
    obtain ⟨k, hk, h_counter, h_x⟩ := h_state h_one
    obtain ⟨i, hi, h_counter', h_coefficient⟩ := h_read h_one
    obtain rfl : k = i := pow_inj (by omega) (by omega) (h_counter.symm.trans h_counter')
    rw [List.getElem?_eq_getElem hi, Option.some_inj] at h_coefficient
    refine ⟨by simp [h_one], by simp [h_one], fun _ => ⟨k + 1, hi, by rw [h_counter, pow_succ], ?_⟩⟩
    rw [run_take_succ program hi, h_x, h_coefficient]
  completeness := by
    circuit_proof_start [stateChannel, programMemory]
    rcases h_assumptions with h | ⟨h, h_state, h_read⟩ <;> simp_all

/-- One row per state pushed to the state channel. Padding rows are disabled. -/
abbrev stepComponent (h_length : program.length < 2 ^ 63) (initial : BF64) : Component BF64 where
  circuit := step program h_length initial
  generation := .demand {
    trigger := .push
    channel := stateChannel program initial
    input
    | (counter, x) =>
      pure { enabled := 1, counter, x, coefficient := .witness (coefficientAt program counter) }
  }

/-- The public input is the final state. The verifier pushes the initial state, and pulls the final
state after all steps. -/
def verifier (initial : BF64) : Verifier.Program BF64 field where
  main final := do
    Verifier.pull (stateChannel program initial) (.const (g ^ program.length), final)
    Verifier.push (stateChannel program initial) (1, .const initial)
  Spec final data := (stateChannel program initial).Guarantees (g ^ program.length, final) data
  soundness := by simp [circuit_norm]

def vm (h_length : program.length < 2 ^ 63) (initial : BF64) : VmTables BF64 field where
  channel := stateChannel program initial
  tables := [stepComponent program h_length initial]
  verifier := verifier program initial
  tables_channel := by simp [circuit_norm, step, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, verifier]
  verifier_requirements _ := by
    simp only [circuit_norm, verifier, stateChannel]
    exact ⟨0, by simp, by simp, by simp [run]⟩

/-- The public statement: running the program on the initial state ends with `final`. -/
def Spec (initial final : BF64) : Prop := final = run program initial

/-- The ensemble, sound under multiset balance. -/
def formalEnsemble (h_length : program.length < 2 ^ 63) (initial : BF64) :
    FormalEnsemble BF64 field .multiset :=
  SoundEnsemble.empty BF64 field .multiset
  |>.addMemory (programMemory program h_length)
    (by simp [circuit_norm, programMemory]) (by simp [circuit_norm, programMemory])
    (by simp [circuit_norm, programMemory])
  |>.addVm (vm program h_length initial)
    (by simp [circuit_norm, vm, stateChannel, programMemory])
    (by simp +instances [circuit_norm, vm, step, verifier, stateChannel, programMemory])
    (by simp +instances [circuit_norm, vm, step, verifier, stateChannel, programMemory])
    (by simp [circuit_norm, vm, step, programMemory])
  |>.toFormal (fun _ => True) (Spec program initial)
    (by simp [circuit_norm, vm])
    (by
      intro witness _ verifier_spec
      obtain ⟨k, hk, h_counter, h_final⟩ := verifier_spec
      obtain rfl : program.length = k := pow_inj (by omega) (by omega) h_counter
      simpa [Spec] using h_final)

/-- End-to-end soundness: a valid proof for the public input `final` shows that running the program
on the initial state ends with `final`. -/
theorem soundness (h_length : program.length < 2 ^ 63) (initial final : BF64) :
    (formalEnsemble program h_length initial).ensemble.Statement .multiset final →
      final = run program initial :=
  (formalEnsemble program h_length initial).soundness final trivial

end BinaryProgram
