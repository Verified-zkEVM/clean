module

public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Air.GenerationCompletenessProof

@[expose] public section

/-!
# Completeness of Fibonacci witness generation

From any public state `(n, x, y)` that is the `n`-th Fibonacci state, of a run short enough for the
field, witness generation returns a valid witness.
-/

open Air.Flat Air.Flat.WitnessGeneration

variable {p : ℕ} [Fact p.Prime] [pGt : Fact (p > 512)]

namespace FibonacciWitness

/-- The Fibonacci step on channel messages `(n, x, y)`. -/
def next (state : Array (F p)) : Array (F p) :=
  #[state[0]?.getD 0 + 1, state[2]?.getD 0,
    ((((state[1]?.getD 0).val + (state[2]?.getD 0).val) % 256 : ℕ) : F p)]

/-- A table height for a run of `steps` steps. -/
def height (steps : ℕ) : ℕ := 2 ^ Nat.clog 2 (max steps 32)

lemma tables_eq : (fibonacciEnsemble (p := p)).ensemble.tables =
    [fib8Component, add8Component, bytesComponent] := by
  with_unfolding_all rfl

lemma channels_eq : (fibonacciEnsemble (p := p)).ensemble.channels =
    [FibonacciChannel.toRaw, Add8Channel.toRaw, BytesChannel.toRaw] := by
  with_unfolding_all rfl

lemma valid : ∃ validPlan, (plan (p := p)).validate (fibonacciEnsemble (p := p)).ensemble =
    .ok validPlan :=
  GenerationPlan.validate_ok (by rw [tables_eq]; rfl)
    (by plan_valid [tables_eq, plan, fibMode, add8Mode, bytesMode, fib8Component, add8Component,
      bytesComponent, fib8, add8, pushBytes, bytesFixedColumns, BytesTable, Add8Channel,
      FibonacciChannel, Gadgets.Equality.circuit, Gadgets.Equality.main])

lemma answers_add8 : Answers (fibonacciEnsemble (p := p)).ensemble plan false "add8" :=
  ⟨add8Component, by simp [tables_eq],
    { mode := .demand add8Mode, padding := { input := #[0, 0, 0, 0], minimumRows := 32 } },
    by simp [plan, add8Component, add8, fib8],
    by simp [Mode.handled, add8Mode, Add8Channel, Channel.toRaw],
    by simp⟩

lemma answers_bytes : Answers (fibonacciEnsemble (p := p)).ensemble plan true "bytes" :=
  ⟨bytesComponent, by simp [tables_eq],
    { mode := .preallocated bytesMode, padding := { input := #[0, 0], minimumRows := 256 } },
    by simp [plan, bytesComponent, pushBytes, add8, fib8],
    by simp [Mode.handled, bytesMode, bytesComponent, pushBytes, BytesTable, handlerDirection,
      circuit_norm, Component.rowOperations], fun _ => ⟨_, rfl⟩⟩

/-- A Fibonacci row answering state `(n, x, y)` pulls it and pushes the next state; it also pulls
the byte addition. -/
lemma fib8_row (n x y : F p) : RowInteractions (fib8 (p := p)) fun input _ interactions =>
    input = fromElements (inputRow Fib8Input #[1, n, x, y]) →
    (∀ message, netOfInteractions interactions "fibonacci" message =
      (if message = next #[n, x, y] then 1 else 0) - (if message = #[n, x, y] then 1 else 0)) ∧
    ∀ interaction ∈ interactions, interaction.channel.name ≠ "fibonacci" →
      SideInteraction (fibonacciEnsemble (p := p)).ensemble plan "fibonacci" false interaction := by
  circuit_proof_start [fib8, FibonacciChannel, Add8Channel]
  intro hinput
  simp [explicit_provable_type, circuit_norm] at hinput
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hinput
  simp [netOfInteractions_cons, netOfInteractions_nil, circuit_norm, explicit_provable_type,
    AbstractInteraction.eval, h_input, h_env, next]
  obtain ⟨k, hfib, -⟩ := (h_assumptions.resolve_left one_ne_zero).2
  obtain ⟨hx, hy⟩ := fibonacci_bytes hfib
  have hsum : ZMod.val (input_x + input_y) = ZMod.val input_x + ZMod.val input_y :=
    ZMod.val_add_of_lt (by linarith [pGt.out])
  refine ⟨fun message => ?_, .inr ⟨⟨rfl, .inr rfl⟩, by simp [Channel.toRaw], answers_add8⟩⟩
  rw [hsum]
  by_cases hnext : message = #[input_n + 1, input_y, ((input_x.val + input_y.val) % 256 : ℕ)] <;>
    by_cases hstate : message = #[input_n, input_x, input_y] <;>
    simp [hnext, hstate, eq_comm]

/-- An addition row for `(x, y, z)` with multiplicity `count` pushes `count` occurrences of the
message and range-checks `z`. -/
lemma add8_row (x y z : F p) (count : ℕ) : RowInteractions (add8 (p := p)) fun input _ interactions =>
    input = fromElements (inputRow Add8Inputs #[x, y, z, (count : F p)]) →
    (∀ other, netOfInteractions interactions "add8" other =
      if other = #[x, y, z] then (count : F p) else 0) ∧
    ∀ interaction ∈ interactions, interaction.channel.name ≠ "add8" →
      SideInteraction (fibonacciEnsemble (p := p)).ensemble plan "fibonacci" false interaction := by
  circuit_proof_start [add8, BytesTable, Add8Channel]
  intro hinput
  simp [explicit_provable_type, circuit_norm] at hinput
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hinput
  simp [netOfInteractions_cons, netOfInteractions_nil, circuit_norm, explicit_provable_type,
    AbstractInteraction.eval, h_input, FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Gadgets.Equality.circuit, Gadgets.Equality.main, Circuit.forEach, BytesTable,
    FlatOperation.interactions]
  refine ⟨fun other => by by_cases h : other = #[input_x, input_y, input_z] <;> simp [h, eq_comm],
    .inr ⟨⟨rfl, .inr rfl⟩, by simp [circuit_norm], ?_⟩⟩
  obtain ⟨component, hcomponent, rowPlan, hplanned, hhandled, -⟩ := answers_bytes (p := p)
  exact ⟨component, hcomponent, rowPlan, hplanned, by simpa [circuit_norm] using hhandled, by simp⟩

/-- Besides its pushes, an addition row only range-checks `z`, whatever its multiplicity. -/
lemma add8_nets (x y z : F p) (count : ℕ) : RowInteractions (add8 (p := p))
    fun input _ interactions =>
    input = fromElements (inputRow Add8Inputs #[x, y, z, (count : F p)]) →
    ∀ channel ≠ "add8", ∀ other, netOfInteractions interactions channel other =
      if channel = "bytes" ∧ other = #[z] then -1 else 0 := by
  circuit_proof_start [add8, BytesTable, Add8Channel]
  intro hinput channel hchannel other
  simp [explicit_provable_type, circuit_norm] at hinput
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hinput
  simp [netOfInteractions_cons, netOfInteractions_nil, circuit_norm, explicit_provable_type,
    AbstractInteraction.eval, h_input, FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Gadgets.Equality.circuit, Gadgets.Equality.main, Circuit.forEach, BytesTable,
    FlatOperation.interactions, Ne.symm hchannel]
  by_cases h : channel = "bytes" ∧ other = #[input_z] <;> simp_all [eq_comm]

/-- The interactions of a byte row: it pushes its byte with its multiplicity. -/
def bytesInteractions (row : Array (F p)) : List (Interaction (F p)) :=
  [{ channel := BytesChannel.toRaw, mult := row[1]?.getD 0, msg := #[row[0]?.getD 0],
     same_size := by simp [circuit_norm], assumeGuarantees := false }]

lemma pushBytes_row (row : Array (F p)) : RowInteractions (pushBytes (p := p))
    fun input _ interactions =>
    input = fromElements (inputRow BytesInput row) → interactions = bytesInteractions row := by
  circuit_proof_start [pushBytes, BytesTable]
  intro hinput
  simp [explicit_provable_type, circuit_norm] at hinput
  obtain ⟨rfl, rfl⟩ := hinput
  simp [bytesInteractions, AbstractInteraction.eval, circuit_norm, explicit_provable_type, h_input]

/-- A disabled Fibonacci row interacts with multiplicity zero. -/
lemma fib8_padding : RowInteractions (fib8 (p := p)) fun input _ interactions =>
    input = fromElements (inputRow Fib8Input #[0, 0, 0, 0]) →
    ∀ interaction ∈ interactions,
      SideInteraction (fibonacciEnsemble (p := p)).ensemble plan "fibonacci" true interaction := by
  circuit_proof_start [fib8, FibonacciChannel, Add8Channel]
  intro hinput
  simp [explicit_provable_type, circuit_norm] at hinput
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hinput
  simp [circuit_norm, explicit_provable_type, AbstractInteraction.eval, h_input, SideInteraction]

/-- A zero addition row range-checks zero and pushes nothing. -/
lemma add8_padding : RowInteractions (add8 (p := p)) fun input _ interactions =>
    input = fromElements (inputRow Add8Inputs #[0, 0, 0, 0]) →
    ∀ interaction ∈ interactions,
      SideInteraction (fibonacciEnsemble (p := p)).ensemble plan "fibonacci" true interaction := by
  circuit_proof_start [add8, BytesTable, Add8Channel]
  intro hinput
  simp [explicit_provable_type, circuit_norm] at hinput
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hinput
  simp [circuit_norm, explicit_provable_type, AbstractInteraction.eval, h_input,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Gadgets.Equality.circuit,
    Gadgets.Equality.main, Circuit.forEach, FlatOperation.interactions, SideInteraction]
  exact ⟨⟨rfl, .inr rfl⟩, by simp [BytesTable], by simpa [BytesTable] using answers_bytes⟩

/-- A zero byte row pushes nothing. -/
lemma bytes_padding (row : Array (F p)) (hrow : row = #[0, 0]) :
    ∀ interaction ∈ bytesInteractions row,
      SideInteraction (fibonacciEnsemble (p := p)).ensemble plan "fibonacci" true interaction := by
  subst hrow
  simp [bytesInteractions, SideInteraction]

/-- Row `row` of the byte table initially holds the byte `row` with multiplicity zero. -/
lemma bytes_initial (hint : ProverHint (F p)) (row : ℕ) :
    preallocatedInput bytesComponent bytesMode hint row = #[((row % 2 ^ 64 : ℕ) : F p), 0] := by
  simp [preallocatedInput, fixedPrefix, bytesComponent, bytesFixedColumns, bytesMode,
    FixedColumns.row, Witgen.RowProgram.eval, Witgen.RowProgram.ofFExprs, Witgen.VExpr.eval, Witgen.FExpr.eval,
    explicit_provable_type, circuit_norm]

lemma inputOf_bytes (row : Array (F p)) :
    inputOf bytesComponent row = { value := row[0]?.getD 0, multiplicity := row[1]?.getD 0 } := by
  with_unfolding_all rfl

lemma verifier_eq : (fibonacciEnsemble (p := p)).ensemble.verifier = fibonacciVerifier := by
  with_unfolding_all rfl

/-! ### The VM and its run -/

def vm : Vm (fibonacciEnsemble (p := p)) (plan (p := p)) where
  channel := FibonacciChannel.toRaw
  component := fib8Component
  mode := fibMode
  padding := { input := #[0, 0, 0, 0], minimumRows := 32 }
  declared := by simp [channels_eq]
  mem := by simp [tables_eq]
  planned := by simp [plan, fib8Component]
  mode_channel := rfl
  mode_direction := rfl
  mode_aggregation := rfl
  no_pull_handler := by
    intro other hother rowPlan hplanned
    simp only [tables_eq, List.mem_cons, List.not_mem_nil, or_false] at hother
    rcases hother with rfl | rfl | rfl <;>
      simp [plan, fib8Component, add8Component, bytesComponent, fib8, add8, pushBytes] at hplanned <;>
      subst hplanned <;>
      simp [Mode.handled, fibMode, add8Mode, bytesMode, handlerDirection, circuit_norm,
        Component.rowOperations, bytesComponent, pushBytes,
        BytesTable, Add8Channel, FibonacciChannel]
  next _ := next
  initial _ := #[0, 0, 1]
  final | (n, x, y) => #[n, x, y]

lemma fibonacci_val (k : ℕ) : ZMod.val (((fibonacci k).1 : ℕ) : F p) = (fibonacci k).1 ∧
    ZMod.val (((fibonacci k).2 : ℕ) : F p) = (fibonacci k).2 := by
  obtain ⟨h1, h2⟩ := fibonacci_bytes (n := k) Prod.mk.eta.symm
  exact ⟨ZMod.val_natCast_of_lt (by linarith [pGt.out]),
    ZMod.val_natCast_of_lt (by linarith [pGt.out])⟩

/-- The `k`-th state of the run is the `k`-th Fibonacci state. -/
lemma vm_state (publicInput : fieldTriple (F p))
    (proverInput : (fibonacciEnsemble (p := p)).ProverInput (F p)) (k : ℕ) :
    (vm (p := p)).state publicInput proverInput k =
      #[(k : F p), ((fibonacci k).1 : F p), ((fibonacci k).2 : F p)] := by
  induction k with
  | zero => simp [Vm.state, vm, fibonacci]
  | succ k ih =>
      simp only [Vm.state, Function.iterate_succ_apply'] at ih ⊢
      rw [ih]
      obtain ⟨h1, h2⟩ := fibonacci_val (p := p) k
      simp [vm, next, h1, h2, fibonacci]

lemma le_height (steps : ℕ) : max steps 32 ≤ height steps :=
  Nat.le_pow_clog (by decide) _

lemma height_le (steps : ℕ) : height steps ≤ 2 * max steps 32 := by
  unfold height
  set m := max steps 32 with hm
  have hm32 : 32 ≤ m := le_max_right _ _
  have hclog : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by decide) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (x := m) (by decide) (by omega)
  have hpow : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m).pred := by
    rw [← pow_succ']
    exact congrArg (2 ^ ·) (Nat.succ_pred_eq_of_pos hclog).symm
  omega

/-- Every component of the ensemble with its row plan. -/
lemma planned_cases {component : Component (F p)}
    (hmem : component ∈ (fibonacciEnsemble (p := p)).ensemble.tables) {rowPlan : RowPlan (F p)}
    (hplanned : (component.circuit.name, rowPlan) ∈ (plan (p := p)).components) :
    (component = fib8Component ∧ rowPlan =
        { mode := .demand fibMode, padding := { input := #[0, 0, 0, 0], minimumRows := 32 } }) ∨
    (component = add8Component ∧ rowPlan =
        { mode := .demand add8Mode, padding := { input := #[0, 0, 0, 0], minimumRows := 32 } }) ∨
    (component = bytesComponent ∧ rowPlan =
        { mode := .preallocated bytesMode, padding := { input := #[0, 0], minimumRows := 256 } }) := by
  simp only [tables_eq, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;>
    simp [plan, fib8Component, add8Component, bytesComponent, fib8, add8, pushBytes] at hplanned <;>
    simp [hplanned]

lemma proverAssumptions_iff (n x y : F p) (proverInput : Unit) :
    (fibonacciEnsemble (p := p)).ProverAssumptions (n, x, y) proverInput ↔
      (x.val, y.val) = fibonacci n.val ∧ 20 * n.val + 1156 < p ∧ n.val ≤ 2 ^ 64 := by
  with_unfolding_all rfl

lemma height_le_size {steps : ℕ} (h : steps ≤ 2 ^ 64) : height steps ≤ UInt64.size := by
  have : Nat.clog 2 (max steps 32) ≤ 64 := Nat.clog_le_of_le_pow (by omega)
  exact le_trans (Nat.pow_le_pow_right (by decide) this) (by decide)

omit [Fact p.Prime] pGt in
lemma interactions_lt {steps : ℕ} (h : 20 * steps + 1156 < p) :
    2 * (2 + (height steps * 3 + (height steps * 2 + 256))) < p := by
  have := height_le steps
  exact lt_of_le_of_lt (by omega) h

/-- The verifier pushes the initial state and pulls the final one, and does nothing else. -/
lemma verifier_row (n x y : F p) (data : ProverData (F p)) :
    let interactions := (fibonacciEnsemble (p := p)).ensemble.verifierOperations.interactionValues
      (Environment.fromInput (Input := fieldTriple) (n, x, y) data)
    (∀ message, netOfInteractions interactions "fibonacci" message =
      (if message = #[0, 0, 1] then 1 else 0) - (if message = #[n, x, y] then 1 else 0)) ∧
    ∀ interaction ∈ interactions, interaction.channel.name ≠ "fibonacci" →
      SideInteraction (fibonacciEnsemble (p := p)).ensemble plan "fibonacci" false interaction ∧
        interaction.ProverGuarantees data := by
  simp [Ensemble.verifierOperations, verifier_eq, fibonacciVerifier, circuit_norm,
    Operations.interactionValues, Verifier.Program.circuitOperations, explicit_provable_type,
    netOfInteractions_cons, netOfInteractions_nil, AbstractInteraction.eval, FibonacciChannel]
  intro message
  by_cases hinitial : message = #[0, 0, 1] <;> by_cases hfinal : message = #[n, x, y] <;>
    simp [hinitial, hfinal, eq_comm] <;> split_ifs <;> ring

def completePlan : CompletePlan (fibonacciEnsemble (p := p)) (plan (p := p)) where
  valid := valid
  no_lazy := by
    intro component hmem rowPlan mode hplanned hmode
    rcases planned_cases hmem hplanned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases hmode
    rfl
  vm
  rowBound steps name := if name = "bytes" then 256 else height steps
  rank _ := 0
  acyclic := by
    intro component hmem rowPlan mode hplanned hmode hvm other hother otherPlan otherMode
      hotherPlanned hotherMode hotherVm hpulls
    rcases planned_cases hmem hplanned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases hmode
    · exact absurd rfl hvm
    rcases planned_cases hother hotherPlanned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases hotherMode
    · exact absurd rfl hotherVm
    · simp [pullsOn, add8Component, add8, add8Mode, Add8Channel, BytesTable, circuit_norm,
        Component.rowOperations, explicit_provable_type, FormalAssertion.toSubcircuit,
        Operations.toNested_toFlat, Gadgets.Equality.circuit, Gadgets.Equality.main,
        Circuit.forEach, FlatOperation.interactions] at hpulls
  run := by
    rintro ⟨n, x, y⟩ proverInput h
    obtain ⟨hfib, hp, hn⟩ := (proverAssumptions_iff n x y proverInput).mp h
    have hx : (((fibonacci n.val).1 : ℕ) : F p) = x := by
      rw [← hfib]
      exact ZMod.natCast_zmod_val x
    have hy : (((fibonacci n.val).2 : ℕ) : F p) = y := by
      rw [← hfib]
      exact ZMod.natCast_zmod_val y
    refine ⟨n.val, ?_, fun k hk heq => ?_, fun k hk data _ => ?_, ?_⟩
    · rw [vm_state]
      simp [vm, hx, hy]
    · rw [vm_state] at heq
      have heq₀ := congrArg (fun state : Array (F p) => state[0]?) heq
      simp [vm] at heq₀
      have := congrArg ZMod.val heq₀
      rw [ZMod.val_natCast_of_lt (by omega)] at this
      omega
    · obtain ⟨h1, h2⟩ := fibonacci_val (p := p) k
      rw [vm_state]
      simp [vm, Vm.input, fibMode, InputTemplate.eval, InputCell.eval, fib8Component,
        fib8, explicit_provable_type, circuit_norm, h1, h2, ZMod.val_natCast_of_lt
        (show k < p by omega)]
      exact ⟨k, rfl, Nat.mod_eq_of_lt (by omega)⟩
    · have hheight := le_height n.val
      have hheight' := height_le n.val
      have hsize := height_le_size hn
      refine ⟨by simp [vm, fib8Component, fib8]; omega, ?_, ?_⟩
      · intro component hmem rowPlan hplanned
        rcases planned_cases hmem hplanned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [fib8Component, fib8]
          exact ⟨⟨_, rfl⟩, by omega, hsize, .inl rfl⟩
        · simp [add8Component, add8]
          refine ⟨⟨_, rfl⟩, by omega, hsize, .inr ?_⟩
          simp [tables_eq, pullsOn, verifierPullsOn, Ensemble.verifierOperations, verifier_eq,
            fibonacciVerifier, Verifier.Program.circuitOperations, fib8Component, add8Component,
            bytesComponent, fib8, add8, pushBytes, add8Mode, Add8Channel, BytesTable,
            FibonacciChannel, circuit_norm, Component.rowOperations, explicit_provable_type,
            FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Gadgets.Equality.circuit,
            Gadgets.Equality.main, Circuit.forEach, FlatOperation.interactions]
        · simp [bytesComponent, pushBytes, bytesMode, bytesFixedColumns]
          exact ⟨⟨8, rfl⟩, by decide⟩
      · simp [tables_eq, Ensemble.verifierOperations, verifier_eq, fibonacciVerifier,
          Verifier.Program.circuitOperations, fib8Component, add8Component, bytesComponent, fib8,
          add8, pushBytes, Add8Channel, BytesTable, FibonacciChannel, circuit_norm,
          Component.rowOperations, explicit_provable_type, FormalAssertion.toSubcircuit,
          Operations.toNested_toFlat, Gadgets.Equality.circuit, Gadgets.Equality.main,
          Circuit.forEach, FlatOperation.interactions]
        exact interactions_lt hp
  vm_row _ state hsize := by
    change state.size = 3 at hsize
    rcases state with ⟨_ | ⟨n, _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hsize
    exact (fib8_row n x y).mono fun _ _ _ h _ _ => h
  verifier := by
    rintro ⟨n, x, y⟩ proverInput - data -
    exact verifier_row n x y data
  demand := by
    intro component hmem rowPlan mode hplanned hmode hvm
    rcases planned_cases hmem hplanned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hvm
    · cases hmode
      refine ⟨by simp [add8Mode, channels_eq], rfl, ?_, fun message count hsize => ?_,
        fun _ message hsize => ?_⟩
      · rintro publicInput proverInput - data - ⟨⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩⟩, hsize⟩ count -
          hguarantees <;> change _ = 3 at hsize <;> simp at hsize
        simp [inputOf_of_size, add8Component, add8, add8Mode, Add8Channel, InputTemplate.eval,
          InputCell.eval, Channel.toRaw, explicit_provable_type, circuit_norm] at hguarantees ⊢
        obtain ⟨hx, hy, hz⟩ := hguarantees
        exact ⟨hx, hy, by omega, hz⟩
      · change message.size = 3 at hsize
        rcases message with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hsize
        exact add8_row x y z count
      · change message.size = 3 at hsize
        rcases message with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hsize
        exact ⟨fun _ _ channel other => if channel = "bytes" ∧ other = #[z] then -1 else 0,
          add8_nets x y z⟩
    · cases hmode
  preallocated := by
    intro component hmem rowPlan mode hplanned hmode
    rcases planned_cases hmem hplanned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases hmode
    refine ⟨fun publicInput proverInput _ data _ => ⟨?_, ?_, ?_⟩, fun row _ _ => bytesInteractions row,
      fun input => pushBytes_row input, ?_, ?_⟩
    · intro row hrow
      simp [bytesMode, bytesFixedColumns] at hrow
      simp [bytes_initial, inputOf_bytes]
      exact ⟨⟨row, hrow⟩, FieldUtils.natToField_eq_natCast _⟩
    · intro handler hhandler row hrow
      simp [bytesMode] at hhandler
      simp [bytes_initial, hhandler]
    · intro input handler hhandler value
      simp [bytesMode] at hhandler
      simp only [inputOf_bytes]
      simp [bytesComponent, pushBytes, hhandler]
    · intro input data hint index hindex other hother
      simp [bytesMode] at hindex
      rcases index with _ | index
      · contradiction
      · simp [bytesInteractions] at hother
    · intro handler hhandler
      simp [bytesMode] at hhandler
      subst hhandler
      refine ⟨BytesChannel.toRaw, by simp [channels_eq], ?_, ?_, ?_, ?_⟩
      · simp [bytesInteractions]
      · simp [bytesInteractions]
      · intro input value data hint index hindex
        rcases index with _ | index
        · contradiction
        · simp [bytesInteractions]
      · rintro publicInput proverInput - data - ⟨⟨_ | ⟨byte, _ | _⟩⟩, hsize⟩ hguarantees <;>
          change _ = 1 at hsize <;> simp at hsize
        simp [BytesTable, Channel.toRaw, Channel.fromStatic, explicit_provable_type,
          circuit_norm] at hguarantees
        refine ⟨byte.val, by simpa [bytesMode, bytesFixedColumns] using hguarantees, ?_⟩
        simp [bytes_initial, bytesInteractions]
  padding := by
    intro component hmem rowPlan hplanned
    rcases planned_cases hmem hplanned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨fun _ _ _ _ _ => ?_, fib8_padding⟩
      simp [inputOf_of_size, fib8Component, fib8, explicit_provable_type, circuit_norm]
    · refine ⟨fun _ _ _ _ _ => ?_, add8_padding⟩
      simp [inputOf_of_size, add8Component, add8, explicit_provable_type, circuit_norm]
    · refine ⟨fun _ _ _ _ _ => ?_, ?_⟩
      · simp [inputOf_of_size, bytesComponent, pushBytes, explicit_provable_type, circuit_norm]
        exact ⟨_, (ByteUtils.fromByte_eq 0 (by simp)).symm⟩
      · exact (pushBytes_row #[0, 0]).mono fun _ _ _ h hinput => h hinput ▸ bytes_padding _ rfl

/-- Fibonacci witness generation is complete: from the `n`-th Fibonacci state of a run short enough
for the field, it returns a witness for that state satisfying the constraints and balancing all
channels. -/
theorem generate_complete (n x y : F p) (hfib : (x.val, y.val) = fibonacci n.val)
    (hp : 20 * n.val + 1156 < p) (hn : n.val ≤ 2 ^ 64) :
    ∃ witness, generate (n, x, y) = .ok witness ∧ witness.publicInput = (n, x, y) ∧
      witness.Constraints ∧ witness.BalancedChannels :=
  Air.Flat.WitnessGeneration.generate_complete completePlan
    ((proverAssumptions_iff n x y ()).mpr ⟨hfib, hp, hn⟩)

end FibonacciWitness
