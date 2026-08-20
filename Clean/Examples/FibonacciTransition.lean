/-
Fibonacci mod 256 as a *transition* AIR component with *boundary assertions* -- the mixed
worked example for the v2 design.

This computes the same public statement as `Clean/Examples/FibonacciVm/Circuit.lean`'s
`fibonacci_soundness`, but the mechanics are those of a classic shift-constraint AIR, with each
device used for exactly what the proof system ships it as:

* the **row-to-row induction** is carried by the transition window (`windowRows = 2`): the
  recurrence is a direct adjacent-row constraint, where `fib8` spends a `FibonacciChannel`
  pull/push pair -- a full logup argument -- per row;
* the **ends of the trace** are pinned by boundary assertions: a first-row assertion pins the
  seed `(enabled, n, x, y) = (1, 0, 0, 1)` and a last-row assertion exports `(n, x, y)` to the
  public input. `fibonacciVm` routes both through verifier channel interactions, which a proof
  system again implements as logup terms rather than as native boundary constraints;
* the **only channel left** is the byte-add lookup -- the one interaction that genuinely is a
  lookup in the deployed system. `bytesComponent`, `add8Component` and their channels are reused
  from the VM example unchanged.

## The `enabled` stutter flag

Backends pad committed traces to a power of two with constraint-satisfying rows, and the
last-row assertion reads the last *committed* row -- whatever it is. So the component must make
"rows past the end" harmless: each row carries a boolean `enabled`, an enabled row advances the
Fibonacci state, and a disabled row freezes it (`next = curr`, including `enabled` itself, so
the flag can never turn back on). Padding rows are then disabled rows, and the frozen state
they carry to the last row is exactly the state at the last enabled row.

## Layout

`Input = Output = Fib8Input` is `(enabled, n, x, y)`, so `size Input = 4` and `main` witnesses
four cells:

    cell 0..3 = input   = row i   = (enabled, n, x, y)
    cell 4..7 = witness = row i+1 = (enabled', n', x', y')

giving `circuit.size = 8 = windowRows * rowWidth` with `windowRows = 2`, `rowWidth = 4`.
-/
import Clean.Examples.FibonacciVm.Circuit

namespace Clean.Examples.FibonacciTransition
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [pGt : Fact (p > 512)]

/--
One Fibonacci-mod-256 step, with the next row as the circuit's **output**.

`main` witnesses the next row's four cells and constrains them against the current row:
disabled rows stutter, enabled rows advance `(n, x, y) ↦ (n + 1, y, (x + y) % 256)`, with the
byte addition checked by a pull from the byte-add lookup channel, gated on the selector so that
disabled rows emit no interactions.

Note what is *not* here: no state channel, and no boundary-marker selectors. The chaining that
`fib8` buys with `FibonacciChannel` is the window itself; the anchoring that `FibonacciNextRow`
attempted with `isBoundary` selectors is the ensemble's boundary assertions below.
-/
def fibStep : GeneralFormalCircuit (F p) Fib8Input Fib8Input where
  name := "fibonacci-transition"
  main | { enabled, n, x, y } => do
    -- selector booleanity, a single-row constraint checked on the window's first row.
    -- Inline rather than `assertBool`: the requirements-channels proof only sees inline
    -- constraints, and it needs booleanity to show the gated pull's multiplicity is lawful.
    assertZero (enabled * (enabled - 1))
    -- the next row, witnessed: these four cells *are* trace row i+1
    let enabled' ← witness (.expr enabled)
    let n' ← witness (.expr (n + enabled))
    let x' ← witness (.expr (x + enabled * (y - x)))
    let y' ← witness (.ite (enabled =? 0) (.expr y) (((x + y).val % 256).toField))
    assertZero (enabled' * (enabled' - 1))
    -- stutter: a disabled row freezes the whole state, so backend padding rows carry the final
    -- state unchanged to the last row; freezing `enabled` itself makes disabling permanent
    assertZero ((1 - enabled) * (enabled' - enabled))
    assertZero ((1 - enabled) * (n' - n))
    assertZero ((1 - enabled) * (x' - x))
    assertZero ((1 - enabled) * (y' - y))
    -- step: an enabled row advances the counter and shifts the pair
    assertZero (enabled * (n' - n - 1))
    assertZero (enabled * (x' - y))
    -- the byte addition y' = (x + y) % 256 is delegated to the add8 lookup, selector-gated
    Add8Channel.pullIf enabled (x, y, y')
    return { enabled := enabled', n := n', x := x', y := y' }

  -- Add8Channel is *not* in `channelsWithRequirements` -- it is a finished lookup channel by
  -- the time this table is added, and the ordered-channel route demands its requirements be
  -- dischargeable from the constraints alone. They are: the selector is boolean, so the pull's
  -- multiplicity is 0 or -1, both lawful.
  requirementsChannelsLawful input i₀ := by
    obtain ⟨enabled, n, x, y⟩ := input
    simp only [circuit_norm, seval, Add8Channel]
    grind

  -- The current row's cells are circuit *inputs*, so completeness cannot pin them; the prover
  -- must know the selector it committed there is boolean.
  ProverAssumptions | { enabled, .. }, _, _ => IsBool enabled
  -- The semantic contract: the adjacent-row transition relation. The byte-add fact arrives
  -- through the channel guarantee, so it is conditional on the inputs being bytes -- the
  -- ensemble-level induction discharges that from the seed.
  Spec
  | { enabled, n, x, y }, next, _ =>
    IsBool enabled ∧ IsBool next.enabled ∧
    (enabled = 0 → next.enabled = 0 ∧ next.n = n ∧ next.x = x ∧ next.y = y) ∧
    (enabled = 1 → next.n = n + 1 ∧ next.x = y ∧
      (x.val < 256 → y.val < 256 → next.y.val = (x.val + y.val) % 256))
  soundness := by
    circuit_proof_start [Add8Channel]
    obtain ⟨hb, hb', hse, hsn, hsx, hsy, htn, htx, hpull⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at hb hb'
    refine ⟨⟨hb, hb', ?_, ?_⟩, ?_⟩
    · -- disabled: the stutter constraints freeze every cell
      rintro rfl
      simp only [sub_zero, one_mul, sub_eq_zero] at hse hsn hsx hsy
      exact ⟨hse, hsn, hsx, hsy⟩
    · -- enabled: counter and shift from the step constraints, the sum from the pull guarantee
      rintro rfl
      simp only [one_mul, sub_sub, sub_eq_zero] at htn htx
      exact ⟨htn, htx, hpull rfl⟩
    · -- residual pull requirement, vacuous for a boolean selector
      intro hne1 hne0
      rcases hb with rfl | rfl
      · exact absurd rfl hne0
      · exact absurd rfl hne1
  completeness := by
    circuit_proof_start [Add8Channel]
    obtain ⟨he, hn, hx, hy⟩ := h_env
    have hp := pGt.out
    rcases h_assumptions with rfl | rfl
    · simp_all
    · simp_all
      intro hx256 hy256
      rw [ZMod.val_add_of_lt (by linarith), Nat.mod_eq_of_lt (by omega)]

/-- `size Fib8Input = 4` and `main` witnesses four cells, so the footprint is exactly two rows. -/
example : (fibStep (p:=p)).size = 8 := by
  simp [GeneralFormalCircuit.size_eq, fibStep, circuit_norm]

/-- The transition component: `window_size : 8 = 2 * 4`, and `input_eq_rowWidth : 4 = 4` -- the
input is the whole current row, as the law demands of a multi-row window. -/
def fibTransitionComponent : Component (F p) where
  circuit := fibStep
  windowRows := 2
  rowWidth := 4
  window_size := by simp [GeneralFormalCircuit.size_eq, fibStep, circuit_norm]
  input_le_rowWidth := by simp [circuit_norm]
  input_eq_rowWidth := by simp [circuit_norm]

/-- A trace of this component is checked on each adjacent pair. -/
example (t : Table (F p)) (h : t.component = fibTransitionComponent) : t.IsTransition := by
  simp [Table.IsTransition, h, fibTransitionComponent]

/-- The circuit's output variable is the canonical next-row layout -- cells `[4, 8)`, the low
cells of the window's second row. This is the per-circuit fact `Table.rowOutput_windowEnv` and
`Table.transition_induction` key on, and it holds definitionally because `main` witnesses the
next row's cells in order and returns them. -/
lemma fibTransitionComponent_output :
    ((fibTransitionComponent (p:=p)).circuit (fibTransitionComponent (p:=p)).rowInputVar).output
        (fibTransitionComponent (p:=p)).rowOffset
      = varFromOffset (fibTransitionComponent (p:=p)).Output
          (fibTransitionComponent (p:=p)).rowWidth := by
  show (fibStep).output (varFromOffset Fib8Input 0) 4 = varFromOffset Fib8Input 4
  simp [fibStep, circuit_norm]

/-! ## Boundary assertions

The two ends of the trace, pinned the way a real AIR pins them: native first/last-row
constraints against public values, not channel messages. Compare `fibonacciVerifier`, which
pushes the seed and pulls the claimed final state on `FibonacciChannel` -- shipped as logup
terms -- and `FibonacciNextRow`, whose selector-chosen boundary rows left the seed reachable
only through channel guarantees and the assembly unbuildable.
-/

/-- First row: the Fibonacci seed. The selector starts enabled, the counter at zero, the pair
at `(0, 1) = fibonacci 0`. -/
def seedAssertion : Boundary.Assertion (F p) fieldTriple Fib8Input where
  row := .first
  constraints | { enabled, n, x, y }, _ => [enabled - 1, n, x, y - 1]
  Spec | { enabled, n, x, y }, _ => enabled = 1 ∧ n = 0 ∧ x = 0 ∧ y = 1
  soundness := by
    intro env input publicIO h
    obtain ⟨enabled, n, x, y⟩ := input
    simp_all [circuit_norm, sub_eq_zero]

/-- Last row: the public input *is* the final row's `(n, x, y)`. Thanks to the stutter rule
this is the state at the last enabled row, whatever padding follows it. -/
def finalAssertion : Boundary.Assertion (F p) fieldTriple Fib8Input where
  row := .last
  constraints | { n, x, y, .. }, (pn, px, py) => [n - pn, x - px, y - py]
  Spec | { n, x, y, .. }, (pn, px, py) => pn = n ∧ px = x ∧ py = y
  soundness := by
    intro env input publicIO h
    obtain ⟨enabled, n, x, y⟩ := input
    obtain ⟨pn, px, py⟩ := publicIO
    simp_all [circuit_norm, sub_eq_zero]

def seedEntry : Boundary.Entry (F p) fieldTriple where
  table := (fibStep (p:=p)).name
  assertion := seedAssertion

def finalEntry : Boundary.Entry (F p) fieldTriple where
  table := (fibStep (p:=p)).name
  assertion := finalAssertion

/-! ## The ensemble

The channel tower is a strict *sub*-tower of `fibonacciEnsemble`'s: bytes and add8, both used
as ordered lookup channels, both finished before the transition component pulls from them. No
`FibonacciChannel`, no `addVm`, and the verifier stays `.empty` -- the state channel's job is
done by the window, and the verifier's by the boundary assertions.
-/

def fibonacciTransitionEnsemble : SoundEnsemble (F p) fieldTriple :=
  SoundEnsemble.empty (F p) fieldTriple
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
  |>.addTable fibTransitionComponent
    (by simp +instances [circuit_norm, fibTransitionComponent, fibStep])
    (by simp [circuit_norm, fibTransitionComponent, fibStep])
    (by
      simp only [SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable_tables,
        SoundEnsemble.empty_tables, List.map_cons, List.map_nil]
      simp [fibTransitionComponent, fibStep, add8Component, add8, bytesComponent, pushBytes])
  |>.addBoundary seedEntry
  |>.addBoundary finalEntry

/-! ## From the step relation to the public specification -/

/-- The per-row invariant carried along the trace: the selector is boolean and the row holds a
genuine Fibonacci pair, with the counter tracking its index mod `p`. -/
def RowInv (row : Fib8Input (F p)) : Prop :=
  IsBool row.enabled ∧
    ∃ k : ℕ, (row.x.val, row.y.val) = fibonacci k ∧ k % p = row.n.val

/-- One window preserves the invariant: a disabled row freezes the state, an enabled row
advances the Fibonacci index by one. The byte bounds that discharge the conditional in
`fibStep.Spec` come from the invariant itself, via `fibonacci_bytes`. -/
lemma rowInv_step {curr next : Fib8Input (F p)} {data : ProverData (F p)}
    (h : (fibStep (p:=p)).Spec curr next data) (hinv : RowInv curr) : RowInv next := by
  obtain ⟨ce, cn, cx, cy⟩ := curr
  obtain ⟨hb, k, hpair, hk⟩ := hinv
  simp only [fibStep] at h
  obtain ⟨-, hb', hfrozen, hadvance⟩ := h
  obtain ⟨hx256, hy256⟩ : cx.val < 256 ∧ cy.val < 256 := fibonacci_bytes hpair
  rcases hb with h0 | h1
  · obtain ⟨he', hn', hx', hy'⟩ := hfrozen h0
    exact ⟨Or.inl he', k, by rw [hx', hy']; exact hpair, by rw [hn']; exact hk⟩
  · obtain ⟨hn', hx', hy'⟩ := hadvance h1
    refine ⟨hb', k + 1, ?_, ?_⟩
    · have hfib : fibonacci (k + 1) = (cy.val, (cx.val + cy.val) % 256) := by
        simp [fibonacci, ← hpair]
      rw [hfib, hx', hy' hx256 hy256]
    · rw [hn', ZMod.val_add, ZMod.val_one, ← hk, Nat.mod_add_mod]

/--
`SpecConsistencyWithBoundaries` for the mixed ensemble.

The two boundary entries resolve, by name uniqueness, to one and the same transition table.
The seed assertion pins its row 0, `Table.transition_induction` carries `RowInv` along the
trace -- the step relation coming from the table's `Spec`, i.e. from `TableSoundness` -- and
the final assertion transports the last row's state to the public input.
-/
theorem fibonacciTransitionEnsemble_specConsistency :
    (fibonacciTransitionEnsemble (p:=p)).SpecConsistencyWithBoundaries
      (fun pub => ∃ k : ℕ, (pub.2.1.val, pub.2.2.val) = fibonacci k ∧ k % p = pub.1.val) := by
  intro witness hspec hboundary
  obtain ⟨-, htables⟩ := hspec
  have hseed := hboundary seedEntry (by simp [circuit_norm, fibonacciTransitionEnsemble])
  have hfinal := hboundary finalEntry (by simp [circuit_norm, fibonacciTransitionEnsemble])
  simp only [Boundary.Entry.Spec] at hseed hfinal
  obtain ⟨t, ht_mem, ht_name, rowL, hrowL, hfinal_spec⟩ := hfinal
  obtain ⟨t', ht'_mem, ht'_name, row0, hrow0, hseed_spec⟩ := hseed
  simp only [seedEntry, finalEntry] at ht_name ht'_name
  -- the two entries name the same table: component names are unique in the witness
  have hnodup : (witness.tables.map fun tb => tb.component.circuit.name).Nodup := by
    have h1 : (witness.tables.map fun tb => tb.component.circuit.name)
        = (fibonacciTransitionEnsemble (p:=p)).tables.map (·.circuit.name) := by
      rw [← witness.tables_map_component, List.map_map]
      rfl
    rw [h1]
    exact (fibonacciTransitionEnsemble (p:=p)).unique_names
  have ht_eq : t' = t :=
    List.inj_on_of_nodup_map hnodup ht'_mem ht_mem (ht'_name.trans ht_name.symm)
  rw [ht_eq] at hrow0
  -- and that table's component is the transition component
  have hc : t.component = fibTransitionComponent (p:=p) := by
    have hmem := witness.mem_component_of_mem ht_mem
    simp only [circuit_norm, fibonacciTransitionEnsemble, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with hc | hc | hc
    · exact hc
    · rw [hc] at ht_name; simp [add8Component, add8, fibStep] at ht_name
    · rw [hc] at ht_name; simp [bytesComponent, pushBytes, fibStep] at ht_name
  -- resolve the boundary rows to indexed rows
  change t.table.head? = some row0 at hrow0
  change t.table.getLast? = some rowL at hrowL
  rw [List.head?_eq_getElem?] at hrow0
  rw [List.getLast?_eq_getElem?] at hrowL
  obtain ⟨hlen0, -⟩ := List.getElem?_eq_some_iff.mp hrow0
  have hrow0! : t.table[0]! = row0 := by
    rw [List.getElem!_eq_getElem?_getD, hrow0]; rfl
  have hrowL! : t.table[t.table.length - 1]! = rowL := by
    rw [List.getElem!_eq_getElem?_getD, hrowL]; rfl
  -- the induction along the trace
  have hind := Table.transition_induction (t := t)
    (by show t.component.windowRows = 2; rw [hc]; rfl)
    (htables t ht_mem)
    (by rw [hc]; exact fibTransitionComponent_output)
    (P := fun i => RowInv (valueFromOffset Fib8Input 0
      (Environment.fromArray t.table[i]! witness.data)))
    (by
      -- base: the seed assertion pins row 0
      rw [hrow0!]
      have hspec0 : seedAssertion.RowSpec row0 witness.publicInput witness.data := hseed_spec
      simp only [Boundary.Assertion.RowSpec, seedAssertion] at hspec0
      obtain ⟨he, hn, hx, hy⟩ := hspec0
      refine ⟨Or.inr he, 0, ?_, ?_⟩
      · rw [hx, hy]; simp [fibonacci, ZMod.val_one]
      · rw [hn]; simp)
    (by
      -- step: the window's Spec is the transition relation
      intro i hi hstep hP
      rw [hc] at hstep
      exact rowInv_step hstep hP)
  -- transport the invariant at the last row through the final assertion
  have hlast := hind (t.table.length - 1) (by omega)
  rw [hrowL!] at hlast
  obtain ⟨-, k, hpair, hk⟩ := hlast
  simp only [Boundary.Assertion.RowSpec, finalEntry, finalAssertion] at hfinal_spec
  obtain ⟨hpn, hpx, hpy⟩ := hfinal_spec
  refine ⟨k, ?_, ?_⟩
  · rw [hpx, hpy]; exact hpair
  · rw [hpn]; exact hk

/-- The mixed ensemble bundled with its public specification, through the boundary-aware
route (`toFormalWithBoundaries`). -/
def fibonacciTransitionFormal : FormalEnsemble (F p) fieldTriple :=
  (fibonacciTransitionEnsemble (p:=p)).toFormalWithBoundaries
    (fun _ => True)
    (fun pub => ∃ k : ℕ, (pub.2.1.val, pub.2.2.val) = fibonacci k ∧ k % p = pub.1.val)
    (by
      intro witness _
      simp only [circuit_norm]
      intro table htable env henv
      have hmem := witness.mem_component_of_mem htable
      simp only [circuit_norm, fibonacciTransitionEnsemble, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with hc | hc | hc <;> rw [hc] <;>
        simp [Component.RowAssumptions, fibTransitionComponent, add8Component, bytesComponent,
          fibStep, add8, pushBytes, circuit_norm])
    fibonacciTransitionEnsemble_specConsistency

/--
**The target theorem.** The same public statement as `fibonacci_soundness`, reached through
the transition window and the boundary assertions instead of a VM state channel: any proof of
the ensemble statement shows the public input is a Fibonacci state.
-/
theorem fibonacciTransition_soundness : ∀ (n x y : F p),
    (fibonacciTransitionEnsemble (p:=p)).ensemble.Statement (n, x, y) →
      ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val := by
  intro n x y statement
  exact (fibonacciTransitionFormal (p:=p)).soundness (n, x, y) trivial statement

/-! ## Non-vacuity

`fibonacciTransition_soundness` is a conditional statement, so it would be vacuously true if
`Ensemble.Statement` had no models at all -- the caveat `falseEnsemble` makes at the end of
`Clean/Examples/FibonacciVm/Circuit.lean`. The way *this* ensemble could fall into that trap is
the one `Boundary.Entry` warns about: an entry naming a component absent from the ensemble is
unsatisfiable rather than vacuous, so a typo in `seedEntry.table` would quietly turn the theorem
above into a tautology. It does not occur here, and the specs the proof transports are refutable
propositions rather than `True` in disguise.
-/

/-- Both boundary entries name a component the ensemble actually carries, so neither
`Entry.Holds` -- nor, with it, `Ensemble.Statement` -- is unsatisfiable by construction. -/
theorem boundary_entries_resolve :
    ∃ component ∈ (fibonacciTransitionEnsemble (p:=p)).tables,
      component.circuit.name = (seedEntry (p:=p)).table ∧
        component.circuit.name = (finalEntry (p:=p)).table := by
  refine ⟨fibTransitionComponent, ?_, rfl, rfl⟩
  simp [fibonacciTransitionEnsemble, circuit_norm]

/-- The step relation genuinely restricts adjacent rows: a disabled row may not turn the
selector back on, so this pair of rows is not related by `fibStep.Spec`. -/
theorem fibStep_spec_not_trivial (data : ProverData (F p)) :
    ¬ (fibStep (p:=p)).Spec ⟨0, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩ data := by
  simp [fibStep]

omit pGt in
/-- The seed assertion rules out rows the transition constraints are perfectly happy with: the
all-zero row steps to itself forever, but it is not a legal first row. -/
theorem seedAssertion_spec_not_trivial (pub : fieldTriple (F p)) :
    ¬ (seedAssertion (p:=p)).Spec ⟨0, 0, 0, 0⟩ pub := by
  simp [seedAssertion]

end Clean.Examples.FibonacciTransition
