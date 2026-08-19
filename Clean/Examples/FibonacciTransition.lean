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

/-- The transition component: `window_size : 8 = 2 * 4`. -/
def fibTransitionComponent : Component (F p) where
  circuit := fibStep
  windowRows := 2
  rowWidth := 4
  window_size := by simp [GeneralFormalCircuit.size_eq, fibStep, circuit_norm]
  input_le_rowWidth := by simp [circuit_norm]

/-- A trace of this component is checked on each adjacent pair. -/
example (t : Table (F p)) (h : t.component = fibTransitionComponent) : t.IsTransition := by
  simp [Table.IsTransition, h, fibTransitionComponent]

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

/--
**Target theorem.** The same public statement as `fibonacci_soundness`, reached through the
transition window and the boundary assertions instead of a VM state channel.

Proof plan (steps 4 and 5 of the v2 plan): `tableSoundness_of_soundChannels` turns the
ensemble's channel discipline into every table's `Spec`; for the transition table that is the
adjacent-row relation at every window. The seed assertion pins row 0, the window-induction
library carries `(x_i.val, y_i.val) = fibonacci k` (with `k % p = n_i.val`, and bytes by
`fibonacci_bytes`) along the trace, stuttering where disabled; the final assertion transports
the last row's state to the public input, and
`soundness_of_tableSoundness_and_specConsistencyWithBoundaries` assembles the pieces.
-/
theorem fibonacciTransition_soundness : ∀ (n x y : F p),
    (fibonacciTransitionEnsemble (p:=p)).ensemble.Statement (n, x, y) →
      ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val := by
  sorry

end Clean.Examples.FibonacciTransition
