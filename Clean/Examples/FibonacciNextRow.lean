/-
Fibonacci as a *transition* AIR component, end to end.

This is the worked contrast to `Clean/Examples/FibonacciVm/Circuit.lean`, whose `fib8` component
carries the running state between rows through `FibonacciChannel` -- a pull of `(n, x, y)` and a
push of `(n+1, y, z)`, costing a full lookup argument for what is really just "the next row
continues this one". Here the recurrence is a direct adjacent-row constraint and that channel
disappears; what remains on the channel is only the *boundary*.

The point of the example is that the component's `Spec` states the recurrence *between adjacent
rows*, which is exactly what no component could express before the next-row-as-output redesign:
under the previous shape `rowInput` read identically from `curr` and from `curr ++ next`, so a
`Spec` could only ever mention `curr`.

Layout. `Input = Output = Row` is `(isBoundary, x, y)`, so `size Input = 3` and `main` witnesses
three cells:

    cell 0 = input   = curr.isBoundary      cell 3 = witness = next.isBoundary
    cell 1 = input   = curr.x               cell 4 = witness = next.x = curr.y
    cell 2 = input   = curr.y               cell 5 = witness = next.y = curr.x + curr.y

giving `circuit.size = 6 = windowRows * rowWidth` with `windowRows = 2`, `rowWidth = 3`.

## Boundaries

`Table.Spec` -- what `weakSoundness` hands you -- quantifies the step relation over every *window*,
and a window exists at `i` only for `i + 2 ≤ length`. So it says nothing whatsoever about which
values the trace starts at: the table `(5,8), (8,13), (13,21)` satisfies every constraint and is
not the Fibonacci sequence. The local relation alone is never enough; it has to be anchored.

`Clean/Table`'s `TableOperation.boundary` is not ported (see `Clean/Air/README.md`), so the anchor
here is a channel, exactly as `Vm.lean` seeds and terminates the VM state channel:

    verifier:   pull (x, y)              -- the public claim about the final pair
                push (0, 1)              -- the seed, a constant
    component:  pullIf isBoundary (x, y)        the current pair
                pushIf b'         (x', y')      the next pair

`isBoundary` is a boolean selector, so the prover chooses which rows join the chain; `b' ===
isBoundary` links the two so a row may only push if it also pulled.

The anchoring runs through the channel's `Guarantees`, not through balance. `FibChannel` carries
"this pair is `(fib k, fib (k+1))` for some `k`". Pulling a message *grants* that fact; pushing
one *owes* it. So `fibStep.soundness` receives the guarantee for the current pair and discharges
it for the next at `k + 1` -- one induction step per boundary row -- while the verifier discharges
the base case, since the seed it pushes is `fibPair 0` literally. The public claim is then the
guarantee the verifier receives from its own pull.

This matters for the ensemble: `Ensemble.SpecConsistency` sees only `witness.Spec`, not channel
balance (see the `TODO` on `Ensemble.SpecConsistency` itself), so a boundary
argument resting on balance alone would not reach the public spec. Routing it through
`Guarantees` -- the same device `FibonacciVm` uses -- keeps it available.
-/
import Clean.Air.OrderedChannel
import Clean.Air.TransitionComponent
import Clean.Gadgets.Boolean

namespace Clean.Examples.FibonacciNextRow
open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- The Fibonacci pair after `n` steps, over `ℕ`: `fibPair n = (fib n, fib (n+1))`. -/
def fibPair : ℕ → (ℕ × ℕ)
  | 0 => (0, 1)
  | n + 1 => let (x, y) := fibPair n; (y, x + y)

/-- The successor equation, in the form the channel guarantee needs. -/
lemma fibPair_succ (k : ℕ) :
    fibPair (k + 1) = ((fibPair k).2, (fibPair k).1 + (fibPair k).2) := by
  simp [fibPair]

/--
The boundary channel. Its `Guarantees` clause carries the whole point: a message on this channel
is a genuine Fibonacci pair, `(fib k, fib (k+1))` for some `k`.

This is the same device `FibonacciVm`'s `FibonacciChannel` uses. Pulling a message *gives* you
the guarantee; pushing one *owes* it. So the component's `soundness` receives "the current pair is
`fibPair k`" and must re-establish "the next pair is `fibPair k'`" -- the induction runs along the
channel, one link per boundary row, and lands in the ensemble spec without needing the balance
argument to be visible to `SpecConsistency`.

The pair is stated in `F p` rather than over `ZMod.val`: unlike `FibonacciVm`, whose rows are
byte-constrained, nothing here bounds the values, so the honest claim is the recurrence in the
field. `fibPair` is cast into `F p` at the use site.
-/
def FibChannel : Channel (F p) fieldPair where
  name := "fibonacci-boundary"
  Guarantees
  | (x, y), _ => ∃ k : ℕ, x = ((fibPair k).1 : F p) ∧ y = ((fibPair k).2 : F p)

/-- A trace row: a boolean boundary selector and the running pair. -/
structure Row (F : Type) where
  isBoundary : F
  x : F
  y : F
deriving ProvableStruct

/--
One Fibonacci step, with the next row as the circuit's **output**.

`main` witnesses the next row's three cells and constrains its pair to `(y, x + y)`. Because those
cells belong to this instantiation, they are pinned by `UsesLocalWitnessesCompleteness`, which is
what makes `completeness` provable. A next row lying outside the circuit's footprint would be
owned by nobody, and no instantiation could pin it.

The boundary interactions are gated on each row's own selector, so the prover chooses which rows
participate; `assertBool` on both selectors is what stops a fractional selector from splitting one
interaction across rows.
-/
def fibStep : GeneralFormalCircuit (F p) Row Row where
  name := "fibonacci-next-row"
  main | { isBoundary, x, y } => do
    assertBool isBoundary
    -- the next row, witnessed: this is the circuit's output, and it *is* trace row i+1
    let b' ← witness (.expr isBoundary)
    let x' ← witness (.expr y)
    let y' ← witness (.expr (x + y))
    x' === y
    y' === x + y
    -- The selectors are linked: a row may only push if it pulled. Without this a row could push
    -- an unearned message, and the chain from the seed would break at that link.
    b' === isBoundary
    -- boundary interactions, gated on the row's selector
    FibChannel.pullIf isBoundary (x, y)
    FibChannel.pushIf b' (x', y')
    return { isBoundary := b', x := x', y := y' }

  channelsWithRequirements := [ FibChannel.toRaw ]
  -- The current row's selector is a circuit *input*, so no constraint of this instantiation can
  -- pin it; `b' === isBoundary` propagates it forward, but row 0's selector is a genuinely free
  -- prover choice. Hence booleanity is an assumption rather than something completeness could
  -- discharge.
  Assumptions | { isBoundary, .. }, _ => IsBool isBoundary
  -- The prover must additionally know the current pair really is a Fibonacci pair when this row
  -- participates in the boundary chain -- that is what it owes for pulling.
  ProverAssumptions
  | { isBoundary, x, y }, _, _ =>
    IsBool isBoundary ∧
      (isBoundary = 1 → ∃ k : ℕ, x = ((fibPair k).1 : F p) ∧ y = ((fibPair k).2 : F p))
  -- The semantic contract: the output pair is the Fibonacci successor of the input pair.
  Spec | { x, y, .. }, out, _ => out.x = y ∧ out.y = x + y
  soundness := by
    circuit_proof_start [FibChannel]
    obtain ⟨hb, h1, h2, hlink, hpull⟩ := h_holds
    refine ⟨⟨h1, h2⟩, ?_, ?_⟩
    · -- the pull requirement is vacuous: `isBoundary` is boolean, so it is `1` or `0`
      intro hne1 hne0
      rcases hb with h | h <;> simp_all
    · -- the push guarantee: `b' = 1` forces `isBoundary = 1`, so the pull fired and gave us `k`
      intro hne1 hne0
      have hbnd : -input_isBoundary = -1 := by
        rcases hb with h | h
        · exact absurd (hlink.trans h) hne0
        · simp [h]
      obtain ⟨k, hkx, hky⟩ := hpull hbnd
      exact ⟨k + 1, by simp [h1, fibPair_succ, hky], by push_cast [h2, fibPair_succ, hkx, hky]; ring⟩
  completeness := by
    circuit_proof_start [FibChannel]
    simp_all [circuit_norm]

/-- `size Row = 3` and `main` witnesses three cells, so the footprint is exactly two rows. -/
example : (fibStep (p:=p)).size = 6 := by
  simp [GeneralFormalCircuit.size_eq, fibStep, circuit_norm]

/--
The transition component: `window_size : 6 = 2 * 3` and `input_eq_rowWidth : 3 = 3` -- the
input is the whole current row, as the law demands of a multi-row window.

Contrast `FibonacciVm.fib8Component`, which is flat (`windowRows = 1`) and needs a channel
interaction *per row* to carry the state. Here the row-to-row structure is carried by the window
itself, and the channel is left holding only the two boundary messages.
-/
def fibComponent : Component (F p) where
  circuit := fibStep
  windowRows := 2
  rowWidth := 3
  window_size := by simp [GeneralFormalCircuit.size_eq, fibStep, circuit_norm]
  input_le_rowWidth := by simp [circuit_norm]
  input_eq_rowWidth := by simp [circuit_norm]

/-- The component's environment spans two rows of width three. -/
example : (fibComponent (p:=p)).envWidth = 6 := rfl

/-- A trace of this component is checked on each adjacent pair. -/
example (t : Table (F p)) (h : t.component = fibComponent) : t.IsTransition := by
  simp [Table.IsTransition, h, fibComponent]

/-! ## From the local step relation to the global sequence

`weakSoundness` gives `Table.Spec`, which is `Component.Spec` at every window -- the step relation
on every adjacent pair, and nothing more. `Table.transition_induction` turns that into a statement
about the whole trace, and the induction is the entire content of a boundary condition: without
`hseed` pinning row 0, the step relation alone is satisfied by any translate of the sequence.

All window plumbing lives in the library. What this example supplies is the one per-component
fact the induction keys on (`fibComponent_output`) and the arithmetic of `fibPair`.
-/

/-- The circuit's output variable is the canonical next-row layout: cells `[3, 6)`, the low cells
of the window's second row. This is the hypothesis `Table.transition_induction` takes rather than
a `Component` field, and it holds definitionally because `main` witnesses the next row's cells in
order and returns them. -/
lemma fibComponent_output :
    ((fibComponent (p:=p)).circuit (fibComponent (p:=p)).rowInputVar).output
        (fibComponent (p:=p)).rowOffset
      = varFromOffset (fibComponent (p:=p)).Output (fibComponent (p:=p)).rowWidth := by
  show (fibStep (p:=p)).output (varFromOffset Row 0) 3 = varFromOffset Row 3
  simp [fibStep, circuit_norm]

/-- Row `i` of the trace, read as the component's typed input. This is exactly the reading
`Table.transition_induction` states its step relation over, so no cell indexing is needed. -/
def rowAt (t : Table (F p)) (data : ProverData (F p)) (i : ℕ) : Row (F p) :=
  valueFromOffset Row 0 (Environment.fromArray t.table[i]! data)

/-- The running pair at row `i`. -/
def pairAt (t : Table (F p)) (data : ProverData (F p)) (i : ℕ) : F p × F p :=
  ((rowAt t data i).x, (rowAt t data i).y)

/-- One window preserves the closed form: the component's `Spec` says the next row's pair is the
Fibonacci successor of the current one, and `fibPair_succ` is the same equation over `ℕ`. -/
lemma fibPair_step {curr next : Row (F p)} {data : ProverData (F p)} {k : ℕ}
    (hstep : (fibStep (p:=p)).Spec curr next data)
    (hcurr : (curr.x, curr.y) = (((fibPair k).1 : F p), ((fibPair k).2 : F p))) :
    (next.x, next.y) = (((fibPair (k + 1)).1 : F p), ((fibPair (k + 1)).2 : F p)) := by
  obtain ⟨b, x, y⟩ := curr
  simp only [fibStep] at hstep
  obtain ⟨hx, hy⟩ := hstep
  simp only [Prod.mk.injEq] at hcurr ⊢
  refine ⟨by rw [hx, hcurr.2, fibPair_succ], ?_⟩
  rw [hy, hcurr.1, hcurr.2, fibPair_succ]
  push_cast
  ring

/--
The trace is the Fibonacci sequence, in closed form.

Row `i` holds `(fib i, fib (i+1))` for every row of the trace, given the step relation on every
window and the seed on row 0.
-/
theorem pairAt_eq_fibPair {t : Table (F p)} (hc : t.component = fibComponent)
    {data : ProverData (F p)} (hspec : t.Spec data)
    (hseed : pairAt t data 0 = (((fibPair 0).1 : F p), ((fibPair 0).2 : F p)))
    {i : ℕ} (hi : i < t.table.length) :
    pairAt t data i = (((fibPair i).1 : F p), ((fibPair i).2 : F p)) := by
  refine Table.transition_induction (t := t)
    (by show t.component.windowRows = 2; rw [hc]; rfl)
    hspec (by rw [hc]; exact fibComponent_output)
    (P := fun i => pairAt t data i = (((fibPair i).1 : F p), ((fibPair i).2 : F p)))
    hseed (fun j _ hstep hj => ?_) i hi
  rw [hc] at hstep
  exact fibPair_step hstep hj

/-! ## The boundary verifier

The verifier is what anchors the trace, and it does so through `Guarantees` rather than balance.

It *pulls* the pair it claims is the final one: pulling grants the channel guarantee, so the
verifier receives "this pair is `(fib k, fib (k+1))` for some `k`" -- which is precisely the
public spec. It then *pushes* the seed, and pushing owes the guarantee, discharged immediately
because `(0, 1)` is `fibPair 0` by definition.

That is the base case of the induction; `fibStep.soundness` supplies the step, re-establishing
the guarantee at `k + 1` for each boundary row. Balance still has to hold for the messages to
match up, but no part of the *spec* argument depends on reasoning about balance directly.
-/
def fibVerifier : Verifier.Program (F p) fieldPair where
  main | (x, y) => do
    -- the claimed final pair: the verifier *pulls* it, so it receives the guarantee that the
    -- pair is a genuine Fibonacci pair -- which is exactly the public claim
    Verifier.pull FibChannel (x, y)
    -- the seed: the verifier *pushes* it, so it owes the guarantee, discharged at `k = 0`
    Verifier.push FibChannel (0, 1)
  Spec | (x, y), _ => ∃ k : ℕ, x = ((fibPair k).1 : F p) ∧ y = ((fibPair k).2 : F p)
  soundness := by
    intro env guarantees
    simp only [circuit_norm, Operations.FullGuarantees, FibChannel,
      AbstractInteraction.Guarantees, Channel.toRaw, explicit_provable_type] at guarantees ⊢
    exact guarantees


/-! ## Assembling the ensemble -- blocked

The component, its table theorem, and the verifier are all proved. Wiring them into a
`SoundEnsemble` is *not* currently possible, and the obstruction is worth stating precisely
because it is a genuine gap in the framework rather than a defect of this example.

`fibStep` both guarantees and requires `FibChannel` -- it pulls the current pair and pushes the
next one. That cycle is exactly what the ordered-channel discipline forbids: `SoundEnsemble.addTable`
requires `circuit.channelsWithGuarantees ⊆ finished`, while `addFinishedChannel` may only close a
channel nothing later requires. A channel a table both pulls and pushes satisfies neither.

The framework's answer to that cycle is `Ensemble.addVm` / `VmTables`, which is built for exactly
this shape -- `FibonacciVm` closes the identical loop on `FibonacciChannel`. But `VmTables` carries

    tables_windowRows : tables.Forall (fun table => table.windowRows = 1)

(`VmTables.tables_windowRows`), and this component has `windowRows = 2`. That field is not
incidental: the VM soundness argument reads a table's environments as one-per-row throughout, at
every use of `vmTables_windowRows_eq_one`.

So a transition component cannot presently reach a public spec through *either* route: the
ordered-channel route rejects the cycle, and the VM route rejects the window. Closing this means
generalizing the VM path to multi-row windows -- `vmPulls`/`vmPushes` would range over window
environments rather than row environments -- which is a substantially larger change than this
example, and is left as follow-up work.

What is proved here stops one step short of that: `pairAt_eq_fibPair` gives the closed form for
the whole trace from the step relation plus a seed, and `fibStep.soundness` carries the seed along
the channel. Only the final hand-off to `Ensemble.Spec` is missing.

`Clean/Examples/FibonacciTransition.lean` is the same window machinery taken all the way to a
public theorem, by anchoring the trace with boundary assertions instead of a channel cycle. This
file is kept as the record of the gap: a transition component whose *only* channel is a
pull/push cycle fits neither route.
-/

end Clean.Examples.FibonacciNextRow
