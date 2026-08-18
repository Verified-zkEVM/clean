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
balance (there is a `TODO` to that effect at `Clean/Air/FlatEnsemble.lean:363`), so a boundary
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
what makes `completeness` provable -- the defect the adversarial review found in the previous
design, where the next row was owned by nobody.

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
The transition component: `window_size : 6 = 2 * 3` and `input_le_rowWidth : 3 ≤ 3`.

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

/-- The component's environment spans two rows of width three. -/
example : (fibComponent (p:=p)).envWidth = 6 := rfl

/-- A trace of this component is checked on each adjacent pair. -/
example (t : Table (F p)) (h : t.component = fibComponent) : t.IsTransition := by
  simp [Table.IsTransition, h, fibComponent]

/-! ## From the local step relation to the global sequence

`weakSoundness` gives `Table.Spec`, which is `Component.Spec` at every window -- the step relation
on every adjacent pair, and nothing more. The theorems below turn that into a statement about the
whole trace. The induction is the entire content of a boundary condition: without `hseed` pinning
row 0, `steps` alone is satisfied by any translate of the sequence.
-/

/-- Reading a row's pair. -/
def pairAt (t : Table (F p)) (i : ℕ) : F p × F p :=
  ((t.table[i]!)[1]!, (t.table[i]!)[2]!)

/--
The step relation, extracted from the component's `Spec` at the window starting at `i`.

This is the bridge: `Component.Spec` is stated about `rowInput`/`rowOutput` of an environment,
and this restates it as a relation between two *indexed rows* of the trace, which is the form
induction can consume.
-/
lemma rowInput_windowEnv {t : Table (F p)} (hc : t.component = fibComponent)
    {data : ProverData (F p)} {i : ℕ} (hi : i ∈ t.windows) :
    (fibComponent (p:=p)).rowInput (t.windowEnv i data) =
      { isBoundary := (t.table[i]!)[0]!, x := (pairAt t i).1, y := (pairAt t i).2 } := by
  show valueFromOffset Row 0 (t.windowEnv i data) = _
  have hw := Table.valueFromOffset_windowEnv (t:=t) hi data
  rw [hc] at hw
  rw [show valueFromOffset Row 0 (t.windowEnv i data)
        = valueFromOffset (fibComponent (p:=p)).Input 0 (t.windowEnv i data) from rfl, hw]
  -- the row has width 3, so all three reads are in range
  have hsize : (t.table[i]'(t.lt_length_of_mem_windows hi)).size = 3 := by
    have := t.uniform_width _ (List.getElem_mem (t.lt_length_of_mem_windows hi))
    rw [this, Component.width, hc]
    rfl
  show fromElements (Vector.mapRange (size Row) fun j => _) = _
  simp [pairAt, explicit_provable_type, circuit_norm,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (t.lt_length_of_mem_windows hi),
    hsize]

lemma rowOutput_windowEnv {t : Table (F p)} (hc : t.component = fibComponent)
    {data : ProverData (F p)} {i : ℕ} (hi : i ∈ t.windows) :
    ((fibComponent (p:=p)).rowOutput (t.windowEnv i data)).x = (pairAt t (i + 1)).1 ∧
    ((fibComponent (p:=p)).rowOutput (t.windowEnv i data)).y = (pairAt t (i + 1)).2 := by
  have htr : t.IsTransition := by simp [Table.IsTransition, hc, fibComponent]
  -- the window is `curr ++ next`, and the output cells 3,4,5 land in `next`
  have henv : t.windowEnv i data = Transition.pairEnv t.table[i]! t.table[i + 1]! data := by
    simp only [Table.windowEnv, Transition.pairEnv, Table.windowRow_eq_pair htr]
  -- `curr` has width 3, so cell `3 + j` of the window is cell `j` of `next`
  have hcurr : (t.table[i]!).size = 3 := by
    have hlt := t.lt_length_of_mem_windows hi
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    have := t.uniform_width _ (List.getElem_mem hlt)
    rw [this, Component.width, hc]
    rfl
  rw [henv]
  -- name the output var concretely, so the `.output` projection reduces before simp runs
  have hout : (fibComponent (p:=p)).rowOutput (Transition.pairEnv t.table[i]! t.table[i + 1]! data)
      = eval (Transition.pairEnv t.table[i]! t.table[i + 1]! data)
          ((fibStep (p:=p)).output (varFromOffset Row 0) 3) := rfl
  rw [hout]
  -- `hcurr` in the form the append lemma needs
  have hsz : (t.table[i]?.getD default : Array (F p)).size = 3 := by
    rw [← hcurr, List.getElem!_eq_getElem?_getD]
  constructor <;>
    simp [fibStep, pairAt, Transition.pairEnv, explicit_provable_type, circuit_norm,
      Array.getElem?_append_right, hsz, Array.getElem!_eq_getD] <;> rfl

lemma pairAt_succ_of_spec {t : Table (F p)} (hc : t.component = fibComponent)
    {data : ProverData (F p)} (hspec : RowEnvs.Spec (F:=F p) t data)
    {i : ℕ} (hi : i ∈ t.windows) :
    pairAt t (i + 1) = ((pairAt t i).2, (pairAt t i).1 + (pairAt t i).2) := by
  have h := hspec _ (Table.mem_envs_of_mem_windows hi (data:=data))
  rw [Table.component_eq, hc] at h
  unfold Component.Spec at h
  obtain ⟨hx, hy⟩ := rowOutput_windowEnv (p:=p) hc (data:=data) hi
  -- rewrite the *reads* first: unfolding `fibComponent` would destroy these patterns
  rw [rowInput_windowEnv hc hi] at h
  -- unfold only the circuit's `Spec`, leaving `rowOutput`'s `fibComponent` intact so that
  -- `hx`/`hy` still match syntactically
  rw [show (fibComponent (p:=p)).circuit = fibStep from rfl] at h
  simp only [fibStep] at h
  rw [hx, hy] at h
  exact Prod.ext h.1 h.2

/--
The trace is the Fibonacci sequence, in closed form.

Row `i` holds `(fib i, fib (i+1))` for every row of the trace, given the step relation on every
window and the seed on row 0.
-/
theorem pairAt_eq_fibPair {t : Table (F p)} (hc : t.component = fibComponent)
    {data : ProverData (F p)} (hspec : RowEnvs.Spec (F:=F p) t data)
    (hseed : pairAt t 0 = (((fibPair 0).1 : F p), ((fibPair 0).2 : F p)))
    {i : ℕ} (hi : i < t.table.length) :
    pairAt t i = (((fibPair i).1 : F p), ((fibPair i).2 : F p)) := by
  induction i with
  | zero => simpa using hseed
  | succ n ih =>
    -- row `n + 1` exists, so the window at `n` exists (it needs rows `n` and `n + 1`)
    have hwin : n ∈ t.windows := by
      rw [Table.mem_windows_iff, hc]
      simp only [fibComponent]
      omega
    rw [pairAt_succ_of_spec hc hspec hwin, ih (by omega)]
    simp [fibPair]

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

(`Clean/Air/Vm.lean:61`), and this component has `windowRows = 2`. That field is not incidental:
the VM soundness argument reads a table's environments as one-per-row throughout
(`Vm.lean:492`, `:559`, `:967`, all via `vmTables_windowRows_eq_one`).

So a transition component cannot presently reach a public spec through *either* route: the
ordered-channel route rejects the cycle, and the VM route rejects the window. Closing this means
generalizing the VM path to multi-row windows -- `vmPulls`/`vmPushes` would range over window
environments rather than row environments -- which is a substantially larger change than this
example, and is left as follow-up work.

What is proved here stops one step short of that: `pairAt_eq_fibPair` gives the closed form for
the whole trace from the step relation plus a seed, and `fibStep.soundness` carries the seed along
the channel. Only the final hand-off to `Ensemble.Spec` is missing.
-/

end Clean.Examples.FibonacciNextRow
