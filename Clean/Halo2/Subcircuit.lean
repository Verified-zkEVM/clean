import Clean.Halo2.Formal
import Clean.Halo2.Lemmas

/-!
# Subcircuit composition: the call-boundary opacity contract

A subcircuit call appends the child's raw op list; the child does not
store its `Spec`. In a parent proof the child appears as one folded
`(child.call config offset input).operations self` chunk (region level) or
`(child.call config input).operations i₀` (layouter level). This file establishes the *call
boundary* — the opaque `call` term that keeps the child folded — and the two accessor lemmas
plus the `CoeFun` instances that let a parent write `child config offset input` and peel its own
binds around the folded chunk.

## The opaque call boundary (why the chunk stays folded)

Plain `circuit_norm` does not unfold `RegionCircuit.operations` / `Circuit.operations` on a
`call` term, so a child chunk stays folded automatically: the parent's own binds decompose via
`operations_bind` → `++` and `RegionOperations.constraints_append` / the layouter
`constraints_region` lemmas split the parent conjunction *around* the folded call term, isolating
it as a clean conjunct. There is no `call_operations` computation lemma (that footgun cracks
`call` open and lets the accessor lemmas reach and shred the child's `synthesize` ops).

## How a parent consumes a folded chunk

The consumption mechanism is the `subcircuit_rw` engine (`Clean/Halo2/Tactics/SubcircuitRw.lean`):
a polarity-aware monotone rewriter that, keying on this same opaque `call` boundary (its own
`isDefEq` matching, not a discrimination tree), weakens a positive-position chunk in a hypothesis
to the child's `EnvAssumptions → Assumptions → Spec` (soundness, `subcircuit_rw at h`) or
strengthens a positive-position goal chunk to the child's precondition bundle while introducing the
derived `Spec ∧ ProverSpec` statement (completeness, `subcircuit_rw`). See
that file and `Clean/Halo2/subcircuit-engine-design.md` for the full design.

### History (v1: the absorption iffs)

The engine replaced an earlier "absorption iff" mechanism. Since `chunk → X` is an implication
(not an `Eq`/`Iff`) that `simp`/`rw` cannot use, v1 rewrote each chunk via the absorption iff
`chunk ↔ chunk ∧ X` (soundness) / `chunk ↔ chunk ∨ precondition` (completeness), hiding the
surviving raw chunk behind an opaque `SubcircuitConstraints` marker so the rewrite fired once.
That approach needed generic + concrete-`α` + bare-`place`/`env` restatements of every iff (its
discrimination-tree key missed the post-`circuit_norm` and loop-lemma spellings), and left marker /
`∨`-side residues for the consumer to discard. The engine subsumes all of it — one tactic, no
restatement families, no residue — so the iff families were retired. This docstring is the only
remaining record of them.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {CI Cfg : Type} {Input Output Witness : TypeMap}

section
variable [CircuitType Input] [CircuitType Output]

/-- `output` of a layouter `call` (the child's output) — a `circuit_norm` accessor lemma. -/
@[circuit_norm, keygen_norm]
theorem FormalCircuit.output_call (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (self.call config input).output i = self.output config input i :=
  -- no longer `rfl`: the full `call` triple is opaque, so project the `output` component
  -- out of the packed `call_eq`
  congrArg (fun t => t.1) (self.call_eq config input i)

/-- `output` of a region-level `call` (the child's elaborated output) — the region-level
analogue of `FormalCircuit.output_call`. `@[circuit_norm]`. -/
@[circuit_norm, keygen_norm]
theorem FormalRegionCircuit.output_call {CI Cfg : Type}
    (self : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (input : Var Input F) (region : RegionIndex) :
    (self.call config offset input).output region
      = self.output config offset input region :=
  congrArg (fun t => t.1) (self.call_eq config offset input region)

/-- Concrete-`α` restatement of `FormalRegionCircuit.output_call` (the `RegionCircuit.output`
element type is rewritten to the concrete `Output (AssignedCell F)` by `var_of_provableType`;
the generic lemma's discr-tree key then misses under `simp`), the region-level analogue of
`FormalCircuit.output_call'`.

`@[circuit_norm]` like the layouter `output_call'` (an earlier exclusion protected v1-era
by-hand `rw [FormalRegionCircuit.output_call]` targets; the corpus no longer depends on it). -/
@[circuit_norm, keygen_norm]
theorem FormalRegionCircuit.output_call' {Output : TypeMap} [ProvableType Output] {CI Cfg : Type}
    (self : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (input : Var Input F) (region : RegionIndex) :
    (@RegionCircuit.output F _ (Output (AssignedCell F)) (self.call config offset input) region)
      = self.output config offset input region :=
  FormalRegionCircuit.output_call self config offset input region

/-- `nextRegionIndex` of a layouter `call`, spelled as the append offset
`Operations.regionCount ((self.call …).operations i)` — so that when a parent's
`operations_bind` splits into `++` and `constraints_append` threads its offset, a *second*
subcircuit call's index matches the append form and the engine still fires on it. Keeping
`call.operations` folded (the opaque boundary), this bridges the two spellings of "how many
regions the first call consumed". `@[circuit_norm]`. -/
@[circuit_norm]
theorem FormalCircuit.nextRegionIndex_call (self : FormalCircuit F CI Cfg Input Output)
    (config : Cfg) (input : Var Input F) (i : RegionIndex) :
    (self.call config input).nextRegionIndex i
      = i + Operations.regionCount ((self.call config input).operations i) := by
  -- the `nextRegionIndex` component is opaque now: project it out of `call_eq` first
  have hnext : (self.call config input).nextRegionIndex i = i + self.regionCount input := by
    show (self.call config input i).2.2 = i + self.regionCount input
    rw [self.call_eq config input i]
  rw [hnext]
  congr 1
  -- `regionCount = ((synthesize …).operations i).regionCount` (elaborated metadata), and
  -- `call_operations` opens the chunk to exactly the `synthesize` ops.
  rw [FormalCircuit.regionCount, self.elaborated.regionCount_eq config input i,
    FormalCircuit.call_operations]

/-- Concrete-`α` restatement of `output_call` (the `Circuit.output`/`operations` element type
is rewritten to the concrete `Output (AssignedCell F)` by `var_of_provableType`; the generic
lemma's discr-tree key then misses under `simp`). -/
@[circuit_norm, keygen_norm]
theorem FormalCircuit.output_call' {Output : TypeMap} [ProvableType Output]
    (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (@Circuit.output F _ (Output (AssignedCell F)) (self.call config input) i)
      = self.output config input i :=
  FormalCircuit.output_call self config input i

/-- Witness-side toFormal boundary crossing: `ExtendsWitnesses` of a `toFormal`-lifted
call's layouter chunk is the underlying region circuit's witness condition (the lifted
wrapper region contributes nothing else). Completeness proofs open lifted chunks with
this to reach per-cell witness equations. NOT `@[circuit_norm]` — chunks open only
deliberately. -/
theorem FormalRegionCircuit.toFormal_call_extendsWitnesses {CI Cfg : Type}
    (b : FormalRegionCircuit F CI Cfg Input Output) (name : String) (cfg : Cfg)
    (inp : Var Input F) (i : RegionIndex) (place : RegionIndex → ℕ)
    (env : ProverEnvironment F) :
    ExtendsWitnesses place env (((b.toFormal name).call cfg inp).operations i) i
      = RegionOperations.ExtendsWitnesses place i env
          ((b.synthesize cfg 0 inp).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [FormalRegionCircuit.toFormal, Circuit.operations, assignRegion,
    ExtendsWitnesses, and_true]
  rfl

/-- Concrete-`α` restatement of `nextRegionIndex_call`, needed for the same reason: inside a
parent's `operations_bind`-produced chunk the `Circuit.nextRegionIndex` element type is the
concrete `Output (AssignedCell F)`, so the generic lemma's key misses under `simp`. -/
@[circuit_norm]
theorem FormalCircuit.nextRegionIndex_call' {Output : TypeMap} [ProvableType Output]
    (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (@Circuit.nextRegionIndex F _ (Output (AssignedCell F)) (self.call config input) i)
      = i + Operations.regionCount
          (@Circuit.operations F _ (Output (AssignedCell F)) (self.call config input) i) :=
  FormalCircuit.nextRegionIndex_call self config input i

end

/-! ## `foldCall` — the serial layouter fold over a formal-circuit family

The layouter-level loop combinator (the `RegionCircuit.foldRange` analogue): round `m`
calls `c m` on the accumulated input var and feeds `toInput` of its output to round
`m + 1`. The accumulator var and base region index at each round are the **closed form**
`foldState` (the ConstantOutput analogue — the maintainer rule from `Loops.lean`), so the
split lemmas turn `Constraints` / `ExtendsWitnesses` of the whole fold into
`∀ i : Fin m, <round i's folded call chunk at its closed-form input/index>` — the shape
`subcircuit_rw` (or the manual `layouter_*_leaf` applications) consume per round. -/

section
variable [CircuitType Input] [CircuitType Output]

/-- A layouter `call` chunk counts exactly the child's regions. -/
theorem FormalCircuit.call_regionCount (self : FormalCircuit F CI Cfg Input Output)
    (config : Cfg) (input : Var Input F) (i : RegionIndex) :
    Operations.regionCount ((self.call config input).operations i)
      = self.regionCount input := by
  rw [FormalCircuit.call_operations]
  exact (self.elaborated.regionCount_eq config input i).symm

/-- Concrete-`α` restatement of `call_regionCount` (same discr-tree-key reason as
`output_call'`); the `ElaboratedCircuit.regionCount_eq` default tactic uses both. -/
theorem FormalCircuit.call_regionCount' {Output : TypeMap} [ProvableType Output]
    {CI Cfg : Type} (self : FormalCircuit F CI Cfg Input Output)
    (config : Cfg) (input : Var Input F) (i : RegionIndex) :
    Operations.regionCount
        (@Circuit.operations F _ (Output (AssignedCell F)) (self.call config input) i)
      = self.regionCount input :=
  FormalCircuit.call_regionCount self config input i

/-! ### Region-count folding (`circuit_norm` simproc)

One simproc folds `Operations.regionCount ((child.call cfg inp).operations j)` to the
child's literal region count, for EVERY layouter bundle (named, parameter-applied, or
`toFormal`-lifted) and in every α-spelling — it does its own matching, so no
per-bundle simp lemma and no discrimination-tree-key duplication. Fires only when the
elaborated metadata `child.regionCount inp` whnf-reduces to a closed `Nat` literal
(a symbolic count stays untouched); the proof is the generic `call_regionCount`, with
the kernel closing the metadata-to-literal gap definitionally — the same obligation
the historical hand-written `rw [FormalCircuit.call_regionCount]; rfl` wrappers
discharged. -/

/-- Per-bundle region-count bridge registry: bundle head constant ↦ proven
`<base>_call_regionCount` lemma. Populated by `derive_contract_bridges` (and the
`ElaboratedCircuit` autogenerator); consumed by `foldCallRegionCount`, which
instantiates the registered lemma by unification instead of re-deriving the fold —
per-use cost drops to a lookup + `isDefEq`, and the kernel checks each bundle's
metadata defeq ONCE (at derive time) instead of at every fold site. -/
initialize regionCountBridges :
    Lean.SimplePersistentEnvExtension (Lean.Name × Lean.Name)
      (Lean.NameMap Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, v) => m.insert k v
    addImportedFn := fun as => as.foldl (fun m es => es.foldl (fun m (k, v) => m.insert k v) m) {}
  }

open Lean in
/-- The registry key for a bundle term: its head constant — except for
`toFormal`-lifted bundles, where every lift shares the `toFormal` head, so the key is
the lifted CHILD's head constant (else all lifts would collide on one entry). -/
def bundleRegistryKey (self : Expr) : Option Name := do
  let .const head _ := self.getAppFn | none
  if head == ``Halo2.FormalRegionCircuit.toFormal then
    let args := self.getAppArgs
    -- toFormal (child) (name := …): child is the second-to-last argument
    let some child := args[args.size - 2]? | none
    let .const childHead _ := child.getAppFn | none
    return childHead
  return head

open Lean Meta Simp in
/-- Instantiate a registered per-bundle bridge against the matched term `e`:
metavarize the lemma's binders, unify its LHS with `e`, return the instantiated
literal + proof. `none` if the lemma does not unify (e.g. a different instantiation
shape) — the caller falls back to the generic whnf route. -/
def tryRegisteredBridge (lemmaName : Name) (e : Expr) : MetaM (Option Step) := do
  let some info := (← getEnv).find? lemmaName | return none
  let (mvars, _, concl) ← forallMetaTelescope info.type
  let some (_, lhs, rhs) := concl.eq? | return none
  unless ← isDefEq lhs e do return none
  let proof ← instantiateMVars (mkAppN (mkConst lemmaName) mvars)
  let rhs ← instantiateMVars rhs
  if proof.hasExprMVar || rhs.hasExprMVar then return none
  return some (.visit { expr := rhs, proof? := some proof })

open Lean Meta Simp in
/-- See the section docstring. -/
def foldCallRegionCountProc : Simproc := fun e => do
  -- e = Operations.regionCount ops
  unless e.isAppOfArity ``Halo2.Operations.regionCount 2 do return .continue
  let ops := e.appArg!
  -- ops = Circuit.operations circuit j (5 args: F, inst, α, circuit, j)
  unless ops.isAppOfArity ``Halo2.Circuit.operations 5 do return .continue
  let circuit := ops.getArg! 3
  let j := ops.getArg! 4
  -- circuit = FormalCircuit.call self config input (last three explicit args)
  unless circuit.getAppFn.isConstOf ``Halo2.FormalCircuit.call do return .continue
  let cargs := circuit.getAppArgs
  unless cargs.size ≥ 3 do return .continue
  -- registered-bridge fast path: amortized per-bundle proof, no whnf, no fresh defeq
  if let some key := bundleRegistryKey cargs[cargs.size - 3]! then
    if let some lemmaName := (regionCountBridges.getState (← getEnv)).find? key then
      if let some step ← tryRegisteredBridge lemmaName e then
        return step
  try
    let count ← withTransparency .default
      (whnf (← mkAppM ``Halo2.FormalCircuit.regionCount
        #[cargs[cargs.size - 3]!, cargs[cargs.size - 1]!]))
    -- fold only to CLOSED counts (`evalNat`: raw/`OfNat`/`One.one` shapes all count);
    -- a symbolic/stuck metadata term stays put
    let some _ ← (Meta.evalNat count).run | return .continue
    -- proof built only on a successful fold (cold path), so `mkAppM` is fine here —
    -- `call_regionCount`'s implicit telescope is ordered differently from `call`'s
    let proof ← mkAppM ``Halo2.FormalCircuit.call_regionCount
      #[cargs[cargs.size - 3]!, cargs[cargs.size - 2]!, cargs[cargs.size - 1]!, j]
    -- the generic lemma's type is the abstract-α spelling with the unreduced metadata
    -- RHS; re-type it at (e = count) — defeq on both sides, kernel-checked
    let proof ← mkExpectedTypeHint proof (← mkEq e count)
    return .visit { expr := count, proof? := some proof }
  catch _ => return .continue

simproc foldCallRegionCount (Halo2.Operations.regionCount _) := foldCallRegionCountProc
attribute [circuit_norm] foldCallRegionCount

open Lean Meta Simp in
/-- Companion to `foldCallRegionCount` for the METADATA spelling: folds
`FormalCircuit.regionCount self input` to its literal (after
`call_regionCount`-style rewrites leave the projection form, e.g. in the
`ElaboratedCircuit.regionCount_eq` default tactic). Same closed-literal guard; the
kernel closes the projection defeq. -/
def foldRegionCountMetaProc : Simproc := fun e => do
  unless e.isAppOf ``Halo2.FormalCircuit.regionCount do return .continue
  try
    let count ← withTransparency .default (whnf e)
    let some _ ← (Meta.evalNat count).run | return .continue
    if count == e then return .continue
    let proof ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e count)
    return .visit { expr := count, proof? := some proof }
  catch _ => return .continue

simproc foldRegionCountMeta (Halo2.FormalCircuit.regionCount _ _) := foldRegionCountMetaProc
attribute [circuit_norm] foldRegionCountMeta

/-- The closed-form fold state: the accumulator input var and the base region index
*entering* round `m`. -/
def FormalCircuit.foldState (c : ℕ → FormalCircuit F CI Cfg Input Output)
    (toInput : Var Output F → Var Input F) (config : Cfg) (init : Var Input F)
    (i₀ : RegionIndex) : ℕ → Var Input F × RegionIndex
  | 0 => (init, i₀)
  | m + 1 =>
    let s := FormalCircuit.foldState c toInput config init i₀ m
    (toInput ((c m).output config s.1 s.2), s.2 + (c m).regionCount s.1)

/-- The serial fold of layouter calls; returns the final accumulated input var. -/
def FormalCircuit.foldCall (c : ℕ → FormalCircuit F CI Cfg Input Output)
    (toInput : Var Output F → Var Input F) (config : Cfg) (init : Var Input F) :
    ℕ → Circuit F (Var Input F)
  | 0 => pure init
  | m + 1 => do
    let acc ← FormalCircuit.foldCall c toInput config init m
    let out ← (c m).call config acc
    pure (toInput out)

/-- The fold's operations: round `i`'s folded call chunk at its closed-form state. -/
def FormalCircuit.foldOps (c : ℕ → FormalCircuit F CI Cfg Input Output)
    (toInput : Var Output F → Var Input F) (config : Cfg) (init : Var Input F)
    (i₀ : RegionIndex) : ℕ → Operations F
  | 0 => []
  | m + 1 =>
    FormalCircuit.foldOps c toInput config init i₀ m
      ++ ((c m).call config (FormalCircuit.foldState c toInput config init i₀ m).1).operations
        (FormalCircuit.foldState c toInput config init i₀ m).2

/-- Reduced synthesis summary of a serial circuit fold, composed from the
already-reduced summaries of its children. -/
def FormalCircuit.foldSynthesisSummary
    (c : ℕ → FormalCircuit F CI Cfg Input Output)
    (toInput : Var Output F → Var Input F) (config : Cfg) (init : Var Input F)
    (i₀ : RegionIndex) : ℕ → FloorPlanner.SynthesisSummary
  | 0 => {}
  | m + 1 =>
    (FormalCircuit.foldSynthesisSummary c toInput config init i₀ m).combine
      ((c m).elaborated.synthesisSummary config
        (FormalCircuit.foldState c toInput config init i₀ m).1
        (FormalCircuit.foldState c toInput config init i₀ m).2)

variable (c : ℕ → FormalCircuit F CI Cfg Input Output)
  (toInput : Var Output F → Var Input F) (config : Cfg) (init : Var Input F)
  (i₀ : RegionIndex)

/-- The fold's run, in closed form: output/ops/next are `foldState`/`foldOps`. -/
theorem FormalCircuit.foldCall_run (m : ℕ) :
    FormalCircuit.foldCall c toInput config init m i₀
      = ((FormalCircuit.foldState c toInput config init i₀ m).1,
         FormalCircuit.foldOps c toInput config init i₀ m,
         (FormalCircuit.foldState c toInput config init i₀ m).2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (FormalCircuit.foldCall c toInput config init m >>= fun acc =>
      (c m).call config acc >>= fun out => pure (toInput out)) i₀ = _
    -- `call`'s triple shape is opaque now: open the round-`m` call application with
    -- `call_eq` (and reconcile the ops spelling via `call_operations`) rather than `rfl`
    simp only [Bind.bind, ih, FormalCircuit.foldOps, FormalCircuit.foldState,
      FormalCircuit.call_eq, FormalCircuit.call_operations, List.append_nil]

theorem FormalCircuit.foldCall_operations (m : ℕ) :
    (FormalCircuit.foldCall c toInput config init m).operations i₀
      = FormalCircuit.foldOps c toInput config init i₀ m := by
  rw [Circuit.operations, FormalCircuit.foldCall_run]

@[synthesis_summary_norm]
theorem FormalCircuit.foldSynthesisSummary_eq (m : ℕ) :
    FormalCircuit.foldSynthesisSummary c toInput config init i₀ m =
      FloorPlanner.synthesisSummary
        (FormalCircuit.foldOps c toInput config init i₀ m) := by
  induction m with
  | zero =>
      simp only [FormalCircuit.foldSynthesisSummary, FormalCircuit.foldOps,
        FloorPlanner.synthesisSummary_nil]
  | succ m inductionHypothesis =>
      rw [FormalCircuit.foldSynthesisSummary, FormalCircuit.foldOps,
        FloorPlanner.synthesisSummary_append, FormalCircuit.call_synthesisSummary,
        inductionHypothesis]

/-- A fold whose children have one common reduced footprint is represented by
the constant-size replicated summary, not a nested composition tree. -/
theorem FormalCircuit.foldSynthesisSummary_eq_replicate
    (summary : FloorPlanner.SynthesisSummary)
    (hsummary : ∀ i,
      (c i).elaborated.synthesisSummary config
        (FormalCircuit.foldState c toInput config init i₀ i).1
        (FormalCircuit.foldState c toInput config init i₀ i).2 = summary)
    (hcolumns : summary.columns.Nodup) : ∀ m,
    FormalCircuit.foldSynthesisSummary c toInput config init i₀ m =
      FloorPlanner.SynthesisSummary.replicate m summary
  | 0 => by
      apply FloorPlanner.SynthesisSummary.ext
      · simp [FormalCircuit.foldSynthesisSummary,
          FloorPlanner.SynthesisSummary.replicate]
      · funext column
        simp [FormalCircuit.foldSynthesisSummary,
          FloorPlanner.SynthesisSummary.replicate]
      · simp [FormalCircuit.foldSynthesisSummary,
          FloorPlanner.SynthesisSummary.replicate]
      · simp [FormalCircuit.foldSynthesisSummary,
          FloorPlanner.SynthesisSummary.replicate]
      · simp [FormalCircuit.foldSynthesisSummary,
          FloorPlanner.SynthesisSummary.replicate]
      · simp [FormalCircuit.foldSynthesisSummary,
          FloorPlanner.SynthesisSummary.replicate]
  | m + 1 => by
      rw [FormalCircuit.foldSynthesisSummary,
        FormalCircuit.foldSynthesisSummary_eq_replicate summary hsummary hcolumns m,
        hsummary m,
        FloorPlanner.SynthesisSummary.replicate_succ m summary hcolumns]

/-- Exact deferred-constant demand of a serial circuit fold. -/
@[synthesis_summary_norm]
theorem FormalCircuit.foldOps_synthesisSummary_constantSiteCount (m : ℕ) :
    (FloorPlanner.synthesisSummary
      (FormalCircuit.foldOps c toInput config init i₀ m)).constantSiteCount =
      (List.ofFn fun i : Fin m =>
        ((c i).elaborated.synthesisSummary config
          (FormalCircuit.foldState c toInput config init i₀ i).1
          (FormalCircuit.foldState c toInput config init i₀ i).2).constantSiteCount).sum := by
  induction m with
  | zero =>
      simp only [FormalCircuit.foldOps, FloorPlanner.synthesisSummary_nil_constantSiteCount,
        List.ofFn_zero, List.sum_nil]
  | succ m inductionHypothesis =>
      rw [FormalCircuit.foldOps, FloorPlanner.synthesisSummary_append,
        FloorPlanner.SynthesisSummary.combine_constantSiteCount,
        inductionHypothesis, FormalCircuit.call_synthesisSummary,
        List.ofFn_succ', List.sum_concat]
      simp only [Fin.val_castSucc, Fin.val_last]
      rfl

/-- `foldCall`-spelled exact deferred-constant demand. -/
@[synthesis_summary_norm]
theorem FormalCircuit.foldCall_synthesisSummary_constantSiteCount (m : ℕ) :
    (FloorPlanner.synthesisSummary
      ((FormalCircuit.foldCall c toInput config init m).operations i₀)).constantSiteCount =
      (List.ofFn fun i : Fin m =>
        ((c i).elaborated.synthesisSummary config
          (FormalCircuit.foldState c toInput config init i₀ i).1
          (FormalCircuit.foldState c toInput config init i₀ i).2).constantSiteCount).sum := by
  rw [FormalCircuit.foldCall_operations,
    FormalCircuit.foldOps_synthesisSummary_constantSiteCount]

/-- Exact occupancy of one column across a serial circuit fold. -/
@[synthesis_summary_norm]
theorem FormalCircuit.foldOps_synthesisSummary_columnOccupancy
    (column : FloorPlanner.RegionColumn) (m : ℕ) :
    (FloorPlanner.synthesisSummary
      (FormalCircuit.foldOps c toInput config init i₀ m)).columnOccupancy column =
      (List.ofFn fun i : Fin m =>
        ((c i).elaborated.synthesisSummary config
          (FormalCircuit.foldState c toInput config init i₀ i).1
          (FormalCircuit.foldState c toInput config init i₀ i).2).columnOccupancy
            column).sum := by
  induction m with
  | zero =>
      simp only [FormalCircuit.foldOps,
        FloorPlanner.synthesisSummary_nil_columnOccupancy,
        List.ofFn_zero, List.sum_nil]
  | succ m inductionHypothesis =>
      rw [FormalCircuit.foldOps, FloorPlanner.synthesisSummary_append,
        FloorPlanner.SynthesisSummary.combine_columnOccupancy,
        inductionHypothesis, FormalCircuit.call_synthesisSummary,
        List.ofFn_succ', List.sum_concat]
      simp only [Fin.val_castSucc, Fin.val_last]
      rfl

/-- `foldCall`-spelled exact occupancy of one column. -/
@[synthesis_summary_norm]
theorem FormalCircuit.foldCall_synthesisSummary_columnOccupancy
    (column : FloorPlanner.RegionColumn) (m : ℕ) :
    (FloorPlanner.synthesisSummary
      ((FormalCircuit.foldCall c toInput config init m).operations i₀)).columnOccupancy
        column =
      (List.ofFn fun i : Fin m =>
        ((c i).elaborated.synthesisSummary config
          (FormalCircuit.foldState c toInput config init i₀ i).1
          (FormalCircuit.foldState c toInput config init i₀ i).2).columnOccupancy
            column).sum := by
  rw [FormalCircuit.foldCall_operations,
    FormalCircuit.foldOps_synthesisSummary_columnOccupancy]

theorem FormalCircuit.foldCall_output (m : ℕ) :
    (FormalCircuit.foldCall c toInput config init m).output i₀
      = (FormalCircuit.foldState c toInput config init i₀ m).1 := by
  rw [Circuit.output, FormalCircuit.foldCall_run]

theorem FormalCircuit.foldCall_nextRegionIndex (m : ℕ) :
    (FormalCircuit.foldCall c toInput config init m).nextRegionIndex i₀
      = (FormalCircuit.foldState c toInput config init i₀ m).2 := by
  rw [Circuit.nextRegionIndex, FormalCircuit.foldCall_run]

/-- The fold's region count, in `foldState` form. -/
theorem FormalCircuit.foldOps_regionCount (m : ℕ) :
    i₀ + Operations.regionCount (FormalCircuit.foldOps c toInput config init i₀ m)
      = (FormalCircuit.foldState c toInput config init i₀ m).2 := by
  induction m with
  | zero => simp [FormalCircuit.foldOps, FormalCircuit.foldState, Operations.regionCount]
  | succ m ih =>
    rw [FormalCircuit.foldOps]
    show _ = (FormalCircuit.foldState c toInput config init i₀ m).2
      + (c m).regionCount (FormalCircuit.foldState c toInput config init i₀ m).1
    rw [Operations.regionCount_append, FormalCircuit.call_regionCount, ← Nat.add_assoc, ih]

/--
An operation-local law holds over a layouter fold exactly when it holds over every
folded child-call chunk.

This is the layouter-level counterpart of `RegionCircuit.loopAux_forall`. In
particular, keygen registration can split a fold without opening any child's
operation stream.
-/
theorem FormalCircuit.foldOps_forall (property : Operation F → Prop) (m : ℕ) :
    (FormalCircuit.foldOps c toInput config init i₀ m).Forall property ↔
      ∀ i : Fin m,
        (((c i).call config
            (FormalCircuit.foldState c toInput config init i₀ i).1).operations
          (FormalCircuit.foldState c toInput config init i₀ i).2).Forall property := by
  induction m with
  | zero =>
    simp only [FormalCircuit.foldOps, List.forall_nil, Fin.forall_fin_zero]
  | succ m ih =>
    rw [FormalCircuit.foldOps, List.forall_append, ih, Fin.forall_fin_succ']
    simp only [Fin.val_castSucc, Fin.val_last]

/-- `foldCall`-spelled operation-local split, registered for static keygen laws. -/
@[keygen_norm, keygen_spine]
theorem FormalCircuit.foldCall_forall (property : Operation F → Prop) (m : ℕ) :
    ((FormalCircuit.foldCall c toInput config init m).operations i₀).Forall property ↔
      ∀ i : Fin m,
        (((c i).call config
            (FormalCircuit.foldState c toInput config init i₀ i).1).operations
          (FormalCircuit.foldState c toInput config init i₀ i).2).Forall property := by
  rw [FormalCircuit.foldCall_operations,
    FormalCircuit.foldOps_forall c toInput config init i₀]

/-- Fixed-assignment agreement composes over a serial fold from the configured
law of each folded child. -/
theorem FormalCircuit.foldCall_fixedAssignmentsAgree
    (m : ℕ) (configured : ∀ i : Fin m, (c i).Configured config) :
    ((FormalCircuit.foldCall c toInput config init m).operations i₀).Forall
      Operation.FixedAssignmentsAgree := by
  rw [FormalCircuit.foldCall_forall]
  intro i
  exact (c i).call_fixedAssignmentsAgree config (configured i)
    (FormalCircuit.foldState c toInput config init i₀ i).1
    (FormalCircuit.foldState c toInput config init i₀ i).2

/-- Lookup-selector assignment agreement composes over a serial fold from the
configured law of each folded child. -/
@[keygen_norm, keygen_spine]
theorem FormalCircuit.foldCall_lookupSelectorAssignmentsAgree
    (m : ℕ) (configured : ∀ i : Fin m, (c i).Configured config) :
    ((FormalCircuit.foldCall c toInput config init m).operations i₀)
      |>.LookupSelectorAssignmentsAgree := by
  rw [Operations.LookupSelectorAssignmentsAgree,
    FormalCircuit.foldCall_forall]
  intro i
  exact (c i).call_lookupSelectorAssignmentsAgree config (configured i)
    (FormalCircuit.foldState c toInput config init i₀ i).1
    (FormalCircuit.foldState c toInput config init i₀ i).2

/-- Register a serial fold compositionally from one configured handle per round and
an invariant covering the equality columns of each folded input. -/
theorem FormalCircuit.foldCall_keygenRegistered
    (m : ℕ)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetFixedColumns : List (Column .fixed)}
    {targetPermutationColumns : List AnyColumn}
    (configured : ∀ i : Fin m, (c i).Configured config)
    (hgates : ∀ i gate,
      gate ∈ (configured i).gates → gate ∈ targetGates)
    (hlookups : ∀ i argument,
      argument ∈ (configured i).lookups → argument ∈ targetLookups)
    (hfixedColumns : ∀ i column,
      column ∈ (configured i).fixedColumns → column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ i column,
      column ∈ (configured i).permutationColumns →
        column ∈ targetPermutationColumns)
    (hinputCells : ∀ i,
      ((configured i).inputCells
          (FormalCircuit.foldState c toInput config init i₀ i).1).Forall fun cell ↦
        cell.column ∈ targetPermutationColumns) :
    ((FormalCircuit.foldCall c toInput config init m).operations i₀).KeygenRegistered
      targetGates targetLookups targetFixedColumns targetPermutationColumns := by
  rw [Operations.KeygenRegistered, FormalCircuit.foldCall_forall]
  intro i
  exact FormalCircuit.call_keygenRegistered
    (c i) config (configured i)
    (FormalCircuit.foldState c toInput config init i₀ i).1
    (FormalCircuit.foldState c toInput config init i₀ i).2
    (hgates i) (hlookups i) (hfixedColumns i) (hpermutationColumns i)
    (hinputCells i)

/-- Copy provenance composes across a serial circuit fold when every round's
declared input cells are either caller inputs or cells assigned by an earlier
round. -/
theorem FormalCircuit.foldOps_copyCellsAssignedFrom
    (m : ℕ) (configured : ∀ i : Fin m, (c i).Configured config)
    {available : List Cell}
    (hinputCells : ∀ i cell,
      cell ∈ (configured i).inputCells
          (FormalCircuit.foldState c toInput config init i₀ i).1 →
        cell ∈ available ++
          (FormalCircuit.foldOps c toInput config init i₀ i).assignedCellsFrom i₀) :
    (FormalCircuit.foldOps c toInput config init i₀ m).CopyCellsAssignedFrom
      i₀ available := by
  induction m with
  | zero => exact .nil i₀ available
  | succ m inductionHypothesis =>
      rw [FormalCircuit.foldOps]
      apply Operations.CopyCellsAssignedFrom.append
      · apply inductionHypothesis
          (fun i => configured i.castSucc)
        intro i cell hcell
        exact hinputCells i.castSucc cell hcell
      · rw [show i₀ + Operations.regionCount
              (FormalCircuit.foldOps c toInput config init i₀ m) =
            (FormalCircuit.foldState c toInput config init i₀ m).2 from
          FormalCircuit.foldOps_regionCount c toInput config init i₀ m]
        apply (c m).call_copyCellsAssignedFrom config
          (configured ⟨m, Nat.lt_succ_self m⟩)
          (FormalCircuit.foldState c toInput config init i₀ m).1
          (FormalCircuit.foldState c toInput config init i₀ m).2
        intro cell hcell
        exact hinputCells ⟨m, Nat.lt_succ_self m⟩ cell hcell

/-- `foldCall` spelling of `foldOps_copyCellsAssignedFrom`. -/
theorem FormalCircuit.foldCall_copyCellsAssignedFrom
    (m : ℕ) (configured : ∀ i : Fin m, (c i).Configured config)
    {available : List Cell}
    (hinputCells : ∀ i cell,
      cell ∈ (configured i).inputCells
          (FormalCircuit.foldState c toInput config init i₀ i).1 →
        cell ∈ available ++
          (FormalCircuit.foldOps c toInput config init i₀ i).assignedCellsFrom i₀) :
    ((FormalCircuit.foldCall c toInput config init m).operations i₀)
      |>.CopyCellsAssignedFrom i₀ available := by
  rw [FormalCircuit.foldCall_operations]
  exact FormalCircuit.foldOps_copyCellsAssignedFrom
    c toInput config init i₀ m configured hinputCells

/-- The soundness-side split: `Constraints` of the fold is the per-round folded chunks. -/
theorem FormalCircuit.foldOps_constraints (place : RegionIndex → ℕ) (env : Environment F)
    (m : ℕ) :
    Halo2.Constraints place env (FormalCircuit.foldOps c toInput config init i₀ m) i₀
      ↔ ∀ i : Fin m,
        Halo2.Constraints place env
          (((c i).call config
              (FormalCircuit.foldState c toInput config init i₀ i).1).operations
            (FormalCircuit.foldState c toInput config init i₀ i).2)
          (FormalCircuit.foldState c toInput config init i₀ i).2 := by
  induction m with
  | zero =>
    simp only [FormalCircuit.foldOps, Halo2.Constraints]
    exact ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | succ m ih =>
    rw [FormalCircuit.foldOps, Halo2.constraints_append, ih,
      show i₀ + Operations.regionCount (FormalCircuit.foldOps c toInput config init i₀ m)
        = (FormalCircuit.foldState c toInput config init i₀ m).2 from
        FormalCircuit.foldOps_regionCount c toInput config init i₀ m,
      Fin.forall_fin_succ']
    simp only [Fin.val_castSucc, Fin.val_last]

/-- The completeness-side split: `ExtendsWitnesses` of the fold is the per-round chunks. -/
theorem FormalCircuit.foldOps_extendsWitnesses (place : RegionIndex → ℕ)
    (env : ProverEnvironment F) (m : ℕ) :
    Halo2.ExtendsWitnesses place env (FormalCircuit.foldOps c toInput config init i₀ m) i₀
      ↔ ∀ i : Fin m,
        Halo2.ExtendsWitnesses place env
          (((c i).call config
              (FormalCircuit.foldState c toInput config init i₀ i).1).operations
            (FormalCircuit.foldState c toInput config init i₀ i).2)
          (FormalCircuit.foldState c toInput config init i₀ i).2 := by
  induction m with
  | zero =>
    simp only [FormalCircuit.foldOps, Halo2.ExtendsWitnesses]
    exact ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | succ m ih =>
    rw [FormalCircuit.foldOps, Halo2.extendsWitnesses_append, ih,
      show i₀ + Operations.regionCount (FormalCircuit.foldOps c toInput config init i₀ m)
        = (FormalCircuit.foldState c toInput config init i₀ m).2 from
        FormalCircuit.foldOps_regionCount c toInput config init i₀ m,
      Fin.forall_fin_succ']
    simp only [Fin.val_castSucc, Fin.val_last]

end

/-! ## `CoeFun` — subcircuits look like function calls -/

section
variable [CircuitType Input] [CircuitType Output]

/-- `child config input` means `child.call config input`. -/
instance : CoeFun (FormalCircuit F CI Cfg Input Output)
    (fun _ => Cfg → Var Input F → Circuit F (Var Output F)) where
  coe self := self.call

/-- `child config offset input` means `child.call config offset input`. -/
instance : CoeFun (FormalRegionCircuit F CI Cfg Input Output)
    (fun _ => Cfg → ℕ → Var Input F → RegionCircuit F (Var Output F)) where
  coe self := self.call

end

/-! ## The `chunk_split` membership (see `Clean/Halo2/Attributes.lean`)

The layouter call-fold's split pair, plus the `operations` bridge that exposes
`foldOps` for them to fire on. -/

attribute [chunk_split] FormalCircuit.foldCall_operations
attribute [chunk_split ↓] FormalCircuit.foldOps_constraints
  FormalCircuit.foldOps_extendsWitnesses

end Halo2
