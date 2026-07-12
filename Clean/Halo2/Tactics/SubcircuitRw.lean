import Lean.Elab.Tactic
import Clean.Halo2.Subcircuit

/-!
# `subcircuit_rw` — the polarity-aware monotone subcircuit rewriter

The proper engine that replaces the absorption-iff mechanism (`Clean/Halo2/Subcircuit.lean`)
as the way parent proofs consume child contracts. See `Clean/Halo2/subcircuit-engine-design.md`
for the full design; this file is its implementation. Both mechanisms coexist until the
migration pass retires the iffs — nothing here retires anything.

## The core idea

`chunk → X` is not an iff, so `simp`/`rw` can't consume a subcircuit chunk. But proof states
don't need iffs: **hypotheses may be weakened and goals strengthened** — one-directional
rewriting under polarity. The engine walks a proposition tracking polarity, replaces every
positive-position subcircuit chunk by the child's instantiated consequence, and builds the
implication `h_old → h_new` (soundness, `at h`) or `goal_new → goal_old` (completeness, goal)
from a fixed, hand-rolled congruence-lemma set (`∧ ∨ → ∀ ∃` monotonicity) with the child's
contract at the leaves.

## Two modes

* `subcircuit_rw at h` (**soundness**): walk `h`; every positive call-keyed chunk
  `RegionOperations.Constraints place self env ((child.call cfg off inp).operations self)`
  (region) or `Halo2.Constraints place env ((child.call cfg inp).operations i₀) i₀`
  (layouter) is replaced by the child's `EnvAssumptions → Assumptions → Spec` (its instantiated
  soundness consequence). `replace h` with the weakened proposition.

* `subcircuit_rw` (**completeness**, no location): co-processes the goal and the
  `ExtendsWitnesses` context (maintainer decision D2 — the two can't be split). For each
  positive goal chunk it (a) locates the matching call-keyed `ExtendsWitnesses` fact in the
  local context (direct hypothesis or a conjunct inside one), (b) strengthens the goal chunk
  to `EnvAssumptions ∧ Assumptions ∧ ProverAssumptions` (ExtendsWitnesses discharged from the
  located fact via the leaf lemma), and (c) introduces the derived contract statement
  `h_spec_<child> : EnvA → A → PA → Spec ∧ ProverSpec` (completeness then soundness — the old
  `call_constraints_and_specs` composition, now internal and read-off-the-term instantiated).

Negative-position chunks and non-targeted shapes are left silently untouched. `set_option
trace.Halo2.subcircuit_rw true` traces matches/skips for development.

## Leaf matching (read the arguments off the term)

The matched chunk contains every argument the child contract needs — `child, cfg, offset,
input, place, env, self` are all subterms of the matched `Constraints`/`call` application.
The engine unifies against the folded `call` boundary (the same opacity contract as the iffs:
`call` is never unfolded), reads the arguments syntactically, and instantiates the child's
contract. This is the tactic's own `isDefEq`, not simp's discrimination-tree lookup, so the
`Placed`-vs-bare and abstract-α-vs-concrete-α spelling families all collapse.
-/

open Lean Elab Tactic Meta

namespace Halo2

initialize registerTraceClass `Halo2.subcircuit_rw

/-! ## Congruence lemmas (the hand-rolled monotone walker's leaves)

Five monotonicity lemmas for `∧ ∨ → ∀ ∃`, written out here rather than pulled from Mathlib's
`mono`/`gcongr` machinery (keeping the set minimal and under the engine's control). `imp` is
contravariant in its left argument — that is where polarity flips. The walker builds a proof
of `P → Q` (where `Q` is `P` with positive chunks rewritten) by structural recursion, applying
one of these at each connective and a child-contract leaf where a chunk was rewritten. -/

namespace SubcircuitRw

theorem and_mono {p p' q q' : Prop} (hp : p → p') (hq : q → q') : p ∧ q → p' ∧ q' :=
  fun ⟨a, b⟩ => ⟨hp a, hq b⟩

theorem or_mono {p p' q q' : Prop} (hp : p → p') (hq : q → q') : p ∨ q → p' ∨ q' :=
  fun h => h.imp hp hq

/-- Implication congruence. Contravariant on the left (`hp : p' → p`), covariant on the right. -/
theorem imp_mono {p p' q q' : Prop} (hp : p' → p) (hq : q → q') : (p → q) → (p' → q') :=
  fun f a => hq (f (hp a))

theorem forall_mono {α : Sort _} {p p' : α → Prop} (h : ∀ a, p a → p' a) :
    (∀ a, p a) → ∀ a, p' a :=
  fun f a => h a (f a)

theorem exists_mono {α : Sort _} {p p' : α → Prop} (h : ∀ a, p a → p' a) :
    (∃ a, p a) → ∃ a, p' a :=
  fun ⟨a, ha⟩ => ⟨a, h a ha⟩

end SubcircuitRw

/-! ## Leaf contract lemmas

Stated over **bare** `place`/`env` (reconstructing the `Placed` record as `⟨place, env⟩`
under the hood), so the engine can instantiate them uniformly whether the matched chunk sits
in a `Placed`-projection context or a bare loop-lemma context. Four lemmas: region/layouter ×
soundness/completeness-derived. They are the content of the absorption iffs, minus the
marker/OR wrapping.

The soundness leaves are the `chunk → (EnvA → A → Spec)` implication directly. The
completeness leaves are the `call_constraints_and_specs` composition packaged as a derived
statement `EnvA → A → PA → Spec ∧ ProverSpec` (completeness for the constraints/ProverSpec,
then soundness at the verifier view for the Spec), taking the located `ExtendsWitnesses` fact
as a hypothesis. -/

namespace SubcircuitRw

variable {F : Type} [FiniteField F] {CI Cfg : Type} {Input Output : TypeMap}
  [CircuitType Input] [CircuitType Output]

/-- Region soundness leaf: a folded call-constraint chunk implies the child's
`EnvAssumptions → Assumptions → Spec`. Over bare `place`/`env`. The soundness iff's content
without the surviving marker chunk. -/
theorem region_soundness_leaf
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (place : RegionIndex → ℕ) (env : Environment F) (input : Var Input F) :
    RegionOperations.Constraints place self env
        ((child.call config offset input).operations self)
    → (child.EnvAssumptions config (⟨place, env⟩ : Placed Environment F) →
        child.Assumptions (eval (⟨place, env⟩ : Placed Environment F) input) →
        child.Spec (eval (⟨place, env⟩ : Placed Environment F) input)
          (eval (⟨place, env⟩ : Placed Environment F) (child.output config offset input self))
          (child.extract config offset input self (⟨place, env⟩ : Placed Environment F))) := by
  have hcall : RegionOperations.Constraints place self env
      ((child.call config offset input).operations self)
      = RegionOperations.Constraints place self env
          ((child.synthesize config offset input).operations self) := by
    simp only [FormalRegionCircuit.call, RegionCircuit.operations,
      RegionOperations.constraints_cons, RegionOperations.constraints_nil,
      RegionOperation.constraints_subcircuit, and_true]
  rw [hcall]
  intro hc hE hA
  exact child.soundness config offset self ⟨place, env⟩ input hE hA hc

/-- Layouter soundness leaf. Over bare `place`/`env`. -/
theorem layouter_soundness_leaf
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment F) (input : Var Input F) :
    Halo2.Constraints place env ((child.call config input).operations i₀) i₀
    → (child.EnvAssumptions config (⟨place, env⟩ : Placed Environment F) →
        child.Assumptions (eval (⟨place, env⟩ : Placed Environment F) input) →
        child.Spec (eval (⟨place, env⟩ : Placed Environment F) input)
          (eval (⟨place, env⟩ : Placed Environment F) (child.output config input i₀))
          (child.extract config input i₀ (⟨place, env⟩ : Placed Environment F))) := by
  have hcall : Halo2.Constraints place env ((child.call config input).operations i₀) i₀
      = Halo2.Constraints place env ((child.synthesize config input).operations i₀) i₀ := by
    simp only [FormalCircuit.call, Circuit.operations, Halo2.Constraints, and_true]
  rw [hcall]
  intro hc hE hA
  exact child.soundness config i₀ ⟨place, env⟩ input hE hA hc

/-- Region completeness derived statement: from the located `ExtendsWitnesses`, the child's
`EnvA → A → PA → (Spec ∧ ProverSpec)` (soundness at the verifier view, ProverSpec from
completeness). The `call_constraints_and_specs` composition, now a framework leaf. Over bare
`place`/`env`. -/
theorem region_completeness_derived
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment F)
    (input : Var Input F)
    (hw : RegionOperations.ExtendsWitnesses place self env
      ((child.call config offset input).operations self)) :
    child.EnvAssumptions config (⟨place, env.toEnvironment⟩ : Placed Environment F) →
    child.Assumptions (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input) →
    child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input) env.hint →
    child.Spec (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment F)
          (child.output config offset input self))
        (child.extract config offset input self (⟨place, env.toEnvironment⟩ : Placed Environment F))
      ∧ child.ProverSpec (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
          (eval (⟨place, env⟩ : Placed ProverEnvironment F) (child.output config offset input self))
          env.hint := by
  have hw' : RegionOperations.ExtendsWitnesses place self env
      ((child.synthesize config offset input).operations self) := by
    have : RegionOperations.ExtendsWitnesses place self env
        ((child.call config offset input).operations self)
        = RegionOperations.ExtendsWitnesses place self env
            ((child.synthesize config offset input).operations self) := by
      simp only [FormalRegionCircuit.call, RegionCircuit.operations,
        RegionOperations.extendsWitnesses_cons, RegionOperations.extendsWitnesses_nil,
        RegionOperation.extendsWitness_subcircuit, and_true]
    rwa [this] at hw
  intro hE hA hpa
  obtain ⟨hcons, hps⟩ :=
    child.completeness config offset self (⟨place, env⟩ : Placed ProverEnvironment F) input hw' hE hA hpa
  exact ⟨child.soundness config offset self (⟨place, env.toEnvironment⟩ : Placed Environment F)
    input hE hA hcons, hps⟩

/-- The parent-facing precondition bundle that a positive goal chunk is strengthened to, and
which the located `ExtendsWitnesses` discharges into the folded call-constraint chunk (region).
The strengthening leaf: `(EnvA ∧ A ∧ PA) → chunk`, closing the goal chunk from the parent's
in-context assumptions. Over bare `place`/`env`. -/
theorem region_completeness_leaf
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment F)
    (input : Var Input F)
    (hw : RegionOperations.ExtendsWitnesses place self env
      ((child.call config offset input).operations self)) :
    (child.EnvAssumptions config (⟨place, env.toEnvironment⟩ : Placed Environment F)
      ∧ child.Assumptions (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
      ∧ child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input) env.hint)
    → RegionOperations.Constraints place self env
        ((child.call config offset input).operations self) := by
  have hw' : RegionOperations.ExtendsWitnesses place self env
      ((child.synthesize config offset input).operations self) := by
    have : RegionOperations.ExtendsWitnesses place self env
        ((child.call config offset input).operations self)
        = RegionOperations.ExtendsWitnesses place self env
            ((child.synthesize config offset input).operations self) := by
      simp only [FormalRegionCircuit.call, RegionCircuit.operations,
        RegionOperations.extendsWitnesses_cons, RegionOperations.extendsWitnesses_nil,
        RegionOperation.extendsWitness_subcircuit, and_true]
    rwa [this] at hw
  have hcall : RegionOperations.Constraints place self env
      ((child.call config offset input).operations self)
      = RegionOperations.Constraints place self env
          ((child.synthesize config offset input).operations self) := by
    simp only [FormalRegionCircuit.call, RegionCircuit.operations,
      RegionOperations.constraints_cons, RegionOperations.constraints_nil,
      RegionOperation.constraints_subcircuit, and_true]
  rw [hcall]
  intro ⟨hE, hA, hpa⟩
  exact (child.completeness config offset self (⟨place, env⟩ : Placed ProverEnvironment F)
    input hw' hE hA hpa).1

/-- Layouter completeness derived statement. Over bare `place`/`env`. -/
theorem layouter_completeness_derived
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment F) (input : Var Input F)
    (hw : Halo2.ExtendsWitnesses place env ((child.call config input).operations i₀) i₀) :
    child.EnvAssumptions config (⟨place, env.toEnvironment⟩ : Placed Environment F) →
    child.Assumptions (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input) →
    child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input) env.hint →
    child.Spec (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) (child.output config input i₀))
        (child.extract config input i₀ (⟨place, env.toEnvironment⟩ : Placed Environment F))
      ∧ child.ProverSpec (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
          (eval (⟨place, env⟩ : Placed ProverEnvironment F) (child.output config input i₀))
          env.hint := by
  have hw' : Halo2.ExtendsWitnesses place env
      ((child.synthesize config input).operations i₀) i₀ := by
    have : Halo2.ExtendsWitnesses place env ((child.call config input).operations i₀) i₀
        = Halo2.ExtendsWitnesses place env ((child.synthesize config input).operations i₀) i₀ := by
      simp only [FormalCircuit.call, Circuit.operations, Halo2.ExtendsWitnesses, and_true]
    rwa [this] at hw
  intro hE hA hpa
  obtain ⟨hcons, hps⟩ :=
    child.completeness config i₀ (⟨place, env⟩ : Placed ProverEnvironment F) input hw' hE hA hpa
  exact ⟨child.soundness config i₀ (⟨place, env.toEnvironment⟩ : Placed Environment F)
    input hE hA hcons, hps⟩

/-- Layouter completeness strengthening leaf: `(EnvA ∧ A ∧ PA) → chunk`. Over bare `place`/`env`. -/
theorem layouter_completeness_leaf
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment F) (input : Var Input F)
    (hw : Halo2.ExtendsWitnesses place env ((child.call config input).operations i₀) i₀) :
    (child.EnvAssumptions config (⟨place, env.toEnvironment⟩ : Placed Environment F)
      ∧ child.Assumptions (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
      ∧ child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input) env.hint)
    → Halo2.Constraints place env ((child.call config input).operations i₀) i₀ := by
  have hw' : Halo2.ExtendsWitnesses place env
      ((child.synthesize config input).operations i₀) i₀ := by
    have : Halo2.ExtendsWitnesses place env ((child.call config input).operations i₀) i₀
        = Halo2.ExtendsWitnesses place env ((child.synthesize config input).operations i₀) i₀ := by
      simp only [FormalCircuit.call, Circuit.operations, Halo2.ExtendsWitnesses, and_true]
    rwa [this] at hw
  have hcall : Halo2.Constraints place env ((child.call config input).operations i₀) i₀
      = Halo2.Constraints place env ((child.synthesize config input).operations i₀) i₀ := by
    simp only [FormalCircuit.call, Circuit.operations, Halo2.Constraints, and_true]
  rw [hcall]
  intro ⟨hE, hA, hpa⟩
  exact (child.completeness config i₀ (⟨place, env⟩ : Placed ProverEnvironment F)
    input hw' hE hA hpa).1

/-! ### Placed-view completeness leaves (finding #1: verifier-view spelling)

When the matched goal chunk sits over the projections `penv.place`/`penv.env` of a common
`penv : Placed ProverEnvironment F` (the shape produced by `FormalRegionCircuit.completeness_iff`
/ `FormalCircuit.completeness_iff`, which intro a single `env : Placed ProverEnvironment` and
constrain over `env.place`/`env.env`), the bare leaves above would spell the child's verifier
view as the *reconstructed* record `⟨penv.place, penv.env.toEnvironment⟩`. That record is
definitionally — but not reducibly — `penv.toEnvironment`, so `env.toEnvironment`-spelled
downstream bridges miss it under `rw`/`simp`. These variants take the `Placed ProverEnvironment`
directly and spell the verifier view as `penv.toEnvironment`, matching how consumer proofs write
their bridges. They are the leaves the engine instantiates whenever it detects the projection
shape; otherwise it falls back to the bare leaves above. -/

/-- Placed-view region completeness derived statement. Verifier parts spelled `penv.toEnvironment`. -/
theorem region_completeness_derived_placed
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (penv : Placed ProverEnvironment F) (input : Var Input F)
    (hw : RegionOperations.ExtendsWitnesses penv.place self penv.env
      ((child.call config offset input).operations self)) :
    child.EnvAssumptions config penv.toEnvironment →
    child.Assumptions (eval penv.toEnvironment input) →
    child.ProverAssumptions (eval penv input) penv.env.hint →
    child.Spec (eval penv.toEnvironment input)
        (eval penv.toEnvironment (child.output config offset input self))
        (child.extract config offset input self penv.toEnvironment)
      ∧ child.ProverSpec (eval penv input)
          (eval penv (child.output config offset input self)) penv.env.hint :=
  region_completeness_derived child config offset self penv.place penv.env input hw

/-- Placed-view region completeness strengthening leaf. -/
theorem region_completeness_leaf_placed
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (penv : Placed ProverEnvironment F) (input : Var Input F)
    (hw : RegionOperations.ExtendsWitnesses penv.place self penv.env
      ((child.call config offset input).operations self)) :
    (child.EnvAssumptions config penv.toEnvironment
      ∧ child.Assumptions (eval penv.toEnvironment input)
      ∧ child.ProverAssumptions (eval penv input) penv.env.hint)
    → RegionOperations.Constraints penv.place self penv.env
        ((child.call config offset input).operations self) :=
  region_completeness_leaf child config offset self penv.place penv.env input hw

/-- Placed-view layouter completeness derived statement. -/
theorem layouter_completeness_derived_placed
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (penv : Placed ProverEnvironment F) (input : Var Input F)
    (hw : Halo2.ExtendsWitnesses penv.place penv.env ((child.call config input).operations i₀) i₀) :
    child.EnvAssumptions config penv.toEnvironment →
    child.Assumptions (eval penv.toEnvironment input) →
    child.ProverAssumptions (eval penv input) penv.env.hint →
    child.Spec (eval penv.toEnvironment input)
        (eval penv.toEnvironment (child.output config input i₀))
        (child.extract config input i₀ penv.toEnvironment)
      ∧ child.ProverSpec (eval penv input)
          (eval penv (child.output config input i₀)) penv.env.hint :=
  layouter_completeness_derived child config i₀ penv.place penv.env input hw

/-- Placed-view layouter completeness strengthening leaf. -/
theorem layouter_completeness_leaf_placed
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (penv : Placed ProverEnvironment F) (input : Var Input F)
    (hw : Halo2.ExtendsWitnesses penv.place penv.env ((child.call config input).operations i₀) i₀) :
    (child.EnvAssumptions config penv.toEnvironment
      ∧ child.Assumptions (eval penv.toEnvironment input)
      ∧ child.ProverAssumptions (eval penv input) penv.env.hint)
    → Halo2.Constraints penv.place penv.env ((child.call config input).operations i₀) i₀ :=
  layouter_completeness_leaf child config i₀ penv.place penv.env input hw

end SubcircuitRw

/-! ## The engine

The walker builds a monotone-implication proof from the congruence lemmas above, with a leaf
lemma wherever a call-keyed chunk was rewritten. Matching reads the arguments off the term:
we recognize the `Constraints` head, dig the `call` application out of its `ops` argument to
read `child`/`config`/`offset`/`input`, and read `place`/`env`/`self` (or `i₀`) off the
`Constraints` head's own arguments.
-/

namespace SubcircuitRw

/-- View `p` as a disjunction `a ∨ b` (`Lean.Expr.and?` has no `Or` counterpart). -/
def or? (p : Expr) : Option (Expr × Expr) :=
  if p.isAppOfArity ``Or 2 then some (p.appFn!.appArg!, p.appArg!) else none

/-- A matched call-keyed constraint chunk, region or layouter level, with everything the leaf
lemmas need read off the term. `offset?` is present at the region level only. -/
structure ChunkMatch where
  /-- `true` = region level (`RegionOperations.Constraints`), `false` = layouter
  (`Halo2.Constraints`). -/
  isRegion : Bool
  F : Expr
  finiteField : Expr
  CI : Expr
  Cfg : Expr
  Input : Expr
  Output : Expr
  ctInput : Expr
  ctOutput : Expr
  child : Expr
  config : Expr
  /-- Region offset (region level only). -/
  offset? : Option Expr
  input : Expr
  place : Expr
  /-- Verifier `Environment`, as it appears in the matched `Constraints` chunk. -/
  env : Expr
  /-- `self` (region) or `i₀` (layouter). -/
  regionIdx : Expr

/-- Recognize a call-keyed constraint chunk. On the `Constraints`/`RegionOperations.Constraints`
head, dig into the `ops` argument for the `call` application and read the child contract's
arguments off it. `isDefEq` (at `.default` transparency) confirms the `ops` argument is the
folded `call` boundary; the α-spelling of `.operations` is irrelevant since we match `call`, not
`operations`, syntactically after stripping the accessor. -/
def matchChunk? (e : Expr) : MetaM (Option ChunkMatch) := do
  let e ← instantiateMVars e
  let fn := e.getAppFn
  let .const headName _ := fn | return none
  let args := e.getAppArgs
  -- Region:   RegionOperations.Constraints  [F, inst, place, self, env, ops]
  -- Layouter: Halo2.Constraints             [F, inst, place, env, ops, i]
  let (isRegion, place, env, regionIdx, ops) ←
    if headName == ``RegionOperations.Constraints then do
      unless args.size == 6 do return none
      pure (true, args[2]!, args[4]!, args[3]!, args[5]!)
    else if headName == ``Halo2.Constraints then do
      unless args.size == 6 do return none
      pure (false, args[2]!, args[3]!, args[5]!, args[4]!)
    else
      return none
  -- `ops` should be `(child.call …).operations regionIdx`, i.e.
  --   region:   RegionCircuit.operations (child.call config offset input) self
  --   layouter: Circuit.operations       (child.call config input) i₀
  let opsFn := ops.getAppFn
  let .const opsName _ := opsFn |
    (do trace[Halo2.subcircuit_rw] "skip: ops head not a const: {ops}"; return none)
  let opsArgs := ops.getAppArgs
  let ok := (isRegion && opsName == ``RegionCircuit.operations)
    || (!isRegion && opsName == ``Circuit.operations)
  unless ok && opsArgs.size ≥ 5 do
    trace[Halo2.subcircuit_rw] "skip: ops accessor mismatch ({opsName})"
    return none
  -- args: [F, inst, α, (child.call …), regionIdx]
  let callTerm := opsArgs[3]!
  -- The call application. `child.call config (offset) input` where `call` is the bundle field's
  -- `FormalRegionCircuit.call`/`FormalCircuit.call` (the `CoeFun` unfolds to it reducibly).
  let callTerm ← whnfR callTerm
  let callFn := callTerm.getAppFn
  let .const callName _ := callFn |
    (do trace[Halo2.subcircuit_rw] "skip: call head not a const: {callTerm}"; return none)
  let callArgs := callTerm.getAppArgs
  -- Both `call` heads share the argument order (from `variable` declaration order):
  --   [0]F [1]inst [2]Input [3]Output [4]ctInput [5]ctOutput [6]CI [7]Cfg [8]child [9]config …
  -- region: … [10]offset [11]input ;  layouter: … [10]input
  if isRegion && callName == ``FormalRegionCircuit.call then
    unless callArgs.size == 12 do
      trace[Halo2.subcircuit_rw] "skip: region call arity {callArgs.size}"; return none
    return some {
      isRegion := true
      F := callArgs[0]!, finiteField := callArgs[1]!, Input := callArgs[2]!, Output := callArgs[3]!
      ctInput := callArgs[4]!, ctOutput := callArgs[5]!, CI := callArgs[6]!, Cfg := callArgs[7]!
      child := callArgs[8]!, config := callArgs[9]!, offset? := some callArgs[10]!, input := callArgs[11]!
      place := place, env := env, regionIdx := regionIdx }
  else if !isRegion && callName == ``FormalCircuit.call then
    unless callArgs.size == 11 do
      trace[Halo2.subcircuit_rw] "skip: layouter call arity {callArgs.size}"; return none
    return some {
      isRegion := false
      F := callArgs[0]!, finiteField := callArgs[1]!, Input := callArgs[2]!, Output := callArgs[3]!
      ctInput := callArgs[4]!, ctOutput := callArgs[5]!, CI := callArgs[6]!, Cfg := callArgs[7]!
      child := callArgs[8]!, config := callArgs[9]!, offset? := none, input := callArgs[10]!
      place := place, env := env, regionIdx := regionIdx }
  else
    trace[Halo2.subcircuit_rw] "skip: call head mismatch ({callName})"
    return none

/-- Build a fully-applied leaf-lemma term of the shape produced by `matchChunk?`. `extraArgs`
are the trailing hypothesis arguments (e.g. the located `ExtendsWitnesses` fact for the
completeness leaves); pass `#[]` for the soundness leaf. Returns the application. -/
def mkLeaf (c : ChunkMatch) (leafName : Name) (env : Expr) (extraArgs : Array Expr) : MetaM Expr := do
  let common := #[c.F, c.finiteField, c.CI, c.Cfg, c.Input, c.Output, c.ctInput, c.ctOutput,
    c.child, c.config]
  let mid := match c.offset? with
    | some off => #[off, c.regionIdx, c.place, env, c.input]
    | none => #[c.regionIdx, c.place, env, c.input]
  return mkAppN (← mkConstWithFreshMVarLevels leafName) (common ++ mid ++ extraArgs)

/-- Build a fully-applied **Placed-view** leaf term (`*_placed` completeness leaves): the same
common prefix, but the `place`/`env` pair is replaced by a single `penv : Placed ProverEnvironment`
argument. Used when the chunk's `place`/`env` are `penv.place`/`penv.env` of a common `penv`. -/
def mkLeafPlaced (c : ChunkMatch) (leafName : Name) (penv : Expr) (extraArgs : Array Expr) :
    MetaM Expr := do
  let common := #[c.F, c.finiteField, c.CI, c.Cfg, c.Input, c.Output, c.ctInput, c.ctOutput,
    c.child, c.config]
  let mid := match c.offset? with
    | some off => #[off, c.regionIdx, penv, c.input]
    | none => #[c.regionIdx, penv, c.input]
  return mkAppN (← mkConstWithFreshMVarLevels leafName) (common ++ mid ++ extraArgs)

/-- If the chunk's `place`/`env` are the `.place`/`.env` projections of one common
`penv : Placed ProverEnvironment F`, return that `penv`. This is the shape
`FormalRegionCircuit.completeness_iff`/`FormalCircuit.completeness_iff` produce (they intro a
single `env : Placed ProverEnvironment` and constrain over `env.place`/`env.env`). When present,
the engine uses the `*_placed` leaves so the verifier view is spelled `penv.toEnvironment` rather
than the non-reducible reconstructed record `⟨penv.place, penv.env.toEnvironment⟩` (finding #1). -/
def placedEnv? (place env : Expr) : Option Expr := do
  -- A completeness GOAL chunk is `Constraints X.place self (X.env).toEnvironment ops` for a common
  -- `X : Placed ProverEnvironment F` (the verifier view of the honest prover env): `place` is
  -- field 0 (`Placed.place`) of `X`, and `env` is `ProverEnvironment.toEnvironment` applied to
  -- field 1 (`Placed.env`) of `X`. Accept both the application and primitive-projection forms of
  -- each projection. When present, return that `X` so the engine uses the `*_placed` leaves, which
  -- spell the verifier view as `X.toEnvironment` (= `⟨X.place, X.env.toEnvironment⟩`) — matching how
  -- consumer proofs write their bridges (finding #1). -/
  let placeProj (e : Expr) : Option Expr :=
    match e with
    | .proj ``Placed 0 s => some s
    | _ => if e.isAppOfArity ``Placed.place 3 then some e.appArg! else none
  let envProj (e : Expr) : Option Expr :=
    match e with
    | .proj ``Placed 1 s => some s
    | _ => if e.isAppOfArity ``Placed.env 3 then some e.appArg! else none
  -- strip the outer `ProverEnvironment.toEnvironment` on the env slot
  let env ← if env.isAppOfArity ``ProverEnvironment.toEnvironment 2 then some env.appArg!
            else if env.isAppOfArity ``ProverEnvironment.toEnvironment 1 then some env.appArg!
            else none
  let p ← placeProj place
  let v ← envProj env
  if p == v then some p else none

/-- Soundness-side leaf: for a matched chunk, produce `(replacementProp, proof : chunk → repl)`.
Instantiates `region_soundness_leaf`/`layouter_soundness_leaf`, confirms its hypothesis is
defeq to the matched chunk, and returns its conclusion as the replacement. -/
def soundnessLeaf? (c : ChunkMatch) (chunk : Expr) : MetaM (Option (Expr × Expr)) := do
  let leafName := if c.isRegion then ``region_soundness_leaf else ``layouter_soundness_leaf
  let leaf ← mkLeaf c leafName c.env #[]
  let leafTy ← inferType leaf
  let some (hyp, concl) := (← instantiateMVars leafTy).arrow? |
    (do trace[Halo2.subcircuit_rw] "soundness leaf not an arrow: {leafTy}"; return none)
  unless ← withTransparency .default <| isDefEq hyp chunk do
    trace[Halo2.subcircuit_rw] "soundness leaf hyp not defeq to chunk"
    return none
  return some (concl, ← instantiateMVars leaf)

/-! ### The polarity walker (soundness mode)

`walkPos P` returns `some (Q, proof : P → Q)` where `Q` is `P` with every **positive**-position
call-keyed chunk replaced by its child's soundness consequence, or `none` if `P` contains no
positive chunk (the caller then leaves `P` untouched). Recurses through `∧ ∨ → ∀ ∃`, flipping
polarity into the left of `→`; on that flipped (negative) side the chunk is left alone
(weakening there is unsound), so we don't recurse for rewrites there — we only need the
identity, handled by returning `none`. The proof is assembled from the congruence lemmas. -/

/-- Walk `p` in positive polarity, rewriting call-keyed chunks to their soundness consequence.
Returns `some (p', proof : p → p')` or `none` (no change). `depth` guards runaway recursion. -/
partial def walkPos (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let p ← instantiateMVars p
  -- Leaf: is `p` itself a call-keyed chunk?
  if let some c ← matchChunk? p then
    if let some (concl, proof) ← soundnessLeaf? c p then
      trace[Halo2.subcircuit_rw] "rewrote positive chunk (region={c.isRegion})"
      return some (concl, proof)
  -- Structural cases.
  match p.and? with
  | some (a, b) =>
    let ra ← walkPos a
    let rb ← walkPos b
    match ra, rb with
    | none, none => return none
    | _, _ =>
      let (a', pa) := ra.getD (a, ← identProof a)
      let (b', pb) := rb.getD (b, ← identProof b)
      let proof ← mkAppM ``SubcircuitRw.and_mono #[pa, pb]
      return some (← mkAppM ``And #[a', b'], proof)
  | none =>
  match or? p with
  | some (a, b) =>
    let ra ← walkPos a
    let rb ← walkPos b
    match ra, rb with
    | none, none => return none
    | _, _ =>
      let (a', pa) := ra.getD (a, ← identProof a)
      let (b', pb) := rb.getD (b, ← identProof b)
      let proof ← mkAppM ``SubcircuitRw.or_mono #[pa, pb]
      return some (← mkAppM ``Or #[a', b'], proof)
  | none =>
  -- `∀`/`→`. Distinguish a dependent ∀ from a plain implication.
  if p.isArrow then
    -- `a → b`: `a` is negative (skip), `b` positive.
    let a := p.bindingDomain!
    let b := p.bindingBody!
    match ← walkPos b with
    | none => return none
    | some (b', pb) =>
      -- left unchanged: `imp_mono (id : a → a) pb`
      let ida ← identProof a
      let proof ← mkAppM ``SubcircuitRw.imp_mono #[ida, pb]
      return some (← mkArrow a b', proof)
  else if p.isForall then
    forallTelescope1? p fun x body => do
      match ← walkPos body with
      | none => return none
      | some (body', pbody) =>
        -- `forall_mono (fun x => pbody) : (∀ x, body) → (∀ x, body')`
        let motiveOld ← mkLambdaFVars #[x] body
        let motiveNew ← mkLambdaFVars #[x] body'
        let hfun ← mkLambdaFVars #[x] pbody
        let proof ← mkAppOptM ``SubcircuitRw.forall_mono
          #[← inferType x, motiveOld, motiveNew, hfun]
        let newProp ← mkForallFVars #[x] body'
        return some (newProp, proof)
  else if p.isAppOf ``Exists then
    -- `∃ x, body x`
    let args := p.getAppArgs
    unless args.size == 2 do return none
    let α := args[0]!
    let pbody := args[1]!  -- a lambda `fun x => body`
    lambdaTelescope1? pbody fun x body => do
      match ← walkPos body with
      | none => return none
      | some (body', pbodyProof) =>
        let motiveOld ← mkLambdaFVars #[x] body
        let motiveNew ← mkLambdaFVars #[x] body'
        let hfun ← mkLambdaFVars #[x] pbodyProof
        let proof ← mkAppOptM ``SubcircuitRw.exists_mono #[α, motiveOld, motiveNew, hfun]
        let newProp ← mkAppOptM ``Exists #[α, motiveNew]
        return some (newProp, proof)
  else
    return none
where
  /-- The identity implication `p → p`, for connective children with no rewrite. -/
  identProof (p : Expr) : MetaM Expr := do
    withLocalDeclD `h p fun h => mkLambdaFVars #[h] h
  /-- Enter one `∀` binder if present. -/
  forallTelescope1? {α} (p : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
    forallBoundedTelescope p (some 1) fun xs body => do
      let #[x] := xs | throwError "subcircuit_rw: expected a ∀ binder"
      k x body
  /-- Enter one `fun` binder of a lambda. -/
  lambdaTelescope1? {α} (p : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
    lambdaBoundedTelescope p 1 fun xs body => do
      let #[x] := xs | throwError "subcircuit_rw: expected a λ binder"
      k x body

/-! ### ExtendsWitnesses location (completeness mode)

For a matched goal chunk, find a matching call-keyed `ExtendsWitnesses` fact in the local
context: either a whole hypothesis or a conjunct buried inside one (we walk `∧`-trees). "Match"
means the located fact's ops argument is `isDefEq` to the chunk's — same child/config/input at
the same region index, up to the prover-vs-verifier `env` (the witnesses fact lives over the
`ProverEnvironment`; the goal chunk over its `toEnvironment`, but the *ops* are identical). -/

/-- Is `cand` a call-keyed `ExtendsWitnesses` fact whose call matches chunk `c`? Compares
child/config/input/regionIdx (`.default` `isDefEq`); the env differs (prover vs verifier), so
we do not compare it. Returns the located fact (`cand`) on success. -/
def witnessMatches? (c : ChunkMatch) (cand : Expr) : MetaM Bool := do
  let cand ← instantiateMVars cand
  let fn := cand.getAppFn
  let .const headName _ := fn | return false
  let args := cand.getAppArgs
  let (isRegion, ops) ←
    if headName == ``RegionOperations.ExtendsWitnesses && args.size == 6 then pure (true, args[5]!)
    else if headName == ``Halo2.ExtendsWitnesses && args.size == 6 then pure (false, args[4]!)
    else return false
  unless isRegion == c.isRegion do return false
  -- dig out the call term and compare child/config/(offset)/input/regionIdx
  let opsFn := ops.getAppFn
  let .const opsName _ := opsFn | return false
  let opsArgs := ops.getAppArgs
  let callTerm ←
    if isRegion && opsName == ``RegionCircuit.operations && opsArgs.size ≥ 5 then pure opsArgs[3]!
    else if !isRegion && opsName == ``Circuit.operations && opsArgs.size ≥ 5 then pure opsArgs[3]!
    else return false
  let regionIdxCand := opsArgs[4]!
  let callTerm ← whnfR callTerm
  let callArgs := callTerm.getAppArgs
  let callFn := callTerm.getAppFn
  let .const callName _ := callFn | return false
  if isRegion && callName == ``FormalRegionCircuit.call && callArgs.size == 12 then
    withTransparency .default do
      return (← isDefEq callArgs[8]! c.child) && (← isDefEq callArgs[9]! c.config)
        && (← isDefEq callArgs[10]! c.offset?.get!) && (← isDefEq callArgs[11]! c.input)
        && (← isDefEq regionIdxCand c.regionIdx)
  else if !isRegion && callName == ``FormalCircuit.call && callArgs.size == 11 then
    withTransparency .default do
      return (← isDefEq callArgs[8]! c.child) && (← isDefEq callArgs[9]! c.config)
        && (← isDefEq callArgs[10]! c.input) && (← isDefEq regionIdxCand c.regionIdx)
  else
    return false

/-- Search the local context for a matching `ExtendsWitnesses` fact for chunk `c`: a whole
hypothesis, or a conjunct inside a hypothesis (`∧`-tree). Returns a proof term of the located
fact (built by projecting into the conjunction) and the fact's type. -/
partial def findWitness? (c : ChunkMatch) : TacticM (Option (Expr × Expr)) := withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some res ← digConjunction? c (.fvar decl.fvarId) ty then
      return some res
  return none
where
  /-- Recurse into `∧` looking for a matching witness fact; `proof : ty`. -/
  digConjunction? (c : ChunkMatch) (proof ty : Expr) : MetaM (Option (Expr × Expr)) := do
    let ty ← instantiateMVars ty
    if ← witnessMatches? c ty then
      return some (proof, ty)
    match ty.and? with
    | some (a, b) =>
      if let some res ← digConjunction? c (← mkAppM ``And.left #[proof]) a then return some res
      if let some res ← digConjunction? c (← mkAppM ``And.right #[proof]) b then return some res
      return none
    | none => return none

/-! ### Completeness leaves

For a matched goal chunk with a located witness fact `hw`, `completenessLeaf?` builds
`(strengthened, proof : strengthened → chunk)` — the goal-chunk strengthening — and
`derivedStatement` builds the derived contract `EnvA → A → PA → Spec ∧ ProverSpec`. -/

/-- Recover the *prover* environment from a located `ExtendsWitnesses` fact's arguments (the
leaf lemmas are stated over the prover env; the goal chunk carries `env.toEnvironment`). -/
def witnessEnv? (isRegion : Bool) (witTy : Expr) : Option Expr :=
  let args := witTy.getAppArgs
  if isRegion && args.size == 6 then some args[4]!
  else if !isRegion && args.size == 6 then some args[3]!
  else none

/-- Completeness strengthening leaf: `(strengthened, proof : strengthened → chunk)` where
`strengthened = EnvA ∧ A ∧ PA`. `witProof/witTy` is the located `ExtendsWitnesses` fact.
Prefers the Placed-view leaf (finding #1) when the chunk's `place`/`env` are projections of a
common `penv : Placed ProverEnvironment`; falls back to the bare leaf otherwise. -/
def completenessLeaf? (c : ChunkMatch) (chunk witProof witTy : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let leaf? ← match placedEnv? c.place c.env with
    | some penv =>
      let leafName := if c.isRegion then ``region_completeness_leaf_placed
        else ``layouter_completeness_leaf_placed
      pure (some (← mkLeafPlaced c leafName penv #[witProof]))
    | none =>
      match witnessEnv? c.isRegion witTy with
      | none =>
        trace[Halo2.subcircuit_rw] "could not recover prover env from witness fact"
        pure none
      | some penv =>
        let leafName := if c.isRegion then ``region_completeness_leaf
          else ``layouter_completeness_leaf
        pure (some (← mkLeaf c leafName penv #[witProof]))
  let some leaf := leaf? | return none
  let leafTy ← inferType leaf
  let some (strengthened, concl) := (← instantiateMVars leafTy).arrow? |
    (do trace[Halo2.subcircuit_rw] "completeness leaf not an arrow"; return none)
  unless ← withTransparency .default <| isDefEq concl chunk do
    trace[Halo2.subcircuit_rw] "completeness leaf conclusion not defeq to goal chunk"
    return none
  return some (strengthened, ← instantiateMVars leaf)

/-- Derived contract statement `EnvA → A → PA → Spec ∧ ProverSpec` from the located witness.
Placed-view (finding #1) when the projection shape is present, else bare. -/
def derivedStatement (c : ChunkMatch) (witProof witTy : Expr) : MetaM (Option (Expr × Expr)) := do
  let leaf? ← match placedEnv? c.place c.env with
    | some penv =>
      let leafName := if c.isRegion then ``region_completeness_derived_placed
        else ``layouter_completeness_derived_placed
      pure (some (← mkLeafPlaced c leafName penv #[witProof]))
    | none =>
      match witnessEnv? c.isRegion witTy with
      | none => pure none
      | some penv =>
        let leafName := if c.isRegion then ``region_completeness_derived
          else ``layouter_completeness_derived
        pure (some (← mkLeaf c leafName penv #[witProof]))
  let some leaf := leaf? | return none
  let leafTy ← inferType leaf
  return some (← instantiateMVars leafTy, ← instantiateMVars leaf)

/-! ### The completeness walker (finding #3: per-chunk precondition subgoals in op order)

Mirrors `walkPos`, but goals are **discharged in op order via a have-chain**. Each positive
call-keyed goal chunk becomes a separate PRECONDITION SUBGOAL `pre_i : EnvA ∧ A ∧ PA`
(sequenced in walk = op order); a fresh metavar `pre_i` stands for it. The chunk position in the
residual goal is closed by the strengthening leaf applied to `pre_i` (so the residual goal is the
parent's own constraints only — chunk conjuncts collapse to `True`). Simultaneously the derived
contract `h_spec_i := derived_i pre_i` — a **bare** `Spec ∧ ProverSpec` with the preconditions
already consumed — is introduced into the context of all later subgoals and the residual goal.

Consequence (the finding #3 fix): each precondition `EnvA ∧ A ∧ PA` is written exactly ONCE (in
its `pre_i` subgoal), instead of once to feed a premised `h_spec_i` and once to discharge the
strengthened goal. Chained bookkeeping (e.g. output threading) reads `h_spec_i` as a bare Spec. -/

/-- A located completeness chunk: the `pre_i` metavar (its type is the `EnvA ∧ A ∧ PA` bundle),
the name/type/proof of the bare derived statement `h_spec_i` (proof references `pre_i`). -/
structure CompChunk where
  /-- The precondition metavar `pre_i : EnvA ∧ A ∧ PA`, surfaced as a subgoal in op order. -/
  preMVar : MVarId
  /-- The bundle type `EnvA ∧ A ∧ PA` (the `pre_i` subgoal's goal). -/
  preType : Expr
  /-- The derived statement's user name `h_spec_i`. -/
  name : Name
  /-- The derived statement's type (`Spec ∧ ProverSpec`, bare — no premises). -/
  derivedType : Expr
  /-- The derived statement's proof term (references `preMVar`). -/
  derivedProof : Expr

/-- Completeness walker state: located chunks (in op order) + a running chunk index.
`legacy` selects the pre-finding-#3 behavior (strengthen the whole goal to the AND of `EnvA ∧ A ∧
PA` bundles + up-front PREMISED `h_spec_i : EnvA → A → PA → Spec ∧ ProverSpec`), kept available
per finding #3's "keep old behavior when the new one can't cover a pattern" clause. When `legacy`
is set the leaf replaces the chunk with the bundle (not `True`) and records the derived statement
in its arrow form. -/
structure WalkState where
  chunks : Array CompChunk := #[]
  idx : Nat := 0
  legacy : Bool := false

/-- Walk goal proposition `p` in positive polarity, discharging call-keyed chunks against fresh
precondition metavars. Returns `some (p', proof : p' → p)` or `none` (no change); in `p'` each
chunk position is `True`. Accumulates `CompChunk`s in op order. Runs in `TacticM` (needs the
local context to locate witness facts). -/
partial def walkGoal (p : Expr) : StateRefT WalkState TacticM (Option (Expr × Expr)) := do
  let p ← instantiateMVars p
  -- Leaf: a call-keyed chunk with a locatable witness fact.
  if let some c ← matchChunk? p then
    if let some (witProof, witTy) ← findWitness? c then
      if let some (bundle, strengthenProof) ← completenessLeaf? c p witProof witTy then
        if let some (dTy, dProof) ← derivedStatement c witProof witTy then
          let idx := (← get).idx
          let legacy := (← get).legacy
          modify fun s => { s with idx := s.idx + 1 }
          let nm := Name.mkSimple s!"h_spec_{idx}"
          if legacy then
            -- LEGACY: strengthen the chunk to the bundle in place (no separate subgoal), record the
            -- derived statement in its PREMISED arrow form; the runner introduces it up front.
            let derivedTy ← instantiateMVars dTy
            let entry : CompChunk :=
              { preMVar := ← mkFreshMVarId, preType := bundle, name := nm,
                derivedType := derivedTy, derivedProof := ← instantiateMVars dProof }
            modify fun s => { s with chunks := s.chunks.push entry }
            trace[Halo2.subcircuit_rw] "strengthened positive goal chunk (legacy, region={c.isRegion})"
            return some (bundle, strengthenProof)
          -- fresh precondition metavar `pre_i : bundle` (= `EnvA ∧ A ∧ PA`), a subgoal in op order
          let preMVar ← mkFreshExprSyntheticOpaqueMVar bundle (tag := Name.mkSimple s!"pre_{idx}")
          -- close the chunk position: `strengthenProof pre_i : chunk`; residual sees `True` here
          let chunkProof := mkApp strengthenProof preMVar
          let toChunk ← withLocalDeclD `h (mkConst ``True) fun h => mkLambdaFVars #[h] chunkProof
          -- the bare derived statement `h_spec_i := dProof pre.1 pre.2.1 pre.2.2 : Spec ∧ ProverSpec`
          -- (`dProof : EnvA → A → PA → Spec ∧ ProverSpec`, so feed the three bundle projections)
          let hE ← mkAppM ``And.left #[preMVar]
          let hAPA ← mkAppM ``And.right #[preMVar]
          let hA ← mkAppM ``And.left #[hAPA]
          let hPA ← mkAppM ``And.right #[hAPA]
          let derivedApplied := mkAppN dProof #[hE, hA, hPA]
          let derivedTy ← instantiateMVars (← inferType derivedApplied)
          let entry : CompChunk :=
            { preMVar := preMVar.mvarId!, preType := bundle, name := nm,
              derivedType := derivedTy, derivedProof := derivedApplied }
          modify fun s => { s with chunks := s.chunks.push entry }
          trace[Halo2.subcircuit_rw] "discharged positive goal chunk (region={c.isRegion})"
          return some (mkConst ``True, toChunk)
        else
          trace[Halo2.subcircuit_rw] "chunk matched but derived statement failed; leaving untouched"
      else
        trace[Halo2.subcircuit_rw] "chunk matched but completeness leaf failed; leaving untouched"
    else
      trace[Halo2.subcircuit_rw] "chunk matched but no ExtendsWitnesses fact located; untouched"
  match p.and? with
  | some (a, b) =>
    let ra ← walkGoal a
    let rb ← walkGoal b
    match ra, rb with
    | none, none => return none
    | _, _ =>
      let (a', pa) := ra.getD (a, ← identProof a)
      let (b', pb) := rb.getD (b, ← identProof b)
      return some (← mkAppM ``And #[a', b'], ← mkAppM ``SubcircuitRw.and_mono #[pa, pb])
  | none =>
  match or? p with
  | some (a, b) =>
    let ra ← walkGoal a
    let rb ← walkGoal b
    match ra, rb with
    | none, none => return none
    | _, _ =>
      let (a', pa) := ra.getD (a, ← identProof a)
      let (b', pb) := rb.getD (b, ← identProof b)
      return some (← mkAppM ``Or #[a', b'], ← mkAppM ``SubcircuitRw.or_mono #[pa, pb])
  | none =>
  if p.isArrow then
    let a := p.bindingDomain!
    let b := p.bindingBody!
    match ← walkGoal b with
    | none => return none
    | some (b', pb) =>
      return some (← mkArrow a b', ← mkAppM ``SubcircuitRw.imp_mono #[← identProof a, pb])
  else if p.isForall then
    forallBoundedTelescope p (some 1) fun xs body => do
      let #[x] := xs | return none
      match ← walkGoal body with
      | none => return none
      | some (body', pbody) =>
        let motiveOld ← mkLambdaFVars #[x] body
        let motiveNew ← mkLambdaFVars #[x] body'
        let hfun ← mkLambdaFVars #[x] pbody
        let proof ← mkAppOptM ``SubcircuitRw.forall_mono #[← inferType x, motiveNew, motiveOld, hfun]
        return some (← mkForallFVars #[x] body', proof)
  else if p.isAppOf ``Exists then
    let args := p.getAppArgs
    unless args.size == 2 do return none
    let α := args[0]!
    lambdaBoundedTelescope args[1]! 1 fun xs body => do
      let #[x] := xs | return none
      match ← walkGoal body with
      | none => return none
      | some (body', pbodyProof) =>
        let motiveOld ← mkLambdaFVars #[x] body
        let motiveNew ← mkLambdaFVars #[x] body'
        let hfun ← mkLambdaFVars #[x] pbodyProof
        let proof ← mkAppOptM ``SubcircuitRw.exists_mono #[α, motiveNew, motiveOld, hfun]
        return some (← mkAppOptM ``Exists #[α, motiveNew], proof)
  else
    return none
where
  identProof (p : Expr) : MetaM Expr := do
    withLocalDeclD `h p fun h => mkLambdaFVars #[h] h

/-- The engine's internal recursion-depth floor. Goal-mode `isDefEq` on deep composed chunks
(the nested-bind main-region term) exceeds the ambient 512; the engine raises its own matching /
instantiation depth so consumers don't set `maxRecDepth` for the tactic's sake (finding #2). Term-
depth value bookkeeping in the consumer (output projections through the deep term) is a separate
concern and keeps its own allowance where needed. -/
def recDepthFloor : Nat := 4096

/-- Soundness mode: rewrite positive call-keyed chunks in hypothesis `h` to the child's
`EnvAssumptions → Assumptions → Spec`, then `replace h`. No-op (silent) if nothing matched. -/
def runSoundness (fvarId : FVarId) : TacticM Unit := withAtLeastMaxRecDepth recDepthFloor <|
    withMainContext do
  let hyp ← instantiateMVars (← fvarId.getType)
  match ← walkPos hyp with
  | none =>
    trace[Halo2.subcircuit_rw] "no positive chunk found in hypothesis"
  | some (newProp, proof) =>
    -- `proof : hyp → newProp`; assert the new hypothesis, clear the old.
    let goal ← getMainGoal
    let hExpr := mkApp proof (.fvar fvarId)
    let (_, goal') ← (← goal.assert (← fvarId.getUserName) newProp hExpr).intro1P
    let goal' ← goal'.tryClearMany #[fvarId]
    replaceMainGoal [goal']

/-- Completeness mode (finding #3 have-chain): co-process the goal and the `ExtendsWitnesses`
context. For each positive goal chunk, in op order, emit a PRECONDITION SUBGOAL
`pre_i : EnvA ∧ A ∧ ProverA` (the chunk is discharged from `pre_i` via the strengthening leaf, so
the residual goal keeps only the parent's own constraints); simultaneously introduce the BARE
derived statement `h_spec_i : Spec ∧ ProverSpec` (preconditions already consumed) into the context
of every LATER subgoal and the residual goal. The surfaced goals are ordered `pre_0, …, pre_{n-1},
<residual>`. Silent no-op if nothing matched. -/
def runCompleteness (legacy : Bool := false) : TacticM Unit :=
    withAtLeastMaxRecDepth recDepthFloor <| withMainContext do
  let goalMVar ← getMainGoal
  let target ← instantiateMVars (← goalMVar.getType)
  let (res, st) ← (walkGoal target).run { legacy }
  match res with
  | none =>
    trace[Halo2.subcircuit_rw] "no strengthenable positive chunk found in goal"
  | some (newGoal, proof) =>
    -- `proof : newGoal → target`. Replace the main goal by `newGoal` via `proof ?_`.
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoal (tag := if legacy then `strengthened else `residual)
    goalMVar.assign (mkApp proof newMVar)
    if legacy then
      -- LEGACY: `newGoal` is the whole goal strengthened to the AND of `EnvA ∧ A ∧ PA` bundles;
      -- introduce all `h_spec_i` (premised `EnvA → A → PA → Spec ∧ ProverSpec`) up front, then hand
      -- the single strengthened goal to the user (the pre-finding-#3 behavior).
      let mut g := newMVar.mvarId!
      for ch in st.chunks do
        let g' ← g.assert ch.name ch.derivedType ch.derivedProof
        let (_, g'') ← g'.intro1P
        g := g''
      replaceMainGoal [g]
      return
    -- NEW (finding #3 have-chain): `newGoal` is the residual (chunk positions are `True`).
    -- Assert `h_spec_0 … h_spec_{k-1}` (the earlier bare derived statements) into a goal `g`, in
    -- order, so each is in scope. Returns the extended goal.
    let assertSpecsUpTo (g : MVarId) (k : Nat) : TacticM MVarId := do
      let mut g := g
      for ch in st.chunks[0:k] do
        let g' ← g.assert ch.name ch.derivedType ch.derivedProof
        let (_, g'') ← g'.intro1P
        g := g''
      return g
    -- The precondition subgoals, in op order; `pre_i` sees `h_spec_0 … h_spec_{i-1}`.
    let mut goals : Array MVarId := #[]
    let mut i := 0
    for ch in st.chunks do
      let g ← assertSpecsUpTo ch.preMVar i
      goals := goals.push g
      i := i + 1
    -- The residual goal sees all `h_spec_i`.
    let residual ← assertSpecsUpTo newMVar.mvarId! st.chunks.size
    goals := goals.push residual
    replaceMainGoal goals.toList

end SubcircuitRw

/-- `subcircuit_rw at h` (soundness) / `subcircuit_rw` (completeness, finding #3 have-chain) /
`subcircuit_rw legacy` (completeness, pre-finding-#3 whole-goal strengthening + premised `h_spec_i`,
kept for the few consumers whose goal shape the have-chain doesn't cleanly cover). See the module
docstring. Silent on shapes it doesn't target; `set_option trace.Halo2.subcircuit_rw true` to
debug. -/
syntax (name := subcircuitRw) "subcircuit_rw" (" at " ident)? (&" legacy")? : tactic

@[tactic subcircuitRw]
def evalSubcircuitRw : Tactic := fun stx => do
  match stx with
  | `(tactic| subcircuit_rw at $h:ident) =>
    let fvarId ← withMainContext <| getFVarId h
    SubcircuitRw.runSoundness fvarId
  | `(tactic| subcircuit_rw legacy) =>
    SubcircuitRw.runCompleteness (legacy := true)
  | `(tactic| subcircuit_rw) =>
    SubcircuitRw.runCompleteness
  | _ => throwUnsupportedSyntax

end Halo2
