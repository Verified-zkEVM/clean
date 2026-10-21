import Lean.Elab.Tactic
import Clean.Halo2.Subcircuit

/-!
# `subcircuit_rw` — the polarity-aware monotone subcircuit rewriter

The engine that parent proofs use to consume child contracts. See
`Clean/Halo2/subcircuit-engine-design.md` for the full design; this file is its implementation.
It replaced an earlier "absorption iff" mechanism, which has since been fully retired: the
migration is done and `subcircuit_rw` is now the sole consumption mechanism. `Subcircuit.lean`
keeps only the `call`-boundary opacity contract (a docstring there is the last record of the
retired iffs).

## The core idea

`chunk → X` is not an iff, so `simp`/`rw` can't consume a subcircuit chunk. But proof states
don't need iffs: **hypotheses may be weakened and goals strengthened** — one-directional
rewriting under polarity. The engine walks a proposition tracking polarity, replaces every
positive-position subcircuit chunk by the child's instantiated consequence, and builds the
implication `h_old → h_new` (soundness, `at h`) or `goal_new → goal_old` (completeness, goal)
from a fixed, hand-rolled congruence-lemma set (`∧ ∨ → ∀ ∃` monotonicity) with the child's
contract at the leaves.

## The two directions

* `subcircuit_rw at h` (**soundness**): walk `h`; every positive call-keyed chunk
  `RegionOperations.Constraints place self env ((child.call cfg off inp).operations self)`
  (region) or `Halo2.Constraints place env ((child.call cfg inp).operations i₀) i₀`
  (layouter) is replaced by the child's `EnvAssumptions → Assumptions → Spec` (its instantiated
  soundness consequence). `replace h` with the weakened proposition.

* `subcircuit_rw` (**completeness**, no location): co-processes the goal and the
  `ExtendsWitnesses` context in a single goal (maintainer decision D2 — the two can't be split;
  reverted to this shape 2026-07-12 after a per-chunk-subgoal redesign proved unable to carry
  shared honest-value bookkeeping across chained/composed subcircuits — see "Decisions" in
  `subcircuit-engine-design.md`). This is the main-Clean-faithful reduction: subcircuit
  statements are premises available in one goal context, exactly as in main Clean. For every
  positive-position chunk (in op order) it (a) locates the matching call-keyed
  `ExtendsWitnesses` fact in the local context (direct hypothesis or a conjunct inside one),
  (b) strengthens the goal chunk **in place** to `EnvAssumptions ∧ Assumptions ∧
  ProverAssumptions` (ExtendsWitnesses discharged from the located fact via the leaf lemma), and
  (c) introduces, up front, the **premised** derived contract statement
  `h_spec_<i> : EnvA → A → PA → Spec ∧ ProverSpec` (completeness then soundness — the old
  `call_constraints_and_specs` composition, now internal and read-off-the-term instantiated).
  The result is a single goal: the original goal with every positive chunk replaced by its
  precondition bundle, plus one premised `h_spec_i` per chunk already in context.

  **Dedup idiom (house style).** Both the goal's `EnvA ∧ A ∧ PA` bundle position AND each
  `h_spec_i`'s premises need the same `EnvA`/`A`/`PA` facts — proving them twice by hand is
  wasteful. Prove the bundle ONCE as a `have`, then feed its components to both the goal and
  `h_spec_i`:
  ```
  have pre₀ : child.EnvAssumptions … ∧ child.Assumptions … ∧ child.ProverAssumptions … :=
    ⟨…, …, …⟩
  refine ⟨pre₀, ?_⟩          -- or however the bundle closes the strengthened goal position
  have hspec := h_spec_0 pre₀.1 pre₀.2.1 pre₀.2.2   -- : Spec ∧ ProverSpec
  ```
  See `Clean/Halo2/Tests/TestSubcircuitRw.lean` (`chainedParent`) for a worked example.

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
    rw [FormalRegionCircuit.call_operations]
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
    rw [FormalCircuit.call_operations]
  rw [hcall]
  intro hc hE hA
  exact child.soundness config i₀ ⟨place, env⟩ input hE hA hc

/-- Consumer-facing call boundary (witness side): a `.call` chunk's `ExtendsWitnesses` is its
`synthesize`'s. Deliberately NOT `@[circuit_norm]` — the engine keys on the folded `.call`
marker; consumers of `∀`-bound loop chunks open it explicitly when they need the per-round
witness equations. -/
theorem FormalRegionCircuit.extendsWitnesses_call {F : Type} [FiniteField F]
    {CI Cfg : Type} {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F)
    (input : Var Input F) :
    RegionOperations.ExtendsWitnesses place self env
        ((child.call config offset input).operations self)
      ↔ RegionOperations.ExtendsWitnesses place self env
        ((child.synthesize config offset input).operations self) := by
  rw [FormalRegionCircuit.call_operations]

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
    child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
      (child.extract config offset input self (⟨place, env.toEnvironment⟩ : Placed Environment F))
      env.hint →
    child.Spec (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment F)
          (child.output config offset input self))
        (child.extract config offset input self (⟨place, env.toEnvironment⟩ : Placed Environment F))
      ∧ child.ProverSpec (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
          (eval (⟨place, env⟩ : Placed ProverEnvironment F) (child.output config offset input self))
          (child.extract config offset input self
            (⟨place, env.toEnvironment⟩ : Placed Environment F))
          env.hint := by
  have hw' : RegionOperations.ExtendsWitnesses place self env
      ((child.synthesize config offset input).operations self) := by
    have : RegionOperations.ExtendsWitnesses place self env
        ((child.call config offset input).operations self)
        = RegionOperations.ExtendsWitnesses place self env
            ((child.synthesize config offset input).operations self) := by
      rw [FormalRegionCircuit.call_operations]
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
      ∧ child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
          (child.extract config offset input self
            (⟨place, env.toEnvironment⟩ : Placed Environment F))
          env.hint)
    → RegionOperations.Constraints place self env
        ((child.call config offset input).operations self) := by
  have hw' : RegionOperations.ExtendsWitnesses place self env
      ((child.synthesize config offset input).operations self) := by
    have : RegionOperations.ExtendsWitnesses place self env
        ((child.call config offset input).operations self)
        = RegionOperations.ExtendsWitnesses place self env
            ((child.synthesize config offset input).operations self) := by
      rw [FormalRegionCircuit.call_operations]
    rwa [this] at hw
  have hcall : RegionOperations.Constraints place self env
      ((child.call config offset input).operations self)
      = RegionOperations.Constraints place self env
          ((child.synthesize config offset input).operations self) := by
    rw [FormalRegionCircuit.call_operations]
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
    child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
      (child.extract config input i₀ (⟨place, env.toEnvironment⟩ : Placed Environment F))
      env.hint →
    child.Spec (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
        (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) (child.output config input i₀))
        (child.extract config input i₀ (⟨place, env.toEnvironment⟩ : Placed Environment F))
      ∧ child.ProverSpec (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
          (eval (⟨place, env⟩ : Placed ProverEnvironment F) (child.output config input i₀))
          (child.extract config input i₀ (⟨place, env.toEnvironment⟩ : Placed Environment F))
          env.hint := by
  have hw' : Halo2.ExtendsWitnesses place env
      ((child.synthesize config input).operations i₀) i₀ := by
    have : Halo2.ExtendsWitnesses place env ((child.call config input).operations i₀) i₀
        = Halo2.ExtendsWitnesses place env ((child.synthesize config input).operations i₀) i₀ := by
      rw [FormalCircuit.call_operations]
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
      ∧ child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input)
          (child.extract config input i₀ (⟨place, env.toEnvironment⟩ : Placed Environment F))
          env.hint)
    → Halo2.Constraints place env ((child.call config input).operations i₀) i₀ := by
  have hw' : Halo2.ExtendsWitnesses place env
      ((child.synthesize config input).operations i₀) i₀ := by
    have : Halo2.ExtendsWitnesses place env ((child.call config input).operations i₀) i₀
        = Halo2.ExtendsWitnesses place env ((child.synthesize config input).operations i₀) i₀ := by
      rw [FormalCircuit.call_operations]
    rwa [this] at hw
  have hcall : Halo2.Constraints place env ((child.call config input).operations i₀) i₀
      = Halo2.Constraints place env ((child.synthesize config input).operations i₀) i₀ := by
    rw [FormalCircuit.call_operations]
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
    child.ProverAssumptions (eval penv input)
      (child.extract config offset input self penv.toEnvironment) penv.env.hint →
    child.Spec (eval penv.toEnvironment input)
        (eval penv.toEnvironment (child.output config offset input self))
        (child.extract config offset input self penv.toEnvironment)
      ∧ child.ProverSpec (eval penv input)
          (eval penv (child.output config offset input self))
          (child.extract config offset input self penv.toEnvironment) penv.env.hint :=
  region_completeness_derived child config offset self penv.place penv.env input hw

/-- Placed-view region completeness strengthening leaf. -/
theorem region_completeness_leaf_placed
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (penv : Placed ProverEnvironment F) (input : Var Input F)
    (hw : RegionOperations.ExtendsWitnesses penv.place self penv.env
      ((child.call config offset input).operations self)) :
    (child.EnvAssumptions config penv.toEnvironment
      ∧ child.Assumptions (eval penv.toEnvironment input)
      ∧ child.ProverAssumptions (eval penv input)
          (child.extract config offset input self penv.toEnvironment) penv.env.hint)
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
    child.ProverAssumptions (eval penv input)
      (child.extract config input i₀ penv.toEnvironment) penv.env.hint →
    child.Spec (eval penv.toEnvironment input)
        (eval penv.toEnvironment (child.output config input i₀))
        (child.extract config input i₀ penv.toEnvironment)
      ∧ child.ProverSpec (eval penv input)
          (eval penv (child.output config input i₀))
          (child.extract config input i₀ penv.toEnvironment) penv.env.hint :=
  layouter_completeness_derived child config i₀ penv.place penv.env input hw

/-- Placed-view layouter completeness strengthening leaf. -/
theorem layouter_completeness_leaf_placed
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (penv : Placed ProverEnvironment F) (input : Var Input F)
    (hw : Halo2.ExtendsWitnesses penv.place penv.env ((child.call config input).operations i₀) i₀) :
    (child.EnvAssumptions config penv.toEnvironment
      ∧ child.Assumptions (eval penv.toEnvironment input)
      ∧ child.ProverAssumptions (eval penv input)
          (child.extract config input i₀ penv.toEnvironment) penv.env.hint)
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
  /-- `self` (region) or `i₀` (layouter): the `Constraints`/`RegionOperations.Constraints`
  head's own region-index argument. Spelled via `regionCount` when a prior raw bind's
  `chunk_split` unfolded the preceding `operations`. -/
  regionIdx : Expr
  /-- The index the child's `.operations` is applied at (`(child.call …).operations HERE`).
  For a genuine chunk this is defeq to `regionIdx`, but it is spelled uniformly across
  the goal and witness sides (both from `operations_bind` → `(preceding).nextRegionIndex`),
  whereas `regionIdx` diverges — so witness matching compares THIS, not `regionIdx`. -/
  opsIdx : Expr

/-- Peel the empty prefix left behind when a monadic call is projected through a packed
result. This is an administrative `Circuit` bind, not part of the child call boundary. -/
private def stripEmptyAppend (operations : Expr) : Expr :=
  let fn := operations.getAppFn
  let args := operations.getAppArgs
  if fn.isConstOf ``List.append && args.size == 3 && args[1]!.getAppFn.isConstOf ``List.nil then
    args[2]!
  else
    operations

/-- Recover the pair underneath a second projection. Depending on elaboration, projections
appear either as `Prod.snd` applications or kernel projection nodes. -/
private def prodSndArg? (expression : Expr) : Option Expr :=
  match expression with
  | .proj typeName 1 pair => if typeName == ``Prod then some pair else none
  | _ =>
    let args := expression.getAppArgs
    if expression.getAppFn.isConstOf ``Prod.snd && !args.isEmpty then
      some args[args.size - 1]!
    else
      none

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
  let ops := stripEmptyAppend ops
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
    -- `RegionCircuit.operations`/`Circuit.operations` can reduce to the public packed
    -- call projections while the call itself remains opaque. Accept that equivalent
    -- boundary directly instead of depending on a particular transparency path.
    if isRegion && opsName == ``Prod.snd then
      let packed := opsArgs[opsArgs.size - 1]!
      let packedArgs := packed.getAppArgs
      if packedArgs.size ≥ 5 then
        let first := packedArgs.size - 5
        let childType ← whnfR (← inferType packedArgs[first]!)
        let .const childTypeName _ := childType.getAppFn | return none
        let childTypeArgs := childType.getAppArgs
        if childTypeName == ``FormalRegionCircuit && childTypeArgs.size == 8 then
          return some {
            isRegion := true
            F := childTypeArgs[0]!, finiteField := childTypeArgs[1]!
            CI := childTypeArgs[2]!, Cfg := childTypeArgs[3]!
            Input := childTypeArgs[4]!, Output := childTypeArgs[5]!
            ctInput := childTypeArgs[6]!, ctOutput := childTypeArgs[7]!
            child := packedArgs[first]!, config := packedArgs[first + 1]!,
            offset? := some packedArgs[first + 2]!, input := packedArgs[first + 3]!,
            place := place, env := env, regionIdx := regionIdx, opsIdx := packedArgs[first + 4]! }
    if !isRegion && opsName == ``Prod.fst then
      let tail := opsArgs[opsArgs.size - 1]!
      if let some packed := prodSndArg? tail then
        let packedArgs := packed.getAppArgs
        if packedArgs.size ≥ 4 then
          let first := packedArgs.size - 4
          let childType ← whnfR (← inferType packedArgs[first]!)
          let .const childTypeName _ := childType.getAppFn | return none
          let childTypeArgs := childType.getAppArgs
          if childTypeName == ``FormalCircuit && childTypeArgs.size == 8 then
            return some {
              isRegion := false
              F := childTypeArgs[0]!, finiteField := childTypeArgs[1]!
              CI := childTypeArgs[2]!, Cfg := childTypeArgs[3]!
              Input := childTypeArgs[4]!, Output := childTypeArgs[5]!
              ctInput := childTypeArgs[6]!, ctOutput := childTypeArgs[7]!
              child := packedArgs[first]!, config := packedArgs[first + 1]!, offset? := none
              input := packedArgs[first + 2]!, place := place, env := env, regionIdx := regionIdx
              opsIdx := packedArgs[first + 3]! }
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
      place := place, env := env, regionIdx := regionIdx, opsIdx := opsArgs[4]! }
  else if !isRegion && callName == ``FormalCircuit.call then
    unless callArgs.size == 11 do
      trace[Halo2.subcircuit_rw] "skip: layouter call arity {callArgs.size}"; return none
    return some {
      isRegion := false
      F := callArgs[0]!, finiteField := callArgs[1]!, Input := callArgs[2]!, Output := callArgs[3]!
      ctInput := callArgs[4]!, ctOutput := callArgs[5]!, CI := callArgs[6]!, Cfg := callArgs[7]!
      child := callArgs[8]!, config := callArgs[9]!, offset? := none, input := callArgs[10]!
      place := place, env := env, regionIdx := regionIdx, opsIdx := opsArgs[4]! }
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

/-- Return the `penv : Placed ProverEnvironment F` whose verifier view a completeness GOAL chunk's
`place`/`env` present, or `none` if `env` is not a `ProverEnvironment.toEnvironment` (no Placed view
to use). Two spellings are recognized:

* **projection shape (finding #1)** — `place = X.place` and `env = (X.env).toEnvironment` of one
  common `X`, as `FormalRegionCircuit.completeness_iff`/`FormalCircuit.completeness_iff` produce when
  a single `env : Placed ProverEnvironment` is introduced. Returns that `X`.
* **split shape** — after `circuit_proof_start` destructures the placed env, the chunk is
  `Constraints place self env.toEnvironment ops` over a bare `place`/`env`. Returns `⟨place, env⟩`.

Either way the `*_placed` leaves spell the verifier view as `penv.toEnvironment`
(`= ⟨penv.place, penv.env.toEnvironment⟩`), defeq to the chunk. Preferring the Placed view whenever
the chunk carries a `toEnvironment` verifier env is what makes the split-env completeness path
total: the bare leaf recovers its env from the located witness, which is NOT reliably defeq to the
chunk's for every child (a unit-input region feeding an abstracted output fails `isDefEq concl
chunk`), so it would silently drop such a chunk. -/
def placedEnv? (place env : Expr) : MetaM (Option Expr) := do
  let placeProj (e : Expr) : Option Expr :=
    match e with
    | .proj ``Placed 0 s => some s
    | _ => if e.isAppOfArity ``Placed.place 3 then some e.appArg! else none
  let envProj (e : Expr) : Option Expr :=
    match e with
    | .proj ``Placed 1 s => some s
    | _ => if e.isAppOfArity ``Placed.env 3 then some e.appArg! else none
  -- strip the outer `ProverEnvironment.toEnvironment` on the env slot; without it there is no
  -- Placed verifier view to reconstruct
  let some strippedEnv :=
    (if env.isAppOfArity ``ProverEnvironment.toEnvironment 2 then some env.appArg!
     else if env.isAppOfArity ``ProverEnvironment.toEnvironment 1 then some env.appArg!
     else none) | return none
  -- projection shape (finding #1): both are `.place`/`.env` of one common placed record `X`
  match placeProj place, envProj strippedEnv with
  | some p, some v => if p == v then return some p
                      else return some (← mkAppM ``Placed.mk #[place, strippedEnv])
  -- split shape (`circuit_proof_start` destructured the placed env): reconstruct `⟨place, env⟩`
  | _, _ => return some (← mkAppM ``Placed.mk #[place, strippedEnv])

/-! ### Abstract-output cooperation (the `abstract_outputs` contract)

`abstract_outputs`, run BEFORE the engine, replaces every child output by an opaque local `x`,
leaving an equation `h_gen_out_i : <child output> = x` in context (the canonical output form
`FormalRegionCircuit.output …`/`FormalCircuit.output …`). The engine must not undo that work:
when it emits a statement mentioning a child's own output (the soundness consequence's `Spec`, the
completeness derived statement's `Spec ∧ ProverSpec`), it emits **over the local** rather than
re-materializing the concrete output term.

`findOutputLocal?` looks up such an equation for a given (canonical) output; `abstractOutputsIn`
rewrites a `(ty, proof)` pair so every canonical-output occurrence that has a local is replaced by
it, threading the rewrite through the proof by `Eq.mpr` (soundness consequence: the conclusion is a
`Prop`; completeness derived: likewise). The rewrite keys on the abstraction equation itself
(`ty[out ↦ x]` via `congrArg` on a motive), so the emitted statement lands on the SAME local
`abstract_outputs` minted — no second local, no re-emission of the concrete output. -/

/-- Is `e` a canonical output-form application (`FormalRegionCircuit.output …` /
`FormalCircuit.output …`)? Same recognizer as `AbstractOutputs.isCanonicalOutput`, duplicated here
because `AbstractOutputs` imports this file (import direction forbids the reverse call). -/
def isOutputApp (e : Expr) : Bool :=
  e.isAppOf ``FormalRegionCircuit.output || e.isAppOf ``FormalCircuit.output

/-- Collect every canonical output-form subterm of `e`, innermost-first, deduped. Skips subterms
with loose bvars. Mirrors `AbstractOutputs.collectOutputs`. -/
partial def collectOutputApps (e : Expr) : StateRefT (Array Expr) MetaM Unit := do
  let e := e.consumeMData
  match e with
  | .app .. =>
    for a in e.getAppArgs do collectOutputApps a
    collectOutputApps e.getAppFn
    if isOutputApp e && !e.hasLooseBVars then
      modify fun acc => if acc.any (· == e) then acc else acc.push e
  | .lam _ t b _ | .forallE _ t b _ => collectOutputApps t; collectOutputApps b
  | .letE _ t v b _ => collectOutputApps t; collectOutputApps v; collectOutputApps b
  | .proj _ _ b => collectOutputApps b
  | .mdata _ b => collectOutputApps b
  | _ => pure ()

/-- Find an existing abstraction equation for output `e`: a hypothesis `h : lhs = x` with `x` a
free variable and `lhs` reducibly defeq to `e`. Returns `(x, heq : e = x)`. The `abstract_outputs`
locals (`h_gen_out_i : <output> = x_gen_out_i`) are exactly this shape. Runs in `MetaM` (reads the
ambient local context via `getLCtx`), so the `MetaM` walkers can call it. -/
def findOutputLocal? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    match ty.eq? with
    | some (_, lhs, rhs) =>
      if rhs.isFVar then
        if ← withTransparency .reducible <| isDefEq lhs e then
          let pf ← mkExpectedTypeHint (.fvar decl.fvarId) (← mkEq e rhs)
          return some (rhs, pf)
    | none => pure ()
  return none

/-- Rewrite a `(ty, proof)` pair (`proof : ty`, `ty : Prop`) so every canonical child-output
occurrence that has an `abstract_outputs` local is replaced by that local. For each such output `e`
with `heq : e = x` (`findOutputLocal?`), build the motive `M := fun z => ty[e ↦ z]` (abstracting `e`'s
occurrences) and rewrite `ty`/`proof` by `heq` via `M x`/`heq ▸ proof`. Returns the pair unchanged
if no output has a local. The rewrite is non-forcing (`kabstract` at `.reducible`), so a deep
composed output never unfolds. -/
def abstractOutputsIn (ty proof : Expr) :
    MetaM (Expr × Expr) := do
  let mut occs : Array Expr := #[]
  let (_, os) ← (collectOutputApps (← instantiateMVars ty)).run occs
  occs := os
  let mut ty := ty
  let mut proof := proof
  for e in occs do
    match ← findOutputLocal? e with
    | none => pure ()
    | some (x, heq) =>
      -- motive `M := fun z => ty[e ↦ z]`; `M e ≡ ty`, `M x = ty'`.
      let ety ← inferType e
      let abs ← withTransparency .reducible <| kabstract ty e
      unless abs.hasLooseBVars do continue
      let motive := Expr.lam `z ety abs .default
      let ty' := abs.instantiate1 x
      -- `proof : ty ≡ M e`; transport along `heq : e = x` to `M x = ty'`.
      let proof' ← mkEqMPR (← mkEqSymm (← mkAppM ``congrArg #[motive, heq])) proof
      trace[Halo2.subcircuit_rw] "engine emitted over abstract local for output"
      ty := ty'
      proof := proof'
  return (ty, proof)

/-- Soundness-side leaf: for a matched chunk, produce `(replacementProp, proof : chunk → repl)`.
Instantiates `region_soundness_leaf`/`layouter_soundness_leaf`, confirms its hypothesis is
defeq to the matched chunk, and returns its conclusion as the replacement. When `abstract_outputs`
has already minted a local for the child's output, the conclusion is emitted over that local (via
`abstractOutputsIn` on the leaf's `chunk → concl` implication, whose codomain mentions the
output). -/
def soundnessLeaf? (c : ChunkMatch) (chunk : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let leafName := if c.isRegion then ``region_soundness_leaf else ``layouter_soundness_leaf
  let leaf ← mkLeaf c leafName c.env #[]
  let leafTy ← inferType leaf
  let some (hyp, concl) := (← instantiateMVars leafTy).arrow? |
    (do trace[Halo2.subcircuit_rw] "soundness leaf not an arrow: {leafTy}"; return none)
  unless ← withTransparency .default <| isDefEq hyp chunk do
    trace[Halo2.subcircuit_rw] "soundness leaf hyp not defeq to chunk"
    return none
  -- emit the consequence over any abstract-output local `abstract_outputs` already minted
  let (_, leaf') ← abstractOutputsIn leafTy (← instantiateMVars leaf)
  let leafTy' ← inferType leaf'
  let some (_, concl') := (← instantiateMVars leafTy').arrow? | return some (concl, ← instantiateMVars leaf)
  return some (concl', leaf')

/-! ### The polarity walker (soundness mode)

`walkPos P` returns `some (Q, proof : P → Q)` where `Q` is `P` with every **positive**-position
call-keyed chunk replaced by its child's soundness consequence, or `none` if `P` contains no
positive chunk (the caller then leaves `P` untouched). Recurses through `∧ ∨ → ∀ ∃`, flipping
polarity into the left of `→`; on that flipped (negative) side the chunk is left alone
(weakening there is unsound), so we don't recurse for rewrites there — we only need the
identity, handled by returning `none`. The proof is assembled from the congruence lemmas. -/

/-- Walk `p` in positive polarity, rewriting call-keyed chunks to their soundness consequence.
Returns `some (p', proof : p → p')` or `none` (no change). `depth` guards runaway recursion.
With `strict` (the cps2 in-peel caller), a MATCHED chunk whose leaf fails is a hard error —
failure classes must surface, not degrade into a silently-raw chunk (maintainer ruling,
`atomic-binds-design.md` review note 3). -/
partial def walkPos (p : Expr) (strict : Bool := false)
    (useOpsIdx : Bool := false) :
    MetaM (Option (Expr × Expr)) := do
  -- Strip `mdata` wrappers (see `walkGoal`): the recognizers key on the bare head.
  let p := (← instantiateMVars p).consumeMData
  -- Leaf: is `p` itself a call-keyed chunk?
  if let some c ← matchChunk? p then
    -- `useOpsIdx` (cps2): emit the consequence at the OPS-index so the child `.output`
    -- lands on the minted atom reducibly (see `witnessMatches?`); v1 keeps `regionIdx`.
    let c := if useOpsIdx then { c with regionIdx := c.opsIdx } else c
    if let some (concl, proof) ← soundnessLeaf? c p then
      trace[Halo2.subcircuit_rw] "rewrote positive chunk (region={c.isRegion})"
      return some (concl, proof)
    else if strict then
      throwError "subcircuit_rw: matched a call-keyed chunk (child {indentExpr c.child}\n) \
        but the soundness leaf failed to instantiate at{indentExpr p}"
  -- Structural cases.
  match p.and? with
  | some (a, b) =>
    let ra ← walkPos a strict useOpsIdx
    let rb ← walkPos b strict useOpsIdx
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
    let ra ← walkPos a strict useOpsIdx
    let rb ← walkPos b strict useOpsIdx
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
    match ← walkPos b strict useOpsIdx with
    | none => return none
    | some (b', pb) =>
      -- left unchanged: `imp_mono (id : a → a) pb`
      let ida ← identProof a
      let proof ← mkAppM ``SubcircuitRw.imp_mono #[ida, pb]
      return some (← mkArrow a b', proof)
  else if p.isForall then
    forallTelescope1? p fun x body => do
      match ← walkPos body strict useOpsIdx with
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
      match ← walkPos body strict useOpsIdx with
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
child/config/(offset)/input/regionIdx, entirely at `.reducible` `isDefEq` (fail-fast): a genuine
match is spelled identically on both sides — the goal chunk and the witness fact originate from the
same `synthesize` unfolding, and `abstract_outputs` rewrote both sides' embedded outputs to the same
locals — so a match never needs unfolding. A `.default` comparison would δ-unfold MISMATCHED
candidates (e.g. `Add.add` vs `double_and_add 124 0` bundle literals, recursive loop `synthesize`
bodies included) and was the engine's residual `maxRecDepth` consumer. A genuinely-missed witness
surfaces as a loud "no ExtendsWitnesses fact located" skip. The env differs (prover vs verifier),
so we do not compare it. Returns the located fact (`cand`) on success. -/
def witnessMatches? (c : ChunkMatch) (cand : Expr)
    (useOpsIdx : Bool := false) : MetaM Bool := do
  let cand ← instantiateMVars cand
  let fn := cand.getAppFn
  let .const headName _ := fn | return false
  let args := cand.getAppArgs
  let (isRegion, ops) ←
    if headName == ``RegionOperations.ExtendsWitnesses && args.size == 6 then pure (true, args[5]!)
    else if headName == ``Halo2.ExtendsWitnesses && args.size == 6 then pure (false, args[4]!)
    else return false
  unless isRegion == c.isRegion do return false
  let ops := stripEmptyAppend ops
  -- dig out the call term and compare child/config/(offset)/input/regionIdx
  let opsFn := ops.getAppFn
  let .const opsName _ := opsFn | return false
  let opsArgs := ops.getAppArgs
  let idxTarget := if useOpsIdx then c.opsIdx else c.regionIdx
  if isRegion && opsName == ``Prod.snd then
    let packed := opsArgs[opsArgs.size - 1]!
    let packedArgs := packed.getAppArgs
    if packedArgs.size ≥ 5 then
      let first := packedArgs.size - 5
      return ← withTransparency .reducible do
        return (← isDefEq packedArgs[first]! c.child)
          && (← isDefEq packedArgs[first + 1]! c.config)
          && (← isDefEq packedArgs[first + 2]! c.offset?.get!)
          && (← isDefEq packedArgs[first + 3]! c.input)
          && (← isDefEq packedArgs[first + 4]! idxTarget)
  if !isRegion && opsName == ``Prod.fst then
    let tail := opsArgs[opsArgs.size - 1]!
    if let some packed := prodSndArg? tail then
      let packedArgs := packed.getAppArgs
      if packedArgs.size ≥ 4 then
        let first := packedArgs.size - 4
        return ← withTransparency .reducible do
          return (← isDefEq packedArgs[first]! c.child)
            && (← isDefEq packedArgs[first + 1]! c.config)
            && (← isDefEq packedArgs[first + 2]! c.input)
            && (← isDefEq packedArgs[first + 3]! idxTarget)
  let callTerm ←
    if isRegion && opsName == ``RegionCircuit.operations && opsArgs.size ≥ 5 then pure opsArgs[3]!
    else if !isRegion && opsName == ``Circuit.operations && opsArgs.size ≥ 5 then pure opsArgs[3]!
    else return false
  let regionIdxCand := opsArgs[4]!
  let callTerm ← whnfR callTerm
  let callArgs := callTerm.getAppArgs
  let callFn := callTerm.getAppFn
  let .const callName _ := callFn | return false
  -- ALL compares are fail-fast at `.reducible`: a MISMATCHED candidate must not
  -- δ-unfold (bundle literals, recursive `synthesize` bodies — the engine's old
  -- maxRecDepth consumer). A genuine match is spelled identically on both sides
  -- (same `synthesize` unfolding), so it never needs unfolding.
  -- `useOpsIdx` (cps2 in-peel only): compare the candidate's OPS-index against the
  -- chunk's OPS-index (`c.opsIdx`), NOT the chunk's `Constraints` region-arg. Both
  -- ops-indices come from the same `operations_bind` split
  -- (`(preceding).nextRegionIndex i₀`) and so are spelled identically on the goal and
  -- witness sides, matching REDUCIBLY — whereas the `Constraints` region-arg is
  -- `regionCount`-based on the goal (a prior raw bind's `chunk_split` unfolded the
  -- preceding `operations`) and diverges. Matching on `opsIdx` is what let the cps2
  -- driver drop the relaxed-transparency pass entirely. The v1 driver keeps the
  -- `regionIdx` compare (default) verbatim.
  if isRegion && callName == ``FormalRegionCircuit.call && callArgs.size == 12 then
    withTransparency .reducible do
      return (← isDefEq callArgs[8]! c.child) && (← isDefEq callArgs[9]! c.config)
        && (← isDefEq callArgs[10]! c.offset?.get!) && (← isDefEq callArgs[11]! c.input)
        && (← isDefEq regionIdxCand idxTarget)
  else if !isRegion && callName == ``FormalCircuit.call && callArgs.size == 11 then
    withTransparency .reducible do
      return (← isDefEq callArgs[8]! c.child) && (← isDefEq callArgs[9]! c.config)
        && (← isDefEq callArgs[10]! c.input) && (← isDefEq regionIdxCand idxTarget)
  else
    return false

/-- Search the local context for a matching `ExtendsWitnesses` fact for chunk `c`: a whole
hypothesis, or a conjunct inside a hypothesis (`∧`-tree). Returns a proof term of the located
fact (built by projecting into the conjunction) and the fact's type. -/
partial def findWitness? (c : ChunkMatch) :
    TacticM (Option (Expr × Expr)) := withMainContext do
  -- single reducible pass: a genuine match is spelled identically on both sides (incl.
  -- the 85-round loop families), so no transparency retry is needed
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some res ← digConjunction? c (.fvar decl.fvarId) ty then
      return some res
  return none
where
  /-- Recurse into `∧` looking for a matching witness fact; `proof : ty`. -/
  digConjunction? (c : ChunkMatch) (proof ty : Expr) :
      MetaM (Option (Expr × Expr)) := do
    let ty ← instantiateMVars ty
    if ← witnessMatches? c ty then
      return some (proof, ty)
    match ty.and? with
    | some (a, b) =>
      if let some res ← digConjunction? c (← mkAppM ``And.left #[proof]) a then
        return some res
      if let some res ← digConjunction? c (← mkAppM ``And.right #[proof]) b then
        return some res
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
  let leaf? ← match ← placedEnv? c.place c.env with
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
def derivedStatement (c : ChunkMatch) (witProof witTy : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let leaf? ← match ← placedEnv? c.place c.env with
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
  -- emit the derived statement (its `Spec ∧ ProverSpec` mentions the child output under `eval`)
  -- over any abstract-output local `abstract_outputs` already minted, instead of the concrete
  -- output term — so the honest bookkeeping downstream sees `x_gen_out_i`, not a re-materialized
  -- composed `.output`.
  let (leafTy', leaf') ← abstractOutputsIn (← instantiateMVars leafTy)
    (← instantiateMVars leaf)
  return some (leafTy', leaf')

/-! ### The completeness walker

Walks the goal in positive polarity. Each positive call-keyed chunk is strengthened **in place**
to its precondition bundle `EnvA ∧ A ∧ PA` (ExtendsWitnesses discharged from the located witness
fact via the strengthening leaf), so the walk produces a single new goal proposition — the
original with every positive chunk replaced by its bundle. Simultaneously, per chunk, the walker
records the **premised** derived contract statement `h_spec_i : EnvA → A → PA → Spec ∧
ProverSpec`; the runner asserts all of these into the context up front, before handing back the
one strengthened goal. -/

/-- A located completeness chunk: the name/type/proof of the premised derived statement
`h_spec_i : EnvA → A → PA → Spec ∧ ProverSpec` that the runner asserts into context. -/
structure CompChunk where
  /-- The derived statement's user name `h_spec_i`. -/
  name : Name
  /-- The derived statement's type (`EnvA → A → PA → Spec ∧ ProverSpec`, premised). -/
  derivedType : Expr
  /-- The derived statement's proof term. -/
  derivedProof : Expr

/-- Completeness walker state: located chunks (in op order). -/
structure WalkState where
  chunks : Array CompChunk := #[]
  idx : Nat := 0

/-- Walk goal proposition `p` in positive polarity, strengthening call-keyed chunks in place to
their precondition bundle. Returns `some (p', proof : p' → p)` or `none` (no change); in `p'`
each chunk position is its `EnvA ∧ A ∧ PA` bundle. Accumulates `CompChunk`s (the premised derived
statements) in op order. Runs in `TacticM` (needs the local context to locate witness facts). -/
partial def walkGoal (p : Expr) :
    StateRefT WalkState TacticM (Option (Expr × Expr)) := do
  -- Strip `mdata` wrappers (e.g. left by a prior `simp only … at ⊢`): the connective/chunk
  -- recognizers below all key on the bare head, and `mdata` is definitionally transparent so the
  -- monotone-implication proof we build against the stripped form still types against the wrapped
  -- goal. Without this the walker sees an `.mdata` node, matches nothing, and silently no-ops.
  let p := (← instantiateMVars p).consumeMData
  -- Leaf: a call-keyed chunk with a locatable witness fact.
  if let some c ← matchChunk? p then
    trace[Halo2.subcircuit_rw] "leaf: chunk matched"
    if let some (witProof, witTy) ← findWitness? c then
      trace[Halo2.subcircuit_rw] "leaf: witness located"
      if let some (bundle, strengthenProof) ← completenessLeaf? c p witProof witTy then
        trace[Halo2.subcircuit_rw] "leaf: strengthening leaf built"
        if let some (dTy, dProof) ← derivedStatement c witProof witTy then
          trace[Halo2.subcircuit_rw] "leaf: derived statement built"
          let idx := (← get).idx
          modify fun s => { s with idx := s.idx + 1 }
          let nm := Name.mkSimple s!"h_spec_{idx}"
          -- strengthen the chunk to the bundle in place; record the derived statement in its
          -- PREMISED arrow form `EnvA → A → PA → Spec ∧ ProverSpec` — the runner introduces it
          -- up front, before handing back this strengthened goal.
          let derivedTy ← instantiateMVars dTy
          let entry : CompChunk :=
            { name := nm, derivedType := derivedTy, derivedProof := ← instantiateMVars dProof }
          modify fun s => { s with chunks := s.chunks.push entry }
          trace[Halo2.subcircuit_rw] "strengthened positive goal chunk (region={c.isRegion})"
          return some (bundle, strengthenProof)
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

/-! ### Soundness/completeness runners

The engine's former deep-argument machinery is FULLY retired — the soundness-side depth threshold
(`boundedDepth`/`generalizeThreshold`/`inputIsDeep`/`collectDeepInputs`/`abstractInExpr`) AND the
completeness-side `recDepthFloor`/`withAtLeastMaxRecDepth` raise. Two mechanisms replaced it:

* `abstract_outputs` (run before the engine) makes every output expression an opaque local — child
  bundle outputs AND (guise 8) a parent's own unfolded composed region output (`(do …).output i₀`,
  e.g. Mul's `(mainRegion …).output` feeding the overflow chunk's input) — so no deep term is left
  in any chunk the walker or its leaf `isDefEq`s traverse;
* `witnessMatches?` compares entirely at `.reducible`: a genuine goal-chunk/witness-fact pair is
  spelled identically (both originate from the same `synthesize` unfolding, and abstraction rewrote
  both sides to the same locals), so a match never needs unfolding — while a MISMATCH (e.g.
  `Add.add` vs `double_and_add 124 0` when scanning the context) would δ-unfold both bundle
  structure literals (including recursive loop `synthesize` bodies) at `.default` and blow the
  recursion budget. Fail-fast means a genuinely-missed witness surfaces as a loud
  "no ExtendsWitnesses fact located" skip, not a silent deep unfold.

The engine therefore runs at the ambient recursion limit; no consumer sets `maxRecDepth`. -/

/-- Soundness mode: rewrite positive call-keyed chunks in hypothesis `h` to the child's
`EnvAssumptions → Assumptions → Spec`, then `replace h`. No-op (silent) if nothing matched.

Deep chunk inputs no longer need special handling here: `abstract_outputs`, run before the engine,
has already replaced every child output by an opaque local, so a chunk input that used to embed a
composed `.output` is shallow by construction. When the weakened hypothesis mentions the child's own
output, `walkPos`'s soundness leaf emits it over the existing abstract local (Stage-1 cooperation),
so nothing derived from the hypothesis re-materializes a deep composed output. -/
def runSoundness (fvarId : FVarId) (strict : Bool := false)
    (useOpsIdx : Bool := false) :
    TacticM Unit := withMainContext do
  let hyp ← instantiateMVars (← fvarId.getType)
  match ← walkPos hyp strict useOpsIdx with
  | none =>
    trace[Halo2.subcircuit_rw] "no positive chunk found in hypothesis"
  | some (newProp, proof) =>
    -- `proof : hyp → newProp`; assert the new hypothesis, clear the old.
    let goal ← getMainGoal
    let hExpr := mkApp proof (.fvar fvarId)
    let (_, goal') ← (← goal.assert (← fvarId.getUserName) newProp hExpr).intro1P
    let goal' ← goal'.tryClearMany #[fvarId]
    replaceMainGoal [goal']

/-- Completeness mode: co-process the goal and the `ExtendsWitnesses` context in a single goal.
For every positive goal chunk, in op order, strengthen it **in place** to its precondition bundle
`EnvA ∧ A ∧ ProverA` (ExtendsWitnesses discharged from the located witness fact via the
strengthening leaf), and introduce the PREMISED derived statement
`h_spec_i : EnvA → A → PA → Spec ∧ ProverSpec` up front, before handing back the single
strengthened goal. Silent no-op if nothing matched. -/
def runCompleteness : TacticM Unit := withMainContext do
  let goalMVar ← getMainGoal
  let target ← instantiateMVars (← goalMVar.getType)
  trace[Halo2.subcircuit_rw] "completeness: walking goal"
  let (res, st) ← (walkGoal target).run {}
  trace[Halo2.subcircuit_rw] "completeness: walk done ({st.chunks.size} chunk(s))"
  match res with
  | none =>
    trace[Halo2.subcircuit_rw] "no strengthenable positive chunk found in goal"
  | some (newGoal, proof) =>
    -- `proof : newGoal → target`. Replace the main goal by `newGoal` via `proof ?_`.
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoal (tag := `strengthened)
    goalMVar.assign (mkApp proof newMVar)
    -- `newGoal` is the whole goal strengthened to the AND of `EnvA ∧ A ∧ PA` bundles; introduce
    -- all `h_spec_i` (premised `EnvA → A → PA → Spec ∧ ProverSpec`) up front, then hand the
    -- single strengthened goal to the user.
    let mut g := newMVar.mvarId!
    trace[Halo2.subcircuit_rw] "completeness: goal strengthened"
    for ch in st.chunks do
      let g' ← g.assert ch.name ch.derivedType ch.derivedProof
      let (_, g'') ← g'.intro1P
      g := g''
      trace[Halo2.subcircuit_rw] "completeness: asserted {ch.name}"
    replaceMainGoal [g]

end SubcircuitRw

/-- `subcircuit_rw at h` (soundness) / `subcircuit_rw` (completeness — the goal is strengthened
in place to the AND of each chunk's `EnvA ∧ A ∧ PA` precondition bundle, and a premised
`h_spec_i : EnvA → A → PA → Spec ∧ ProverSpec` is introduced up front per chunk). See the module
docstring. Silent on shapes it doesn't target; `set_option trace.Halo2.subcircuit_rw true` to
debug. -/
syntax (name := subcircuitRw) "subcircuit_rw" (" at " ident)? : tactic

@[tactic subcircuitRw]
def evalSubcircuitRw : Tactic := fun stx => do
  match stx with
  | `(tactic| subcircuit_rw at $h:ident) =>
    let fvarId ← withMainContext <| getFVarId h
    SubcircuitRw.runSoundness fvarId
  | `(tactic| subcircuit_rw) =>
    SubcircuitRw.runCompleteness
  | _ => throwUnsupportedSyntax

end Halo2
