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
`strengthened = EnvA ∧ A ∧ PA`. `witProof/witTy` is the located `ExtendsWitnesses` fact. -/
def completenessLeaf? (c : ChunkMatch) (chunk witProof witTy : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some penv := witnessEnv? c.isRegion witTy |
    (do trace[Halo2.subcircuit_rw] "could not recover prover env from witness fact"; return none)
  let leafName := if c.isRegion then ``region_completeness_leaf else ``layouter_completeness_leaf
  let leaf ← mkLeaf c leafName penv #[witProof]
  let leafTy ← inferType leaf
  let some (strengthened, concl) := (← instantiateMVars leafTy).arrow? |
    (do trace[Halo2.subcircuit_rw] "completeness leaf not an arrow"; return none)
  unless ← withTransparency .default <| isDefEq concl chunk do
    trace[Halo2.subcircuit_rw] "completeness leaf conclusion not defeq to goal chunk"
    return none
  return some (strengthened, ← instantiateMVars leaf)

/-- Derived contract statement `EnvA → A → PA → Spec ∧ ProverSpec` from the located witness. -/
def derivedStatement (c : ChunkMatch) (witProof witTy : Expr) : MetaM (Option (Expr × Expr)) := do
  let some penv := witnessEnv? c.isRegion witTy | return none
  let leafName := if c.isRegion then ``region_completeness_derived else ``layouter_completeness_derived
  let leaf ← mkLeaf c leafName penv #[witProof]
  let leafTy ← inferType leaf
  return some (← instantiateMVars leafTy, ← instantiateMVars leaf)

/-! ### The completeness walker

Mirrors `walkPos`, but goals are **strengthened**: `walkGoal P` returns `some (Q, proof : Q → P)`
with positive chunks replaced by their strengthened preconditions. Side output: the list of
derived statements (name-suffixed per child) to introduce. -/

/-- Fresh-name suffix for a chunk's derived statement. The scheme is the **positional index**
of the chunk within the goal (in walk order, 0-based): the introduced hypotheses are
`h_spec_0`, `h_spec_1`, …, one per positive goal chunk. Positional (not name-derived) because
child bundle names may be long, contain spaces, or repeat when a parent composes two instances
of the same child (the `TestLayouterSubcircuit` parent does exactly that) — the index is always
unique and predictable. -/
def chunkSuffix (_c : ChunkMatch) (idx : Nat) : MetaM String := do
  return s!"{idx}"

/-- Accumulator entry for a derived statement to introduce: user-facing name, type, proof. -/
structure Derived where
  name : Name
  type : Expr
  proof : Expr

/-- Completeness walker state: located derived statements + a running chunk index. -/
structure WalkState where
  derived : Array Derived := #[]
  idx : Nat := 0

/-- Walk goal proposition `p` in positive polarity, strengthening call-keyed chunks. Returns
`some (p', proof : p' → p)` or `none` (no change). Accumulates derived statements in the state.
Runs in `TacticM` (needs the local context to locate witness facts). -/
partial def walkGoal (p : Expr) : StateRefT WalkState TacticM (Option (Expr × Expr)) := do
  let p ← instantiateMVars p
  -- Leaf: a call-keyed chunk with a locatable witness fact.
  if let some c ← matchChunk? p then
    if let some (witProof, witTy) ← findWitness? c then
      if let some (strengthened, proof) ← completenessLeaf? c p witProof witTy then
        let idx := (← get).idx
        let suffix ← chunkSuffix c idx
        modify fun s => { s with idx := s.idx + 1 }
        if let some (dTy, dProof) ← derivedStatement c witProof witTy then
          let nm := Name.mkSimple s!"h_spec_{suffix}"
          modify fun s => { s with derived := s.derived.push ⟨nm, dTy, dProof⟩ }
        trace[Halo2.subcircuit_rw] "strengthened positive goal chunk (region={c.isRegion})"
        return some (strengthened, proof)
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

/-- Soundness mode: rewrite positive call-keyed chunks in hypothesis `h` to the child's
`EnvAssumptions → Assumptions → Spec`, then `replace h`. No-op (silent) if nothing matched. -/
def runSoundness (fvarId : FVarId) : TacticM Unit := withMainContext do
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

/-- Completeness mode: co-process the goal and the `ExtendsWitnesses` context. Strengthen every
positive goal chunk to `EnvA ∧ A ∧ ProverA` (discharging `ExtendsWitnesses` from a located
context fact), and introduce the derived contract statement `h_spec_<child> : EnvA → A → PA →
Spec ∧ ProverSpec` for each. Silent no-op if nothing matched. -/
def runCompleteness : TacticM Unit := withMainContext do
  let goalMVar ← getMainGoal
  let target ← instantiateMVars (← goalMVar.getType)
  let (res, st) ← (walkGoal target).run {}
  match res with
  | none =>
    trace[Halo2.subcircuit_rw] "no strengthenable positive chunk found in goal"
  | some (newGoal, proof) =>
    -- `proof : newGoal → target`. Replace the goal by `newGoal` via `proof ?_`.
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoal
    goalMVar.assign (mkApp proof newMVar)
    let mut g := newMVar.mvarId!
    -- Introduce the derived statements as fresh hypotheses (before the user continues).
    for d in st.derived do
      let g' ← g.assert d.name d.type d.proof
      let (_, g'') ← g'.intro1P
      g := g''
    replaceMainGoal [g]

end SubcircuitRw

/-- `subcircuit_rw at h` (soundness) / `subcircuit_rw` (completeness). See the module docstring.
Silent on shapes it doesn't target; `set_option trace.Halo2.subcircuit_rw true` to debug. -/
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
