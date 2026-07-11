import Clean.Halo2.Formal
import Clean.Halo2.Lemmas

/-!
# Subcircuit composition: the absorption-iff mechanism

A subcircuit call emits `.subcircuit ops` carrying the child's raw op list; the child does
not store its `Spec`. In a parent soundness proof the child appears as one folded
`(child.call config offset input).operations self` chunk. We have the *forward* fact
`chunk → (Assumptions → Spec)` (raw constraints are strictly stronger than the spec), an
implication — and `simp`/`rw` fire only on `Eq`/`Iff`. The trick: whenever `chunk → X`,
the **absorption iff** `chunk ↔ chunk ∧ X` holds, and an iff simp *can* use. One generic
simp lemma then rewrites every subcircuit chunk in place to expose the child's spec.

## The opaque call boundary (why this is robust)

The iffs key on `RegionOperations.Constraints … ((child.call …).operations self)` — the
CALL term as a whole, NOT `(child.synthesize …).operations self`. Plain `circuit_norm`
does not unfold `RegionCircuit.operations` on a `call` term, so the child chunk stays
folded automatically: the parent's own binds decompose via `operations_bind` → `++` and
`RegionOperations.constraints_append` splits the parent conjunction *around* the folded
call term, isolating it as a clean conjunct the iff matches. No scoped simp set, no
`call_operations` computation lemma (that footgun cracked `call` open and let the accessor
lemmas reach and shred the child's `synthesize` ops). The iff's *proof* unfolds `call`
internally (defeq to `[.subcircuit ((child.synthesize …).operations self)]`) to reach the
child's contract; the *statement* keeps `call` folded.

The surviving raw chunk on the RHS is `(call).operations`-keyed too (same as the LHS), so
without a guard `simp` would re-fire the iff on it forever. We hide it behind the opaque
`SubcircuitConstraints` marker (a distinct head `circuit_norm`/this iff never match), so the
rewrite happens exactly once.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {CI Cfg : Type} {Input Output Witness : TypeMap}

/-- Opaque marker wrapping a raw `RegionOperations.Constraints` chunk — definitionally equal
to it, but with a *distinct head* so the absorption iffs below (and `circuit_norm`) never
re-fire on the surviving RHS copy. Not tagged `@[circuit_norm]`. -/
def SubcircuitConstraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) (ops : RegionOperations F) : Prop :=
  RegionOperations.Constraints place self env ops

/-- Layouter-level counterpart of `SubcircuitConstraints`: opaque marker wrapping a raw
layouter `Halo2.Constraints` chunk (definitionally equal, distinct head), so the layouter
absorption iffs never re-fire on the surviving RHS copy. Not tagged `@[circuit_norm]`. -/
def SubcircuitConstraintsL (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) : Prop :=
  Halo2.Constraints place env ops i

section
variable [CircuitType Input] [CircuitType Output]

/-- `output` of a layouter `call` (the child's output) — a `circuit_norm` accessor lemma. -/
@[circuit_norm]
theorem FormalCircuit.output_call (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (self.call config input).output i = self.output config input i := rfl

/-- `nextRegionIndex` of a layouter `call`, spelled as the append offset
`Operations.regionCount ((self.call …).operations i)` — so that when a parent's
`operations_bind` splits into `++` and `constraints_append` threads its offset, a *second*
subcircuit call's index matches the append form and the absorption iff still fires on it.
Keeping `call.operations` folded (the iff key), this bridges the two spellings of "how many
regions the first call consumed". `@[circuit_norm]`. -/
@[circuit_norm]
theorem FormalCircuit.nextRegionIndex_call (self : FormalCircuit F CI Cfg Input Output)
    (config : Cfg) (input : Var Input F) (i : RegionIndex) :
    (self.call config input).nextRegionIndex i
      = i + Operations.regionCount ((self.call config input).operations i) := by
  show i + self.regionCount config input
    = i + Operations.regionCount ((self.call config input).operations i)
  congr 1
  -- `regionCount = ((synthesize …).operations i).regionCount` (elaborated metadata), and the
  -- `call`'s single `.subcircuit` op has exactly that `Operations.regionCount`.
  rw [FormalCircuit.regionCount, (self.elaborated config).regionCount_eq input i]
  simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount, Nat.add_zero]

/-- Concrete-`α` restatement of `output_call` (the `Circuit.output`/`operations` element type
is rewritten to the concrete `Output (AssignedCell F)` by `var_of_provableType`; the generic
lemma's discr-tree key then misses under `simp`, as with the iffs). -/
@[circuit_norm]
theorem FormalCircuit.output_call' {Output : TypeMap} [ProvableType Output]
    (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (@Circuit.output F _ (Output (AssignedCell F)) (self.call config input) i)
      = self.output config input i := rfl

/-- Concrete-`α` restatement of `nextRegionIndex_call`, needed for the same reason: inside a
parent's `operations_bind`-produced chunk the `Circuit.nextRegionIndex` element type is the
concrete `Output (AssignedCell F)`, so the generic lemma's key misses under `simp`. This is
the layouter analogue of the concrete-`α` iff finding, at the *index* rather than the chunk. -/
@[circuit_norm]
theorem FormalCircuit.nextRegionIndex_call' {Output : TypeMap} [ProvableType Output]
    (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (@Circuit.nextRegionIndex F _ (Output (AssignedCell F)) (self.call config input) i)
      = i + Operations.regionCount
          (@Circuit.operations F _ (Output (AssignedCell F)) (self.call config input) i) :=
  FormalCircuit.nextRegionIndex_call self config input i

/-- `ExtendsWitness` of a region-level subcircuit op is the child's `ExtendsWitnesses`.
The completeness dual of `RegionOperation.constraints_subcircuit`; used inside the
completeness iff's proof to reach the child's witness condition. -/
theorem RegionOperation.extendsWitness_subcircuit (place : RegionIndex → ℕ)
    (self : RegionIndex) (env : ProverEnvironment F) (ops : RegionOperations F) :
    (RegionOperation.subcircuit ops).ExtendsWitness place self env
      = RegionOperations.ExtendsWitnesses place self env ops := rfl

/-- Soundness forward iff (absorption). Rewrites a child's folded call-constraint chunk
into that same chunk conjoined with the child's `Assumptions → Spec` implication — the
one-shot rewrite that lets a parent soundness proof consume the child by its contract.
Keyed on the opaque `(child.call …).operations self` boundary, so plain
`simp only [circuit_norm, this] at hc` fires it without unfolding the child. -/
theorem FormalRegionCircuit.subcircuit_constraints_iff_soundness
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (env : Placed Environment F) (input : Var Input F) :
    RegionOperations.Constraints env.place self env.env
        ((child.call config offset input).operations self)
    ↔ SubcircuitConstraints env.place self env.env
          ((child.call config offset input).operations self)
      ∧ (child.EnvAssumptions config env → child.Assumptions (eval env input) →
          child.Spec (eval env input)
            (eval env (child.output config offset input self))
            (child.extract config offset input self env)) := by
  -- the call term is defeq to a single `.subcircuit` op over the child's synthesize ops,
  -- whose `Constraints` is exactly the child's `RegionOperations.Constraints`
  unfold SubcircuitConstraints
  have hcall : RegionOperations.Constraints env.place self env.env
      ((child.call config offset input).operations self)
      = RegionOperations.Constraints env.place self env.env
          ((child.synthesize config offset input).operations self) := by
    simp only [FormalRegionCircuit.call, RegionCircuit.operations,
      RegionOperations.constraints_cons, RegionOperations.constraints_nil,
      RegionOperation.constraints_subcircuit, and_true]
  rw [hcall]
  constructor
  · intro hc
    exact ⟨hc, fun hE hA => child.soundness config offset self env input hE hA hc⟩
  · intro ⟨hc, _⟩
    exact hc

/-- Completeness forward iff (OR-shaped). For completeness the chunk appears in the *goal*;
rewriting it to `chunk ∨ precondition` (where `precondition → chunk`) lets the proof pick
`Or.inr` and discharge the precondition from the parent's in-context
`ExtendsWitnesses`/assumptions. Keyed on the same opaque call boundary. -/
theorem FormalRegionCircuit.subcircuit_constraints_iff_completeness
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment F) (input : Var Input F) :
    RegionOperations.Constraints env.place self env.env
        ((child.call config offset input).operations self)
    ↔ SubcircuitConstraints env.place self env.env
          ((child.call config offset input).operations self)
      ∨ (RegionOperations.ExtendsWitnesses env.place self env.env
              ((child.call config offset input).operations self)
          ∧ child.EnvAssumptions config env.toEnvironment
          ∧ child.Assumptions (eval env.toEnvironment input)
          ∧ child.ProverAssumptions (eval env input) env.env.hint) := by
  unfold SubcircuitConstraints
  have hcall : RegionOperations.Constraints env.place self env.env
      ((child.call config offset input).operations self)
      = RegionOperations.Constraints env.place self env.env
          ((child.synthesize config offset input).operations self) := by
    simp only [FormalRegionCircuit.call, RegionCircuit.operations,
      RegionOperations.constraints_cons, RegionOperations.constraints_nil,
      RegionOperation.constraints_subcircuit, and_true]
  have hwit : RegionOperations.ExtendsWitnesses env.place self env.env
      ((child.call config offset input).operations self)
      = RegionOperations.ExtendsWitnesses env.place self env.env
          ((child.synthesize config offset input).operations self) := by
    simp only [FormalRegionCircuit.call, RegionCircuit.operations,
      RegionOperations.extendsWitnesses_cons, RegionOperations.extendsWitnesses_nil,
      RegionOperation.extendsWitness_subcircuit, and_true]
  rw [hcall, hwit]
  constructor
  · intro hc; exact Or.inl hc
  · intro h
    cases h with
    | inl hc => exact hc
    | inr h =>
      obtain ⟨hw, hE, hA, hpa⟩ := h
      exact (child.completeness config offset self env input hw hE hA hpa).1

/-! ## Layouter-level absorption iffs

The layouter mirror of the region-level iffs above, keyed on the opaque
`(child.call config input).operations i₀` boundary. `child.call` emits a single layouter
`.subcircuit` op carrying the child's `synthesize` ops and advances the region counter by
`regionCount`; the iff's proof unfolds `call` to that single op (defeq) to reach the child's
contract, while the statement keeps `call` folded. Because the trailing `Operations` is empty
after the one subcircuit op, the `regionCount` bookkeeping contributes only a `∧ True` that
the proof discharges. -/

/-- Layouter soundness forward iff (absorption). Rewrites a child's folded layouter
call-constraint chunk into that chunk conjoined with the child's `EnvAssumptions →
Assumptions → Spec`. -/
theorem FormalCircuit.subcircuit_constraints_iff_soundness
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (env : Placed Environment F) (input : Var Input F) :
    Halo2.Constraints env.place env.env ((child.call config input).operations i₀) i₀
    ↔ SubcircuitConstraintsL env.place env.env
          ((child.call config input).operations i₀) i₀
      ∧ (child.EnvAssumptions config env → child.Assumptions (eval env input) →
          child.Spec (eval env input)
            (eval env (child.output config input i₀))
            (child.extract config input i₀ env)) := by
  unfold SubcircuitConstraintsL
  have hcall : Halo2.Constraints env.place env.env
      ((child.call config input).operations i₀) i₀
      = Halo2.Constraints env.place env.env
          ((child.synthesize config input).operations i₀) i₀ := by
    simp only [FormalCircuit.call, Circuit.operations, Halo2.Constraints, and_true]
  rw [hcall]
  constructor
  · intro hc
    exact ⟨hc, fun hE hA => child.soundness config i₀ env input hE hA hc⟩
  · intro ⟨hc, _⟩
    exact hc

/-- Layouter completeness forward iff (OR-shaped). Same shape as the region version. -/
theorem FormalCircuit.subcircuit_constraints_iff_completeness
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (env : Placed ProverEnvironment F) (input : Var Input F) :
    Halo2.Constraints env.place env.env ((child.call config input).operations i₀) i₀
    ↔ SubcircuitConstraintsL env.place env.env
          ((child.call config input).operations i₀) i₀
      ∨ (Halo2.ExtendsWitnesses env.place env.env
              ((child.call config input).operations i₀) i₀
          ∧ child.EnvAssumptions config env.toEnvironment
          ∧ child.Assumptions (eval env.toEnvironment input)
          ∧ child.ProverAssumptions (eval env input) env.env.hint) := by
  unfold SubcircuitConstraintsL
  have hcall : Halo2.Constraints env.place env.env
      ((child.call config input).operations i₀) i₀
      = Halo2.Constraints env.place env.env
          ((child.synthesize config input).operations i₀) i₀ := by
    simp only [FormalCircuit.call, Circuit.operations, Halo2.Constraints, and_true]
  have hwit : Halo2.ExtendsWitnesses env.place env.env
      ((child.call config input).operations i₀) i₀
      = Halo2.ExtendsWitnesses env.place env.env
          ((child.synthesize config input).operations i₀) i₀ := by
    simp only [FormalCircuit.call, Circuit.operations, Halo2.ExtendsWitnesses, and_true]
  rw [hcall, hwit]
  constructor
  · intro hc; exact Or.inl hc
  · intro h
    cases h with
    | inl hc => exact hc
    | inr h =>
      obtain ⟨hw, hE, hA, hpa⟩ := h
      exact (child.completeness config i₀ env input hw hE hA hpa).1

end

/-! ## Concrete-`α` variants (the `simp`-firing form for `ProvableType` outputs)

`circuit_norm` contains `var_of_provableType : Var Output F = Output (AssignedCell F)`, which
(for a `ProvableType Output`) rewrites the implicit element type `α` of `RegionCircuit.operations`
from the `Var Output F`-spelling to the concrete `Output (AssignedCell F)` head. After
`simp only [circuit_norm] …` the folded call chunk therefore carries a *concrete-headed* `α`,
which the generic iffs above (whose discrimination-tree key is `Var …`-headed) miss — `rw` still
matches by full `isDefEq`, but `simp` does not fire. These variants restate the same iff with the
`.operations` element type pinned to `Output (AssignedCell F)`, so the discr-tree key head matches
the post-`circuit_norm` chunk and `simp only [circuit_norm, this]` fires. Definitionally equal to
the generic iffs (`Var Output F` reduces to `Output (AssignedCell F)` under `toCircuitType`), so
each proof is just the generic lemma. -/

section
variable [CircuitType Input] {Output : TypeMap} [ProvableType Output]

/-- Concrete-`α` restatement of `subcircuit_constraints_iff_soundness`, tagged so plain
`simp only [circuit_norm, this]` fires it on a post-`circuit_norm` (concrete-`α`) chunk. -/
theorem FormalRegionCircuit.subcircuit_constraints_iff_soundness'
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (env : Placed Environment F) (input : Var Input F) :
    RegionOperations.Constraints env.place self env.env
        (@RegionCircuit.operations F _ (Output (AssignedCell F))
          (child.call config offset input) self)
    ↔ SubcircuitConstraints env.place self env.env
          (@RegionCircuit.operations F _ (Output (AssignedCell F))
            (child.call config offset input) self)
      ∧ (child.EnvAssumptions config env → child.Assumptions (eval env input) →
          child.Spec (eval env input)
            (eval env (child.output config offset input self))
            (child.extract config offset input self env)) :=
  FormalRegionCircuit.subcircuit_constraints_iff_soundness child config offset self env input

/-- Concrete-`α` restatement of `subcircuit_constraints_iff_completeness`. -/
theorem FormalRegionCircuit.subcircuit_constraints_iff_completeness'
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment F) (input : Var Input F) :
    RegionOperations.Constraints env.place self env.env
        (@RegionCircuit.operations F _ (Output (AssignedCell F))
          (child.call config offset input) self)
    ↔ SubcircuitConstraints env.place self env.env
          (@RegionCircuit.operations F _ (Output (AssignedCell F))
            (child.call config offset input) self)
      ∨ (RegionOperations.ExtendsWitnesses env.place self env.env
              (@RegionCircuit.operations F _ (Output (AssignedCell F))
                (child.call config offset input) self)
          ∧ child.EnvAssumptions config env.toEnvironment
          ∧ child.Assumptions (eval env.toEnvironment input)
          ∧ child.ProverAssumptions (eval env input) env.env.hint) :=
  FormalRegionCircuit.subcircuit_constraints_iff_completeness child config offset self env input

/-- Concrete-`α` restatement of the *layouter* `subcircuit_constraints_iff_soundness`. -/
theorem FormalCircuit.subcircuit_constraints_iff_soundness'
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (env : Placed Environment F) (input : Var Input F) :
    Halo2.Constraints env.place env.env
        (@Circuit.operations F _ (Output (AssignedCell F))
          (child.call config input) i₀) i₀
    ↔ SubcircuitConstraintsL env.place env.env
          (@Circuit.operations F _ (Output (AssignedCell F))
            (child.call config input) i₀) i₀
      ∧ (child.EnvAssumptions config env → child.Assumptions (eval env input) →
          child.Spec (eval env input)
            (eval env (child.output config input i₀))
            (child.extract config input i₀ env)) :=
  FormalCircuit.subcircuit_constraints_iff_soundness child config i₀ env input

/-- Concrete-`α` restatement of the *layouter* `subcircuit_constraints_iff_completeness`. -/
theorem FormalCircuit.subcircuit_constraints_iff_completeness'
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (env : Placed ProverEnvironment F) (input : Var Input F) :
    Halo2.Constraints env.place env.env
        (@Circuit.operations F _ (Output (AssignedCell F))
          (child.call config input) i₀) i₀
    ↔ SubcircuitConstraintsL env.place env.env
          (@Circuit.operations F _ (Output (AssignedCell F))
            (child.call config input) i₀) i₀
      ∨ (Halo2.ExtendsWitnesses env.place env.env
              (@Circuit.operations F _ (Output (AssignedCell F))
                (child.call config input) i₀) i₀
          ∧ child.EnvAssumptions config env.toEnvironment
          ∧ child.Assumptions (eval env.toEnvironment input)
          ∧ child.ProverAssumptions (eval env input) env.env.hint) :=
  FormalCircuit.subcircuit_constraints_iff_completeness child config i₀ env input

end

/-! ## Bare-`place`/`env` variants (fire inside loop lemmas)

The primed variants key on `Placed` projections (`env.place`, `env.env`), so inside a loop
lemma phrased over a bare `place : RegionIndex → ℕ` and `env : Environment F` (the
`Mul.lean` headline finding) `simp only [circuit_norm, <iff>]` never fires — the
discrimination-tree key sees a raw `place`/`env`, not a projection of a `Placed` record.
These restate all four absorption iffs over bare `place`/`env` (and `ProverEnvironment` for
completeness), reconstructing the `Placed` record as `⟨place, env⟩` under the hood; the
proofs delegate to the generic (`Placed`) versions, on which `⟨place, env⟩.place`/`.env`
reduce definitionally. Suffix: `_bare`. -/

section
variable [CircuitType Input] [CircuitType Output]

/-- Region soundness iff over bare `place`/`env`. -/
theorem FormalRegionCircuit.subcircuit_constraints_iff_soundness_bare
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (place : RegionIndex → ℕ) (env : Environment F) (input : Var Input F) :
    RegionOperations.Constraints place self env
        ((child.call config offset input).operations self)
    ↔ SubcircuitConstraints place self env
          ((child.call config offset input).operations self)
      ∧ (child.EnvAssumptions config (⟨place, env⟩ : Placed Environment F) → child.Assumptions (eval (⟨place, env⟩ : Placed Environment F) input) →
          child.Spec (eval (⟨place, env⟩ : Placed Environment F) input)
            (eval (⟨place, env⟩ : Placed Environment F) (child.output config offset input self))
            (child.extract config offset input self (⟨place, env⟩ : Placed Environment F))) :=
  FormalRegionCircuit.subcircuit_constraints_iff_soundness child config offset self ⟨place, env⟩ input

/-- Region completeness iff over bare `place`/`env`. -/
theorem FormalRegionCircuit.subcircuit_constraints_iff_completeness_bare
    (child : FormalRegionCircuit F CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment F)
    (input : Var Input F) :
    RegionOperations.Constraints place self env
        ((child.call config offset input).operations self)
    ↔ SubcircuitConstraints place self env
          ((child.call config offset input).operations self)
      ∨ (RegionOperations.ExtendsWitnesses place self env
              ((child.call config offset input).operations self)
          ∧ child.EnvAssumptions config (⟨place, env.toEnvironment⟩ : Placed Environment F)
          ∧ child.Assumptions (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
          ∧ child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input) env.hint) :=
  FormalRegionCircuit.subcircuit_constraints_iff_completeness child config offset self ⟨place, env⟩ input

/-- Layouter soundness iff over bare `place`/`env`. -/
theorem FormalCircuit.subcircuit_constraints_iff_soundness_bare
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment F) (input : Var Input F) :
    Halo2.Constraints place env ((child.call config input).operations i₀) i₀
    ↔ SubcircuitConstraintsL place env ((child.call config input).operations i₀) i₀
      ∧ (child.EnvAssumptions config (⟨place, env⟩ : Placed Environment F) → child.Assumptions (eval (⟨place, env⟩ : Placed Environment F) input) →
          child.Spec (eval (⟨place, env⟩ : Placed Environment F) input)
            (eval (⟨place, env⟩ : Placed Environment F) (child.output config input i₀))
            (child.extract config input i₀ (⟨place, env⟩ : Placed Environment F))) :=
  FormalCircuit.subcircuit_constraints_iff_soundness child config i₀ ⟨place, env⟩ input

/-- Layouter completeness iff over bare `place`/`env`. -/
theorem FormalCircuit.subcircuit_constraints_iff_completeness_bare
    (child : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment F) (input : Var Input F) :
    Halo2.Constraints place env ((child.call config input).operations i₀) i₀
    ↔ SubcircuitConstraintsL place env ((child.call config input).operations i₀) i₀
      ∨ (Halo2.ExtendsWitnesses place env ((child.call config input).operations i₀) i₀
          ∧ child.EnvAssumptions config (⟨place, env.toEnvironment⟩ : Placed Environment F)
          ∧ child.Assumptions (eval (⟨place, env.toEnvironment⟩ : Placed Environment F) input)
          ∧ child.ProverAssumptions (eval (⟨place, env⟩ : Placed ProverEnvironment F) input) env.hint) :=
  FormalCircuit.subcircuit_constraints_iff_completeness child config i₀ ⟨place, env⟩ input

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

end Halo2
