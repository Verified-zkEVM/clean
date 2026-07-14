import Clean.Halo2.Formal
import Clean.Halo2.Lemmas

/-!
# Subcircuit composition: the call-boundary opacity contract

A subcircuit call emits `.subcircuit ops` carrying the child's raw op list; the child does not
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
@[circuit_norm]
theorem FormalCircuit.output_call (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (self.call config input).output i = self.output config input i := rfl

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
  show i + self.regionCount config input
    = i + Operations.regionCount ((self.call config input).operations i)
  congr 1
  -- `regionCount = ((synthesize …).operations i).regionCount` (elaborated metadata), and the
  -- `call`'s single `.subcircuit` op has exactly that `Operations.regionCount`.
  rw [FormalCircuit.regionCount, (self.elaborated config).regionCount_eq input i]
  simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount, Nat.add_zero]

/-- Concrete-`α` restatement of `output_call` (the `Circuit.output`/`operations` element type
is rewritten to the concrete `Output (AssignedCell F)` by `var_of_provableType`; the generic
lemma's discr-tree key then misses under `simp`). -/
@[circuit_norm]
theorem FormalCircuit.output_call' {Output : TypeMap} [ProvableType Output]
    (self : FormalCircuit F CI Cfg Input Output) (config : Cfg)
    (input : Var Input F) (i : RegionIndex) :
    (@Circuit.output F _ (Output (AssignedCell F)) (self.call config input) i)
      = self.output config input i := rfl

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

/-- `ExtendsWitness` of a region-level subcircuit op is the child's `ExtendsWitnesses`.
The completeness dual of `RegionOperation.constraints_subcircuit`; used by the `subcircuit_rw`
engine's completeness leaves to reach the child's witness condition. -/
theorem RegionOperation.extendsWitness_subcircuit (place : RegionIndex → ℕ)
    (self : RegionIndex) (env : ProverEnvironment F) (ops : RegionOperations F) :
    (RegionOperation.subcircuit ops).ExtendsWitness place self env
      = RegionOperations.ExtendsWitnesses place self env ops := rfl

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
