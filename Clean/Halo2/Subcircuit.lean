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

No `SubcircuitConstraints` marker is needed: the LHS is `(call).operations`-keyed and the
RHS raw chunk is `(synthesize).operations`-keyed — different heads once the proof unfolds —
so simp does not loop.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {CI Cfg : Type} {Input Output Witness : TypeMap}

section
variable [CircuitType Input] [CircuitType Output]

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
    ↔ RegionOperations.Constraints env.place self env.env
          ((child.call config offset input).operations self)
      ∧ (child.EnvAssumptions config env → child.Assumptions (eval env input) →
          child.Spec (eval env input)
            (eval env (child.output config offset input self))
            (child.extract config offset input self env)) := by
  -- the call term is defeq to a single `.subcircuit` op over the child's synthesize ops,
  -- whose `Constraints` is exactly the child's `RegionOperations.Constraints`
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
    ↔ RegionOperations.Constraints env.place self env.env
          ((child.call config offset input).operations self)
      ∨ (RegionOperations.ExtendsWitnesses env.place self env.env
              ((child.call config offset input).operations self)
          ∧ child.EnvAssumptions config env.toEnvironment
          ∧ child.Assumptions (eval env.toEnvironment input)
          ∧ child.ProverAssumptions (eval env input) env.env.hint) := by
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
