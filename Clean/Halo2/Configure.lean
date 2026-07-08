import Clean.Halo2.Expression

/-!
# Halo2 configure layer — DESIGN SKETCH

The configure layer defines the constraint system: custom gates, lookup arguments,
column allocation, equality-enabled columns. Chip `configure` functions are ported
verbatim from Rust.

**Why a monad**: column indices, selector indices, and gate *order* in the real
constraint system are execution-order artifacts of the Rust `configure()` calls.
Executing verbatim-ported configure code in a small state monad reproduces them by
construction; hand-maintaining them (10 advice + 29 fixed columns, 56 selectors,
gate order across all chips) would be unmaintainable and un-checkable.

**Why gate bodies are pure**: `Query` atoms carry no query index (indices are assigned
by a deterministic first-encounter walk at VK-compilation time), so `meta.query_advice`
ports as the pure function `queryAdvice` and `create_gate` closures become pure
`Expression` terms. No `VirtualCells` state.

**Proofs never look inside `Configure`**: it is a data-construction device, run once to
produce config structs and the `ConstraintSystem`. The proof surface is the synthesize
layer (`Basic.lean`), which references gates as data. Formal gate packages
(`FormalAssertion` analogues binding a `Spec` to a gate) come with the formal-circuit
port.

Rust reference: `halo2_proofs/src/plonk/circuit.rs` (`ConstraintSystem`,
`create_gate`, `VirtualCells`, `Constraints::with_selector`).
-/

namespace Halo2

variable {F : Type}

/-!
## Pure query helpers

Verbatim-port counterparts of Rust `meta.query_*` inside `create_gate` closures.
-/

@[circuit_norm] def querySelector (s : Selector) : Expression F Query := var (.selector s)
/-- Rust `query_fixed` takes no rotation in this halo2 version (always the current row);
the `Query.fixed` constructor keeps a rotation for generality of the compiled CS. -/
@[circuit_norm] def queryFixed (c : Column .fixed) : Expression F Query := var (.fixed c 0)
@[circuit_norm] def queryAdvice (c : Column .advice) (rot : Rotation) : Expression F Query := var (.advice c rot)
@[circuit_norm] def queryInstance (c : Column .instance) (rot : Rotation) : Expression F Query := var (.instance c rot)

/-- One named constraint of a custom gate. Rust: `Constraint<F>`. -/
structure Constraint (F : Type) where
  name : String := ""
  poly : Expression F Query

/-- A custom gate.

`constraints` are the **compiled** polynomials, verbatim as the Rust source builds them
— usually `Constraints.withSelector` shapes `q * poly`, but e.g. `witness_point` builds
`(q * x) * curve_eqn` manually for pinned-VK AST reasons. `selector` is the gate's
activation handle: per the selector survey (`halo2-selector-survey.md`), every gate in
scope is activated by exactly one simple `Selector`, and genuine selectors never occur
in a foreign gate's polynomials — so the semantics of enabling the gate at a row is
"all compiled polys vanish there under the valuation `selector ↦ 1`"
(see `FlatRegionOperation.Constraints`). The bridge to the CS view "`∀` rows, poly = 0 with the
actual 0/1 activation table" is a once-per-circuit lemma at the VK boundary.
-/
structure Gate (F : Type) where
  name : String
  selector : Selector
  constraints : List (Constraint F)

/-- Rust: `Constraints::with_selector(q, [(name, poly), …])` — multiplies every
constraint by the selector, building exactly the Rust AST `q * poly`. -/
def Constraints.withSelector (s : Selector) (constraints : List (String × Expression F Query)) :
    List (Constraint F) :=
  constraints.map fun (name, poly) => { name, poly := querySelector s * poly }

/-- A lookup argument: per row, the input expressions must be a row of the table.
Rust: `lookup::Argument`. SKETCH — semantics and table loading TBD with the lookup port. -/
structure LookupArgument (F : Type) where
  tableMap : List (Expression F Query × TableColumn)

/--
The constraint system under construction: the state of the `Configure` monad, mirroring
the builder role of Rust's `ConstraintSystem<F>`. Allocation counters plus accumulated
gates/lookups/permutation data, in creation order.
-/
structure ConstraintSystem (F : Type) where
  numAdviceColumns : ℕ := 0
  numFixedColumns : ℕ := 0
  numInstanceColumns : ℕ := 0
  numSelectors : ℕ := 0
  gates : List (Gate F) := []
  lookups : List (LookupArgument F) := []
  /-- Equality-enabled columns (the permutation argument's columns), in call order. -/
  permutationColumns : List AnyColumn := []
  /-- Columns that constants are assigned into (`enable_constant`). -/
  constants : List (Column .fixed) := []

/--
The configure monad: threads the `ConstraintSystem` being built. Mirrors passing
`meta : &mut ConstraintSystem<F>` through Rust configure code.
-/
abbrev Configure (F : Type) := StateM (ConstraintSystem F)

/-- Rust: `meta.advice_column()`. -/
def adviceColumn : Configure F (Column .advice) :=
  fun cs => (⟨cs.numAdviceColumns⟩, { cs with numAdviceColumns := cs.numAdviceColumns + 1 })

/-- Rust: `meta.fixed_column()`. -/
def fixedColumn : Configure F (Column .fixed) :=
  fun cs => (⟨cs.numFixedColumns⟩, { cs with numFixedColumns := cs.numFixedColumns + 1 })

/-- Rust: `meta.instance_column()`. -/
def instanceColumn : Configure F (Column .instance) :=
  fun cs => (⟨cs.numInstanceColumns⟩, { cs with numInstanceColumns := cs.numInstanceColumns + 1 })

/-- Rust: `meta.selector()` (a simple selector). -/
def selector : Configure F Selector :=
  fun cs => (⟨cs.numSelectors, true⟩, { cs with numSelectors := cs.numSelectors + 1 })

/-- Rust: `meta.complex_selector()`. -/
def complexSelector : Configure F Selector :=
  fun cs => (⟨cs.numSelectors, false⟩, { cs with numSelectors := cs.numSelectors + 1 })

/-- Rust: `meta.enable_equality(column)`. -/
def enableEquality (c : AnyColumn) : Configure F Unit :=
  fun cs => ((), { cs with permutationColumns := cs.permutationColumns ++ [c] })

/-- Rust: `meta.enable_constant(column)`: registers the constants column and enables
equality on it (constants are enforced via copies into this column). -/
def enableConstant (c : Column .fixed) : Configure F Unit :=
  fun cs => ((),
    { cs with
      constants := cs.constants ++ [c]
      permutationColumns := cs.permutationColumns ++ [c.toAny] })

/-- Rust: `meta.lookup_table_column()`. -/
def lookupTableColumn : Configure F TableColumn := do
  return { inner := ← fixedColumn }

/-- Rust: `meta.create_gate(name, |meta| Constraints::with_selector(guard, [...]))`.
The gate is registered in creation order; its body is pure data (see module docs).

TODO surface syntax: decide when porting the first chip whether to mirror
`Constraints::with_selector` more literally. -/
def createGate (gate : Gate F) : Configure F Unit :=
  fun cs => ((), { cs with gates := cs.gates ++ [gate] })

/-- Rust: `meta.lookup(|meta| ...)`. SKETCH. -/
def lookup (arg : LookupArgument F) : Configure F Unit :=
  fun cs => ((), { cs with lookups := cs.lookups ++ [arg] })

end Halo2
