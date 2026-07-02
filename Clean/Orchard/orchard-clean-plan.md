# Orchard Clean Source-Conformance Plan

This PR represents an effort to model the Zcash Orchard circuit, written in Halo2,
faithfully in Clean.

## Goal

- All Orchard circuits are faithfully ported to Clean.
- Circuit input/output signatures exactly match Halo2 signatures.
- Clean specs and assumptions precisely model the intended contractual API of Orchard
  circuits.

## How We Model Halo2 In Clean

Halo2 cell layout (advice/fixed/instance columns, current/next row, regions) is richer
than Clean's linear witness tape.

Furthermore, Halo2 has two circuit layers: `configure`, where custom gates are defined,
and `synthesize`, where regions are created, witness values are assigned, custom gates
are "called" by enabling their selectors, and wires/copy constraints between cells are
added. Clean has just one circuit layer.

To still represent the Halo2 circuits faithfully, we will add additional ad-hoc
structure to our Clean circuits that approximates the intended Halo2 structure and will
later enable a mechanical translation of our Clean circuits into a verification key that
exactly matches the pinned Halo2 VK.

### Configure / Custom Gates

- Serializing Clean circuits preserves their subcircuit structure and marks subcircuits
  with their given `name`. This can be used to recover custom gate definitions from the
  single-layer serialized Clean circuits.
- Halo2 custom gates are modeled as `FormalAssertion`s with
  `name := "GATE <halo2 gate name>"`.
- Advice column inputs are modeled by a struct that distinguishes values clearly by
  current and next row.
- Fixed column inputs are modeled as Lean parameters that the entire `FormalAssertion`
  depends on. The parameters should be in value form (field elements) and translated to
  `.const` expressions inside the gate.
- Selectors are not modeled. To enable a gate, call it from the outside as a Clean
  subcircuit.
- Halo2 lookups should be modeled by Clean `lookup` operations and `Table` definitions.

### Synthesize / High-Level Circuit Wiring

- Every individual `synthesize` or other circuit method in Halo2 should be ported to a
  formalized circuit package in Clean (`FormalCircuit`, `FormalAssertion`, or
  `GeneralFormalCircuit`).
- Clean circuits compose by calling dependent chips, `synthesize()` methods, or
  `assign_region()` methods as subcircuits.
- When a Halo2 circuit enables a custom gate, its Clean equivalent calls the gate circuit
  as a subcircuit.
- When a custom gate has fixed columns whose concrete values are decided by the caller
  (`assign_fixed` in Halo2), the Clean circuit should instantiate the gate with the same
  explicit parameters.
- Copy constraints are modeled by the Clean `===` operator.
- If two values are genuinely different cells on the Halo2 side, do not use the same
  variable for them in Clean. Witness a new `Expression` and connect it to the copied one
  by `===`.
- Clean's `<==` operator does witnessing and equality constraints in one step and should
  be used whenever Halo2 does `copy_advice`.
- When a Halo2 circuit witnesses auxiliary variables internally, the Clean circuit should
  do the same. Do not expose that variable to the caller as input.
- Halo2 `Value<T>` inputs are prover-side inputs. In Clean, model them with
  `CircuitType` using `Unconstrained T` or `UnconstrainedDep T`, and package the method as
  a `GeneralFormalCircuit.WithHint` when the circuit witnesses cells from that value.
- The input/output schema of any Clean circuit should precisely match some method on the
  Halo2 side.
- `Input` and `Output` should closely model high-level types, such as elliptic curve
  points, when Halo2 does the same.

## Specs And Assumptions

Clean `Spec` and `Assumptions` must faithfully model the high-level intended contract of
the Halo2 circuit.

When a Halo2 circuit constrains a given relation internally, such as scalar
multiplication, the Clean circuit must establish the same fact in its spec. Do not weaken
the relation by deferring properties to assumptions.

## Circuit Field

Orchard uses the Pallas base field as its circuit field. Clean circuits should use the
same explicit field and make use of established properties of that field and curve
defined over it, see `Clean/Orchard/Specs`.

Mathematical properties that are known and needed within the scope of a circuit should
not be deferred as obligations to callers via assumptions.

Do not add generic parameters for the field with bespoke assumptions such as:

```lean
variable {F : Type} [Field F] [OfNat F 2]
```

Instead, use the concrete Pallas base field and prove whatever assumption is needed about
that concrete field.

## Hard Reference Rule

Every gadget must be ported from the actual Halo2/Orchard implementation. Do not infer a
gadget from memory, from the protocol description alone, or from a simplified
mathematical guess.

Reference sources for this branch:

- Orchard: `orchard@orchard-0.14.0`
- halo2_gadgets: `halo2@halo2_gadgets-0.5.0/halo2_gadgets`
- halo2_proofs, if needed for utility semantics:
  `halo2@halo2_gadgets-0.5.0/halo2_proofs`

If a future agent cannot find the relevant source code, it must stop and ask Gregor
instead of guessing the implementation.

## Naming And Style

Each Clean formal circuit should be given its own namespace, which defines `circuit`
(the formal package).

Example:

```lean
def circuit : FormalCircuit <Field> <Input> <Output> where
  main input := do ...
  Assumptions input := ...
  Spec input output := ...
  soundness := by ...
  completeness := by ...
```

When soundness and completeness proofs get long, factor out additional definitions, in this order:

- `main`, the `Circuit` itself
- `Assumptions` and `Spec`, the contract (when using `GeneralFormalCircuit`, also `ProverAssumptions`)
- `elaborated`, the `ElaboratedCircuit`, a typeclass instance needed by soundness and `circuit`, defined by `:= by elaborate_circuit`
- `soundness` and `completeness` theorems

In the latter case, the `circuit` declaration should look roughly like this:

```lean
def circuit : FormalCircuit <Field> <Input> <Output> where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness
```

If a given Halo2 API has both a low-level gate and a synthesis-level entry point circuit,
use a `.Gate` namespace for the gate, not a `.Entry` namespace for the entry point. The
source-shaped entry point should live directly in the source namespace as `main` and
`circuit`; the custom-gate assertion should live under `Namespace.Gate.main` and
`Namespace.Gate.circuit`.

Namespace-local structs that exist only to collect inputs to a gate or method should be
called `Input`, not `Row`, unless the Halo2 source type itself is row-like and explicitly
named that way.

In general, follow Halo2 file/chip organization and naming closely.

Use dotted namespace declarations for multi-component source paths. Prefer
`namespace Orchard.Poseidon.Permute` over stacked declarations like
`namespace Orchard; namespace Poseidon; namespace Permute`. Local one-component
subnamespaces are fine when grouping adjacent definitions inside an already-open source
namespace.

For example, if Halo2 has source modules `add_incomplete.rs` and `add.rs`, then Clean
modules and namespaces should follow that source shape as `AddIncomplete` and `Add`.

Similarly, match halo2 names of columns and assigned cells with the same Clean variable names.

If a gate takes a column and then uses both `Rotation::curr` and `Rotation::next`, pass an input struct
containing both `{ curr: F; next: F }`.

**Code style**. Don't add layers of indirection that don't exist in the halo2 source. In particular, do **not** name tiny expression fragments or individual constraint checks when Halo2 writes them inline in `configure` / `create_gate`.

Bad:

```lean
def output0 (params : Params Fp) (row : Input Fp) : Fp :=
  pow5 (row.cur0 + params.rcA0) * params.m00 +
    pow5 (row.cur1 + params.rcA1) * params.m01 +
    pow5 (row.cur2 + params.rcA2) * params.m02

def next0Check (params : Params Fp) (row : Input Fp) : Fp :=
  output0 params row - row.next0

def main (params : Params Fp) (row : Var Input Fp) : Circuit Fp Unit := do
  assertZero (next0Check params row)
```

Good:

```lean
def main (params : Params Fp) (row : Var Input Fp) : Circuit Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (
    pow5 (row.cur0 + paramsExpr.rcA0) * paramsExpr.m00 +
      pow5 (row.cur1 + paramsExpr.rcA1) * paramsExpr.m01 +
      pow5 (row.cur2 + paramsExpr.rcA2) * paramsExpr.m02 - row.next0)
```
