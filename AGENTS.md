# AGENTS.md - AI Agent Context for Clean

This document provides context for AI coding agents working on the `clean` codebase.

## What is Clean?

Clean is an embedded Lean DSL for writing formally verified zk (zero-knowledge) circuits. It targets popular arithmetizations like AIR, PLONK, and R1CS. The key value proposition is producing **formally verified, bug-free circuits** with proofs of soundness and completeness.

## Project Structure

```
Clean/
├── Circuit/           # Core circuit DSL and monad
│   ├── Basic.lean     # Circuit monad, FormalCircuit, soundness/completeness definitions
│   ├── Expression.lean # Expression AST (var, const, add, mul)
│   ├── Operations.lean # Operation types (witness, assert, lookup, subcircuit)
│   ├── Provable.lean  # ProvableType, ProvableStruct - typed circuit values
│   ├── Subcircuit.lean # Composing formal circuits
│   ├── Lookup.lean    # Lookup table support
│   └── Theorems.lean  # Core theorems about circuit semantics
├── Gadgets/           # Reusable verified circuit components
│   ├── Boolean.lean   # Boolean constraints (IsBool, assertBool)
│   ├── Equality.lean  # Equality assertions (===)
│   ├── IsZero.lean    # Zero-check circuits
│   ├── ByteDecomposition/ # Byte manipulation
│   ├── BLAKE3/        # BLAKE3 hash function circuits
│   ├── Keccak/        # Keccak hash circuits
│   └── ...
├── Types/             # Domain-specific types (U32, U64, etc.)
├── Tables/            # Lookup tables and table-based circuits
├── Specs/             # Pure specifications (BLAKE3, Keccak specs)
├── Utils/             # Utilities and tactics
│   └── Tactics/
│       ├── CircuitProofStart.lean  # Main proof automation
│       └── ProvableStructDeriving.lean # Deriving handler
└── Circomlib/         # Circom library ports
```

## Core Concepts

### The Circuit Monad

Circuits are written using the `Circuit F α` monad, which accumulates operations:

```lean
def myCircuit (x : Expression F) : Circuit F (Expression F) := do
  let y ← witness fun env => env x + 1  -- witness a new variable
  y === x + 1                           -- add constraint: y = x + 1
  return y
```

In that example, `===` is custom syntax which adds an `assertZero` operation.

### Key Operations

- `witness` / `witnessVar` / `witnessField`: Create new witness variables
- `lookup`: Add lookup constraint (value must be in table)
- `===`: Assert equality between two values
- `<==`: Witness and constrain equal to expression

### ProvableType and ProvableStruct

Types that can appear in circuits implement `ProvableType`:

- `field`: Single field element
- `fieldPair`, `fieldTriple`: 2- and 3-tuples of field elements
- `fields n`: Vector of n field elements
- `ProvableVector α n`: Vector of n elements of type α
- Custom structures via `ProvableStruct`

Use `deriving ProvableStruct` for automatic instance generation:

```lean
structure MyInputs (F : Type) where
  x : F
  y : U32 F
  data : Vector (U32 F) 16
deriving ProvableStruct
```

For complex or more generic cases, one can always implement a `ProvableType` instance directly.

### FormalCircuit

A `FormalCircuit` bundles a circuit with its correctness proofs:

```lean
structure FormalCircuit (F : Type) (Input Output : TypeMap) where
  main : Var Input F → Circuit F (Var Output F)
  Assumptions : Input F → Prop      -- preconditions
  Spec : Input F → Output F → Prop  -- postcondition (input-output relation)
  soundness : Soundness F ...       -- constraints → assumptions → spec
  completeness : Completeness F ... -- assumptions → constraints satisfiable
```

**Soundness**: For any witness assignment satisfying constraints, the spec holds.
**Completeness**: Given assumptions, there exists a witness satisfying constraints.

### Subcircuits

Compose formal circuits using the subcircuit mechanism and the `CoeFun` instance for `FormalCircuit`:

```lean
def main (input : Var Inputs F) : Circuit F (Var Outputs F) := do
  let result ← innerCircuit input.someField -- `innerCircuit : FormalCircuit ..` being used like a function
  ...
```

When composing already-defined gadgets or circuits, always call the bundled circuit as a
subcircuit. Do not inline a child gadget by calling `Child.main input` from a parent
circuit. Inlining defeats Clean's subcircuit proof structure and forces parent proofs to
trace through every nested child operation.

### ElaboratedCircuit and `elaborate_circuit`

FormalCircuit and variants carry an instance of `ElaboratedCircuit`, which exposes
circuit data like `localLength` and `output` in explicit, fully reduced form. This helps parent
circuits simplify without unfolding child circuit internals.

Inline `FormalCircuit` declarations get their elaborated metadata from the default `elaborated := by elaborate_circuit`; factored circuits have to define a standalone `ElaboratedCircuit` instance since that is needed by `Soundness`. In the latter case, for performance reasons, it is _very_ important to pass in `elaborated` as an explicit field (otherwise `soundness` has to elaborate with metavariables since `elaborate` is not filled in at that time).

If elaboration fails, do not treat that as an insurmountable blocker. Inspect a potential failing `ExplicitCircuit` / `ExplicitCircuits` goal. Sometimes adding the right leaf instance can get past that. In rare cases, defining the `ElaboratedCircuit` by hand is a workaround for failing `elaborate_circuit`.

Relevant code and examples are in `Clean/Circuit/Explicit.lean`, especially `infer_explicit_circuit`,
`infer_explicit_circuits`, `elaborate_circuit`, `elaborate_circuit_with`.

## Proof Patterns

### Starting a Proof

Use `circuit_proof_start` tactic to set up soundness/completeness proofs:

```lean
theorem soundness : Soundness F elaborated Assumptions Spec := by
  circuit_proof_start
  -- Now have: h_input, h_assumptions, h_holds
  ...
```

Do not pass the current circuit's `main`, `Spec`, or `Assumptions` to
`circuit_proof_start`; the tactic unfolds them automatically. Use the argument list for
helper definitions, child circuit specs, theorem names, or extra simp facts needed after
setup.

### Key Simp Sets

- `circuit_norm`: Main simplification set for circuit reasoning
- `explicit_provable_type`: Unfolds ProvableType definitions when needed

## Conventions

- Use `F p` for field type where `p` is prime
- Specs are pure Lean propositions relating inputs to outputs
- Specs must state the highest-level intended meaning of the circuit that can be described
  from its inputs and outputs. The circuit operations are the implementation; the `Spec` is
  the semantic contract being proved.
- Do not define specs by copying, restating, or trivially wrapping the circuit constraints.
  Do not introduce separate `constraints` definitions as substitutes for semantic specs.
  For example, an incomplete-addition gadget spec should state the intended incomplete
  elliptic-curve addition relation, not merely the finite-field equations enforced by the
  circuit.
- Assumptions capture preconditions (e.g., value ranges)
- Follow Mathlib naming conventions
- Never modify maxHeartbeats

## Key Files to Understand

1. `Clean/Circuit/Basic.lean` - Circuit monad and FormalCircuit
2. `Clean/Circuit/Provable.lean` - ProvableType/ProvableStruct system
3. `Clean/Circuit/Subcircuit.lean` - Circuit composition
4. `Clean/Gadgets/Boolean.lean` - Simple gadget example
5. `Clean/Gadgets/ByteDecomposition/ByteDecomposition.lean` - Complex gadget with lookups

## Common Tasks

### Adding a New Gadget

1. Define the `main` circuit function
2. Define `Assumptions` and `Spec`
3. Create `ElaboratedCircuit` instance with `localLength` and `output`
4. Prove `soundness` and `completeness`
5. Bundle into `FormalCircuit`

Before proving the gadget, check that all child gadgets are composed through their bundled
`.circuit`/formal assertion interface and that the `Spec` describes meaning rather than
constraints.

### Working on Lean Proofs

When writing or debugging Lean proofs, the **lean-mcp skill** in `./skills/lean-mcp/SKILL.md` is useful.

Practical recommendations:

- To get an overview of failing steps and sorries, use the `lean_diagnostic_messages` command.
- After finding out where the holes are, work on **one at a time**, not all at once.
- When iterating on a proof hole, inspect exact goal state with `lean_goal` (lean-mcp skill) at the relevant line number.
- Prefer robust simplification, and use the library's custom `circuit_norm` simp set.
  - start with `simp_all only [circuit_norm]` (or `simp_all [circuit_norm]` when closing a goal),
  - avoid brittle `exact h.1.2` style proofs. `simp_all` can do the same work of using the right assumptions, in a more robust way.
  - do not use `simpa`, which is a closing tactic and will often fail. use `simp` and `simp_all`, which can advance the goal state without failing.
- Definitional equality is a **superpower** to perform otherwise tricky unifications. The following tactics force Lean to look past definitions and elaborate as far as possible:
  - try `rfl` when the goal is an equality
  - try `convert <assumption>` when one of the assumptions has the same shape as the conclusion but differs in 1-2 places
  - try `congr` when proving two sides of an equality that already have the same shape but differ in 1-2 places
  - use `change <new type> (at <assumption>)` to rewrite a hypothesis or the goal into any form that is definitionally equal.
- Always fix failures first, by targeted changes to the relevant lines. When getting a tactic error from `lean_goal`, do not revert the entire (mostly working) proof block to `sorry`. Addressing the error concretely is more likely to move you forward. Treat errors as feedback for iterative proving, not as catastrophic.
- If stuck, use `lean_multi_attempt` to quickly test candidate tactics.
- If proof steps get complicated, move them into a local helper lemma. Make the lemma as general as possible and leave out hypotheses of the current proof likely not needed for that lemma. That reduces noise in the lemma's goal state and makes proving it easier.
- At the very end of a proving task, run `lean_diagnostic_messages` and fix all linter warnings you can easily address. For example, fix "unnecessary simpa" warnings by replacing simpa with simp.
- In general, avoid non-lean-mcp commands like `lake build <file>` (full dependency rebuild) and `lake env lean <file>` (targeted check without rebuild). Their output is way too large. Use these commands only as a fallback to get maximum information when you feel lost.

Check `doc/proving-guide.md` for more tips especially related to user-facing circuit formalization proofs.

When a proof exceeds `maxHeartbeats` or fails with `(kernel) deep recursion detected`,
read `doc/performance-problems.md` first.

### Debugging

To understand performance of a Lean command, wrap it with `#count_heartbeats` from mathlib:

```lean
import Mathlib.Util.CountHeartbeats

#count_heartbeats in
example : ElaboratedCircuit F field (fields 8) main := by
  elaborate_circuit
```

To profile tactic scripts, per-command `#count_heartbeats in` should give fine-grained feedback.

For profiling meta tactics in this codebase, temporary `IO.getNumHeartbeats` logging inside the
tactic has been checked against `#count_heartbeats` on small declarations and matched the same
scale closely enough to identify bottlenecks.

To inspect what `simp` is doing, enable tracing around the failing proof:

```lean
set_option trace.Meta.Tactic.simp true in
example : P := by
  simp only [circuit_norm]
```

For a shorter "what was used" summary, try:

```lean
set_option trace.Meta.Tactic.simp.rewrite true in
example : P := by
  simp only [circuit_norm]
```
