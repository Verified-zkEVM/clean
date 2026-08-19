# The witgen wire format (`version: 1`)

The JSON contract between Clean's witness generators and any external consumer — a Rust
proving backend, a reference interpreter, a codegen pipeline. `#witgen_json` /
`Operations.witgenJson?` emit it; `Operations.witgenJsonShared?` emits the same format
with subterm sharing (see below). This is the companion of `doc/witgen-authoring.md`,
which covers the *authoring* surface (`witness`, `witnessProgram`, the expression
operators); this file specifies what crosses the serialization boundary and how to
evaluate it.

**Normative source.** This document is descriptive. The format is defined by the
serializer — `Clean/Circuit/WitnessExport.lean` and `Clean/Circuit/Json.lean` — and the
evaluation semantics by `Clean/Circuit/WitnessIR.lean` (`FExpr.eval` and friends) and
`Clean/Circuit/WitnessGeneration.lean` (`Circuit.witgen`). On any disagreement, the
Lean code wins and this file gets fixed.

## The envelope

```json
{"version": 1, "localLength": N, "operations": [ ... ]}
```

- `version` — the wire version; this document describes exactly `1`.
- `localLength` — the total number of witness cells the program appends (the sum of the
  `witness` fields below).
- `operations` — the circuit's complete flattened operation list, in emission order,
  with all subcircuits inlined (names erased). Four operation forms:

| form | shape |
|---|---|
| witness | `{"witness": m, "code": {"steps": [...], "output": <VExpr>}}` |
| assert | `{"assert": <Expression>}` — the constraint `<Expression> = 0` |
| lookup | `{"lookup": {"table": <string>, "entry": [<Expression>, ...]}}` |
| interact | `{"interact": {"channel": <string>, "multiplicity": <Expression>, "message": [<Expression>, ...]}}` |

A **witness interpreter evaluates only the `witness` operations** and skips the rest;
they are carried so one artifact describes the whole circuit (constraints and channel
interactions included) for consumers that want them.

The wire format deliberately records neither the field, the circuit's input width, nor
the hint-table schema — those are properties of the deployment, not of the program.
Consumers should ship them alongside the payload (the hint schema is derivable from the
payload itself by walking it for `hintGet`/`dataGet` nodes).

## Variable indexing and the evaluation loop

A formal circuit's input row occupies absolute variable indices `0 .. inputWidth - 1`;
the circuit's own cells begin at `inputWidth`. The evaluation loop is a transcription
of `Circuit.witgen` / `witgenStep`:

1. Seed a growing cell array with the `inputWidth` input values.
2. Fold over `operations` in order. On `{"witness": m, "code": {steps, output}}`:
   evaluate `steps` left to right into a locals array (each step sees only the locals
   before it), then evaluate `output` and append **exactly `m`** field elements to the
   cell array. Skip `assert`/`lookup`/`interact`.
3. The final array has length `inputWidth + localLength`.

An out-of-range cell read yields `0`.

## The four expression sorts — parse by slot, not by tag

`type` tags **collide across sorts** (`const`, `add`, `mul`, `ite`, `localVar`, `and`
each appear in two or three vocabularies), so a deserializer must be sort-directed by
the parent slot. The sorts:

**`Expression`** — the circuit-constraint AST. Tags: `var {index}` (an **absolute**
cell index), `const {value}`, `add {lhs, rhs}`, `mul {lhs, rhs}`. Appears in:
`assert`, `lookup.entry[]`, `interact.multiplicity`, `interact.message[]`, and inside
`FExpr`'s `expr` node.

**`FExpr`** — field-sorted witness expressions:

| tag | fields | semantics |
|---|---|---|
| `expr` | `expr: <Expression>` | evaluate against the cell array |
| `const` | `value: ℕ` | the field element with that canonical value |
| `localVar` | `index: ℕ` | step-local reference (a `field`-sorted step) |
| `add`, `mul` | `lhs, rhs: FExpr` | field arithmetic |
| `inv` | `arg: FExpr` | field inverse, **with `0⁻¹ = 0`** |
| `ofU64` | `arg: U64Expr` | lift: the field element with value `arg` (mod p) |
| `ite` | `cond: BExpr; then, else: FExpr` | conditional |
| `listGet` | `items: [FExpr]; index: U64Expr` | item at index, **`0` if out of range** |
| `dataGet` | `table, width, row: U64Expr, col` | committed prover data read (`Environment.data`) |
| `hintGet` | `table, width, row: U64Expr, col` | prover hint read; **missing table/row reads as `0`** |

**`U64Expr`** — u64-sorted, everything wraps mod 2⁶⁴ like Rust's `u64`:

| tag | semantics |
|---|---|
| `const {value}` | literal |
| `val {arg: FExpr}` | the field element's canonical value, **truncated** to 64 bits |
| `idx {}` | the innermost enclosing `mapRange` index (`0` outside) |
| `localVar {index}` | step-local reference (a `u64`-sorted step) |
| `add`, `mul` | wrapping arithmetic |
| `div`, `mod` | **Lean semantics: `x / 0 = 0`, `x % 0 = x`** (Rust `/`/`%` panic — guard) |
| `and`, `or`, `xor` | bitwise |
| `shiftLeft`, `shiftRight` | **shift amount masked mod 64** (`wrapping_shl`/`wrapping_shr`) |
| `ite {cond, then, else}` | conditional |

**`BExpr`** — conditions. ⚠ Three wire tags disagree with the Lean constructor names;
**the wire tags are authoritative**, and an implementation should name its cases after
them:

| tag | operands | semantics |
|---|---|---|
| `true`, `false` | — | literals |
| `eq` | FExpr | field equality |
| `u64Eq` | U64Expr | u64 **equality** (the Lean ctor is confusingly named `neq`) |
| `u64Lt` | U64Expr | u64 `<` (the Lean ctor is named `lt`) |
| `lt` | FExpr | canonical-value `<` on **field** elements (the Lean ctor is named `flt`) |
| `bit {arg: FExpr, bit: ℕ}` | | bit `i` of the canonical value is set |
| `not {arg}` | BExpr | negation |
| `and {lhs, rhs}` | BExpr | conjunction — **there is no `or` node** (De Morgan) |

There are also no subtraction or negation nodes in any sort: `x - y` is encoded as
`x + (p-1)·y`, so `p − 1` constants are common in payloads.

**`steps`** — a list of `{"sort": "field"|"u64", "value": <FExpr|U64Expr>}`
let-bindings, referenced positionally by `localVar` in the matching sort. **A
sort-mismatched or out-of-range `localVar` reads as `0`** (this is total-evaluation
semantics, not an error). Steps evaluate at `idx = 0`.

**`output`** (`VExpr`) — the vector former producing the witness cells:

| tag | semantics |
|---|---|
| `elements {elements: [FExpr]}` | a literal cell list |
| `mapRange {n, body: FExpr}` | `n` cells, the body re-evaluated with `idx = 0..n-1` |
| `envRange {n, offset}` | `n` consecutive cells read from **absolute** index `offset` |
| `bitsOf {n, arg: FExpr}` | the `n` low bits of the canonical value (field-level: `n` may exceed 64) |
| `append {left, right}` | concatenation |

## Field arithmetic

Field elements serialize as their canonical value (`0 ≤ v < p`). The operations a
consumer must implement: `+`, `·`, inverse with `0⁻¹ = 0`, canonical value (for `val`,
`lt`, `bit`, `bitsOf`), and value-to-element (for `ofU64`; on a prime field this is
just `n mod p`). For a 31-bit field such as KoalaBear (`p = 2³¹ − 2²⁴ + 1`), products
fit in `u64` and no Montgomery form is needed for a reference interpreter.

## Sharing (`steps`) and the size guarantee

Authored witness programs are deeply shared terms, and a naive serialization expands
every shared subterm into a fresh copy — at production scale this is fatal (a real
64-bit division circuit serialized to **1.22 GB** this way).
`Operations.witgenJsonShared?` therefore rebuilds each witness program with every
distinct non-trivial scalar subterm interned as a `let`-step (`WitgenIR.share`) before
serializing. The transformation is **proven evaluation-preserving**
(`WitgenIR.eval_share`, axiom-clean), so consumers may treat shared and unshared
payloads as the same program; the same division circuit is 1.04 MB shared. An
interpreter gets the same win at evaluation time: cost is proportional to distinct
subterms, provided each step is evaluated once into the locals array (the loop above
does exactly that).

`witgenJsonShared?` needs `[DecidableEq F] [Hashable F]` for the interning memo; the
scoped instance `Witgen.instHashableOfVal` (canonical-value hashing, available for any
`FiniteField` via `open scoped Witgen`) satisfies the latter.

## Determinism

JSON object key order is code-determined and the serializer embeds no timestamps, so
serialization is deterministic: the same program at the same revision produces the same
bytes. Downstream projects can (and do) commit payloads and byte-diff them against
fresh exports in CI to catch wire-format drift on a version bump.
