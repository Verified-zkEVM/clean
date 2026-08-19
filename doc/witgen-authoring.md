# Writing circuit witnesses (witness IR)

Witness generators in Clean are written in a deep-embedded IR (`Clean/Circuit/WitnessIR.lean`),
so that witness generation is _data_: serializable for Rust proving backends
(`#witgen_json`), checkable (`#assert_exportable`), and still evaluated in Lean by a
verified reference interpreter (`Circuit.witgen`). This guide shows the authoring
surface; the serialized JSON contract is specified in `doc/witgen-wire-format.md`.

## The common case: `witness` with typed expressions

`witness` takes per-element IR expressions _in the shape of the value type_, so the
type is inferred from the argument (like the old closure API):

```lean
-- scalar: an `FExpr` (field-sorted IR expression)
let z ← witness (.ite (x =? 0) 0 x⁻¹)                  -- IsZeroField
let and ← witness ((x.val &&& y.val).toField)           -- And8

-- structs: the value type's constructor, fields are FExprs
let z ← witness <| U64.mk (x.x0.val ^^^ y.x0.val).toField ... -- Xor64

-- vectors
let z ← witness (Vector.ofFn fun (i : Fin 32) => .expr (a[i] * b[i]))
```

Building blocks:

- `Expression F` coerces into `FExpr` (`.expr`), so circuit vars/expressions drop in.
- `x.val : U64Expr` (the **u64** value of an expression: `ZMod.val` truncated to 64 bits),
  `n.toField : FExpr` (cast back, via `FiniteField.fromNat` so it is also correct on
  binary fields).
- `U64Expr` has `+ * / % &&& ||| ^^^ <<< >>>` and `OfNat` literals, all with wrapping
  `u64` semantics; `FExpr` has `+ * - ⁻¹` and constants.
- conditions: `a =? b` (equality) and `a <? b` (comparison), used with `.ite`. Both
  overload on the operand sort: field-sorted operands compare `ZMod.val`s exactly,
  u64-sorted operands compare `u64`s.
- bit extraction is field-sorted, so it is not limited to 64 bits: `x.bit i : FExpr` is
  bit `i` of `ZMod.val x`, and `x.bits n : VExpr F n` is its `n` low bits.
- `VExpr.envRange offset` witnesses a run of `n` consecutive environment cells.

### Wrapping, and what it means for proofs

The integer sort is `UInt64` and every operation on it wraps modulo `2^64`, exactly like
Rust's `u64`. Gadgets work on bytes, 32-bit limbs and small indices, so the wraps are
never taken — and in proofs the `circuit_norm` simproc `u64Wrap` erases a `% 2^64` (or a
shift's `% 64`) as soon as `omega` can bound the operand from the gadget's own
assumptions. If a wrap survives simplification, the missing piece is usually a bound that
has not been destructured into the local context yet.

Anything genuinely wider than 64 bits must stay field-sorted: `x.bit i` / `x.bits n` for
bit decomposition, `a <? b` on field operands for comparison.

## Programs with sharing: `witnessProgram`

When a typed witness needs `let`-bound shared values, use `witnessProgram`.
It is `witness`, but in the `Witgen.M` builder monad. Binding an `FExpr` or
`U64Expr` with `←` creates a shared witness-IR step:

```lean
let z ← witnessProgram do
  let y ← x + 1
  return U64.mk y ...
```

For vector witnesses, `witnessVectorProgram` exposes the lower-level `VExpr` API,
including compact loops via `.range` (the lambda receives the index as a `U64Expr`):

```lean
-- SHA256 Add32: shared 32-bit sum, then one output bit per index
let z ← witnessVectorProgram 32 do
  let sum ← (bitsVal a + bitsVal b) % (2^32 : ℕ)
  return .range 32 fun i => ((sum >>> i) % 2).toField

-- generic-length bit decomposition (Bits, Bitify) — field-level, so `n` may exceed 64
let bits ← witnessVector n (x.bits n)
```

`witnessIR` remains available for constructing a `WitgenIR` directly.

### Sharing after an opaque program prefix: use plain `let`

When a program starts by binding an *opaque* sub-program — typically reading an
`Unconstrained*` hint passed in from the caller — derive values from it with a plain
Lean `let`, not `←`/`letU`/`letF`:

```lean
let row ← witnessProgram do
  let s ← scalar               -- opaque hint program: the one monadic bind
  let k := s / (8 ^ w : ℕ) % 8 -- plain `let`: duplicates the node in the IR, and that's fine
  return CoordsRow.mk k.toField xs[k] ys[k] us[k]
```

A `letU` here would allocate its local at a step index that depends on the opaque
prefix's step count, and — more fundamentally — proofs would need to know that the
prefix's own output is unaffected by the extension of the locals array, an invariant
with no syntactic handle in `circuit_norm`. Plain `let` duplicates the derived node in
the serialized IR (usually one small arithmetic node), and every read matches the
hint's `h_input` equation directly. Reserve `←`-sharing for programs whose prefix
consists of literal steps. If a use case ever genuinely needs sharing behind an opaque
prefix, that's the signal to add a locals-boundedness lawfulness class to `Witgen.M` —
deliberately deferred until then.

## Nondeterminism: tables, prover data, hints

- `.arrGet xs i` — read a constant `Array F` at a computed index (0 out of bounds).
  Example: FemtoCairo instruction fetch over `Array.ofFn program`.
- `.dataGet key width row col` / `.hintGet ...` — read committed prover data /
  uncommitted hints (`ProverData`-keyed). Prefer `Table.dataGet` / `Table.hintGet`,
  which return typed rows (see FemtoCairo).
- `witnessNative fun env => ...` — the escape hatch for genuinely arbitrary Lean.
  Not exportable: `#assert_exportable` rejects it, and it stays interpreted in Lean.

## Checking and export

```lean
#assert_exportable (Gadgets.Xor64.circuit (p := pBabybear))   -- fails on .native
#witgen_json (Gadgets.IsZeroField.circuit (F := F pBabybear)) -- Rust payload
```
