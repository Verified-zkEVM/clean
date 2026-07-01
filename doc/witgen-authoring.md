# Writing circuit witnesses (witness IR)

Witness generators in Clean are written in a deep-embedded IR (`Clean/Circuit/WitnessIR.lean`),
so that witness generation is _data_: serializable for Rust proving backends
(`#witgen_json`), checkable (`#assert_exportable`), and still evaluated in Lean by a
verified reference interpreter (`Circuit.witgen`). This guide shows the authoring
surface; see `doc/witgen-ir-plan.md` for the design history.

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
- `x.val : NExpr` (the `ℕ` value of an expression), `n.toField : FExpr` (cast back,
  via `FiniteField.fromNat` so it is also correct on binary fields).
- `NExpr` has `+ * / % &&& ||| ^^^ <<< >>>` and `OfNat` literals; `FExpr` has
  `+ * - ⁻¹` and constants.
- conditions: `a =? b` (field equality), `a <? b` (Nat comparison), used with `.ite`.

## Programs with sharing: `witnessProgram`

When a typed witness needs `let`-bound shared values, use `witnessProgram`.
It is `witness`, but in the `Witgen.M` builder monad. Binding an `FExpr` or
`NExpr` with `←` creates a shared witness-IR step:

```lean
let z ← witnessProgram do
  let y ← x + 1
  return U64.mk y ...
```

For vector witnesses, `witnessVectorProgram` exposes the lower-level `VExpr` API,
including compact loops via `.range` (the lambda receives the index as an `NExpr`):

```lean
-- SHA256 Add32: shared 32-bit sum, then one output bit per index
let z ← witnessVectorProgram 32 do
  let sum ← (bitsVal a + bitsVal b) % (2^32 : ℕ)
  return .range 32 fun i => ((sum >>> i) % 2).toField

-- generic-length bit decomposition (Bits, Bitify)
let bits ← witnessVector n (.range n fun i => ((x.val >>> i) % 2).toField)
```

`witnessIR` remains available for constructing a `WitgenIR` directly.

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
