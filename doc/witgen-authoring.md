# Writing circuit witnesses (witness IR)

Witness generators in Clean are written in a deep-embedded IR (`Clean/Circuit/WitnessIR.lean`),
so that witness generation is *data*: serializable for Rust proving backends
(`#witgen_json`), checkable (`#assert_exportable`), and still evaluated in Lean by a
verified reference interpreter (`Circuit.witgen`). This guide shows the authoring
surface; see `doc/witgen-ir-plan.md` for the design history.

## The common case: `witness` with typed expressions

`witness` takes per-element IR expressions *in the shape of the value type*, so the
type is inferred from the argument (like the old closure API):

```lean
open Witgen  -- for `=?`, `<?` notation

-- scalar: an `FExpr` (field-sorted IR expression)
let z ← witness (.ite (x =? 0) 0 x⁻¹)                  -- IsZeroField
let and ← witness ((x.val &&& y.val).toField)           -- And8

-- structs: the value type's constructor, fields are FExprs
let z ← witness (U64.mk (xorByte x.x0 y.x0) ... )       -- Xor64

-- vectors
let z ← witness (Vector.ofFn fun (i : Fin 32) => Witgen.FExpr.expr (a[i] * b[i]))
```

Building blocks:
- `Expression F` coerces into `FExpr` (`.expr`), so circuit vars/expressions drop in.
- `x.val : NExpr` (the `ℕ` value of an expression), `n.toField : FExpr` (cast back,
  via `FiniteField.fromNat` so it is also correct on binary fields).
- `NExpr` has `+ * / % &&& ||| ^^^ <<< >>>` and `OfNat` literals; `FExpr` has
  `+ * - ⁻¹` and constants.
- conditions: `a =? b` (field equality), `a <? b` (Nat comparison), used with `.ite`.

## Programs with sharing or loops: `witnessIR`

When the witness needs `let`-bound shared values or a length-`n` loop, use a full
program. Reference `let`-steps by position (`.localVar 0`), build loop bodies with
`.range` (the lambda receives the index as an `NExpr`):

```lean
-- SHA256 Add32: shared 32-bit sum, then one output bit per index
let z ← witnessIR (value := (Vector · 32)) (.ir
  [.letN ((bitsVal a + bitsVal b) % ((2^32 : ℕ) : Witgen.NExpr (F p)))]
  (.range 32 fun i => (((.localVar 0) >>> i) % 2).toField))

-- generic-length bit decomposition (Bits, Bitify)
let bits ← witnessVector n (.range n fun i => ((x.val >>> i) % 2).toField)
```

`witnessIR` usually needs the value type named (`(value := ...)`) or a binder
annotation — a program's type does not determine it.

## Nondeterminism: tables, prover data, hints

- `.arrGet xs i` — read a constant `Array F` at a computed index (0 out of bounds).
  Example: FemtoCairo instruction fetch over `Array.ofFn program`.
- `.dataGet key width row col` / `.hintGet ...` — read committed prover data /
  uncommitted hints (`ProverData`-keyed). Example: FemtoCairo memory,
  `witness (.dataGet "memory" 2 addr.val 1)`.
- `witnessNative fun env => ...` — the escape hatch for genuinely arbitrary Lean
  (e.g. a `Bool`-valued hint closure, `HintExample`). Not exportable:
  `#assert_exportable` rejects it, and it stays interpreted in Lean.

## Checking and export

```lean
#assert_exportable (Gadgets.Xor64.circuit (p := pBabybear))   -- fails on .native
#witgen_json (Gadgets.IsZeroField.circuit (F := F pBabybear)) -- Rust payload
```

## Proof-side notes (when porting or writing proofs)

The `circuit_norm` simp set reduces IR evaluation to the same normal forms the old
closures produced. The recurring local fixes:
1. Proof steps using the *default* simp set on witness values need `circuit_norm`
   added (`simpa [circuit_norm, h_input] using h_env 0`).
2. Proof-carrying normal forms bridge via dedicated lemmas:
   `FieldUtils.mod_eq_natCast` / `floorDiv_eq_natCast`, `Utils.Bits.getElem_fieldToBits`.
3. IR conditionals are data until per-element extraction reduces them; resolve the
   resulting `if`-conditions at the extraction sites with `FiniteField.val_inj_F`
   (deliberately not in `circuit_norm`) plus the case facts.

## Remaining `.native` uses (audited, phase 7)

- `HintExample` — a `Bool`-valued hint closure; the canonical escape-hatch use.
- `LookupCircuit.fromTable` — the output is computed by the circuit's
  `constantOutput` function (a per-circuit Lean function, i.e. a hint); making such
  circuits exportable means registering their function as a named intrinsic with a
  Rust-side implementation (future work, see plan phase 6 notes).
- `Clean/Examples/WitnessExport.lean` — a deliberately-native circuit testing that
  `#assert_exportable` rejects it.

`.native` remains available for prototyping: write the closure first, port to IR when
the gadget stabilizes; `grep witnessNative` / `#assert_exportable` show what's left.
