import Clean.Circuit

/-!
# R1CS cost meter

A small utility to measure the arithmetization cost of a circuit under an R1CS
cost model:

* `witnesses`   — length of the witness vector (number of allocated cells),
* `constraints` — number of R1CS rows (one per `assert`), and
* `lookups`     — number of lookup arguments (should be `0` for a pure-R1CS circuit).

In R1CS, *linear combinations are free*: building up an additive/scalar
combination of variables inside a constraint costs nothing, only the
multiplicative `assert` row and the witness allocation are charged. The number
of `assert` operations therefore equals the R1CS constraint count, and the
witness count equals `localLength`. Both recurse through subcircuits via the
existing `Operations` API (`localLength`, `constraints`, `lookups`).

## Charging one row per `assert` is only honest if every `assert` *is* one row

A single R1CS row is `⟨A,z⟩ · ⟨B,z⟩ = ⟨C,z⟩` with `A, B, C` affine — i.e. the
asserted expression has the shape `A * B - C` (degree ≤ 2, the degree-2 part a
*single* product of two affine forms). An `assert` of, say, a degree-3 polynomial,
or of `a*b + c*d` (two independent products, a rank-2 form) is **not** one row:
the latter needs an auxiliary witness `m = a*b` plus a second product row. To stop
such an `assert` from being silently miscounted as a single constraint, the meter
**validates every asserted expression** with `isR1CSRow` and aborts (`panic!`) on
the first one that is not a genuine single row. `a*b + c*d` is rejected, not
transformed — the author must emit the extra witness/row explicitly so the cost is
counted truthfully.
-/

namespace Clean.CostR1CS

/-! ## Structural R1CS-row validation -/

variable {F : Type}

/-- Structural multiplicative degree of an expression: an upper bound on its
polynomial degree (exact unless a product cancels, which only makes the check
conservative). `var` is degree 1, `const` degree 0, `add` takes the max, `mul`
adds. -/
def degree : Expression F → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max (degree a) (degree b)
  | .mul a b => degree a + degree b

/-- Number of genuine degree-2 product terms along the top-level `add` spine, or
`none` if some summand is not a valid R1CS term. The `add` spine sums the counts,
so `a*b + c*d` reports `2`.

For a `mul` node we first look through any **constant** factor: a degree-0 factor
only *scales* the other side, adding no product and not raising the degree, so its
count is the count of the other factor. This is what lets a *negated* product such
as `(-1) * (A*B)` — which is how `a - b*c` and in particular `Ch`'s
`z - g - e*(f-g)` desugar (`Sub`/`Neg` build `add _ (mul (const (-1)) _)`) — still
count as the single product it genuinely is. With both factors non-constant, the
node is one quadratic product exactly when both are affine (degree ≤ 1); a factor
of degree ≥ 2 means total degree ≥ 3, which is not an R1CS row (`none`). -/
def r1csProducts : Expression F → Option ℕ
  | .const _ => some 0
  | .var _ => some 0
  | .add a b =>
    match r1csProducts a, r1csProducts b with
    | some m, some n => some (m + n)
    | _, _ => none
  | .mul a b =>
    if degree a = 0 then r1csProducts b
    else if degree b = 0 then r1csProducts a
    else if degree a ≤ 1 ∧ degree b ≤ 1 then some 1
    else none

/-- An expression is a single R1CS constraint iff, along its `add` spine, every
summand is affine plus at most one product of two affine forms — exactly the
shape `A * B - C` (one rank-1 row `⟨A,z⟩·⟨B,z⟩ = ⟨C,z⟩`). Pure-affine `A` is
allowed (it is `A · 1 = 0`). Rejected: degree ≥ 3, and two-or-more products such
as `a*b + c*d` (rank-2, which needs an auxiliary witness + a second row).

NOTE: `r1csProducts` is a *sound over-approximation*, not the exact rank of the
quadratic form. It counts products **syntactically** (modulo constant scalars),
so `rank ≤ r1csProducts` always — but the two can differ when products share a
factor and could be re-factored, e.g. `a*b + a*c = a*(b+c)` is genuinely rank 1
yet is counted as `2`. That is the *safe* direction: a true multi-row assert can
never be charged as one row (we only ever over-reject, forcing a re-factored
rewrite, never under-count). Computing the exact answer would require factoring
the degree-2 part (a rank/signature check on its Hessian). Every assert this
codebase emits has ≤ 1 product as written, so the bound is exact in practice. -/
def isR1CSRow (e : Expression F) : Bool :=
  match r1csProducts e with
  | some k => k ≤ 1
  | none => false

/-! ## Cost -/

/-- R1CS cost summary of a circuit. -/
structure Cost where
  witnesses : ℕ
  constraints : ℕ
  lookups : ℕ
deriving Repr, DecidableEq, Inhabited

instance : Add Cost where
  add a b := ⟨a.witnesses + b.witnesses, a.constraints + b.constraints, a.lookups + b.lookups⟩

/-- The asserted expressions of a circuit that are not valid single R1CS rows. -/
def r1csViolations [Field F] (ops : Operations F) : List (Expression F) :=
  (Operations.constraints ops).filter (fun e => ! isR1CSRow e)

/-- Cost of a flat list of operations. Aborts if any `assert` is not a single
R1CS row (see `isR1CSRow`), so a non-row `assert` can never be silently charged
as one constraint. -/
def operationsCost [Field F] (ops : Operations F) : Cost :=
  let cs := Operations.constraints ops
  let bad := cs.filter (fun e => ! isR1CSRow e)
  if bad.isEmpty then
    { witnesses := Operations.localLength ops
      constraints := cs.length
      lookups := (Operations.lookups ops).length }
  else
    panic! s!"CostR1CS: {bad.length} of {cs.length} asserted expression(s) are not single \
      R1CS rows (first at constraint index {cs.findIdx (fun e => ! isR1CSRow e)}); each must \
      have shape A*B - C with A, B, C affine. A term like a*b + c*d is two products and needs \
      an auxiliary witness plus a second row, so it cannot be charged as one constraint."

/-- Cost of running a circuit at offset `n` (default `0`; counts are
offset-independent). Aborts if any `assert` is not a single R1CS row. -/
def circuitCost {α : Type} [Field F] (c : Circuit F α) (n : ℕ := 0) : Cost :=
  operationsCost (Circuit.operations c n)

/-- Compute a circuit's cost and assert it equals `expected`, aborting otherwise.
Validates both the per-`assert` R1CS-row shape (via `circuitCost`) and the exact
witness / constraint / lookup counts — e.g. pass `lookups := 0` to lock in a
pure-R1CS circuit, or pin the full triple to guard against regressions. -/
def checkCost {α : Type} [Field F] (c : Circuit F α) (expected : Cost) (n : ℕ := 0) : Cost :=
  let actual := circuitCost c n
  if actual = expected then actual
  else panic! s!"CostR1CS: cost mismatch — expected {repr expected}, got {repr actual}"

end Clean.CostR1CS
