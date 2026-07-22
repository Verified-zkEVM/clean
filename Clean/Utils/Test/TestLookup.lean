import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Utilities.LookupRangeCheck

open Clean

/-!
Shape / composition regression tests for the lookup axis (`lookup-design.md` §2.2/§2.4).

Each `example` pins a claim the design's normal-form conventions depend on:

- (a) an `enableLookup` op's `Constraints` reduces under `circuit_norm` to the membership
  existential over the typed-accessor atoms (`env.advice`/`env.fixed`), with **no record
  literals** — the syntactic-pin guard. Pinned for BOTH per-row activation variants of the
  range-check argument (`lookup-design.md` §1.4): a two-selector enable
  (`[qLookup, qRunning]`, running-sum row) where the gated input reduces to the running
  word `z_cur − 2^K·z_next`, and a one-selector enable (`[qLookup]`, short row —
  `q_running` OFF) where the *same* argument's input reduces to `z_cur`. This pair is the
  regression test that the activation valuation is the per-row `enabled ↦ 1, rest ↦ 0`
  (an all-ones valuation would wrongly assert running-word membership at short rows).
- (b) a `loadTable` op's `Constraints` reduces to the two `∀`-conjuncts (explicit block +
  conditional default-fill) over `env.fixed`.
- (c) a mini end-to-end: from a `loadTable [0,1,2,3]` constraint plus a (bounded) membership
  fact, derive a `x.val < 4` range conclusion by hand — proving the pieces compose the way
  a range-check gadget's soundness composes them.
-/

namespace Halo2.Lookup.Test
open Halo2 Zcash.Circuits

/-- `q_lookup`, `q_running`: the range-check gating selectors (complex,
`lookup_range_check.rs:320-321`). Concrete indices so the per-row activation valuation
reduces to literals in the shape pins below. -/
def qLookup : Selector := ⟨0, false⟩
def qRunning : Selector := ⟨1, false⟩

/-- The range-check lookup argument, verbatim input shape from `lookup-design.md` §1.4
(K = 4): `q_lookup · (q_running · (z_cur − 2^K·z_next) + (1 − q_running) · z_cur)`,
table = the table column's rotation-0 fixed query. ONE argument whose input reduces to
*different* words depending on which selectors are enabled at the row. -/
def rcArg (z : Column .advice) (tbl : TableColumn) : LookupArgument Fp where
  inputs :=
    let qL : Expression Fp Query := querySelector qLookup
    let qR : Expression Fp Query := querySelector qRunning
    let zCur : Expression Fp Query := queryAdvice z 0
    let zNext : Expression Fp Query := queryAdvice z 1
    [qL * (qR * (zCur - (2 ^ 4 : Fp) * zNext) + (1 - qR) * zCur)]
  tables := [queryFixed tbl.inner]

-- (a-1) Running-sum row: `enableLookup … [qLookup, qRunning] row` — both selectors on.
-- The gated input reduces to the running word `z_cur − 2^4·z_next`; the RHS is written
-- entirely in `env.advice`/`env.fixed` normal form (no `{ … }` record literals, no
-- `env.get … .toAny`), so if the reduction ever stopped landing on that form (or on the
-- wrong word) this example would fail.
example (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (z : Column .advice) (tbl : TableColumn) (row : ℕ) :
    (RegionOperation.enableLookup (rcArg z tbl) [qLookup, qRunning] row).Constraints
        place self env
      ↔ ∃ tableRow : ℕ, tableRow < env.usableRows ∧
          env.advice z ((place self + row : ℕ) : ℤ)
              - 2 ^ 4 * env.advice z ((place self + (row + 1) : ℕ) : ℤ)
            = env.fixed tbl.inner (tableRow : ℤ) := by
  simp only [circuit_norm, rcArg, qLookup, qRunning, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, List.mem_cons, List.not_mem_nil, or_false]
  norm_num

-- (a-2) Short row: `enableLookup … [qLookup] row` — `q_running` OFF. The *same* argument's
-- input reduces to `z_cur` (the directly-witnessed short word), NOT the running word.
-- This is the regression pin for the per-row activation valuation: under an (unsound)
-- all-ones valuation this example would instead assert running-word membership and fail.
example (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (z : Column .advice) (tbl : TableColumn) (row : ℕ) :
    (RegionOperation.enableLookup (rcArg z tbl) [qLookup] row).Constraints place self env
      ↔ ∃ tableRow : ℕ, tableRow < env.usableRows ∧
          env.advice z ((place self + row : ℕ) : ℤ) = env.fixed tbl.inner (tableRow : ℤ) := by
  simp only [circuit_norm, rcArg, qLookup, qRunning, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, List.mem_cons, List.not_mem_nil, or_false]
  norm_num

-- The same via the DSL atom `LookupArgument.enable`, through the accessor lemma
-- (short-row variant).
example (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (z : Column .advice) (tbl : TableColumn) (row : ℕ) :
    RegionOperations.Constraints place self env
      ((rcArg z tbl |>.enable [qLookup] row).operations self)
      ↔ ∃ tableRow : ℕ, tableRow < env.usableRows ∧
          env.advice z ((place self + row : ℕ) : ℤ) = env.fixed tbl.inner (tableRow : ℤ) := by
  simp only [circuit_norm, rcArg, qLookup, qRunning, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, List.mem_cons, List.not_mem_nil, or_false]
  norm_num

-- (b) `loadTable`'s constraint reduces to the explicit block + conditional default-fill,
-- both over `env.fixed`, followed by the remaining-ops constraint (here `True`).
example (place : RegionIndex → ℕ) (env : Environment Fp) (tbl : TableColumn)
    (values : List Fp) (i : RegionIndex) :
    Halo2.Constraints place env [.loadTable tbl values] i
      ↔ (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
        (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
          env.fixed tbl.inner (r : ℤ) = values[0]!) := by
  simp only [circuit_norm]

-- Same through the DSL atom `loadTable`.
example (place : RegionIndex → ℕ) (env : Environment Fp) (tbl : TableColumn)
    (values : List Fp) :
    (loadTable tbl values).Constraints place env
      ↔ (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
        (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
          env.fixed tbl.inner (r : ℤ) = values[0]!) := by
  simp only [Circuit.Constraints, circuit_norm]

-- (c) End-to-end: `loadTable [0,1,2,3]` + a bounded membership witness ⇒ `x.val < 4`.
-- This is exactly the composition a range-check gadget's soundness performs: the
-- `enableLookup` existential delivers a table row holding `x`; the loaded-table facts
-- characterize that row's value; together they force `x ∈ {0,1,2,3}`, hence `x.val < 4`.
example (place : RegionIndex → ℕ) (env : Environment Fp) (tbl : TableColumn) (i : RegionIndex)
    (x : Fp)
    -- the table is loaded with [0,1,2,3]:
    (hload : Halo2.Constraints place env [.loadTable tbl ([0, 1, 2, 3] : List Fp)] i)
    -- the membership witness a gadget extracts: some row r < 4 holds x
    (r : ℕ) (hr : r < 4) (hmem : x = env.fixed tbl.inner (r : ℤ)) :
    x.val < 4 := by
  -- peel the load into its explicit-block conjunct
  simp only [circuit_norm] at hload
  obtain ⟨hexplicit, _hfill⟩ := hload
  -- the loaded value at row r
  have hval : env.fixed tbl.inner (r : ℤ) = ([0, 1, 2, 3] : List Fp)[r]! := by
    have := hexplicit r (by simpa using hr)
    simpa using this
  -- x equals one of 0,1,2,3; interval_cases pins r and evaluates the literal lookup
  subst hmem
  interval_cases r <;>
    simp_all <;>
    decide

/-! ## `range_check` loop normal-form pins (`Ironwood/Utilities/LookupRangeCheck.lean`)

The running-sum gadget is the first with a LOOP in `synthesize`, now built on the framework
`RegionCircuit.forRange'` combinator (`Clean/Halo2/Loops.lean`). These pin the normal form the
migrated loop proofs depend on: the per-round **split** of the loop's `Constraints` into
`∀ i : Fin numWords, <round i>` (the combinator's `forRange'_constraints`, replacing the old
hand-written `++` operations-succ pin), and the running-word membership a single round reduces to. -/

namespace RangeCheckLoop
open Zcash.Circuits.LookupRangeCheck RegionCircuit

-- (d-1) The framework `forRange'` split: the loop's `Constraints` become `∀ i : Fin numWords,
-- <round i's constraints at base row offset + i>`. This `circuit_norm ↓` split (from
-- `Clean/Halo2/Loops.lean`) is what the migrated z-chain lemmas consume — replacing the old
-- hand-written per-round `++` operations-succ recursion.
example (K : ℕ) (cfg : Config K) (element : AssignedCell Fp) (offset numWords : ℕ)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) :
    RegionOperations.Constraints place self env
        ((rangeCheckLoop K cfg element offset numWords).operations self)
      ↔ ∀ i : Fin numWords, RegionOperations.Constraints place self env
          ((rangeCheckRound K cfg element i.val (offset + i.val * 1)).operations self) := by
  simp only [rangeCheckLoop, circuit_norm]

-- (d-2) A single round's ops: `enableLookup [qLookup, qRunning]` (running-sum row at base `row`)
-- then the `assignAdvice` of `z_{idx+1}` at `row + 1`. Pins that a round is exactly those two ops.
example (K : ℕ) (cfg : Config K) (element : AssignedCell Fp) (idx row : ℕ)
    (self : RegionIndex) :
    (rangeCheckRound K cfg element idx row).operations self
      = [.enableLookup (rangeCheckLookup K cfg) [cfg.qLookup, cfg.qRunning] row,
         .assignAdvice cfg.runningSum (row + 1) (zWitness K (idx + 1) element)] := rfl

-- (d-3) A round's `Constraints` reduce to the running-word membership: both `q_lookup` and
-- `q_running` on ⇒ the gated input is `z_cur − z_next·2^K` (the running word, §1.4; the
-- `2^K` is a `.scaled` field factor on the right of `z_next`, VK-faithful), NOT
-- `z_cur` (which would be the short-row reduction). The `assignAdvice` adds no constraint.
example (K : ℕ) (cfg : Config K) (element : AssignedCell Fp) (place : RegionIndex → ℕ)
    (self : RegionIndex) (env : Environment Fp) (idx row : ℕ) :
    RegionOperations.Constraints place self env
        ((rangeCheckRound K cfg element idx row).operations self)
      ↔ ∃ tableRow : ℕ, tableRow < env.usableRows ∧
          env.advice cfg.runningSum ((place self + row : ℕ) : ℤ)
              - env.advice cfg.runningSum ((place self + (row + 1) : ℕ) : ℤ) * 2 ^ K
            = env.fixed cfg.tableIdx.inner (tableRow : ℤ) := by
  simp only [rangeCheckRound, circuit_norm, rangeCheckLookup, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, one_mul, zero_mul, add_zero, sub_self]

end RangeCheckLoop

end Halo2.Lookup.Test
