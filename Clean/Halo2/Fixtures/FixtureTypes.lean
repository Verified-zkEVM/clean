import Clean.Ironwood.Ecc.Basic

/-!
# VK-matching fixture types (vendored ironwood `Expr` mirror)

Local, minimal copies of the ironwood `Fixture.lean` value types (`Zcash.Snark.Expr` and a
`CsFixture` record over the CS-data fields), used to compare a Halo2-Clean `ConstraintSystem`
projection against a fixture dumped from the actual Rust circuit.

**Vendored, not imported** (design doc `vk-matching-design.md` D5): clean2 does not import
ironwood, so we mirror ironwood's `Expr` (`Verifier/Expressions.lean:29-51`) exactly here.
The erasure target of `Expression Fp Query` (`Clean/Halo2/Expression.lean:104-109`) is this
`Expr Fp`. `deriving DecidableEq, Repr` powers the `#eval …  == fixture` comparison.

The dumper (`halo2_proofs::plonk::dump_lean`) emits `CsFixture` literals into
`AddPre.lean` / `AddPost.lean` in this namespace.
-/

namespace Halo2.Fixtures

open _root_.Halo2.Ironwood (Fp)

/-- Ironwood's gate-polynomial AST (`Zcash.Snark.Expr`), index-based: `fixed`/`advice`/
`instance` carry a **query index**, not a `(column, rotation)`. This is the erasure target
of `Halo2.Expression Fp Query`. -/
inductive Expr (F : Type) where
  | constant : F → Expr F
  | fixed : ℕ → Expr F
  | advice : ℕ → Expr F
  | instance : ℕ → Expr F
  | negated : Expr F → Expr F
  | sum : Expr F → Expr F → Expr F
  | product : Expr F → Expr F → Expr F
  | scaled : Expr F → F → Expr F
  /-- Pre-compression only: a simple selector, by index. Post-compression this never
  appears (each is substituted by a fixed-column root-finding polynomial). -/
  | selector : ℕ → Expr F
deriving DecidableEq, Repr

/-- Build an `Fp` from four little-endian u64 limbs, matching the ironwood fixture's `mkFp`
and the Rust dumper's `to_repr()` limb encoding. -/
def mkFp (a b c d : ℕ) : Fp :=
  (a : Fp) + (b : Fp) * (2 : Fp) ^ 64 + (c : Fp) * (2 : Fp) ^ 128 + (d : Fp) * (2 : Fp) ^ 192

/-- One projected lookup argument, in the ironwood `(lookupInputExprs, lookupTableExprs)`
per-lookup shape (`Verifier/Assemble.lean:68-69`). Both sides are index-based `Expr`s (the
table side is a rotation-0 fixed query on the table column). The Rust dumper emits these
from `cs.lookups[i].{input,table}_expressions`. -/
structure LookupFixture where
  inputs : List (Expr Fp)
  tables : List (Expr Fp)
deriving DecidableEq, Repr

/-- The constraint-system data a Halo2-Clean projection must reproduce, in the ironwood
`VerifyingKey` CS-field shape (`Verifier/Assemble.lean:64-79`), specialised to a single
circuit's dump. Query layouts are `(column, rotation)` lists; `gates` is the flat
index-based polynomial list; `lookups` is the per-lookup input/table expression lists in
registration order. -/
structure CsFixture where
  numAdviceColumns : ℕ
  numFixedColumns : ℕ
  numInstanceColumns : ℕ
  numSelectors : ℕ
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  instanceQueryLayout : List (ℕ × ℤ)
  gates : List (Expr Fp)
  lookups : List LookupFixture := []
deriving DecidableEq, Repr

/-- One selector's compression datum, from the Rust `compress_selectors` run: the packed
fixed-column index, the combination length (how many selectors share the column), and this
selector's assigned root (`1..=combinationLen`). The replacement expression is
`q·∏_{i∈[1,len], i≠root}((i : Fp) − q)` over the packed column's rotation-0 fixed query `q`
(`compress_selectors.rs:184-208`); degree-0 (complex/lookup-only) selectors are alone in
their column with the bare-query replacement (`len = 1, root = 1`). -/
structure SelCompress where
  packedCol : ℕ
  combinationLen : ℕ
  assignedRoot : ℕ
deriving DecidableEq, Repr

/-- The whole selector-compression map, dumped by the Rust `dump_prepost_acts`: how many NEW
fixed columns compression appended, and per selector index its `SelCompress`. **Trust
boundary**: the map's *derivation* (exclusion matrix over the real synthesize's activation
table, greedy packing, root assignment) happens Rust-side; Lean applies it mechanically and
the resulting CS is still checked EQUAL to the dumped post-compression fixture, so any
divergence in the reconstruction conventions surfaces as a gate mismatch. -/
structure SelCompressMap where
  newFixedCols : ℕ
  entries : List (ℕ × SelCompress)
deriving DecidableEq, Repr

end Halo2.Fixtures
