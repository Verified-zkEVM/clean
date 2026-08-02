import Clean.Halo2.Configure

/-!
# `compress_selectors`, ported: the selector-compression map and its algebra

Derives the `SelCompressMap` from the circuit — halo2's whole `compress_selectors`
pipeline (`circuit.rs` `compress_selectors` + `compress_selectors.rs` `process`), whose
*exact* greedy order matters: a valid-but-different packing produces different gate
polynomials and fails VK comparison.

* per-selector degrees — the maximal `Expression.degree` of a gate polynomial whose
  simple selector is this one (`selectorMaxDegrees`; complex and gate-less selectors
  stay at `0`);
* the degree budget — `ConstraintSystem::degree()` (`csDegree`): the permutation
  argument's constant `3`, the lookups' `max 4 (2 + input + table)`, the gate degrees
  (Clean's constraint system has no `minimum_degree`, matching Orchard, which never
  sets one);
* the packing (`process`): degree-`0` selectors get their own columns first, in index
  order; the rest combine greedily in index order — a candidate joins if it conflicts
  with no member (never co-enabled on a row) and the combination stays within budget,
  with halo2's short-circuit once the budget is exactly filled;
* the root-finding replacement algebra (`selReplacement`/`substSelectorMap`) each
  selector is substituted by over its packed column.

The activation input is `activations` over the synthesized operations at their floor-planned
placement (`Clean.Halo2.Keygen.FloorPlanner`).
-/

namespace Halo2.Expression

/-- halo2 `Expression::degree`: queries and selectors are degree `1`, constants `0`,
sums take the max, products add. -/
def degree {F L : Type} : Expression F L → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree

/-- halo2 `Expression::extract_simple_selector`, first-found: the simple selector
occurring in the expression, if any (the constraint system enforces at most one). -/
def simpleSelector? {F : Type} : Expression F Query → Option Selector
  | .var (.selector s) => if s.simple then some s else none
  | .var _ => none
  | .const _ => none
  | .add a b => a.simpleSelector? <|> b.simpleSelector?
  | .mul a b => a.simpleSelector? <|> b.simpleSelector?

end Halo2.Expression

namespace Halo2

variable {F : Type}

/-- halo2 `lookup::Argument::required_degree`: `max 4 (2 + input + table)` over the
argument's expression degrees (each at least `1`). -/
def LookupArgument.requiredDegree (l : LookupArgument F) : ℕ :=
  let inputDeg := l.inputs.foldl (fun m e => max m e.degree) 1
  let tableDeg := l.tables.foldl (fun m e => max m e.degree) 1
  max 4 (2 + inputDeg + tableDeg)

/-- Flatten a `ConstraintSystem`'s gates to the ordered list of all constraint polynomials
(mirrors halo2 `PinnedGates`' `flat_map(polynomials)`). -/
def flatGates (cs : ConstraintSystem F) : List (Expression F Query) :=
  cs.gates.flatMap (fun g => g.constraints.map (·.poly))

/-! ## The selector-compression map -/

/-- One selector's compression datum, from `compress_selectors`: the packed fixed-column
index, the combination length (how many selectors share the column), and this selector's
assigned root (`1..=combinationLen`). The replacement expression is
`q·∏_{i∈[1,len], i≠root}((i : F) − q)` over the packed column's rotation-0 fixed query `q`
(`compress_selectors.rs:184-208`); degree-0 (complex/lookup-only) selectors are alone in
their column with the bare-query replacement (`len = 1, root = 1`). -/
structure SelCompress where
  packedCol : ℕ
  combinationLen : ℕ
  assignedRoot : ℕ
deriving DecidableEq, Repr

/-- The whole selector-compression map: how many NEW fixed columns compression appended,
and per selector index its `SelCompress`. -/
structure SelCompressMap where
  newFixedCols : ℕ
  entries : List (ℕ × SelCompress)
deriving DecidableEq, Repr

/-- Look up a selector's compression datum by index (`entries` is an association list
keyed by selector index). -/
def SelCompressMap.lookup (map : SelCompressMap) (s : ℕ) : Option SelCompress :=
  (map.entries.find? (fun e => e.1 = s)).map (·.2)

section Field
variable [Field F]

/-- Build the root-finding replacement polynomial `q·∏_{i≠root}((i : F) − q)` for a selector,
`q` being the packed column's fixed query (`compress_selectors.rs:184-208`; left-assoc fold,
matching Rust's `expression = expression * (Constant(root) − query)` accumulation). For
`combinationLen = 1` this is the bare `q` (empty product) — the single-selector and
degree-0 (complex/lookup-only selector) cases. -/
def selReplacement (d : SelCompress) : Expression F Query :=
  let q : Expression F Query := var (.fixed ⟨d.packedCol⟩ 0)
  let factors := (List.range d.combinationLen).filterMap (fun j =>
    let i := j + 1
    if i = d.assignedRoot then none
    else some (((i : F) : Expression F Query) - q))
  factors.foldl (· * ·) q

/-- Substitute each `Query.selector k` by its root-finding replacement from the map `m`
(`k ↦ SelCompress`). Selectors not in the map are left as-is (should not happen for a
complete map). Rust substitutes in gates AND lookups (`circuit.rs:1321-1335` — lookup
expressions carry the complex selectors). -/
def substSelectorMap (m : ℕ → Option SelCompress) :
    Expression F Query → Expression F Query
  | .var (.selector s) => match m s.index with
      | some d => selReplacement d
      | none => .var (.selector s)
  | .var q => .var q
  | .const c => .const c
  | .add a b => .add (substSelectorMap m a) (substSelectorMap m b)
  | .mul a b => .mul (substSelectorMap m a) (substSelectorMap m b)

omit [Field F] in
private theorem noSimpleSelectors_foldl_mul
    (factors : List (Expression F Query))
    (accumulator : Expression F Query)
    (haccumulator : accumulator.NoSimpleSelectors)
    (hfactors : ∀ factor ∈ factors, factor.NoSimpleSelectors) :
    (factors.foldl (· * ·) accumulator).NoSimpleSelectors := by
  induction factors generalizing accumulator with
  | nil =>
      exact haccumulator
  | cons factor rest ih =>
      rw [List.foldl_cons]
      apply ih
      · exact ⟨haccumulator, hfactors factor (by simp)⟩
      · intro next hnext
        exact hfactors next (by simp [hnext])

/-- The root-finding replacement contains no selector leaves. -/
theorem selReplacement_noSimpleSelectors (description : SelCompress) :
    (selReplacement (F := F) description).NoSimpleSelectors := by
  unfold selReplacement
  apply noSimpleSelectors_foldl_mul
  · trivial
  · intro factor hfactor
    rw [List.mem_filterMap] at hfactor
    obtain ⟨index, _, hresult⟩ := hfactor
    by_cases hroot : index + 1 = description.assignedRoot
    · simp [hroot] at hresult
    · rw [if_neg hroot, Option.some_inj] at hresult
      subst factor
      trivial

/-- Selector substitution preserves the prohibition on simple selector leaves. -/
theorem substSelectorMap_noSimpleSelectors
    (m : ℕ → Option SelCompress)
    (expression : Expression F Query)
    (hfree : expression.NoSimpleSelectors) :
    (substSelectorMap m expression).NoSimpleSelectors := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          simp only [Expression.NoSimpleSelectors] at hfree
          simp only [substSelectorMap]
          split
          · exact selReplacement_noSimpleSelectors _
          · simpa [Expression.NoSimpleSelectors] using hfree
      | fixed column rotation =>
          trivial
      | advice column rotation =>
          trivial
      | «instance» column rotation =>
          trivial
  | const value =>
      trivial
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft hfree.1, ihRight hfree.2⟩
  | mul left right ihLeft ihRight =>
      exact ⟨ihLeft hfree.1, ihRight hfree.2⟩

end Field

/-! ## Deriving the map from the circuit -/

/-- halo2 `compress_selectors::SelectorDescription`: a selector index, its activation
rows, and the maximal degree of a gate involving it. -/
structure SelectorDescription where
  selector : ℕ
  activations : Array Bool
  maxDegree : ℕ

/-- Two selectors conflict if they are enabled on a common row. -/
def SelectorDescription.conflicts (a b : SelectorDescription) : Bool :=
  (a.activations.toList.zip b.activations.toList).any fun (x, y) => x && y

/-- One pass of halo2's inner combination loop: scan the candidates in order, adding
each that conflicts with no member and keeps `max-degree-so-far + len + 1` within the
budget; stop scanning entirely once `d + len` fills the budget (halo2's
short-circuit). Returns the finished combination and the not-added candidates in their
original order. -/
def extendCombination (maxDegree : ℕ) :
    ℕ → List SelectorDescription → List SelectorDescription →
    List SelectorDescription × List SelectorDescription
  | _, comb, [] => (comb, [])
  | d, comb, s :: rest =>
      if d + comb.length = maxDegree then
        (comb, s :: rest)
      else if comb.any (·.conflicts s) then
        let (comb', rem) := extendCombination maxDegree d comb rest
        (comb', s :: rem)
      else
        let nd := max d (s.maxDegree - 1)
        if nd + comb.length + 1 > maxDegree then
          let (comb', rem) := extendCombination maxDegree d comb rest
          (comb', s :: rem)
        else
          extendCombination maxDegree nd (comb ++ [s]) rest

/-- Form combinations by seeding each with the first unassigned selector and extending
greedily (`fuel` bounds the recursion by the selector count; each round consumes at
least the seed). -/
def buildCombinations (maxDegree : ℕ) :
    ℕ → List SelectorDescription → List (List SelectorDescription)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, s :: rest =>
      let (comb, rem) := extendCombination maxDegree (s.maxDegree - 1) [s] rest
      comb :: buildCombinations maxDegree fuel rem

/-- halo2 `compress_selectors::process`, packing only: degree-`0` selectors take their
own columns first (index order, bare-query replacement `len = 1, root = 1`), then the
greedy combinations. Packed-column indices are relative to the first newly allocated
column; entries are in halo2's assignment order. -/
def process (selectors : List SelectorDescription) (maxDegree : ℕ) : SelCompressMap :=
  let deg0 := selectors.filter (·.maxDegree = 0)
  let rest := selectors.filter (·.maxDegree ≠ 0)
  let deg0Entries := deg0.zipIdx.map fun (s, k) =>
    (s.selector, SelCompress.mk k 1 1)
  let combs := buildCombinations maxDegree rest.length rest
  let combEntries := combs.zipIdx.flatMap fun (comb, k) =>
    comb.zipIdx.map fun (s, p) =>
      (s.selector, SelCompress.mk (deg0.length + k) comb.length (p + 1))
  { newFixedCols := deg0.length + combs.length
    entries := deg0Entries ++ combEntries }

/-- Every packed column emitted by `process` lies in its newly allocated fixed-column
prefix. -/
theorem process_entry_packedCol_lt_newFixedCols
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    {entry : ℕ × SelCompress}
    (hentry : entry ∈ (process selectors maxDegree).entries) :
    entry.2.packedCol < (process selectors maxDegree).newFixedCols := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change entry ∈
    (degreeZero.zipIdx.map fun (description, column) =>
      (description.selector, SelCompress.mk column 1 1)) ++
    (combinations.zipIdx.flatMap fun (combination, column) =>
      combination.zipIdx.map fun (description, position) =>
        (description.selector,
          SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))) at hentry
  change entry.2.packedCol < degreeZero.length + combinations.length
  rw [List.mem_append] at hentry
  rcases hentry with hdegreeZero | hcombination
  · obtain ⟨indexed, hindexed, hentryEq⟩ :=
      List.mem_map.mp hdegreeZero
    rcases indexed with ⟨description, column⟩
    subst entry
    change column < degreeZero.length + combinations.length
    have hcolumn := List.snd_lt_of_mem_zipIdx hindexed
    omega
  · rw [List.mem_flatMap] at hcombination
    obtain ⟨indexedCombination, hindexed, hentry⟩ := hcombination
    rcases indexedCombination with ⟨combination, column⟩
    obtain ⟨indexedDescription, _, hentryEq⟩ :=
      List.mem_map.mp hentry
    rcases indexedDescription with ⟨description, position⟩
    subst entry
    change degreeZero.length + column <
      degreeZero.length + combinations.length
    have hcolumn := List.snd_lt_of_mem_zipIdx hindexed
    omega

/-- A successful association-list lookup originates in the map's entries. -/
theorem SelCompressMap.exists_mem_entries_of_lookup
    (map : SelCompressMap) {selector : ℕ} {compressed : SelCompress}
    (hlookup : map.lookup selector = some compressed) :
    ∃ entry ∈ map.entries, entry.2 = compressed := by
  simp only [SelCompressMap.lookup, Option.map_eq_some_iff] at hlookup
  obtain ⟨entry, hfind, hcompressed⟩ := hlookup
  exact ⟨entry, List.mem_of_find?_eq_some hfind, hcompressed⟩

/-- Per-selector maximal gate degree (`circuit.rs` `compress_selectors`, the `degrees`
loop): over every gate polynomial, the simple selector it contains — if any — records
the polynomial's degree. -/
def selectorMaxDegrees (cs : ConstraintSystem F) : Array ℕ :=
  (flatGates cs).foldl (init := (List.replicate cs.numSelectors 0).toArray)
    fun degs p =>
      match p.simpleSelector? with
      | some s => degs.modify s.index (max · p.degree)
      | none => degs

/-- halo2 `ConstraintSystem::degree`: the max of the permutation argument's constant
`3`, the lookups' required degrees, and the gate degrees (no `minimum_degree` — Clean's
constraint system does not model it and Orchard never sets one). -/
def csDegree (cs : ConstraintSystem F) : ℕ :=
  let lookupDeg := cs.lookups.foldl (fun m l => max m l.requiredDegree) 1
  let gateDeg := (flatGates cs).foldl (fun m p => max m p.degree) 0
  max 3 (max lookupDeg gateDeg)

/-- The per-selector activation table from `activations`' `(selector, absRow)` pairs, as
`numSelectors` rows of `n` booleans. -/
def activationTable (n numSelectors : ℕ) (acts : List (ℕ × ℕ)) : Array (Array Bool) :=
  acts.foldl (init := (List.replicate numSelectors
      ((List.replicate n false).toArray)).toArray)
    fun tbl (sel, row) => tbl.modify sel (·.set! row true)

/-- **Derive the selector-compression map from the circuit**: the constraint system
supplies the degrees and budget, the synthesized activations supply the packing
constraints, and the packed columns append after the existing fixed columns. -/
def deriveSelCompressMap (cs : ConstraintSystem F) (n : ℕ) (acts : List (ℕ × ℕ)) :
    SelCompressMap :=
  let tbl := activationTable n cs.numSelectors acts
  let degs := selectorMaxDegrees cs
  let descs := (List.range cs.numSelectors).map fun i =>
    SelectorDescription.mk i tbl[i]! degs[i]!
  let m := process descs (csDegree cs)
  { newFixedCols := m.newFixedCols
    entries := m.entries.map fun (s, sc) =>
      (s, { sc with packedCol := sc.packedCol + cs.numFixedColumns }) }

/-- Every successful lookup in the circuit-derived map names one of the packed fixed
columns allocated by selector compression. -/
theorem deriveSelCompressMap_lookup_packedColumn
    (cs : ConstraintSystem F) (n : ℕ) (acts : List (ℕ × ℕ))
    {selector : ℕ} {compressed : SelCompress}
    (hlookup : (deriveSelCompressMap cs n acts).lookup selector =
      some compressed) :
    ∃ index < (deriveSelCompressMap cs n acts).newFixedCols,
      compressed.packedCol = cs.numFixedColumns + index := by
  let table := activationTable n cs.numSelectors acts
  let degrees := selectorMaxDegrees cs
  let descriptions := (List.range cs.numSelectors).map fun index =>
    SelectorDescription.mk index table[index]! degrees[index]!
  let packing := process descriptions (csDegree cs)
  obtain ⟨entry, hentry, hcompressed⟩ :=
    SelCompressMap.exists_mem_entries_of_lookup
      (deriveSelCompressMap cs n acts) hlookup
  change entry ∈ packing.entries.map (fun (sourceSelector, source) =>
    (sourceSelector,
      { source with
        packedCol := source.packedCol + cs.numFixedColumns })) at hentry
  obtain ⟨⟨sourceSelector, source⟩, hsource, hentryEq⟩ :=
    List.mem_map.mp hentry
  subst entry
  simp only at hcompressed
  subst compressed
  have hcolumn := process_entry_packedCol_lt_newFixedCols
    descriptions (csDegree cs) hsource
  refine ⟨source.packedCol, ?_, ?_⟩
  · simpa [packing] using hcolumn
  · change source.packedCol + cs.numFixedColumns =
      cs.numFixedColumns + source.packedCol
    omega

end Halo2
