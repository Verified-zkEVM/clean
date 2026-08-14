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

/-- halo2 `Expression::extract_simple_selector`, first-found: the simple selector
occurring in the expression, if any (the constraint system enforces at most one). -/
def simpleSelector? {F : Type} : Expression F Query → Option Selector
  | .var (.selector s) => if s.simple then some s else none
  | .var _ => none
  | .const _ => none
  | .add a b => a.simpleSelector? <|> b.simpleSelector?
  | .mul a b => a.simpleSelector? <|> b.simpleSelector?

/-- A selector returned by `simpleSelector?` is simple. -/
theorem simpleSelector?_eq_some_simple
    {F : Type} (expression : Expression F Query) {selected : Selector}
    (hselector : expression.simpleSelector? = some selected) :
    selected.simple = true := by
  induction expression with
  | var query =>
      cases query with
      | selector candidate =>
          simp only [simpleSelector?] at hselector
          split at hselector
          next hsimple =>
            simp only [Option.some.injEq] at hselector
            subst selected
            exact hsimple
          next => simp at hselector
      | fixed column rotation => simp [simpleSelector?] at hselector
      | advice column rotation => simp [simpleSelector?] at hselector
      | «instance» column rotation => simp [simpleSelector?] at hselector
  | const value => simp [simpleSelector?] at hselector
  | add left right ihLeft ihRight =>
      simp only [simpleSelector?] at hselector
      cases hleft : left.simpleSelector? with
      | none =>
          simp [hleft] at hselector
          exact ihRight hselector
      | some candidate =>
          simp [hleft] at hselector
          subst selected
          exact ihLeft hleft
  | mul left right ihLeft ihRight =>
      simp only [simpleSelector?] at hselector
      cases hleft : left.simpleSelector? with
      | none =>
          simp [hleft] at hselector
          exact ihRight hselector
      | some candidate =>
          simp [hleft] at hselector
          subst selected
          exact ihLeft hleft

/-- Gate ownership identifies the selector found by the simple-selector walk with the
gate's distinguished selector, including its kind. -/
theorem simpleSelector?_eq_some_of_selectorsOwnedBy
    {F : Type} (expression : Expression F Query) (owner selected : Selector)
    (howned : expression.SelectorsOwnedBy owner)
    (hselector : expression.simpleSelector? = some selected) :
    selected = owner := by
  induction expression with
  | var query =>
      cases query with
      | selector candidate =>
          simp only [SelectorsOwnedBy] at howned
          subst candidate
          simp only [simpleSelector?] at hselector
          split at hselector
          next => exact Option.some.inj hselector.symm
          next => simp at hselector
      | fixed column rotation => simp [simpleSelector?] at hselector
      | advice column rotation => simp [simpleSelector?] at hselector
      | «instance» column rotation => simp [simpleSelector?] at hselector
  | const value => simp [simpleSelector?] at hselector
  | add left right ihLeft ihRight =>
      simp only [SelectorsOwnedBy] at howned
      simp only [simpleSelector?] at hselector
      cases hleft : left.simpleSelector? with
      | none =>
          simp [hleft] at hselector
          exact ihRight howned.2 hselector
      | some candidate =>
          simp [hleft] at hselector
          subst selected
          exact ihLeft howned.1 hleft
  | mul left right ihLeft ihRight =>
      simp only [SelectorsOwnedBy] at howned
      simp only [simpleSelector?] at hselector
      cases hleft : left.simpleSelector? with
      | none =>
          simp [hleft] at hselector
          exact ihRight howned.2 hselector
      | some candidate =>
          simp [hleft] at hselector
          subst selected
          exact ihLeft howned.1 hleft
end Halo2.Expression

namespace Halo2

variable {F : Type}

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

private theorem foldl_selectorMaxDegrees_getElem?_eq_zero
    (polynomials : List (Expression F Query)) (degrees : Array ℕ)
    {selector : ℕ}
    (hzero : degrees[selector]? = some 0)
    (havoids : ∀ polynomial ∈ polynomials, ∀ candidate,
      polynomial.simpleSelector? = some candidate →
        candidate.index ≠ selector) :
    (polynomials.foldl (init := degrees) fun current polynomial =>
      match polynomial.simpleSelector? with
      | some candidate =>
          current.modify candidate.index (max · polynomial.degree)
      | none => current)[selector]? = some 0 := by
  induction polynomials generalizing degrees with
  | nil => exact hzero
  | cons polynomial polynomials ih =>
      simp only [List.foldl_cons]
      apply ih
      · cases hsimple : polynomial.simpleSelector? with
        | none => exact hzero
        | some candidate =>
            rw [Array.getElem?_modify]
            have hne := havoids polynomial List.mem_cons_self candidate hsimple
            simp [hne, hzero]
      · intro remaining hremaining candidate hsimple
        exact havoids remaining (List.mem_cons_of_mem _ hremaining)
          candidate hsimple

private theorem foldl_selectorMaxDegrees_size
    (polynomials : List (Expression F Query)) (degrees : Array ℕ) :
    (polynomials.foldl (init := degrees) fun current polynomial =>
      match polynomial.simpleSelector? with
      | some candidate =>
          current.modify candidate.index (max · polynomial.degree)
      | none => current).size = degrees.size := by
  induction polynomials generalizing degrees with
  | nil => rfl
  | cons polynomial polynomials ih =>
      simp only [List.foldl_cons]
      rw [ih]
      cases polynomial.simpleSelector? <;> simp

/-- A selector for which every same-index gate selector is complex has degree zero in
selector compression. Gate well-formedness identifies a polynomial's selector with
the gate's distinguished selector, including its kind. -/
theorem selectorMaxDegrees_eq_zero_of_complexGateSelectors
    (cs : ConstraintSystem F) {selector : ℕ}
    (hallocated : selector < cs.numSelectors)
    (hcomplex : cs.gates.Forall fun gate =>
      gate.selector.index = selector → gate.selector.simple = false) :
    (selectorMaxDegrees cs)[selector]! = 0 := by
  let initial := (List.replicate cs.numSelectors 0).toArray
  have hinitial : initial[selector]? = some 0 := by
    rw [getElem?_pos initial selector]
    · simp [initial]
    · simpa [initial] using hallocated
  have hpolynomials : ∀ polynomial ∈ flatGates cs, ∀ candidate,
      polynomial.simpleSelector? = some candidate →
        candidate.index ≠ selector := by
    intro polynomial hpolynomial candidate hsimple hequal
    rw [flatGates, List.mem_flatMap] at hpolynomial
    obtain ⟨gate, hgate, hconstraint⟩ := hpolynomial
    obtain ⟨constraint, hconstraintMem, rfl⟩ := List.mem_map.mp hconstraint
    have howned := List.forall_iff_forall_mem.mp
      gate.wellFormed.selectorsOwned constraint hconstraintMem
    have howner := Expression.simpleSelector?_eq_some_of_selectorsOwnedBy
      constraint.poly gate.selector candidate howned hsimple
    have hsimpleTrue :=
      Expression.simpleSelector?_eq_some_simple constraint.poly hsimple
    have hgateComplex := List.forall_iff_forall_mem.mp hcomplex gate hgate
      (howner ▸ hequal)
    rw [howner] at hsimpleTrue
    simp [hgateComplex] at hsimpleTrue
  have hfold := foldl_selectorMaxDegrees_getElem?_eq_zero
    (flatGates cs) initial hinitial hpolynomials
  let result := (flatGates cs).foldl (init := initial)
    fun current polynomial =>
      match polynomial.simpleSelector? with
      | some candidate =>
          current.modify candidate.index (max · polynomial.degree)
      | none => current
  have hresultBound : selector < result.size := by
    rw [show result.size = initial.size by
      exact foldl_selectorMaxDegrees_size (flatGates cs) initial]
    simpa [initial] using hallocated
  rw [selectorMaxDegrees, getElem!_pos result selector hresultBound]
  rw [getElem?_pos result selector hresultBound] at hfold
  exact Option.some.inj hfold

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
