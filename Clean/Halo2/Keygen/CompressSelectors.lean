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

/-- Two descriptions enabled on the same in-bounds row conflict. -/
theorem SelectorDescription.conflicts_eq_true_of_activated
    (left right : SelectorDescription) (row : ℕ)
    (hleftBound : row < left.activations.size)
    (hrightBound : row < right.activations.size)
    (hleft : left.activations[row] = true)
    (hright : right.activations[row] = true) :
    left.conflicts right = true := by
  rw [SelectorDescription.conflicts, List.any_eq_true]
  refine ⟨(true, true), ?_, by simp⟩
  rw [List.mem_iff_getElem]
  refine ⟨row, ?_, ?_⟩
  · simpa using And.intro hleftBound hrightBound
  · rw [List.getElem_zip, Array.getElem_toList, Array.getElem_toList,
      hleft, hright]

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

/-- The greedy inner loop preserves pairwise non-conflict of its chosen combination. -/
theorem extendCombination_pairwise_nonconflicting
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription)
    (hcomb : comb.Pairwise fun left right => left.conflicts right = false) :
    (extendCombination maxDegree d comb selectors).1.Pairwise
      fun left right => left.conflicts right = false := by
  induction selectors generalizing d comb with
  | nil => simpa [extendCombination] using hcomb
  | cons selector rest inductionHypothesis =>
      simp only [extendCombination]
      split
      · exact hcomb
      · split
        · exact inductionHypothesis d comb hcomb
        · split
          · exact inductionHypothesis d comb hcomb
          · apply inductionHypothesis
            rw [List.pairwise_append]
            refine ⟨hcomb, by simp, ?_⟩
            intro previous hprevious next hnext
            simp only [List.mem_singleton] at hnext
            subst next
            have hany : comb.any (·.conflicts selector) = false :=
              Bool.eq_false_of_not_eq_true ‹¬comb.any (·.conflicts selector) = true›
            exact Bool.eq_false_of_not_eq_true
              (List.any_eq_false.mp hany previous hprevious)

/-- Every combination returned by selector packing is pairwise non-conflicting. -/
theorem pairwise_nonconflicting_of_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors combination : List SelectorDescription)
    (hcombination :
      combination ∈ buildCombinations maxDegree fuel selectors) :
    combination.Pairwise fun left right => left.conflicts right = false := by
  induction fuel generalizing selectors with
  | zero => simp [buildCombinations] at hcombination
  | succ fuel inductionHypothesis =>
      cases selectors with
      | nil => simp [buildCombinations] at hcombination
      | cons selector rest =>
          simp only [buildCombinations, List.mem_cons] at hcombination
          rcases hcombination with hcurrent | hremaining
          · subst combination
            apply extendCombination_pairwise_nonconflicting
            simp
          · exact inductionHypothesis _ hremaining

/-- The greedy inner loop only redistributes descriptions from its two inputs. -/
theorem extendCombination_forall
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription)
    (predicate : SelectorDescription → Prop)
    (hcomb : comb.Forall predicate) (hselectors : selectors.Forall predicate) :
    (extendCombination maxDegree d comb selectors).1.Forall predicate ∧
      (extendCombination maxDegree d comb selectors).2.Forall predicate := by
  induction selectors generalizing d comb with
  | nil => simpa [extendCombination] using hcomb
  | cons selector rest inductionHypothesis =>
      rw [List.forall_cons] at hselectors
      simp only [extendCombination]
      split
      · exact ⟨hcomb,
          (List.forall_cons predicate selector rest).mpr hselectors⟩
      · split
        · obtain ⟨hchosen, hremaining⟩ :=
            inductionHypothesis d comb hcomb hselectors.2
          exact ⟨hchosen,
            (List.forall_cons predicate selector _).mpr
              ⟨hselectors.1, hremaining⟩⟩
        · split
          · obtain ⟨hchosen, hremaining⟩ :=
              inductionHypothesis d comb hcomb hselectors.2
            exact ⟨hchosen,
              (List.forall_cons predicate selector _).mpr
                ⟨hselectors.1, hremaining⟩⟩
          · apply inductionHypothesis
            · rw [List.forall_append]
              exact ⟨hcomb, by simp [hselectors.1]⟩
            · exact hselectors.2

/-- Every description in every packed combination comes from the source list. -/
theorem forall_of_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors combination : List SelectorDescription)
    (predicate : SelectorDescription → Prop)
    (hselectors : selectors.Forall predicate)
    (hcombination : combination ∈
      buildCombinations maxDegree fuel selectors) :
    combination.Forall predicate := by
  induction fuel generalizing selectors with
  | zero => simp [buildCombinations] at hcombination
  | succ fuel inductionHypothesis =>
      cases selectors with
      | nil => simp [buildCombinations] at hcombination
      | cons selector rest =>
          rw [List.forall_cons] at hselectors
          simp only [buildCombinations, List.mem_cons] at hcombination
          have hpartition := extendCombination_forall maxDegree
            (selector.maxDegree - 1) [selector] rest predicate
            (by simp [hselectors.1]) hselectors.2
          rcases hcombination with hcurrent | hremaining
          · subst combination
            exact hpartition.1
          · exact inductionHypothesis _ hpartition.2 hremaining

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

private theorem fst_eq_of_mem_zipIdx_of_snd_eq
    {alpha : Type} (items : List alpha) {left right : alpha × ℕ}
    (hleft : left ∈ items.zipIdx) (hright : right ∈ items.zipIdx)
    (hindex : left.2 = right.2) :
    left.1 = right.1 := by
  rcases left with ⟨left, index⟩
  rcases right with ⟨right, otherIndex⟩
  simp only at hindex
  subst otherIndex
  exact Option.some.inj <|
    (List.mk_mem_zipIdx_iff_getElem?.mp hleft).symm.trans
      (List.mk_mem_zipIdx_iff_getElem?.mp hright)

/-- Coactivated selector writes that `process` places in one packed column carry the
same assigned root. -/
theorem process_entry_roots_agree_of_activated
    (selectors : List SelectorDescription) (maxDegree n row : ℕ)
    (left right : ℕ × SelCompress)
    (hsizes : selectors.Forall fun description =>
      description.activations.size = n)
    (hactivated : ∀ description ∈ selectors,
      description.selector = left.1 ∨ description.selector = right.1 →
        description.activations[row]! = true)
    (hrow : row < n)
    (hleft : left ∈ (process selectors maxDegree).entries)
    (hright : right ∈ (process selectors maxDegree).entries)
    (hcolumn : left.2.packedCol = right.2.packedCol) :
    left.2.assignedRoot = right.2.assignedRoot := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change left ∈
      (degreeZero.zipIdx.map fun (description, column) =>
        (description.selector, SelCompress.mk column 1 1)) ++
      (combinations.zipIdx.flatMap fun (combination, column) =>
        combination.zipIdx.map fun (description, position) =>
          (description.selector,
            SelCompress.mk (degreeZero.length + column)
              combination.length (position + 1))) at hleft
  change right ∈
      (degreeZero.zipIdx.map fun (description, column) =>
        (description.selector, SelCompress.mk column 1 1)) ++
      (combinations.zipIdx.flatMap fun (combination, column) =>
        combination.zipIdx.map fun (description, position) =>
          (description.selector,
            SelCompress.mk (degreeZero.length + column)
              combination.length (position + 1))) at hright
  rw [List.mem_append] at hleft hright
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · obtain ⟨leftIndexed, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightIndexed, _, rfl⟩ := List.mem_map.mp hright
    rfl
  · obtain ⟨leftIndexed, hleftIndexed, rfl⟩ := List.mem_map.mp hleft
    rw [List.mem_flatMap] at hright
    obtain ⟨rightCombination, hrightCombination, hright⟩ := hright
    obtain ⟨rightIndexed, _, rfl⟩ := List.mem_map.mp hright
    rcases leftIndexed with ⟨leftDescription, leftColumn⟩
    rcases rightCombination with ⟨rightItems, rightColumn⟩
    rcases rightIndexed with ⟨rightDescription, rightPosition⟩
    have hleftColumn := List.snd_lt_of_mem_zipIdx hleftIndexed
    have hrightColumn := List.snd_lt_of_mem_zipIdx hrightCombination
    simp only at hcolumn
    exfalso
    omega
  · rw [List.mem_flatMap] at hleft
    obtain ⟨leftCombination, hleftCombination, hleft⟩ := hleft
    obtain ⟨leftIndexed, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightIndexed, hrightIndexed, rfl⟩ := List.mem_map.mp hright
    rcases leftCombination with ⟨leftItems, leftColumn⟩
    rcases leftIndexed with ⟨leftDescription, leftPosition⟩
    rcases rightIndexed with ⟨rightDescription, rightColumn⟩
    have hleftColumn := List.snd_lt_of_mem_zipIdx hleftCombination
    have hrightColumn := List.snd_lt_of_mem_zipIdx hrightIndexed
    simp only at hcolumn
    exfalso
    omega
  · rw [List.mem_flatMap] at hleft hright
    obtain ⟨leftCombination, hleftCombination, hleft⟩ := hleft
    obtain ⟨rightCombination, hrightCombination, hright⟩ := hright
    obtain ⟨leftIndexed, hleftIndexed, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightIndexed, hrightIndexed, rfl⟩ := List.mem_map.mp hright
    rcases leftCombination with ⟨leftItems, leftColumn⟩
    rcases rightCombination with ⟨rightItems, rightColumn⟩
    rcases leftIndexed with ⟨leftDescription, leftPosition⟩
    rcases rightIndexed with ⟨rightDescription, rightPosition⟩
    simp only at hcolumn
    have hcombinationColumn : leftColumn = rightColumn := by omega
    have hcombination : leftItems = rightItems :=
      fst_eq_of_mem_zipIdx_of_snd_eq combinations
        hleftCombination hrightCombination hcombinationColumn
    subst rightItems
    subst rightColumn
    by_cases hposition : leftPosition = rightPosition
    · change leftPosition + 1 = rightPosition + 1
      omega
    · exfalso
      have hleftMember : leftDescription ∈ leftItems :=
        List.fst_mem_of_mem_zipIdx hleftIndexed
      have hrightMember : rightDescription ∈ leftItems :=
        List.fst_mem_of_mem_zipIdx hrightIndexed
      have hcombinationMember : leftItems ∈ combinations :=
        List.fst_mem_of_mem_zipIdx hleftCombination
      have hremainingSizes : remaining.Forall fun description =>
          description.activations.size = n := by
        rw [List.forall_iff_forall_mem]
        intro description hdescription
        exact List.forall_iff_forall_mem.mp hsizes description
          (List.mem_filter.mp hdescription).1
      have hitemSizes := forall_of_mem_buildCombinations
        maxDegree remaining.length remaining leftItems
        (fun description => description.activations.size = n)
        hremainingSizes hcombinationMember
      have hleftSize := List.forall_iff_forall_mem.mp hitemSizes
        leftDescription hleftMember
      have hrightSize := List.forall_iff_forall_mem.mp hitemSizes
        rightDescription hrightMember
      have hleftSource : leftDescription ∈ selectors :=
        List.forall_iff_forall_mem.mp
          (forall_of_mem_buildCombinations maxDegree remaining.length
            remaining leftItems (fun description => description ∈ selectors)
            (by
              rw [List.forall_iff_forall_mem]
              intro description hdescription
              exact (List.mem_filter.mp hdescription).1)
            hcombinationMember) leftDescription hleftMember
      have hrightSource : rightDescription ∈ selectors :=
        List.forall_iff_forall_mem.mp
          (forall_of_mem_buildCombinations maxDegree remaining.length
            remaining leftItems (fun description => description ∈ selectors)
            (by
              rw [List.forall_iff_forall_mem]
              intro description hdescription
              exact (List.mem_filter.mp hdescription).1)
            hcombinationMember) rightDescription hrightMember
      have hleftActive : leftDescription.activations[row]! = true :=
        hactivated leftDescription hleftSource (Or.inl rfl)
      have hrightActive : rightDescription.activations[row]! = true :=
        hactivated rightDescription hrightSource (Or.inr rfl)
      have hleftBound : row < leftDescription.activations.size := by
        omega
      have hrightBound : row < rightDescription.activations.size := by
        omega
      have hleftActive' : leftDescription.activations[row] = true := by
        rw [← getElem!_pos leftDescription.activations row hleftBound]
        exact hleftActive
      have hrightActive' : rightDescription.activations[row] = true := by
        rw [← getElem!_pos rightDescription.activations row hrightBound]
        exact hrightActive
      have hconflictForward :=
        SelectorDescription.conflicts_eq_true_of_activated
          leftDescription rightDescription row hleftBound hrightBound
          hleftActive' hrightActive'
      have hconflictBackward :=
        SelectorDescription.conflicts_eq_true_of_activated
          rightDescription leftDescription row hrightBound hleftBound
          hrightActive' hleftActive'
      have hpairwise := pairwise_nonconflicting_of_mem_buildCombinations
        maxDegree remaining.length remaining leftItems hcombinationMember
      rw [List.pairwise_iff_getElem] at hpairwise
      have hleftPosition : leftPosition < leftItems.length :=
        List.snd_lt_of_mem_zipIdx hleftIndexed
      have hrightPosition : rightPosition < leftItems.length :=
        List.snd_lt_of_mem_zipIdx hrightIndexed
      by_cases horder : leftPosition < rightPosition
      · have hnonconflict := hpairwise leftPosition rightPosition
            hleftPosition hrightPosition horder
        have hleftEq := List.fst_eq_of_mem_zipIdx hleftIndexed
        have hrightEq := List.fst_eq_of_mem_zipIdx hrightIndexed
        simp only [Nat.sub_zero] at hleftEq hrightEq
        rw [← hleftEq, ← hrightEq, hconflictForward] at hnonconflict
        simp at hnonconflict
      · have horder' : rightPosition < leftPosition := by omega
        have hnonconflict := hpairwise rightPosition leftPosition
            hrightPosition hleftPosition horder'
        have hleftEq := List.fst_eq_of_mem_zipIdx hleftIndexed
        have hrightEq := List.fst_eq_of_mem_zipIdx hrightIndexed
        simp only [Nat.sub_zero] at hleftEq hrightEq
        rw [← hrightEq, ← hleftEq, hconflictBackward] at hnonconflict
        simp at hnonconflict

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

/-- A successful lookup identifies the corresponding keyed association-list entry. -/
theorem SelCompressMap.mem_entries_of_lookup
    (map : SelCompressMap) {selector : ℕ} {compressed : SelCompress}
    (hlookup : map.lookup selector = some compressed) :
    (selector, compressed) ∈ map.entries := by
  simp only [SelCompressMap.lookup, Option.map_eq_some_iff] at hlookup
  obtain ⟨entry, hfind, hcompressed⟩ := hlookup
  have hkey : entry.1 = selector := by
    have hpredicate : decide (entry.1 = selector) = true := by
      exact List.find?_some
        (p := fun candidate : ℕ × SelCompress => candidate.1 = selector) hfind
    exact of_decide_eq_true hpredicate
  rw [← hkey, ← hcompressed]
  exact List.mem_of_find?_eq_some hfind

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

private def ActivationRowsSized (n : ℕ) (table : Array (Array Bool)) : Prop :=
  ∀ selector (hselector : selector < table.size), table[selector].size = n

private theorem activationRowsSized_initial (n numSelectors : ℕ) :
    ActivationRowsSized n
      ((List.replicate numSelectors
        ((List.replicate n false).toArray)).toArray) := by
  intro selector hselector
  simp

private theorem activationRowsSized_modify
    (n : ℕ) (table : Array (Array Bool)) (selector row : ℕ)
    (hsized : ActivationRowsSized n table) :
    ActivationRowsSized n (table.modify selector (·.set! row true)) := by
  intro target htarget
  have htarget' : target < table.size := by simpa using htarget
  rw [Array.getElem_modify]
  split
  · simp [Array.set!, hsized target htarget']
  · exact hsized target htarget'

private theorem activationRowsSized_foldl
    (n : ℕ) (table : Array (Array Bool)) (acts : List (ℕ × ℕ))
    (hsized : ActivationRowsSized n table) :
    ActivationRowsSized n
      (acts.foldl
        (fun current activation =>
          current.modify activation.1 (·.set! activation.2 true))
        table) := by
  induction acts generalizing table with
  | nil => exact hsized
  | cons activation rest inductionHypothesis =>
      rw [List.foldl_cons]
      exact inductionHypothesis _
        (activationRowsSized_modify n table
          activation.1 activation.2 hsized)

private theorem activationTable_foldl_size
    (table : Array (Array Bool)) (acts : List (ℕ × ℕ)) :
    (acts.foldl
      (fun current activation =>
        current.modify activation.1 (·.set! activation.2 true))
      table).size = table.size := by
  induction acts generalizing table with
  | nil => rfl
  | cons activation rest inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      simp

private theorem activationTable_cell_preserved
    (table : Array (Array Bool)) (selector row : ℕ)
    (hselector : selector < table.size)
    (hrow : row < table[selector]!.size)
    (hvalue : table[selector]![row]! = true)
    (updatedSelector updatedRow : ℕ) :
    (table.modify updatedSelector (·.set! updatedRow true))[selector]![row]! =
      true := by
  rw [getElem!_pos table selector hselector] at hrow hvalue
  rw [getElem!_pos table[selector] row hrow] at hvalue
  let updated := table.modify updatedSelector (·.set! updatedRow true)
  have hselectorUpdated : selector < updated.size := by
    simpa [updated] using hselector
  change updated[selector]![row]! = true
  rw [getElem!_pos updated selector hselectorUpdated]
  simp only [updated, Array.getElem_modify]
  split
  · rw [getElem!_pos _ _ (by simp [Array.set!, hrow])]
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds (by simpa using hrow)]
    split
    · rfl
    · exact hvalue
  · rw [getElem!_pos table[selector] row hrow]
    exact hvalue

private theorem activationTable_cell_preserved_foldl
    (table : Array (Array Bool)) (selector row : ℕ)
    (hselector : selector < table.size)
    (hrow : row < table[selector]!.size)
    (hvalue : table[selector]![row]! = true)
    (acts : List (ℕ × ℕ)) :
    (acts.foldl
      (fun current activation =>
        current.modify activation.1 (·.set! activation.2 true))
      table)[selector]![row]! = true := by
  induction acts generalizing table with
  | nil => exact hvalue
  | cons activation rest inductionHypothesis =>
      rw [List.foldl_cons]
      let updated := table.modify activation.1 (·.set! activation.2 true)
      have hupdatedSelector : selector < updated.size := by
        simpa [updated] using hselector
      have hupdatedRow : row < updated[selector]!.size := by
        have hrow' : row < table[selector].size := by
          rw [← getElem!_pos table selector hselector]
          exact hrow
        rw [getElem!_pos updated selector hupdatedSelector]
        simp only [updated, Array.getElem_modify]
        split
        · simpa [Array.set!] using hrow'
        · exact hrow'
      exact inductionHypothesis updated hupdatedSelector hupdatedRow
        (activationTable_cell_preserved table selector row
          hselector hrow hvalue activation.1 activation.2)

private theorem activationTable_cell_true_of_mem_foldl
    (n : ℕ) (table : Array (Array Bool)) (acts : List (ℕ × ℕ))
    (hsized : ActivationRowsSized n table)
    (selector row : ℕ)
    (hactivation : (selector, row) ∈ acts)
    (hselector : selector < table.size) (hrow : row < n) :
    (acts.foldl
      (fun current activation =>
        current.modify activation.1 (·.set! activation.2 true))
      table)[selector]![row]! = true := by
  induction acts generalizing table with
  | nil => simp at hactivation
  | cons activation rest inductionHypothesis =>
      rw [List.foldl_cons]
      simp only [List.mem_cons] at hactivation
      let updated := table.modify activation.1 (·.set! activation.2 true)
      have hsizedUpdated : ActivationRowsSized n updated :=
        activationRowsSized_modify n table activation.1 activation.2 hsized
      have hselectorUpdated : selector < updated.size := by
        simpa [updated] using hselector
      rcases hactivation with hcurrent | hremaining
      · rcases activation with ⟨currentSelector, currentRow⟩
        injection hcurrent with hselectorEq hrowEq
        subst currentSelector
        subst currentRow
        apply activationTable_cell_preserved_foldl
        · exact hselectorUpdated
        · rw [getElem!_pos updated selector hselectorUpdated,
            hsizedUpdated selector hselectorUpdated]
          exact hrow
        · change updated[selector]![row]! = true
          rw [getElem!_pos updated selector hselectorUpdated,
            Array.getElem_modify, if_pos rfl]
          have hsourceRow : row < table[selector].size := by
            rw [hsized selector hselector]
            exact hrow
          rw [getElem!_pos _ _ (by simp [Array.set!, hsourceRow])]
          simp only [Array.set!]
          rw [Array.getElem_setIfInBounds hsourceRow]
          simp
      · exact inductionHypothesis updated hsizedUpdated
          hremaining hselectorUpdated

/-- Every in-bounds activation is recorded in the derived activation table. -/
theorem activationTable_getElem_eq_true_of_mem
    (n numSelectors : ℕ) (acts : List (ℕ × ℕ))
    (selector row : ℕ)
    (hactivation : (selector, row) ∈ acts)
    (hselector : selector < numSelectors) (hrow : row < n) :
    (activationTable n numSelectors acts)[selector]![row]! = true := by
  unfold activationTable
  apply activationTable_cell_true_of_mem_foldl n _ acts
    (activationRowsSized_initial n numSelectors) selector row hactivation
  · simpa using hselector
  · exact hrow

/-- Every row in an activation table has the configured domain length. -/
theorem activationTable_getElem_size
    (n numSelectors : ℕ) (acts : List (ℕ × ℕ))
    (selector : ℕ) (hselector : selector < numSelectors) :
    (activationTable n numSelectors acts)[selector]!.size = n := by
  have hsized := activationRowsSized_foldl n
    ((List.replicate numSelectors
      ((List.replicate n false).toArray)).toArray)
    acts (activationRowsSized_initial n numSelectors)
  have htableSize : (activationTable n numSelectors acts).size =
      numSelectors := by
    unfold activationTable
    rw [activationTable_foldl_size]
    simp
  have hbound : selector < (activationTable n numSelectors acts).size := by
    omega
  have hsized' : ActivationRowsSized n
      (activationTable n numSelectors acts) := by
    simpa only [activationTable] using hsized
  rw [getElem!_pos (activationTable n numSelectors acts) selector hbound]
  exact hsized' selector hbound

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

/-- Coactivated entries in a circuit-derived selector map agree whenever compression
places them in the same packed fixed column. -/
theorem deriveSelCompressMap_lookup_roots_agree_of_activated
    (cs : ConstraintSystem F) (n : ℕ) (acts : List (ℕ × ℕ))
    {leftSelector rightSelector row : ℕ}
    {left right : SelCompress}
    (hrow : row < n)
    (hleftActivation : (leftSelector, row) ∈ acts)
    (hrightActivation : (rightSelector, row) ∈ acts)
    (hleftLookup : (deriveSelCompressMap cs n acts).lookup leftSelector =
      some left)
    (hrightLookup : (deriveSelCompressMap cs n acts).lookup rightSelector =
      some right)
    (hcolumn : left.packedCol = right.packedCol) :
    left.assignedRoot = right.assignedRoot := by
  let table := activationTable n cs.numSelectors acts
  let degrees := selectorMaxDegrees cs
  let descriptions := (List.range cs.numSelectors).map fun index =>
    SelectorDescription.mk index table[index]! degrees[index]!
  let packing := process descriptions (csDegree cs)
  have hleftEntry := SelCompressMap.mem_entries_of_lookup
    (deriveSelCompressMap cs n acts) hleftLookup
  have hrightEntry := SelCompressMap.mem_entries_of_lookup
    (deriveSelCompressMap cs n acts) hrightLookup
  change (leftSelector, left) ∈
    packing.entries.map (fun (sourceSelector, source) =>
      (sourceSelector,
        { source with
          packedCol := source.packedCol + cs.numFixedColumns })) at hleftEntry
  change (rightSelector, right) ∈
    packing.entries.map (fun (sourceSelector, source) =>
      (sourceSelector,
        { source with
          packedCol := source.packedCol + cs.numFixedColumns })) at hrightEntry
  obtain ⟨⟨leftSourceSelector, leftSource⟩,
    hleftSource, hleftEq⟩ := List.mem_map.mp hleftEntry
  obtain ⟨⟨rightSourceSelector, rightSource⟩,
    hrightSource, hrightEq⟩ := List.mem_map.mp hrightEntry
  have hleftKey : leftSourceSelector = leftSelector :=
    congrArg Prod.fst hleftEq
  have hrightKey : rightSourceSelector = rightSelector :=
    congrArg Prod.fst hrightEq
  have hleftPacked : leftSource.packedCol + cs.numFixedColumns =
      left.packedCol := congrArg (fun entry => entry.2.packedCol) hleftEq
  have hrightPacked : rightSource.packedCol + cs.numFixedColumns =
      right.packedCol := congrArg (fun entry => entry.2.packedCol) hrightEq
  have hsourceColumn : leftSource.packedCol = rightSource.packedCol := by
    omega
  have hsizes : descriptions.Forall fun description =>
      description.activations.size = n := by
    rw [List.forall_iff_forall_mem]
    intro description hdescription
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hdescription
    apply activationTable_getElem_size
    exact List.mem_range.mp hindex
  have hactivated : ∀ description ∈ descriptions,
      description.selector = leftSourceSelector ∨
          description.selector = rightSourceSelector →
        description.activations[row]! = true := by
    intro description hdescription hselector
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hdescription
    have hindexBound := List.mem_range.mp hindex
    rcases hselector with hselector | hselector
    · have hindex : index = leftSelector := hselector.trans hleftKey
      subst index
      apply activationTable_getElem_eq_true_of_mem
        n cs.numSelectors acts leftSelector row
      · exact hleftActivation
      · exact hindexBound
      · exact hrow
    · have hindex : index = rightSelector := hselector.trans hrightKey
      subst index
      apply activationTable_getElem_eq_true_of_mem
        n cs.numSelectors acts rightSelector row
      · exact hrightActivation
      · exact hindexBound
      · exact hrow
  have hroots := process_entry_roots_agree_of_activated
    descriptions (csDegree cs) n row
    (leftSourceSelector, leftSource)
    (rightSourceSelector, rightSource)
    hsizes hactivated hrow hleftSource hrightSource hsourceColumn
  have hleftRoot : leftSource.assignedRoot = left.assignedRoot :=
    congrArg (fun entry => entry.2.assignedRoot) hleftEq
  have hrightRoot : rightSource.assignedRoot = right.assignedRoot :=
    congrArg (fun entry => entry.2.assignedRoot) hrightEq
  exact hleftRoot.symm.trans (hroots.trans hrightRoot)

end Halo2
