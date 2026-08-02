import Clean.Halo2.Keygen.PinnedCs

/-!
# The VK-match projection preserves evaluation

`projectCS` (`Clean.Halo2.Keygen.Projection`) performs selector compression
(`substSelectorMap`) then the query-index walk that erases `Expression F Query` into the
verifier's gate AST `RichExpression F`. This module supplies the *semantic* half a
soundness bridge needs:

* `substSelectorMap_eval` — compression is evaluation under a rewritten valuation: each
  selector reads its root-finding replacement instead (`substValuation`).
* `selReplacement_eval` and its corollaries — the replacement's value at a row is
  decided by the packed column: `0` where no member is active (`_of_zero`) or where
  another member's root is written (`_of_other`), nonzero at the selector's own root
  (`_of_root`).
* `substSelectorMap_selectorFree` — compression leaves
  exactly the uncovered selector atoms (`selectorsCovered`), so for a covering map the
  erasure's residual selector arm is unreachable.
* `eraseExpr_eval` — the query-walk erasure of a selector-free expression evaluates to
  the original, when the evaluation families interpret the walk's final query layout
  (`Interprets`).
* `eraseGates_eval` / `derive_gates_eval` — the gate-list and derived-record forms.
-/

namespace Halo2

variable {F : Type} [Field F]

/-! ## Syntactic selector bounds imply coverage -/

omit [Field F] in
/--
If an expression's one-past-largest selector index is at most `bound`, every selector
atom in the expression satisfies the corresponding strict index bound.
-/
theorem Expression.selectorsCovered_lt_of_selectorBound_le
    (expression : Expression F Query) (bound : ℕ)
    (hbound : expression.selectorBound ≤ bound) :
    expression.selectorsCovered
        (fun selector => decide (selector < bound)) = true := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          simp only [Expression.selectorBound] at hbound
          simp only [Expression.selectorsCovered, decide_eq_true_eq]
          omega
      | fixed _ _ | advice _ _ | «instance» _ _ =>
          rfl
  | const _ =>
      rfl
  | add left right ihLeft ihRight
  | mul left right ihLeft ihRight =>
      simp only [Expression.selectorBound] at hbound
      have hleft : left.selectorBound ≤ bound :=
        le_trans (le_max_left _ _) hbound
      have hright : right.selectorBound ≤ bound :=
        le_trans (le_max_right _ _) hbound
      simp only [Expression.selectorsCovered, Bool.and_eq_true]
      exact ⟨ihLeft hleft, ihRight hright⟩

/-! ## Selector compression is evaluation under a rewritten valuation -/

/-- The valuation `substSelectorMap` simulates: selectors in the map read their
root-finding replacement, everything else reads `v`. -/
def substValuation (m : ℕ → Option SelCompress) (v : Query → F) : Query → F
  | .selector s => match m s.index with
      | some d => (selReplacement d).eval v
      | none => v (.selector s)
  | q => v q

/-- Selector compression preserves evaluation: the substituted expression at `v` is the
original at `substValuation m v`. -/
theorem substSelectorMap_eval (m : ℕ → Option SelCompress) (v : Query → F)
    (e : Expression F Query) :
    (substSelectorMap m e).eval v = e.eval (substValuation m v) := by
  induction e with
  | var q =>
      cases q with
      | selector s =>
          cases hm : m s.index with
          | some d => simp only [substSelectorMap, substValuation, hm, Expression.eval]
          | none => simp only [substSelectorMap, substValuation, hm, Expression.eval]
      | fixed c r => rfl
      | advice c r => rfl
      | «instance» c r => rfl
  | const c => rfl
  | add a b iha ihb => simp only [substSelectorMap, Expression.eval, iha, ihb]
  | mul a b iha ihb => simp only [substSelectorMap, Expression.eval, iha, ihb]

/-! ## The root-finding replacement's value -/

/-- Closed form of the replacement's value: the packed query's value times the product of
`(i − q)` over the other members' roots. -/
theorem selReplacement_eval (d : SelCompress) (v : Query → F) :
    (selReplacement d).eval v
      = v (.fixed ⟨d.packedCol⟩ 0) *
        (((List.range d.combinationLen).filterMap (fun j =>
            if j + 1 = d.assignedRoot then none
            else some (((j + 1 : ℕ) : F) - v (.fixed ⟨d.packedCol⟩ 0)))).prod) := by
  have hfold : ∀ (fs : List (Expression F Query)) (acc : Expression F Query),
      (fs.foldl (· * ·) acc).eval v = acc.eval v * (fs.map (Expression.eval v)).prod := by
    intro fs
    induction fs with
    | nil => intro acc; simp
    | cons f fs ih =>
        intro acc
        rw [List.foldl_cons, ih (acc * f), List.map_cons, List.prod_cons,
          show ((acc * f).eval v) = acc.eval v * f.eval v from rfl]
        ring
  unfold selReplacement
  rw [hfold]
  congr 1
  rw [List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun j _ => ?_
  by_cases hcase : j + 1 = d.assignedRoot
  · simp [hcase]
  · simp only [hcase, ite_false, Option.map_some]
    congr 1
    show (_ : Expression F Query).eval v = _
    simp only [Expression.eval, sub_eq_add_neg]
    ring

/-- Where no member of the combination is active the packed cell is `0`, and the
replacement vanishes. -/
theorem selReplacement_eval_of_zero (d : SelCompress) (v : Query → F)
    (hq : v (.fixed ⟨d.packedCol⟩ 0) = 0) : (selReplacement d).eval v = 0 := by
  rw [selReplacement_eval, hq, zero_mul]

/-- Where another member (root `i₀ ≠ assignedRoot`, `1 ≤ i₀ ≤ len`) is active, its factor
`(i₀ − q)` kills the replacement. -/
theorem selReplacement_eval_of_other (d : SelCompress) (v : Query → F)
    (i₀ : ℕ) (hq : v (.fixed ⟨d.packedCol⟩ 0) = (i₀ : F))
    (h1 : 1 ≤ i₀) (hlen : i₀ ≤ d.combinationLen) (hne : i₀ ≠ d.assignedRoot) :
    (selReplacement d).eval v = 0 := by
  rw [selReplacement_eval, hq]
  refine mul_eq_zero_of_right _ (List.prod_eq_zero ?_)
  rw [List.mem_filterMap]
  refine ⟨i₀ - 1, by rw [List.mem_range]; omega, ?_⟩
  have h : i₀ - 1 + 1 = i₀ := by omega
  rw [h, if_neg hne, sub_self]

/-- At the selector's own enabled rows the packed cell holds `assignedRoot`, and the
replacement is nonzero: the root itself is nonzero (`1 ≤ root`), and every other member's
factor `(i − root)` is a difference of distinct naturals. The `hcast` hypothesis captures
that small naturals inject into `F` (over a prime field, distinct roots below the
characteristic are distinct); this replaces the pasta-specific cardinality bound the
original carried, keeping the lemma field-generic. -/
theorem selReplacement_eval_of_root (d : SelCompress) (v : Query → F)
    (hq : v (.fixed ⟨d.packedCol⟩ 0) = (d.assignedRoot : F))
    (h1 : 1 ≤ d.assignedRoot) (hlen : d.assignedRoot ≤ d.combinationLen)
    (hcast : ∀ i j : ℕ, i ≤ d.combinationLen → j ≤ d.combinationLen →
      (i : F) = (j : F) → i = j) :
    (selReplacement d).eval v ≠ 0 := by
  rw [selReplacement_eval, hq]
  refine mul_ne_zero ?_ ?_
  · intro h0
    have : d.assignedRoot = 0 := hcast _ 0 hlen (by omega) (by simpa using h0)
    omega
  · intro h0
    obtain ⟨x, hx, hx0⟩ := List.mem_filterMap.mp (List.prod_eq_zero_iff.mp h0)
    rw [List.mem_range] at hx
    by_cases hroot : x + 1 = d.assignedRoot
    · simp [hroot] at hx0
    · rw [if_neg hroot, Option.some_inj] at hx0
      rw [sub_eq_zero] at hx0
      exact hroot (hcast _ _ (by omega) hlen hx0)

/-! ## Selector-freeness -/

set_option linter.unusedSectionVars false in
private theorem selectorFree_foldl_mul (fs : List (Expression F Query))
    (acc : Expression F Query) (hacc : acc.SelectorFree)
    (hfs : ∀ f ∈ fs, f.SelectorFree) :
    (fs.foldl (· * ·) acc).SelectorFree := by
  induction fs generalizing acc with
  | nil => exact hacc
  | cons f fs ih =>
      rw [List.foldl_cons]
      refine ih (acc * f) ?_ (fun g hg => hfs g (List.mem_cons_of_mem f hg))
      show (Expression.mul acc f).SelectorFree
      simp [Expression.SelectorFree, hacc, hfs f (List.mem_cons_self ..)]

/-- The root-finding replacement's atoms are a fixed query and constants. -/
theorem selReplacement_selectorFree (d : SelCompress) :
    (selReplacement (F := F) d).SelectorFree := by
  unfold selReplacement
  refine selectorFree_foldl_mul _ _ trivial ?_
  intro f hf
  rw [List.mem_filterMap] at hf
  obtain ⟨j, _, hj⟩ := hf
  by_cases hcase : j + 1 = d.assignedRoot
  · simp [hcase] at hj
  · rw [if_neg hcase, Option.some_inj] at hj
    subst hj
    simp [Expression.SelectorFree]

/-- Compression leaves exactly the uncovered selector atoms: the substituted expression
is selector-free iff the map covers every selector occurrence. -/
theorem substSelectorMap_selectorFree (m : ℕ → Option SelCompress)
    (e : Expression F Query) :
    (substSelectorMap m e).SelectorFree ↔
      e.selectorsCovered (fun i => (m i).isSome) = true := by
  induction e with
  | var q =>
      cases q with
      | selector sel =>
          cases hs : m sel.index with
          | some d =>
              simp [substSelectorMap, hs, Expression.selectorsCovered,
                selReplacement_selectorFree d]
          | none => simp [substSelectorMap, hs, Expression.selectorsCovered,
              Expression.SelectorFree]
      | fixed c r =>
          simp [substSelectorMap, Expression.SelectorFree,
            Expression.selectorsCovered]
      | advice c r =>
          simp [substSelectorMap, Expression.SelectorFree,
            Expression.selectorsCovered]
      | «instance» c r =>
          simp [substSelectorMap, Expression.SelectorFree,
            Expression.selectorsCovered]
  | const c =>
      simp [substSelectorMap, Expression.SelectorFree,
        Expression.selectorsCovered]
  | add a b iha ihb =>
      simp [substSelectorMap, Expression.SelectorFree,
        Expression.selectorsCovered, iha, ihb, Bool.and_eq_true]
  | mul a b iha ihb =>
      simp [substSelectorMap, Expression.SelectorFree,
        Expression.selectorsCovered, iha, ihb, Bool.and_eq_true]

/-! ## Query resolution preserves evaluation

`eraseExpr` resolves ordinary queries against a fixed `QueryState`. `Interprets` says the
evaluation families read that layout correctly; `QueriesResolved` rules out the
diagnostic out-of-range fallback used for malformed inputs. -/

/-- A query has an authoritative slot in a projection layout. Selectors use their own
pre-compression representation and need no ordinary-query slot. -/
def QueryState.ResolvesQuery (s : QueryState) : Query → Prop
  | .selector _ => True
  | .advice column rotation => (column.index, rotation) ∈ s.advice
  | .fixed column rotation => (column.index, rotation) ∈ s.fixed
  | .instance column rotation => (column.index, rotation) ∈ s.inst

/-- Every ordinary query in an expression resolves against the supplied layout. -/
def Expression.QueriesResolved
    (s : QueryState) : Expression F Query → Prop
  | .var query => s.ResolvesQuery query
  | .const _ => True
  | .add left right =>
      left.QueriesResolved s ∧ right.QueriesResolved s
  | .mul left right =>
      left.QueriesResolved s ∧ right.QueriesResolved s

omit [Field F] in
private theorem queriesResolved_foldl_mul
    (queries : QueryState) (factors : List (Expression F Query))
    (accumulator : Expression F Query)
    (haccumulator : accumulator.QueriesResolved queries)
    (hfactors : ∀ factor ∈ factors, factor.QueriesResolved queries) :
    (factors.foldl (· * ·) accumulator).QueriesResolved queries := by
  induction factors generalizing accumulator with
  | nil => exact haccumulator
  | cons factor factors ih =>
      rw [List.foldl_cons]
      exact ih _ ⟨haccumulator, hfactors factor (by simp)⟩
        (fun next hnext => hfactors next (by simp [hnext]))

/-- A selector replacement resolves as soon as its packed fixed query does. -/
theorem selReplacement_queriesResolved (description : SelCompress)
    (queries : QueryState)
    (hpacked : queries.ResolvesQuery (.fixed ⟨description.packedCol⟩ 0)) :
    (selReplacement (F := F) description).QueriesResolved queries := by
  unfold selReplacement
  apply queriesResolved_foldl_mul queries
  · exact hpacked
  · intro factor hfactor
    rw [List.mem_filterMap] at hfactor
    obtain ⟨index, _, hresult⟩ := hfactor
    by_cases hroot : index + 1 = description.assignedRoot
    · simp [hroot] at hresult
    · rw [if_neg hroot, Option.some_inj] at hresult
      subst factor
      simpa [Expression.QueriesResolved] using hpacked

/-- Selector substitution preserves resolution when every replacement's packed query
has been registered by selector compression. -/
theorem substSelectorMap_queriesResolved
    (map : ℕ → Option SelCompress) (queries : QueryState)
    (expression : Expression F Query)
    (hsource : expression.QueriesResolved queries)
    (hpacked : ∀ selector description,
      map selector = some description →
        queries.ResolvesQuery (.fixed ⟨description.packedCol⟩ 0)) :
    (substSelectorMap map expression).QueriesResolved queries := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          simp only [substSelectorMap]
          split
          · rename_i description hdescription
            exact selReplacement_queriesResolved description queries
              (hpacked selector.index description hdescription)
          · trivial
      | advice | fixed | «instance» => exact hsource
  | const => trivial
  | add left right ihLeft ihRight
  | mul left right ihLeft ihRight =>
      exact ⟨ihLeft hsource.1, ihRight hsource.2⟩

omit [Field F] in
theorem ConfigureDelta.RegistersQuery.resolves_recordedQueries_apply
    {delta : ConfigureDelta F} {counts : ConfigureCounts}
    {initial : ConstraintSystem F} {query : Query}
    (hquery : delta.RegistersQuery query) :
    (recordedQueries (delta.apply initial counts)).ResolvesQuery query := by
  cases query with
  | selector => trivial
  | advice column rotation =>
      simp only [QueryState.ResolvesQuery, recordedQueries,
        ConfigureDelta.apply, List.mem_toArray, List.mem_map]
      exact ⟨(column, rotation),
        (mem_appendFirstEncounters _ _ _).2 (Or.inr hquery), rfl⟩
  | fixed column rotation =>
      simp only [QueryState.ResolvesQuery, recordedQueries,
        ConfigureDelta.apply, List.mem_toArray, List.mem_map]
      exact ⟨(column, rotation),
        (mem_appendFirstEncounters _ _ _).2 (Or.inr hquery), rfl⟩
  | «instance» column rotation =>
      simp only [QueryState.ResolvesQuery, recordedQueries,
        ConfigureDelta.apply, List.mem_toArray, List.mem_map]
      exact ⟨(column, rotation),
        (mem_appendFirstEncounters _ _ _).2 (Or.inr hquery), rfl⟩

omit [Field F] in
theorem QueryState.ResolvesQuery.registerFixed
    {queries : QueryState} {query : Query} (column : ℕ)
    (hquery : queries.ResolvesQuery query) :
    (queries.registerFixed column).ResolvesQuery query := by
  cases query with
  | selector => trivial
  | advice | «instance» =>
      unfold QueryState.registerFixed
      split <;> exact hquery
  | fixed queryColumn rotation =>
      unfold QueryState.registerFixed
      split
      · exact hquery
      · exact Array.mem_push_of_mem (column, 0) hquery

omit [Field F] in
theorem QueryState.ResolvesQuery.of_recorded_queryWalkInit
    {cs : ConstraintSystem F} {map : SelCompressMap} {query : Query}
    (hquery : (recordedQueries cs).ResolvesQuery query) :
    (queryWalkInit map cs).ResolvesQuery query := by
  unfold Halo2.queryWalkInit
  have aux (indices : List ℕ) (state : QueryState)
      (hquery : state.ResolvesQuery query) :
      (indices.foldl (fun current index =>
        current.registerFixed (cs.numFixedColumns + index)) state).ResolvesQuery
          query := by
    induction indices generalizing state with
    | nil => exact hquery
    | cons index indices ih =>
        rw [List.foldl_cons]
        exact ih _ (hquery.registerFixed (cs.numFixedColumns + index))
  exact aux _ _ hquery

omit [Field F] in
theorem recordedQueries_resolves_fixed_of_mem
    {cs : ConstraintSystem F} {column : Column .fixed} {rotation : Rotation}
    (hquery : (column, rotation) ∈ cs.fixedQueries) :
    (recordedQueries cs).ResolvesQuery (.fixed column rotation) := by
  simp only [QueryState.ResolvesQuery, recordedQueries,
    List.mem_toArray, List.mem_map]
  exact ⟨(column, rotation), hquery, rfl⟩

omit [Field F] in
/-- Every fixed query recorded by configure remains in the selector-compressed query
layout. -/
theorem queryWalkInit_resolves_fixed_of_mem
    {cs : ConstraintSystem F} (map : SelCompressMap)
    {column : Column .fixed} {rotation : Rotation}
    (hquery : (column, rotation) ∈ cs.fixedQueries) :
    (queryWalkInit map cs).ResolvesQuery (.fixed column rotation) :=
  QueryState.ResolvesQuery.of_recorded_queryWalkInit
    (recordedQueries_resolves_fixed_of_mem hquery)

omit [Field F] in
private theorem QueryState.registerFixed_fixed_forall
    (queries : QueryState) (bound column : ℕ)
    (hqueries : queries.fixed.toList.Forall fun query => query.1 < bound)
    (hcolumn : column < bound) :
    (queries.registerFixed column).fixed.toList.Forall fun query =>
      query.1 < bound := by
  unfold QueryState.registerFixed
  split
  · exact hqueries
  · simpa using And.intro hqueries hcolumn

omit [Field F] in
/-- The query projection contains only configure-recorded fixed columns and the packed
selector suffix. -/
theorem queryWalkInit_fixedQueries_bounded
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (hrecorded : cs.fixedQueries.Forall fun query =>
      query.1.index < cs.numFixedColumns) :
    (queryWalkInit map cs).fixed.toList.Forall fun query =>
      query.1 < cs.numFixedColumns + map.newFixedCols := by
  unfold queryWalkInit
  have hinitial : (recordedQueries cs).fixed.toList.Forall fun query =>
      query.1 < cs.numFixedColumns + map.newFixedCols := by
    have hlist : (recordedQueries cs).fixed.toList =
        cs.fixedQueries.map fun query => (query.1.index, query.2) := by
      simp [recordedQueries]
    rw [hlist, List.forall_map_iff]
    exact hrecorded.imp fun query hquery =>
      hquery.trans_le (Nat.le_add_right _ _)
  have aux (indices : List ℕ) (state : QueryState)
      (hindices : indices.Forall (· < map.newFixedCols))
      (hstate : state.fixed.toList.Forall fun query =>
        query.1 < cs.numFixedColumns + map.newFixedCols) :
      (indices.foldl (fun current index =>
        current.registerFixed (cs.numFixedColumns + index)) state).fixed.toList.Forall
          fun query => query.1 < cs.numFixedColumns + map.newFixedCols := by
    induction indices generalizing state with
    | nil => exact hstate
    | cons index indices ih =>
        rw [List.foldl_cons, List.forall_cons] at *
        apply ih _ hindices.2
        exact state.registerFixed_fixed_forall _ _ hstate
          (Nat.add_lt_add_left hindices.1 _)
  apply aux _ _ (List.forall_iff_forall_mem.mpr fun index hindex => ?_) hinitial
  exact List.mem_range.mp hindex

omit [Field F] in
/-- Configure-time semantic registration gives read-only projection resolution. -/
theorem Expression.QueriesRegistered.queriesResolved_queryWalkInit_apply
    {delta : ConfigureDelta F} {counts : ConfigureCounts}
    {initial : ConstraintSystem F} (map : SelCompressMap)
    {expression : Expression F Query}
    (hregistered : expression.QueriesRegistered delta) :
    expression.QueriesResolved
      (queryWalkInit map (delta.apply initial counts)) := by
  induction expression with
  | var query =>
      exact hregistered.resolves_recordedQueries_apply
        |>.of_recorded_queryWalkInit
  | const => trivial
  | add _ _ ihLeft ihRight | mul _ _ ihLeft ihRight =>
      exact ⟨ihLeft hregistered.1, ihRight hregistered.2⟩

/-- The families `fE`/`aE`/`iE` interpret `s`'s query layouts against the valuation `v`:
index `i` of a layout reads the same value as its registered `(column, rotation)` query. -/
structure Interprets (s : QueryState) (fE aE iE : ℕ → F) (v : Query → F) : Prop where
  advice : ∀ (i c : ℕ) (r : ℤ), s.advice[i]? = some (c, r) → aE i = v (.advice ⟨c⟩ r)
  fixed : ∀ (i c : ℕ) (r : ℤ), s.fixed[i]? = some (c, r) → fE i = v (.fixed ⟨c⟩ r)
  inst : ∀ (i c : ℕ) (r : ℤ), s.inst[i]? = some (c, r) → iE i = v (.instance ⟨c⟩ r)

/-! ### Registration correctness of the three index lookups -/

private theorem findQuery_spec {arr : Array (ℕ × ℤ)} {c : ℕ} {r : ℤ} {i : ℕ}
    (h : findQuery arr c r = some i) : arr[i]? = some (c, r) := by
  unfold findQuery at h
  obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨h1, h2⟩ := of_decide_eq_true hp
  rw [Array.getElem?_eq_some_iff]
  exact ⟨hlt, Prod.ext h1 h2⟩

omit [Field F] in
theorem QueryState.registerFixed_resolves
    (queries : QueryState) (column : ℕ) :
    (queries.registerFixed column).ResolvesQuery (.fixed ⟨column⟩ 0) := by
  unfold QueryState.registerFixed
  split
  · rename_i hexisting
    simp only [QueryState.ResolvesQuery]
    have hspec := Array.getElem?_eq_some_iff.mp
      (findQuery_spec hexisting)
    rw [← hspec.2]
    exact Array.getElem_mem hspec.1
  · simp [QueryState.ResolvesQuery]

omit [Field F] in
theorem queryWalkInit_resolves_packedColumn
    (cs : ConstraintSystem F) (map : SelCompressMap) {index : ℕ}
    (hindex : index < map.newFixedCols) :
    (queryWalkInit map cs).ResolvesQuery
      (.fixed ⟨cs.numFixedColumns + index⟩ 0) := by
  unfold queryWalkInit
  have hmem : index ∈ List.range map.newFixedCols :=
    List.mem_range.mpr hindex
  have preserve (indices : List ℕ) (queries : QueryState)
      {query : Query} (hquery : queries.ResolvesQuery query) :
      (indices.foldl (fun state next => state.registerFixed
        (cs.numFixedColumns + next)) queries).ResolvesQuery query := by
    induction indices generalizing queries with
    | nil => exact hquery
    | cons next indices ih =>
        rw [List.foldl_cons]
        exact ih _ (hquery.registerFixed (cs.numFixedColumns + next))
  have aux (indices : List ℕ) (queries : QueryState)
      (hmem : index ∈ indices) :
      (indices.foldl (fun state next => state.registerFixed
        (cs.numFixedColumns + next)) queries).ResolvesQuery
          (.fixed ⟨cs.numFixedColumns + index⟩ 0) := by
    induction indices generalizing queries with
    | nil => simp at hmem
    | cons next indices ih =>
        rw [List.foldl_cons]
        rw [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact preserve indices _
            (queries.registerFixed_resolves (cs.numFixedColumns + index))
        · exact ih _ hmem
  exact aux _ _ hmem

omit [Field F] in
theorem queryWalkInit_resolves_deriveSelCompressMap_lookup
    (cs : ConstraintSystem F) (n : ℕ) (acts : List (ℕ × ℕ))
    {selector : ℕ} {compressed : SelCompress}
    (hlookup : (deriveSelCompressMap cs n acts).lookup selector =
      some compressed) :
    (queryWalkInit (deriveSelCompressMap cs n acts) cs).ResolvesQuery
      (.fixed ⟨compressed.packedCol⟩ 0) := by
  obtain ⟨index, hindex, hcolumn⟩ :=
    deriveSelCompressMap_lookup_packedColumn cs n acts hlookup
  rw [hcolumn]
  exact queryWalkInit_resolves_packedColumn cs
    (deriveSelCompressMap cs n acts) hindex

private theorem advIdx_spec (s : QueryState) (c : ℕ) (r : ℤ)
    (hregistered : (c, r) ∈ s.advice) :
    s.advice[s.advIdx c r]? = some (c, r) := by
  unfold QueryState.advIdx
  cases hf : findQuery s.advice c r with
  | some i => simpa using findQuery_spec hf
  | none =>
      have hnone : s.advice.findIdx?
          (fun pair => pair.1 = c ∧ pair.2 = r) = none := by
        simpa [findQuery] using hf
      have hfalse := Array.findIdx?_eq_none_iff.mp hnone
        (c, r) hregistered
      simp at hfalse

private theorem fixIdx_spec (s : QueryState) (c : ℕ) (r : ℤ)
    (hregistered : (c, r) ∈ s.fixed) :
    s.fixed[s.fixIdx c r]? = some (c, r) := by
  unfold QueryState.fixIdx
  cases hf : findQuery s.fixed c r with
  | some i => simpa using findQuery_spec hf
  | none =>
      have hnone : s.fixed.findIdx?
          (fun pair => pair.1 = c ∧ pair.2 = r) = none := by
        simpa [findQuery] using hf
      have hfalse := Array.findIdx?_eq_none_iff.mp hnone
        (c, r) hregistered
      simp at hfalse

private theorem instIdx_spec (s : QueryState) (c : ℕ) (r : ℤ)
    (hregistered : (c, r) ∈ s.inst) :
    s.inst[s.instIdx c r]? = some (c, r) := by
  unfold QueryState.instIdx
  cases hf : findQuery s.inst c r with
  | some i => simpa using findQuery_spec hf
  | none =>
      have hnone : s.inst.findIdx?
          (fun pair => pair.1 = c ∧ pair.2 = r) = none := by
        simpa [findQuery] using hf
      have hfalse := Array.findIdx?_eq_none_iff.mp hnone
        (c, r) hregistered
      simp at hfalse

variable [DecidableEq F]

/-! ### Reduction helpers for the guarded `eraseExpr` arms

`eraseExpr`'s later `mul` arms only apply when the subterms do *not* match the earlier
arms; the functional-induction cases carry those guards as hypotheses, and these helpers
turn them into plain unfolding equations by splitting the guarded subterm's head. -/

private theorem eraseExpr_mulConstant (e : Expression F Query) (c : F) (s : QueryState)
    (he : ∀ c' : F, e = .const c' → False) :
    eraseExpr (.mul e (.mul (.const c) (.const 1))) s
      = (eraseExpr e s).product (.constant c) := by
  cases e with
  | const c' => exact absurd rfl (he c')
  | var q => simp only [eraseExpr, if_true]
  | add a b => simp only [eraseExpr, if_true]
  | mul a b => simp only [eraseExpr, if_true]

private theorem eraseExpr_mul_const_mul_const_of_ne_one (e : Expression F Query) (c one : F)
    (s : QueryState) (he : ∀ c' : F, e = .const c' → False) (hone : ¬one = 1) :
    eraseExpr (.mul e (.mul (.const c) (.const one))) s
      = (eraseExpr e s).product
          (eraseExpr (.mul (.const c) (.const one)) s) := by
  cases e with
  | const c' => exact absurd rfl (he c')
  | var q => simp only [eraseExpr, if_neg hone]
  | add a b => simp only [eraseExpr, if_neg hone]
  | mul a b => simp only [eraseExpr, if_neg hone]

private theorem eraseExpr_mul_const (e : Expression F Query) (c : F) (s : QueryState)
    (he : ∀ c' : F, e = .const c' → False) :
    eraseExpr (.mul e (.const c)) s
      = (eraseExpr e s).scaled c := by
  cases e with
  | const c' => exact absurd rfl (he c')
  | var q => simp only [eraseExpr]
  | add a b => simp only [eraseExpr]
  | mul a b => simp only [eraseExpr]

private theorem eraseExpr_mul (a b : Expression F Query) (s : QueryState)
    (ha : ∀ c : F, a = .const c → False)
    (hb1 : ∀ c one : F, b = .mul (.const c) (.const one) → False)
    (hb2 : ∀ c : F, b = .const c → False) :
    eraseExpr (.mul a b) s
      = (eraseExpr a s).product (eraseExpr b s) := by
  cases a with
  | const c => exact absurd rfl (ha c)
  | var qa =>
      cases b with
      | const c => exact absurd rfl (hb2 c)
      | var qb => simp only [eraseExpr]
      | add x y => simp only [eraseExpr]
      | mul x y =>
          cases x with
          | const cx =>
              cases y with
              | const cy => exact absurd rfl (hb1 cx cy)
              | var q => simp only [eraseExpr]
              | add _ _ => simp only [eraseExpr]
              | mul _ _ => simp only [eraseExpr]
          | var q => simp only [eraseExpr]
          | add _ _ => simp only [eraseExpr]
          | mul _ _ => simp only [eraseExpr]
  | add xa ya =>
      cases b with
      | const c => exact absurd rfl (hb2 c)
      | var qb => simp only [eraseExpr]
      | add x y => simp only [eraseExpr]
      | mul x y =>
          cases x with
          | const cx =>
              cases y with
              | const cy => exact absurd rfl (hb1 cx cy)
              | var q => simp only [eraseExpr]
              | add _ _ => simp only [eraseExpr]
              | mul _ _ => simp only [eraseExpr]
          | var q => simp only [eraseExpr]
          | add _ _ => simp only [eraseExpr]
          | mul _ _ => simp only [eraseExpr]
  | mul xa ya =>
      cases b with
      | const c => exact absurd rfl (hb2 c)
      | var qb => simp only [eraseExpr]
      | add x y => simp only [eraseExpr]
      | mul x y =>
          cases x with
          | const cx =>
              cases y with
              | const cy => exact absurd rfl (hb1 cx cy)
              | var q => simp only [eraseExpr]
              | add _ _ => simp only [eraseExpr]
              | mul _ _ => simp only [eraseExpr]
          | var q => simp only [eraseExpr]
          | add _ _ => simp only [eraseExpr]
          | mul _ _ => simp only [eraseExpr]

/-- **Erasure preserves evaluation.** If every query resolves against the interpreted
layout, erasing a selector-free expression preserves its value. -/
theorem eraseExpr_eval (fE aE iE : ℕ → F) (v : Query → F)
    (e : Expression F Query) (queries : QueryState)
    (hfree : e.SelectorFree)
    (hresolved : e.QueriesResolved queries)
    (hint : Interprets queries fE aE iE v) :
    RichExpression.eval fE aE iE (eraseExpr e queries) = e.eval v := by
  induction e, queries using eraseExpr.induct with
  | case1 c queries => rfl
  | case2 sel queries => simp [Expression.SelectorFree] at hfree
  | case3 col rot queries =>
      exact hint.advice (queries.advIdx col.index rot) col.index rot
        (advIdx_spec queries col.index rot hresolved)
  | case4 col rot queries =>
      exact hint.fixed (queries.fixIdx col.index rot) col.index rot
        (fixIdx_spec queries col.index rot hresolved)
  | case5 col rot queries =>
      exact hint.inst (queries.instIdx col.index rot) col.index rot
        (instIdx_spec queries col.index rot hresolved)
  | case6 e queries ih =>
      simp only [Expression.SelectorFree, true_and] at hfree
      simp only [Expression.QueriesResolved, true_and] at hresolved
      simp only [eraseExpr, if_true]
      rw [RichExpression.eval, ih hfree hresolved hint,
        show (Expression.mul (.const (-1)) e).eval v = -1 * e.eval v from rfl]
      ring
  | case7 c e queries hc ih =>
      simp only [Expression.SelectorFree, true_and] at hfree
      simp only [Expression.QueriesResolved, true_and] at hresolved
      simp only [eraseExpr, if_neg hc]
      rw [RichExpression.eval, RichExpression.eval, ih hfree hresolved hint]
      rfl
  | case8 e c queries he ih =>
      rw [eraseExpr_mulConstant e c queries he]
      simp only [Expression.SelectorFree, and_true] at hfree
      simp only [Expression.QueriesResolved, and_true] at hresolved
      rw [RichExpression.eval, RichExpression.eval, ih hfree hresolved hint,
        show (Expression.mul e (.mul (.const c) (.const 1))).eval v
          = e.eval v * (c * 1) from rfl]
      ring
  | case9 e c one queries he hone ih₁ ih₂ =>
      rw [eraseExpr_mul_const_mul_const_of_ne_one e c one queries he hone]
      simp only [Expression.SelectorFree, and_true] at hfree
      simp only [Expression.QueriesResolved, and_true] at hresolved
      simp only [RichExpression.eval]
      rw [ih₁ hfree hresolved hint,
        ih₂ (by simp [Expression.SelectorFree])
          (by simp [Expression.QueriesResolved]) hint]
      rfl
  | case10 e c queries he ih =>
      rw [eraseExpr_mul_const e c queries he]
      simp only [Expression.SelectorFree, and_true] at hfree
      simp only [Expression.QueriesResolved, and_true] at hresolved
      rw [RichExpression.eval, ih hfree hresolved hint]
      rfl
  | case11 a b queries ih₁ ih₂ =>
      simp only [Expression.SelectorFree] at hfree
      simp only [Expression.QueriesResolved] at hresolved
      simp only [eraseExpr, RichExpression.eval]
      rw [ih₁ hfree.1 hresolved.1 hint,
        ih₂ hfree.2 hresolved.2 hint]
      rfl
  | case12 a b queries ha hb1 hb2 ih₁ ih₂ =>
      rw [eraseExpr_mul a b queries ha hb1 hb2]
      simp only [Expression.SelectorFree] at hfree
      simp only [Expression.QueriesResolved] at hresolved
      simp only [RichExpression.eval]
      rw [ih₁ hfree.1 hresolved.1 hint,
        ih₂ hfree.2 hresolved.2 hint]
      rfl

/-! ## The composed per-gate step -/

/-- **The whole projection preserves evaluation**: compress, erase, then evaluate at
families interpreting the walk's layout — the result is the original gate expression at
the selector-replacement valuation. -/
theorem eraseExpr_substSelectorMap_eval (m : ℕ → Option SelCompress)
    (fE aE iE : ℕ → F) (v : Query → F)
    (p : Expression F Query) (queries : QueryState)
    (hcov : p.selectorsCovered (fun i => (m i).isSome) = true)
    (hresolved : (substSelectorMap m p).QueriesResolved queries)
    (hint : Interprets queries fE aE iE v) :
    RichExpression.eval fE aE iE (eraseExpr (substSelectorMap m p) queries)
      = p.eval (substValuation m v) := by
  rw [eraseExpr_eval fE aE iE v _ queries
      ((substSelectorMap_selectorFree m p).2 hcov) hresolved hint,
    substSelectorMap_eval]

/-! ## Lifting erasure to the gate list -/

/-- The walk erases gate lists length-preservingly. -/
theorem eraseGates_length (ps : List (Expression F Query)) (s : QueryState) :
    (eraseGates ps s).length = ps.length := by
  simp [eraseGates]

/-- **Erasure preserves evaluation, gate-list form.** Each erased gate evaluates to its
source expression position by position. -/
theorem eraseGates_eval (fE aE iE : ℕ → F) (v : Query → F)
    (ps : List (Expression F Query)) (queries : QueryState)
    (hfree : ∀ p ∈ ps, p.SelectorFree)
    (hresolved : ∀ p ∈ ps, p.QueriesResolved queries)
    (hint : Interprets queries fE aE iE v) :
    ∀ (j : ℕ) (_h1 : j < (eraseGates ps queries).length) (_h2 : j < ps.length),
      RichExpression.eval fE aE iE (eraseGates ps queries)[j] =
        Expression.eval v ps[j] := by
  intro j hprojected hsource
  simp only [eraseGates, List.getElem_map]
  exact eraseExpr_eval fE aE iE v ps[j] queries
    (hfree ps[j] (List.getElem_mem hsource))
    (hresolved ps[j] (List.getElem_mem hsource)) hint

/-! ## Semantics of the derived record -/

/-- The derived gate list, unfolded: the erasure of the compressed flat gates from the
configure-recorded walk state. -/
theorem PinnedConstraintSystem.derive_gates (cs : ConstraintSystem F)
    (map : SelCompressMap) :
    (PinnedConstraintSystem.derive cs map).gates
      = eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
          (queryWalkInit map cs) := by
  simp only [PinnedConstraintSystem.derive, projectCS]

/-- The derived record has one gate polynomial per flattened source gate. -/
theorem PinnedConstraintSystem.derive_gates_length (cs : ConstraintSystem F)
    (map : SelCompressMap) :
    (PinnedConstraintSystem.derive cs map).gates.length = (flatGates cs).length := by
  rw [PinnedConstraintSystem.derive_gates, eraseGates_length, List.length_map]

/-- **Each derived gate evaluates to its source gate.** Given selector coverage, the
`j`-th derived gate — at query families interpreting the walk's layout — evaluates to
the `j`-th flattened Clean gate expression under the selector-replacement valuation. -/
theorem PinnedConstraintSystem.derive_gates_eval (cs : ConstraintSystem F)
    (map : SelCompressMap) (fE aE iE : ℕ → F) (v : Query → F)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hresolved : ∀ p ∈ flatGates cs,
      (substSelectorMap map.lookup p).QueriesResolved
        (queryWalkInit map cs))
    (hint : Interprets (queryWalkInit map cs) fE aE iE v)
    (j : ℕ) (hg : j < (PinnedConstraintSystem.derive cs map).gates.length)
    (hp : j < (flatGates cs).length) :
    RichExpression.eval fE aE iE (PinnedConstraintSystem.derive cs map).gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  have hfree : ∀ p ∈ (flatGates cs).map (substSelectorMap map.lookup),
      p.SelectorFree := by
    intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    exact (substSelectorMap_selectorFree _ q).2 (hcov q hq)
  rw [List.getElem_of_eq (PinnedConstraintSystem.derive_gates cs map) hg]
  have h := eraseGates_eval fE aE iE v
    ((flatGates cs).map (substSelectorMap map.lookup)) (queryWalkInit map cs)
    hfree (by
      intro p hp'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
      exact hresolved q hq) hint j
    ((PinnedConstraintSystem.derive_gates cs map) ▸ hg) (by simpa using hp)
  rw [List.getElem_map, substSelectorMap_eval] at h
  exact h

end Halo2
