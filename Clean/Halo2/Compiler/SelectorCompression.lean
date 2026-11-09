import Clean.Halo2.Compiler.SelectorEvaluation
import Clean.Halo2.Keygen.Layout
import Std.Data.HashSet.Lemmas

/-!
# Selector compiler coherence

Structural facts about Clean's `compress_selectors` port.  These proofs are
circuit-independent: they reason about the greedy packing algorithm rather than a
captured Action selector map.
-/

variable {F : Type} [FiniteField F]

namespace Halo2

set_option maxHeartbeats 20000

/-- Selector coverage is monotone in its domain predicate. -/
theorem Expression.selectorsCovered_mono
    {F : Type} (source target : ℕ → Bool)
    (hdom : ∀ selector, source selector = true →
      target selector = true)
    (expression : Expression F Query)
    (hcovered : expression.selectorsCovered source = true) :
    expression.selectorsCovered target = true := by
  induction expression with
  | var query =>
      cases query with
      | selector selector => exact hdom selector.index hcovered
      | fixed | advice | «instance» => rfl
  | const => rfl
  | add left right ihLeft ihRight
  | mul left right ihLeft ihRight =>
      simp only [Expression.selectorsCovered,
        Bool.and_eq_true] at hcovered ⊢
      exact ⟨ihLeft hcovered.1, ihRight hcovered.2⟩

/--
The inner greedy scan partitions the initial combination and candidate list:
it neither drops nor invents selector descriptions.
-/
theorem mem_extendCombination_iff
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription)
    (description : SelectorDescription) :
    description ∈ (extendCombination maxDegree d comb selectors).1 ∨
        description ∈ (extendCombination maxDegree d comb selectors).2 ↔
      description ∈ comb ∨ description ∈ selectors := by
  induction selectors generalizing d comb with
  | nil =>
      simp [extendCombination]
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · simp [or_assoc, or_comm]
      · split
        · generalize hresult :
            extendCombination maxDegree d comb rest = result
          rcases result with ⟨chosen, remaining⟩
          have hpartition := ih d comb
          rw [hresult] at hpartition
          simp only [List.mem_cons] at *
          change
            (description ∈ chosen ∨ description = selector ∨
              description ∈ remaining) ↔
            (description ∈ comb ∨ description = selector ∨
              description ∈ rest)
          constructor
          · intro h
            rcases h with hchosen | rfl | hremaining
            · rcases hpartition.mp (Or.inl hchosen) with
                hcomb | hrest
              · exact Or.inl hcomb
              · exact Or.inr (Or.inr hrest)
            · exact Or.inr (Or.inl rfl)
            · rcases hpartition.mp (Or.inr hremaining) with
                hcomb | hrest
              · exact Or.inl hcomb
              · exact Or.inr (Or.inr hrest)
          · intro h
            rcases h with hcomb | rfl | hrest
            · rcases hpartition.mpr (Or.inl hcomb) with
                hchosen | hremaining
              · exact Or.inl hchosen
              · exact Or.inr (Or.inr hremaining)
            · exact Or.inr (Or.inl rfl)
            · rcases hpartition.mpr (Or.inr hrest) with
                hchosen | hremaining
              · exact Or.inl hchosen
              · exact Or.inr (Or.inr hremaining)
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · generalize hresult :
              extendCombination maxDegree d comb rest = result
            rcases result with ⟨chosen, remaining⟩
            have hpartition := ih d comb
            rw [hresult] at hpartition
            simp only [List.mem_cons] at *
            change
              (description ∈ chosen ∨ description = selector ∨
                description ∈ remaining) ↔
              (description ∈ comb ∨ description = selector ∨
                description ∈ rest)
            constructor
            · intro h
              rcases h with hchosen | rfl | hremaining
              · rcases hpartition.mp (Or.inl hchosen) with
                  hcomb | hrest
                · exact Or.inl hcomb
                · exact Or.inr (Or.inr hrest)
              · exact Or.inr (Or.inl rfl)
              · rcases hpartition.mp (Or.inr hremaining) with
                  hcomb | hrest
                · exact Or.inl hcomb
                · exact Or.inr (Or.inr hrest)
            · intro h
              rcases h with hcomb | rfl | hrest
              · rcases hpartition.mpr (Or.inl hcomb) with
                  hchosen | hremaining
                · exact Or.inl hchosen
                · exact Or.inr (Or.inr hremaining)
              · exact Or.inr (Or.inl rfl)
              · rcases hpartition.mpr (Or.inr hrest) with
                  hchosen | hremaining
                · exact Or.inl hchosen
                · exact Or.inr (Or.inr hremaining)
          · generalize hresult :
              extendCombination maxDegree nextDegree
                (comb ++ [selector]) rest = result
            rcases result with ⟨chosen, remaining⟩
            have hpartition :=
              ih nextDegree (comb ++ [selector])
            rw [hresult] at hpartition
            simp only [List.mem_cons] at *
            change
              (description ∈ chosen ∨ description ∈ remaining) ↔
              (description ∈ comb ∨ description = selector ∨
                description ∈ rest)
            simpa only [List.mem_append, List.mem_singleton,
              or_assoc] using hpartition

/-- The inner scan's remaining candidates are no longer than its input candidates. -/
theorem extendCombination_remaining_length_le
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription) :
    (extendCombination maxDegree d comb selectors).2.length ≤
      selectors.length := by
  induction selectors generalizing d comb with
  | nil =>
      simp [extendCombination]
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · simp
      · split
        · generalize hresult :
            extendCombination maxDegree d comb rest = result
          rcases result with ⟨chosen, remaining⟩
          have hlength := ih d comb
          rw [hresult] at hlength
          change remaining.length ≤ rest.length at hlength
          simpa only [List.length_cons] using
            Nat.succ_le_succ hlength
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · generalize hresult :
              extendCombination maxDegree d comb rest = result
            rcases result with ⟨chosen, remaining⟩
            have hlength := ih d comb
            rw [hresult] at hlength
            change remaining.length ≤ rest.length at hlength
            simpa only [List.length_cons] using
              Nat.succ_le_succ hlength
          · exact (ih nextDegree (comb ++ [selector])).trans
              (Nat.le_succ _)

/-- Every list member occurs in the list paired with its zero-based index. -/
private theorem exists_mem_zipIdx_of_mem
    {α : Type} {item : α} {items : List α}
    (hitem : item ∈ items) :
    ∃ index, (item, index) ∈ items.zipIdx := by
  obtain ⟨index, hindex, hget⟩ :=
    List.mem_iff_getElem.mp hitem
  refine ⟨index, ?_⟩
  rw [List.mk_mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  exact ⟨hindex, hget⟩

/--
With enough outer-loop fuel, every candidate occurs in one returned selector
combination.
-/
theorem exists_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors : List SelectorDescription)
    (hfuel : selectors.length ≤ fuel)
    {description : SelectorDescription}
    (hdescription : description ∈ selectors) :
    ∃ combination ∈ buildCombinations maxDegree fuel selectors,
      description ∈ combination := by
  induction fuel generalizing selectors with
  | zero =>
      have : selectors = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this] at hdescription
  | succ fuel ih =>
      cases selectors with
      | nil =>
          simp at hdescription
      | cons selector rest =>
          simp only [buildCombinations]
          generalize hresult :
              extendCombination maxDegree
                (selector.maxDegree - 1) [selector] rest =
                result
          rcases result with ⟨chosen, remaining⟩
          have hsource :
              description ∈ [selector] ∨ description ∈ rest := by
            simpa only [List.mem_cons, List.mem_singleton,
              List.not_mem_nil, or_false] using hdescription
          have hpartition :=
            (mem_extendCombination_iff maxDegree
              (selector.maxDegree - 1) [selector] rest
              description).mpr hsource
          rw [hresult] at hpartition
          rcases hpartition with hchosen | hremaining
          · exact ⟨chosen, List.mem_cons_self, hchosen⟩
          · have hremainingLength :=
              extendCombination_remaining_length_le maxDegree
                (selector.maxDegree - 1) [selector] rest
            rw [hresult] at hremainingLength
            change remaining.length ≤ rest.length at hremainingLength
            have hremainingFuel : remaining.length ≤ fuel := by
              simp only [List.length_cons] at hfuel
              omega
            obtain ⟨combination, hcombination, hmember⟩ :=
              ih remaining hremainingFuel hremaining
            exact ⟨combination,
              List.mem_cons_of_mem chosen hcombination, hmember⟩

/--
The greedy extension never exceeds the degree budget when its initial combination
already fits.  Candidate degrees need no separate bound: the algorithm checks the
updated degree and length before every insertion.
-/
theorem extendCombination_length_le
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription)
    (hcomb : comb.length ≤ maxDegree) :
    (extendCombination maxDegree d comb selectors).1.length ≤
      maxDegree := by
  induction selectors generalizing d comb with
  | nil =>
      simpa [extendCombination] using hcomb
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · exact hcomb
      · split
        · exact ih d comb hcomb
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · exact ih d comb hcomb
          · apply ih nextDegree (comb ++ [selector])
            simp only [List.length_append, List.length_singleton]
            omega

/--
Every combination returned by the outer packing loop fits in the selector
compression degree budget.
-/
theorem length_le_maxDegree_of_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors combination :
      List SelectorDescription)
    (hpositive : 1 ≤ maxDegree)
    (hcombination :
      combination ∈ buildCombinations maxDegree fuel selectors) :
    combination.length ≤ maxDegree := by
  induction fuel generalizing selectors with
  | zero =>
      simp [buildCombinations] at hcombination
  | succ fuel ih =>
      cases selectors with
      | nil =>
          simp [buildCombinations] at hcombination
      | cons selector rest =>
          simp only [buildCombinations] at hcombination
          generalize hresult :
              extendCombination maxDegree
                (selector.maxDegree - 1) [selector] rest =
                result at hcombination
          rcases result with ⟨chosen, remaining⟩
          simp only [List.mem_cons] at hcombination
          rcases hcombination with rfl | hcombination
          · have hchosen :=
              extendCombination_length_le maxDegree
                (selector.maxDegree - 1) [selector] rest
                (by simpa using hpositive)
            simpa [hresult] using hchosen
          · exact ih remaining hcombination

/--
Every `process` entry's assigned root is bounded by the compression degree,
independently of how many selectors the circuit declares.
-/
theorem process_entry_root_degree_bounds
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (hpositive : 1 ≤ maxDegree)
    (entry : ℕ × SelCompress)
    (hentry : entry ∈ (process selectors maxDegree).entries) :
    1 ≤ entry.2.assignedRoot ∧
      entry.2.assignedRoot ≤ entry.2.combinationLen ∧
      entry.2.combinationLen ≤ maxDegree := by
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
  rw [List.mem_append] at hentry
  rcases hentry with hdegreeZero | hcombination
  · obtain ⟨indexed, _hindexed, rfl⟩ :=
      List.mem_map.mp hdegreeZero
    simpa using hpositive
  · rw [List.mem_flatMap] at hcombination
    obtain ⟨indexedCombination, hindexedCombination,
      hcombinationEntry⟩ := hcombination
    rcases indexedCombination with ⟨combination, column⟩
    obtain ⟨indexedDescription, hindexedDescription, rfl⟩ :=
      List.mem_map.mp hcombinationEntry
    rcases indexedDescription with ⟨description, position⟩
    have hposition :
        position < combination.length := by
      simpa using
        List.snd_lt_of_mem_zipIdx hindexedDescription
    have hcombinationMem :
        combination ∈ combinations :=
      List.fst_mem_of_mem_zipIdx hindexedCombination
    have hcombinationLength :
        combination.length ≤ maxDegree :=
      length_le_maxDegree_of_mem_buildCombinations
        maxDegree remaining.length remaining combination
        hpositive hcombinationMem
    change 1 ≤ position + 1 ∧
      position + 1 ≤ combination.length ∧
      combination.length ≤ maxDegree
    exact ⟨by omega, by omega, hcombinationLength⟩

/-- Every input selector description receives an entry in the packed map. -/
theorem exists_mem_process_entries
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    {description : SelectorDescription}
    (hdescription : description ∈ selectors) :
    ∃ compressed,
      (description.selector, compressed) ∈
        (process selectors maxDegree).entries := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change ∃ compressed,
    (description.selector, compressed) ∈
      (degreeZero.zipIdx.map fun (source, column) =>
        (source.selector, SelCompress.mk column 1 1)) ++
      (combinations.zipIdx.flatMap fun (combination, column) =>
        combination.zipIdx.map fun (source, position) =>
          (source.selector,
            SelCompress.mk (degreeZero.length + column)
              combination.length (position + 1)))
  by_cases hdegree : description.maxDegree = 0
  · have hdegreeZero : description ∈ degreeZero :=
      List.mem_filter.mpr ⟨hdescription, by simp [hdegree]⟩
    obtain ⟨column, hzip⟩ :=
      exists_mem_zipIdx_of_mem hdegreeZero
    refine ⟨SelCompress.mk column 1 1, ?_⟩
    apply List.mem_append_left
    exact List.mem_map.mpr
      ⟨(description, column), hzip, rfl⟩
  · have hremaining : description ∈ remaining :=
      List.mem_filter.mpr ⟨hdescription, by simp [hdegree]⟩
    obtain ⟨combination, hcombination, hmember⟩ :=
      exists_mem_buildCombinations maxDegree remaining.length
        remaining (Nat.le_refl _) hremaining
    obtain ⟨column, hcombinationZip⟩ :=
      exists_mem_zipIdx_of_mem hcombination
    obtain ⟨position, hdescriptionZip⟩ :=
      exists_mem_zipIdx_of_mem hmember
    refine
      ⟨SelCompress.mk (degreeZero.length + column)
        combination.length (position + 1), ?_⟩
    apply List.mem_append_right
    rw [List.mem_flatMap]
    exact ⟨(combination, column), hcombinationZip,
      List.mem_map.mpr
        ⟨(description, position), hdescriptionZip, rfl⟩⟩

/-- An association-list entry makes the corresponding map lookup present. -/
theorem SelCompressMap.lookup_isSome_of_mem
    (map : SelCompressMap) {selector : ℕ} {compressed : SelCompress}
    (hentry : (selector, compressed) ∈ map.entries) :
    (map.lookup selector).isSome = true := by
  have hfind :
      (map.entries.find? (fun entry => entry.1 = selector)).isSome := by
    rw [List.find?_isSome]
    exact ⟨(selector, compressed), hentry, by simp⟩
  obtain ⟨entry, hentryEq⟩ :=
    Option.isSome_iff_exists.mp hfind
  simp [SelCompressMap.lookup, hentryEq]

/-- `process` covers every input selector key. -/
theorem process_lookup_isSome_of_mem
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    {description : SelectorDescription}
    (hdescription : description ∈ selectors) :
    ((process selectors maxDegree).lookup
      description.selector).isSome = true := by
  obtain ⟨compressed, hentry⟩ :=
    exists_mem_process_entries selectors maxDegree hdescription
  exact SelCompressMap.lookup_isSome_of_mem
    (process selectors maxDegree) hentry

/-- Selector lookup commutes with the compiler's packed-column offset. -/
theorem deriveSelCompressMap_lookup_eq {F : Type}
    (cs : ConstraintSystem F) (n : ℕ) (activations : List (ℕ × ℕ)) (selector : ℕ) :
    (deriveSelCompressMap cs n activations).lookup selector =
      ((process ((List.range cs.numSelectors).map fun index =>
        SelectorDescription.mk index
          (activationTable n cs.numSelectors activations)[index]!
          (selectorMaxDegrees cs)[index]!) (csDegree cs)).lookup selector).map
        (fun source => { source with packedCol := source.packedCol + cs.numFixedColumns }) := by
  simp only [deriveSelCompressMap, SelCompressMap.lookup, List.find?_map,
    Function.comp_def, Option.map_map]

/--
The circuit-derived compression map covers every allocated selector index.
Selector packing changes columns and roots, but never drops a configured selector.
-/
theorem deriveSelCompressMap_lookup_isSome_of_lt
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ)) {selector : ℕ}
    (hselector : selector < cs.numSelectors) :
    ((deriveSelCompressMap cs n activations).lookup selector).isSome =
      true := by
  rw [deriveSelCompressMap_lookup_eq, Option.isSome_map]
  exact process_lookup_isSome_of_mem _ _ (description := ⟨selector, _, _⟩)
    (List.mem_map.mpr ⟨selector, List.mem_range.mpr hselector, rfl⟩)

/--
A selector with no gate degree is packed alone by the circuit-derived map. Its
column is in the newly appended fixed-column suffix.
-/
theorem deriveSelCompressMap_lookup_degreeZero_of_lt
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ)) {selector : ℕ}
    (hselector : selector < cs.numSelectors)
    (hdegree : (selectorMaxDegrees cs)[selector]! = 0) :
    ∃ compressed,
      (deriveSelCompressMap cs n activations).lookup selector =
        some compressed ∧
      compressed.combinationLen = 1 ∧
      compressed.assignedRoot = 1 ∧
      cs.numFixedColumns ≤ compressed.packedCol := by
  obtain ⟨compressed, hlookup, hlength, hroot⟩ :=
    deriveSelCompressMap_lookup_singleton_of_degree_zero cs n activations selector hselector hdegree
  obtain ⟨index, _, hcolumn⟩ := deriveSelCompressMap_lookup_packedColumn cs n activations hlookup
  exact ⟨compressed, hlookup, hlength, hroot, by omega⟩

/--
The circuit-derived compression map covers every selector atom of every configured
gate once the configure phase certifies that those atoms name allocated selectors.
-/
theorem selectorsCovered_of_mem_flatGates_deriveSelCompressMap
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ))
    (hallocated : cs.gates.Forall fun gate =>
      gate.selector.index < cs.numSelectors) :
    ∀ expression ∈ flatGates cs,
      expression.selectorsCovered
        (fun selector =>
          ((deriveSelCompressMap cs n activations).lookup selector).isSome) =
        true := by
  intro expression hexpression
  rw [flatGates, List.mem_flatMap] at hexpression
  obtain ⟨gate, hgate, hexpression⟩ := hexpression
  obtain ⟨constraint, hconstraint, hexpression⟩ :=
    List.mem_map.mp hexpression
  subst expression
  apply Expression.selectorsCovered_mono
    (fun selector => decide (selector = gate.selector.index))
  · intro selector hselector
    have hselectorLt : selector < cs.numSelectors := by
      rw [of_decide_eq_true hselector]
      exact List.forall_iff_forall_mem.mp hallocated gate hgate
    exact deriveSelCompressMap_lookup_isSome_of_lt
      cs n activations hselectorLt
  · exact Expression.selectorsCovered_of_selectorsOwnedBy
      gate.selector constraint.poly <|
        List.forall_iff_forall_mem.mp
          gate.wellFormed.selectorsOwned constraint hconstraint

end Halo2

namespace Halo2

open Layout

set_option maxHeartbeats 20000

/--
The selector packer assigns valid roots whenever its compression degree fits below
the field characteristic.
-/
theorem hasWellFormedSelectorRoots_process
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (hpositive : 1 ≤ maxDegree)
    (hdegree : maxDegree < ringChar F) :
    HasWellFormedSelectorRoots F (process selectors maxDegree) := by
  intro selector compressed hlookup
  obtain ⟨entry, hentry, hcompressed⟩ :=
    SelCompressMap.exists_mem_entries_of_lookup
      (process selectors maxDegree) hlookup
  have hbounds :=
    process_entry_root_degree_bounds selectors maxDegree
      hpositive entry hentry
  rw [← hcompressed]
  exact ⟨hbounds.1, hbounds.2.1,
    hbounds.2.2.trans_lt hdegree⟩

/--
The circuit-derived selector map has valid roots under the minimal generic size
condition: the constraint-system degree is below the field characteristic.
-/
theorem hasWellFormedSelectorRoots_deriveSelCompressMap
    {F : Type} [FiniteField F] (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ))
    (hdegree : csDegree cs < ringChar F) :
    HasWellFormedSelectorRoots F
      (deriveSelCompressMap cs n activations) := by
  intro selector compressed hlookup
  rw [deriveSelCompressMap_lookup_eq] at hlookup
  obtain ⟨source, hsource, rfl⟩ := Option.map_eq_some_iff.mp hlookup
  have hroots := hasWellFormedSelectorRoots_process _ (csDegree cs)
    (by unfold csDegree; exact le_trans (by omega) (Nat.le_max_left _ _)) hdegree hsource
  exact hroots

/-- It is enough to realize the packed assignments emitted by the canonical fixed
compiler to realize every selector activation expected by the gate resolver. -/
theorem realizesSelectorActivations_of_selectorAssignments
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (environment : Environment F)
    (hfixed :
      ∀ {assignment : Layout.FixedAssignment F},
        assignment ∈ Layout.selectorAssignments map activationRows →
          environment.fixed ⟨assignment.1⟩ assignment.2.1 =
            assignment.2.2) :
    RealizesSelectorActivations map activationRows environment := by
  intro selector row compressed hactivation hlookup
  exact hfixed
    (Layout.mem_selectorAssignments_of_activation (F := F) map activationRows
      hactivation hlookup)

end Halo2
