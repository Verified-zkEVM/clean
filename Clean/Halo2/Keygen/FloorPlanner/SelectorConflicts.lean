import Clean.Halo2.Keygen.CompressSelectors
import Clean.Halo2.Keygen.FloorPlanner.ConstantAllocation

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

/-!
# Selector conflicts from region-local synthesis summaries

Selector compression only needs to know whether two selectors can be active at the
same absolute row.  The definitions below retain the source region and local row of
each activation, allowing V1's generic region-disjointness theorem to answer most
of those questions without evaluating the planner's concrete sort.
-/

/-- A selector activation before the floor planner chooses an absolute row. -/
structure SelectorSite where
  region : ℕ
  columns : List RegionColumn
  row : ℕ
deriving DecidableEq, Repr

/-- Region-local sites for one selector, extracted from the reduced synthesis
summary. -/
def selectorSites (summary : SynthesisSummary)
    (selector : ℕ) : List SelectorSite :=
  ((indexRegionSummaries 0 summary.regionShapes).zip
      summary.regionSelectorActivations).flatMap
    fun (shape, activations) =>
      activations.filterMap fun activation =>
        if activation.1 = selector then
          some (SelectorSite.mk shape.index shape.columns activation.2)
        else none

/-- A finite, planner-independent sufficient condition for two selectors not to
conflict. Sites in one region must use different local rows; sites in distinct
regions must share a measured column, so V1 places their intervals disjointly. -/
def SelectorSitesSeparated (summary : SynthesisSummary)
    (left right : ℕ) : Prop :=
  ∀ leftSite ∈ selectorSites summary left,
    ∀ rightSite ∈ selectorSites summary right,
      if leftSite.region = rightSite.region then
        leftSite.row ≠ rightSite.row
      else
        ∃ column,
          column ∈ leftSite.columns ∧ column ∈ rightSite.columns

instance (summary : SynthesisSummary) (left right : ℕ) :
    Decidable (SelectorSitesSeparated summary left right) := by
  unfold SelectorSitesSeparated
  infer_instance

/-- The same-region half of selector separation. Cross-region separation can be
supplied uniformly by a circuit's selector-anchor theorem. -/
def SelectorLocalRowsSeparated (summary : SynthesisSummary)
    (left right : ℕ) : Prop :=
  ∀ region ∈ (indexRegionSummaries 0 summary.regionShapes).zip
      summary.regionSelectorActivations,
    ∀ leftActivation ∈ region.2, leftActivation.1 = left →
      ∀ rightActivation ∈ region.2, rightActivation.1 = right →
        leftActivation.2 ≠ rightActivation.2

instance (summary : SynthesisSummary) (left right : ℕ) :
    Decidable (SelectorLocalRowsSeparated summary left right) := by
  unfold SelectorLocalRowsSeparated
  infer_instance

private theorem initial_le_index_of_mem_indexedRegionSummaries_zip
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (activations : List (List (ℕ × ℕ)))
    (shape : RegionShape) (localActivations : List (ℕ × ℕ))
    (hregion : (shape, localActivations) ∈
      (indexRegionSummaries initial summaries).zip activations) :
    initial ≤ shape.index := by
  induction summaries generalizing initial activations with
  | nil => simp [indexRegionSummaries] at hregion
  | cons summary rest inductionHypothesis =>
      cases activations with
      | nil => simp at hregion
      | cons current remaining =>
          simp only [indexRegionSummaries, List.zip_cons_cons,
            List.mem_cons] at hregion
          rcases hregion with hhead | hrest
          · have hshape := congrArg (fun pair => pair.1.index) hhead
            simpa [measureRegionSummary] using hshape.symm.le
          · exact Nat.le_trans (Nat.le_add_right initial 1)
              (inductionHypothesis (initial + 1) remaining hrest)

private theorem localActivations_eq_of_regionIndex_eq
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (activations : List (List (ℕ × ℕ)))
    (leftShape rightShape : RegionShape)
    (leftActivations rightActivations : List (ℕ × ℕ))
    (hleft : (leftShape, leftActivations) ∈
      (indexRegionSummaries initial summaries).zip activations)
    (hright : (rightShape, rightActivations) ∈
      (indexRegionSummaries initial summaries).zip activations)
    (hindex : leftShape.index = rightShape.index) :
    leftActivations = rightActivations := by
  induction summaries generalizing initial activations with
  | nil => simp [indexRegionSummaries] at hleft
  | cons summary rest inductionHypothesis =>
      cases activations with
      | nil => simp at hleft
      | cons current remaining =>
          simp only [indexRegionSummaries, List.zip_cons_cons,
            List.mem_cons] at hleft hright
          rcases hleft with hleftHead | hleftRest <;>
            rcases hright with hrightHead | hrightRest
          · exact congrArg Prod.snd (hleftHead.trans hrightHead.symm)
          · have hleftIndex := congrArg (fun pair => pair.1.index) hleftHead
            have hrightBound :=
              initial_le_index_of_mem_indexedRegionSummaries_zip
                (initial + 1) rest remaining rightShape rightActivations
                hrightRest
            simp only [measureRegionSummary] at hleftIndex
            omega
          · have hrightIndex := congrArg (fun pair => pair.1.index) hrightHead
            have hleftBound :=
              initial_le_index_of_mem_indexedRegionSummaries_zip
                (initial + 1) rest remaining leftShape leftActivations
                hleftRest
            simp only [measureRegionSummary] at hrightIndex
            omega
          · exact inductionHypothesis (initial + 1) remaining
              hleftRest hrightRest

theorem synthesisSummary_regionShapes_length_eq_selectorActivations
    (operations : Operations F) :
    (synthesisSummary operations).regionShapes.length =
      (synthesisSummary operations).regionSelectorActivations.length := by
  induction operations with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp [synthesisSummary, SynthesisSummary.combine,
          SynthesisSummary.ofRegion, SynthesisSummary.ofInstanceRow,
          SynthesisSummary.ofTableValues, inductionHypothesis]

private theorem mem_regionOperationSelectorActivations_iff
    (operation : RegionOperation F) (selector row : ℕ) :
    (selector, row) ∈ regionOperationSelectorActivations operation ↔
      operation.ActivatesSelectorAt selector row := by
  cases operation with
  | enableGate gate operationRow =>
      simp only [regionOperationSelectorActivations, List.mem_singleton,
        Prod.mk.injEq, RegionOperation.ActivatesSelectorAt]
      aesop
  | enableLookup argument enabled operationRow =>
      simp only [regionOperationSelectorActivations, List.mem_map,
        Prod.mk.injEq, RegionOperation.ActivatesSelectorAt,
        SelectorEnabledAtIndex]
      aesop
  | assignAdvice | assignFixed | constrainEqual | constrainConstant |
      constrainInstance =>
      simp [regionOperationSelectorActivations,
        RegionOperation.ActivatesSelectorAt]

private theorem localSelectorActivation_wellFormed
    (index : ℕ) (body : RegionOperations F)
    (selector row : ℕ)
    (hactivation :
      (selector, row) ∈ (regionSynthesisSummary body).selectorActivations) :
    RegionColumn.selector selector ∈ (measureRegion index body).columns ∧
      row < (measureRegion index body).rowCount := by
  rw [regionSynthesisSummary_selectorActivations_eq_flatMap,
    List.mem_flatMap] at hactivation
  obtain ⟨operation, hoperation, hactivation⟩ := hactivation
  have hactivates :=
    (mem_regionOperationSelectorActivations_iff operation selector row).mp
      hactivation
  exact ⟨selector_mem_measureRegion_of_activatesSelectorAt
      index body hoperation hactivates,
    row_lt_measureRegion_of_activatesSelectorAt
      index body hoperation hactivates⟩

private theorem indexedRegionSelectorSummaries_eq
    (operations : Operations F) (initial : ℕ) :
    (indexRegionSummaries initial
        (synthesisSummary operations).regionShapes).zip
        (synthesisSummary operations).regionSelectorActivations =
      (indexedRegions operations initial).1.map fun (index, body) =>
        (measureRegion index body,
          (regionSynthesisSummary body).selectorActivations) := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          simp only [synthesisSummary,
            SynthesisSummary.combine_regionShapes,
            SynthesisSummary.combine_regionSelectorActivations,
            SynthesisSummary.ofRegion_regionShapes,
            SynthesisSummary.ofRegion_regionSelectorActivations,
            List.singleton_append, indexRegionSummaries,
            List.zip_cons_cons, indexedRegions, List.map_cons,
            measureRegion_eq_measureRegionSummary]
          exact congrArg (List.cons
            (measureRegion initial body,
              (regionSynthesisSummary body).selectorActivations))
            (inductionHypothesis (initial + 1))
      | constrainInstance cell column row =>
          simpa only [synthesisSummary,
            SynthesisSummary.combine_regionShapes,
            SynthesisSummary.combine_regionSelectorActivations,
            SynthesisSummary.ofInstanceRow, List.nil_append,
            indexedRegions] using inductionHypothesis initial
      | loadTable column values =>
          simpa only [synthesisSummary,
            SynthesisSummary.combine_regionShapes,
            SynthesisSummary.combine_regionSelectorActivations,
            SynthesisSummary.ofTableValues, List.nil_append,
            indexedRegions] using inductionHypothesis initial

private theorem mem_placeSelectorActivations_iff
    (starts : List ℕ) (summaries : List RegionShapeSummary)
    (activations : List (List (ℕ × ℕ)))
    (hlength : summaries.length = activations.length)
    (initial : ℕ)
    (selector absoluteRow : ℕ) :
    (selector, absoluteRow) ∈
        placeSelectorActivations starts initial activations ↔
      ∃ shape localActivations localRow,
        (shape, localActivations) ∈
          (indexRegionSummaries initial summaries).zip activations ∧
          (selector, localRow) ∈ localActivations ∧
          absoluteRow = starts.getD shape.index 0 + localRow := by
  induction summaries generalizing activations initial with
  | nil =>
      have : activations = [] := List.eq_nil_of_length_eq_zero (by simpa using hlength.symm)
      subst activations
      simp [placeSelectorActivations]
  | cons summary rest inductionHypothesis =>
      cases activations with
      | nil => simp at hlength
      | cons current remaining =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [placeSelectorActivations, List.mem_append,
            List.mem_map, indexRegionSummaries, List.zip_cons_cons,
            List.mem_cons]
          rw [inductionHypothesis remaining hlength (initial + 1)]
          constructor
          · rintro (⟨activation, hactivation, hequal⟩ | hrest)
            · rcases activation with ⟨sourceSelector, localRow⟩
              simp only [Prod.mk.injEq] at hequal
              refine ⟨measureRegionSummary initial summary, current, localRow,
                Or.inl rfl, ?_, hequal.2.symm⟩
              simpa only [hequal.1] using hactivation
            · obtain ⟨shape, localActivations, localRow,
                hsite, hactivation, habsolute⟩ := hrest
              exact ⟨shape, localActivations, localRow,
                Or.inr hsite, hactivation, habsolute⟩
          · rintro ⟨shape, localActivations, localRow,
              hsite, hactivation, habsolute⟩
            rcases hsite with hhead | hrest
            · have hshape : shape = measureRegionSummary initial summary :=
                congrArg Prod.fst hhead
              have hlocal : localActivations = current :=
                congrArg Prod.snd hhead
              exact Or.inl ⟨(selector, localRow), hlocal ▸ hactivation,
                by simpa [hshape, measureRegionSummary] using habsolute.symm⟩
            · exact Or.inr ⟨shape, localActivations, localRow,
                hrest, hactivation, habsolute⟩

theorem mem_selectorSites_iff
    (summary : SynthesisSummary) (selector : ℕ) (site : SelectorSite) :
    site ∈ selectorSites summary selector ↔
      ∃ shape localActivations,
        (shape, localActivations) ∈
          (indexRegionSummaries 0 summary.regionShapes).zip
            summary.regionSelectorActivations ∧
          (selector, site.row) ∈ localActivations ∧
          site.region = shape.index ∧ site.columns = shape.columns := by
  simp only [selectorSites, List.mem_flatMap]
  constructor
  · rintro ⟨⟨shape, localActivations⟩, hregion, hsite⟩
    simp only [List.mem_filterMap] at hsite
    obtain ⟨activation, hactivation, hequal⟩ := hsite
    split at hequal <;> rename_i hcondition
    · rcases activation with ⟨sourceSelector, localRow⟩
      have hselector : sourceSelector = selector := by simpa using hcondition
      subst sourceSelector
      have hsite :
          (SelectorSite.mk shape.index shape.columns localRow) = site :=
        Option.some.inj hequal
      rw [← hsite]
      refine ⟨shape, localActivations, hregion, ?_, rfl, rfl⟩
      exact hactivation
    · simp at hequal
  · rintro ⟨shape, localActivations, hregion, hactivation,
      hindex, hcolumns⟩
    refine ⟨(shape, localActivations), hregion, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨(selector, site.row), hactivation, ?_⟩
    cases site with
    | mk region columns row =>
        change region = shape.index at hindex
        change columns = shape.columns at hcolumns
        change (if selector = selector then
            some (SelectorSite.mk shape.index shape.columns row)
          else none) = some (SelectorSite.mk region columns row)
        rw [if_pos rfl]
        subst region
        subst columns
        rfl

/-- Every selector site exported by a synthesized summary lies inside its source
region and records that selector's measured virtual column. -/
theorem selectorSites_wellFormed
    (operations : Operations F) (selector : ℕ) (site : SelectorSite)
    (hsite : site ∈ selectorSites (synthesisSummary operations) selector) :
    ∃ index body,
      (index, body) ∈ (indexedRegions operations 0).1 ∧
        site.region = index ∧
        site.columns = (measureRegion index body).columns ∧
        RegionColumn.selector selector ∈
          (measureRegion index body).columns ∧
        site.row < (measureRegion index body).rowCount := by
  rw [mem_selectorSites_iff] at hsite
  obtain ⟨shape, localActivations, hregion, hactivation,
    hindex, hcolumns⟩ := hsite
  rw [indexedRegionSelectorSummaries_eq] at hregion
  rw [List.mem_map] at hregion
  obtain ⟨⟨index, body⟩, hindexed, hequal⟩ := hregion
  have hshape : shape = measureRegion index body :=
    (congrArg Prod.fst hequal).symm
  have hlocal : localActivations =
      (regionSynthesisSummary body).selectorActivations :=
    (congrArg Prod.snd hequal).symm
  have hwell := localSelectorActivation_wellFormed index body selector site.row
    (hlocal ▸ hactivation)
  refine ⟨index, body, hindexed, ?_, ?_, hwell.1, hwell.2⟩
  · simpa [hshape] using hindex
  · simpa [hshape] using hcolumns

/-- Physical columns common to every source region of a selector. -/
def selectorCommonColumns (summary : SynthesisSummary)
    (selector : ℕ) : List RegionColumn :=
  match selectorSites summary selector with
  | [] => []
  | first :: rest => first.columns.filter fun column =>
      rest.all fun site => column ∈ site.columns

theorem mem_selectorSite_of_mem_commonColumns
    (summary : SynthesisSummary) (selector : ℕ)
    (column : RegionColumn) (site : SelectorSite)
    (hcolumn : column ∈ selectorCommonColumns summary selector)
    (hsite : site ∈ selectorSites summary selector) :
    column ∈ site.columns := by
  unfold selectorCommonColumns at hcolumn
  cases hsites : selectorSites summary selector with
  | nil => simp [hsites] at hsite
  | cons first rest =>
      simp only [hsites, List.mem_filter, decide_eq_true_eq,
        List.all_eq_true] at hcolumn
      rw [hsites, List.mem_cons] at hsite
      rcases hsite with rfl | hrest
      · exact hcolumn.1
      · exact hcolumn.2 site hrest

/-- A common measured column handles every cross-region case; only same-region
local-row separation remains to be checked. -/
theorem selectorSitesSeparated_of_commonColumn
    (summary : SynthesisSummary) (left right : ℕ)
    (hlocal : SelectorLocalRowsSeparated summary left right)
    (hcommon : ∃ column,
      column ∈ selectorCommonColumns summary left ∧
        column ∈ selectorCommonColumns summary right) :
    SelectorSitesSeparated summary left right := by
  intro leftSite hleftSite rightSite hrightSite
  split <;> rename_i hregions
  · rw [mem_selectorSites_iff] at hleftSite hrightSite
    obtain ⟨leftShape, leftActivations, hleftRegion, hleftActivation,
      hleftIndex, _⟩ := hleftSite
    obtain ⟨rightShape, rightActivations, hrightRegion,
      hrightActivation, hrightIndex, _⟩ := hrightSite
    have hindex : leftShape.index = rightShape.index := by
      rw [← hleftIndex, ← hrightIndex]
      exact hregions
    have hactivations : leftActivations = rightActivations :=
      localActivations_eq_of_regionIndex_eq 0 summary.regionShapes
        summary.regionSelectorActivations leftShape rightShape
        leftActivations rightActivations hleftRegion hrightRegion hindex
    intro hrows
    subst rightActivations
    exact hlocal (leftShape, leftActivations) hleftRegion
      (left, leftSite.row) hleftActivation rfl
      (right, rightSite.row) hrightActivation rfl hrows
  · obtain ⟨column, hleftColumn, hrightColumn⟩ := hcommon
    exact ⟨column,
      mem_selectorSite_of_mem_commonColumns summary left column
        leftSite hleftColumn hleftSite,
      mem_selectorSite_of_mem_commonColumns summary right column
        rightSite hrightColumn hrightSite⟩

theorem mem_placeSelectorActivations_iff_mem_selectorSites
    (starts : List ℕ) (operations : Operations F)
    (selector absoluteRow : ℕ) :
    (selector, absoluteRow) ∈ placeSelectorActivations starts 0
        (synthesisSummary operations).regionSelectorActivations ↔
      ∃ site ∈ selectorSites (synthesisSummary operations) selector,
        absoluteRow = starts.getD site.region 0 + site.row := by
  rw [mem_placeSelectorActivations_iff starts
    (synthesisSummary operations).regionShapes
    (synthesisSummary operations).regionSelectorActivations
    (synthesisSummary_regionShapes_length_eq_selectorActivations operations)
    0 selector absoluteRow]
  constructor
  · rintro ⟨shape, localActivations, localRow,
      hregion, hactivation, habsolute⟩
    let site := SelectorSite.mk shape.index shape.columns localRow
    refine ⟨site, ?_, habsolute⟩
    rw [mem_selectorSites_iff]
    exact ⟨shape, localActivations, hregion, hactivation, rfl, rfl⟩
  · rintro ⟨site, hsite, habsolute⟩
    rw [mem_selectorSites_iff] at hsite
    obtain ⟨shape, localActivations, hregion, hactivation,
      hindex, hcolumns⟩ := hsite
    exact ⟨shape, localActivations, site.row, hregion,
      hactivation, by simpa only [hindex] using habsolute⟩

/-- V1's region placement turns the local separation check into an exact
non-conflict fact for selector compression. -/
theorem selectorActivationsConflict_eq_false_of_sitesSeparated
    (operations : Operations F) (left right : ℕ)
    (hseparated : SelectorSitesSeparated
      (synthesisSummary operations) left right) :
    selectorActivationsConflict
        (placeSelectorActivations (V1.starts operations) 0
          (synthesisSummary operations).regionSelectorActivations)
        left right = false := by
  apply Bool.eq_false_iff.mpr
  intro hconflict
  rw [selectorActivationsConflict, List.any_eq_true] at hconflict
  obtain ⟨absoluteRow, hleftRow, hrightActivation⟩ := hconflict
  have hleftActivation :
      (left, absoluteRow) ∈ placeSelectorActivations
        (V1.starts operations) 0
        (synthesisSummary operations).regionSelectorActivations :=
    (mem_selectorActivationRows_iff _ left absoluteRow).mp hleftRow
  have hrightActivation' :
      (right, absoluteRow) ∈ placeSelectorActivations
        (V1.starts operations) 0
        (synthesisSummary operations).regionSelectorActivations := by
    simpa only [decide_eq_true_eq] using hrightActivation
  rw [mem_placeSelectorActivations_iff_mem_selectorSites] at hleftActivation
  rw [mem_placeSelectorActivations_iff_mem_selectorSites] at hrightActivation'
  obtain ⟨leftSite, hleftSite, hleftAbsolute⟩ := hleftActivation
  obtain ⟨rightSite, hrightSite, hrightAbsolute⟩ := hrightActivation'
  have hleftSource := selectorSites_wellFormed operations left leftSite hleftSite
  have hrightSource := selectorSites_wellFormed operations right rightSite hrightSite
  obtain ⟨leftIndex, leftBody, hleftRegion, hleftIndex,
    hleftColumns, _, hleftBound⟩ := hleftSource
  obtain ⟨rightIndex, rightBody, hrightRegion, hrightIndex,
    hrightColumns, _, hrightBound⟩ := hrightSource
  have hcondition := hseparated leftSite hleftSite rightSite hrightSite
  split at hcondition <;> rename_i hindices
  · have hlocal : leftSite.row = rightSite.row := by
      have habsolute :
          (V1.starts operations).getD leftSite.region 0 + leftSite.row =
            (V1.starts operations).getD rightSite.region 0 + rightSite.row :=
        hleftAbsolute.symm.trans hrightAbsolute
      rw [hindices] at habsolute
      exact Nat.add_left_cancel habsolute
    exact hcondition hlocal
  · obtain ⟨column, hleftColumn, hrightColumn⟩ := hcondition
    have hindexNe : leftIndex ≠ rightIndex := by
      simpa only [hleftIndex, hrightIndex] using hindices
    have hrowNe := region_rows_ne_of_sharedColumnIntervalsDisjoint
      (V1.starts_sharedColumnIntervalsDisjoint operations)
      (List.mem_map.mpr ⟨(leftIndex, leftBody), hleftRegion, rfl⟩)
      (List.mem_map.mpr ⟨(rightIndex, rightBody), hrightRegion, rfl⟩)
      hindexNe
      (by simpa only [hleftColumns] using hleftColumn)
      (by simpa only [hrightColumns] using hrightColumn)
      hleftBound hrightBound
    apply hrowNe
    simpa only [hleftIndex, hrightIndex] using
      hleftAbsolute.symm.trans hrightAbsolute

end Halo2.FloorPlanner
