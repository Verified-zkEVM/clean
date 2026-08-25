import Clean.Halo2.Configure.Queries

namespace Halo2

variable {F : Type}

/--
Every gate selector and lookup-input selector emitted by a configure delta lies below
the final allocated selector count. Gate well-formedness then gives the same bound for
every selector atom in each gate constraint.
-/
structure ConfigureDelta.SelectorsAllocated
    (delta : ConfigureDelta F) (numSelectors : ℕ) : Prop where
  gates :
    delta.gates.Forall fun gate => gate.selector.index < numSelectors
  lookupMasters :
    delta.lookups.Forall fun argument =>
      argument.masterSelector.index < numSelectors
  lookups :
    lookupInputSelectorBound delta.lookups ≤ numSelectors

/-- Every selector used by a configure contribution lies below a boundary. This is a
small compositional summary for reasoning about two sequential configure programs;
unlike `SelectorsAllocated`, it includes each lookup's distinguished master selector. -/
structure ConfigureDelta.SelectorsBounded
    (delta : ConfigureDelta F) (bound : ℕ) : Prop where
  gates : delta.gates.Forall fun gate => gate.selector.index < bound
  lookups : delta.lookups.Forall fun argument =>
    argument.selectorIndices.Forall (fun selector => selector < bound)

/-- Every selector used by a configure contribution was allocated at or after a
boundary. Programs that allocate their own selectors expose this compact fact without
revealing their configure tree. -/
structure ConfigureDelta.SelectorsFreshFrom
    (delta : ConfigureDelta F) (lowerBound : ℕ) : Prop where
  gates : delta.gates.Forall fun gate => lowerBound ≤ gate.selector.index
  lookups : delta.lookups.Forall fun argument =>
    argument.selectorIndices.Forall (fun selector => lowerBound ≤ selector)

/-- Reduced selector data emitted by configure. It retains exactly what is needed for
gate/lookup compatibility, while discarding gate polynomials and lookup expressions. -/
structure ConfigureSelectorSummary where
  gates : List Selector := []
  lookups : List LookupSelectorUsage := []

@[ext]
theorem ConfigureSelectorSummary.ext
    {left right : ConfigureSelectorSummary}
    (gates : left.gates = right.gates)
    (lookups : left.lookups = right.lookups) : left = right := by
  cases left
  cases right
  simp_all

/-- Every selector represented by a reduced summary lies below a boundary. -/
def ConfigureSelectorSummary.Bounded
    (summary : ConfigureSelectorSummary) (bound : ℕ) : Prop :=
  (summary.gates.Forall fun gate => gate.index < bound) ∧
    summary.lookups.Forall fun usage =>
      usage.master.index < bound ∧
        usage.auxiliary.Forall (fun selector => selector < bound) ∧
        usage.selectors.Forall fun selector => selector < bound

/-- The selector usages inherited from outside a configure program. A lookup is kept
whole when any of its selectors predates the program, since its master selector is
needed to state lookup compatibility. -/
@[configure_selector_norm, keygen_norm]
def LookupSelectorUsage.HasSelectorBefore
    (usage : LookupSelectorUsage) (boundary : ℕ) : Bool :=
  decide (usage.master.index < boundary) ||
    usage.auxiliary.any (fun selector => selector < boundary) ||
    usage.selectors.any fun selector => selector < boundary

@[configure_selector_norm, keygen_norm]
def ConfigureSelectorSummary.externalAt
    (summary : ConfigureSelectorSummary) (boundary : ℕ) :
    ConfigureSelectorSummary :=
  { gates := summary.gates.filter fun gate => gate.index < boundary
    lookups := summary.lookups.filter fun usage =>
      usage.HasSelectorBefore boundary }

@[configure_selector_norm, keygen_norm]
def ConfigureSelectorSummary.append
    (left right : ConfigureSelectorSummary) : ConfigureSelectorSummary :=
  { gates := left.gates ++ right.gates
    lookups := left.lookups ++ right.lookups }

@[configure_selector_norm, keygen_norm]
theorem ConfigureSelectorSummary.externalAt_append
    (left right : ConfigureSelectorSummary) (boundary : ℕ) :
    (left.append right).externalAt boundary =
      (left.externalAt boundary).append (right.externalAt boundary) := by
  simp [ConfigureSelectorSummary.externalAt,
    ConfigureSelectorSummary.append, List.filter_append]

theorem LookupSelectorUsage.hasSelectorBefore_mono
    {usage : LookupSelectorUsage} {source target : ℕ}
    (hbound : source ≤ target) (hsource : usage.HasSelectorBefore source) :
    usage.HasSelectorBefore target := by
  simp only [LookupSelectorUsage.HasSelectorBefore, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true] at hsource ⊢
  rcases hsource with (hmaster | hauxiliary) | hselector
  · exact Or.inl <| Or.inl (hmaster.trans_le hbound)
  · exact Or.inl <| Or.inr <| hauxiliary.imp fun _ h =>
      ⟨h.1, h.2.trans_le hbound⟩
  · exact Or.inr <| hselector.imp fun _ h =>
      ⟨h.1, h.2.trans_le hbound⟩

theorem ConfigureSelectorSummary.externalAt_externalAt
    (summary : ConfigureSelectorSummary) {source target : ℕ}
    (hbound : source ≤ target) :
    (summary.externalAt target).externalAt source =
      summary.externalAt source := by
  apply ConfigureSelectorSummary.ext
  · simp only [ConfigureSelectorSummary.externalAt]
    rw [List.filter_filter]
    apply List.filter_congr
    intro gate _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, h.trans_le hbound⟩
  · simp only [ConfigureSelectorSummary.externalAt]
    rw [List.filter_filter]
    apply List.filter_congr
    intro usage _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true]
    constructor
    · exact fun h => h.1
    · exact fun h =>
        ⟨h, usage.hasSelectorBefore_mono hbound h⟩

theorem ConfigureSelectorSummary.externalAt_eq_empty_of_fresh
    {summary : ConfigureSelectorSummary} {boundary : ℕ}
    (hgates : summary.gates.Forall fun gate => boundary ≤ gate.index)
    (hlookups : summary.lookups.Forall fun usage =>
      boundary ≤ usage.master.index ∧
        usage.auxiliary.Forall (fun selector => boundary ≤ selector) ∧
        usage.selectors.Forall fun selector => boundary ≤ selector) :
    summary.externalAt boundary = {} := by
  apply ConfigureSelectorSummary.ext
  · simp only [ConfigureSelectorSummary.externalAt]
    apply List.filter_eq_nil_iff.mpr
    intro gate hgate
    have hfresh := List.forall_iff_forall_mem.mp hgates gate hgate
    simp
    omega
  · simp only [ConfigureSelectorSummary.externalAt]
    apply List.filter_eq_nil_iff.mpr
    intro usage husage
    have hfresh := List.forall_iff_forall_mem.mp hlookups usage husage
    intro hbefore
    simp only [LookupSelectorUsage.HasSelectorBefore, Bool.or_eq_true,
      decide_eq_true_eq, List.any_eq_true] at hbefore
    rcases hbefore with (hmaster | hauxiliary) | hselector
    · omega
    · obtain ⟨selector, hselectorMem, hselectorBefore⟩ := hauxiliary
      have hselectorFresh :=
        List.forall_iff_forall_mem.mp hfresh.2.1 selector hselectorMem
      omega
    · obtain ⟨selector, hselectorMem, hselectorBefore⟩ := hselector
      have hselectorFresh :=
        List.forall_iff_forall_mem.mp hfresh.2.2 selector hselectorMem
      omega

def ConfigureDelta.selectorSummary
    (delta : ConfigureDelta F) : ConfigureSelectorSummary :=
  { gates := delta.gates.map Gate.selector
    lookups := delta.lookups.map LookupArgument.selectorUsage }

theorem ConfigureDelta.selectorSummary_externalAt_eq_empty_of_fresh
    {delta : ConfigureDelta F} {boundary : ℕ}
    (hfresh : delta.SelectorsFreshFrom boundary) :
    delta.selectorSummary.externalAt boundary = {} := by
  apply ConfigureSelectorSummary.externalAt_eq_empty_of_fresh
  · simpa [ConfigureDelta.selectorSummary, List.forall_map_iff]
      using hfresh.gates
  · rw [List.forall_iff_forall_mem]
    intro usage husage
    obtain ⟨argument, hargument, rfl⟩ :=
      List.mem_map.mp husage
    have hselectors := List.forall_iff_forall_mem.mp hfresh.lookups
      argument hargument
    have hselectors' :
        boundary ≤ argument.masterSelector.index ∧
          argument.auxiliarySelectorIndices.Forall
            (fun selector => boundary ≤ selector) := by
      simpa [LookupArgument.selectorIndices] using hselectors
    exact ⟨hselectors'.1, hselectors'.2, hselectors⟩

def ConfigureSelectorSummary.CrossCompatible
    (left right : ConfigureSelectorSummary) : Prop :=
  (left.gates.Forall fun gate =>
    right.lookups.Forall (gate.LookupSelectorsCompatible ·)) ∧
  (right.gates.Forall fun gate =>
    left.lookups.Forall (gate.LookupSelectorsCompatible ·)) ∧
  (left.lookups.Forall fun source =>
    right.lookups.Forall source.SelectorsCompatible) ∧
  (right.lookups.Forall fun source =>
    left.lookups.Forall source.SelectorsCompatible)

@[configure_selector_norm, keygen_norm]
theorem listForall_nil {A : Type} (predicate : A → Prop) :
    List.Forall predicate [] := by
  trivial

@[configure_selector_norm, keygen_norm]
theorem listForall_true {A : Type} (values : List A) :
    List.Forall (fun _ => True) values := by
  induction values <;> simp_all [List.Forall]

@[configure_selector_norm, keygen_norm]
theorem ConfigureSelectorSummary.crossCompatible_withoutLookups
    (leftGates rightGates : List Selector) :
    CrossCompatible { gates := leftGates } { gates := rightGates } := by
  simp [CrossCompatible, listForall_true]

@[configure_selector_norm, keygen_norm]
theorem ConfigureSelectorSummary.crossCompatible_empty
    (summary : ConfigureSelectorSummary) :
    summary.CrossCompatible {} := by
  simp [CrossCompatible, listForall_true]

@[configure_selector_norm, keygen_norm]
theorem ConfigureSelectorSummary.empty_crossCompatible
    (summary : ConfigureSelectorSummary) :
    ({} : ConfigureSelectorSummary).CrossCompatible summary := by
  simp [CrossCompatible, listForall_true]

theorem ConfigureSelectorSummary.CrossCompatible.facts
    {left right : ConfigureSelectorSummary}
    (self : left.CrossCompatible right) :
    (left.gates.Forall fun gate =>
      right.lookups.Forall (gate.LookupSelectorsCompatible ·)) ∧
    (right.gates.Forall fun gate =>
      left.lookups.Forall (gate.LookupSelectorsCompatible ·)) ∧
    (left.lookups.Forall fun source =>
      right.lookups.Forall source.SelectorsCompatible) ∧
    (right.lookups.Forall fun source =>
      left.lookups.Forall source.SelectorsCompatible) := by
  exact self

theorem ConfigureSelectorSummary.gate_fresh_of_not_mem_externalAt
    {summary : ConfigureSelectorSummary} {boundary : ℕ}
    {gate : Selector} (hgate : gate ∈ summary.gates)
    (hexternal : gate ∉ (summary.externalAt boundary).gates) :
    boundary ≤ gate.index := by
  simp [ConfigureSelectorSummary.externalAt, hgate] at hexternal
  exact hexternal

theorem ConfigureSelectorSummary.lookup_fresh_of_not_mem_externalAt
    {summary : ConfigureSelectorSummary} {boundary : ℕ}
    {usage : LookupSelectorUsage} (husage : usage ∈ summary.lookups)
    (hexternal : usage ∉ (summary.externalAt boundary).lookups) :
    boundary ≤ usage.master.index ∧
      usage.auxiliary.Forall (fun selector => boundary ≤ selector) ∧
      usage.selectors.Forall fun selector => boundary ≤ selector := by
  constructor
  · by_contra hfresh
    apply hexternal
    simp [ConfigureSelectorSummary.externalAt,
      LookupSelectorUsage.HasSelectorBefore, husage]
    exact Or.inl (by omega)
  constructor
  · rw [List.forall_iff_forall_mem]
    intro selector hselector
    by_contra hfresh
    apply hexternal
    simp [ConfigureSelectorSummary.externalAt,
      LookupSelectorUsage.HasSelectorBefore, husage]
    exact Or.inl <| Or.inr ⟨selector, hselector, by omega⟩
  · rw [List.forall_iff_forall_mem]
    intro selector hselector
    by_contra hfresh
    apply hexternal
    simp [ConfigureSelectorSummary.externalAt,
      LookupSelectorUsage.HasSelectorBefore, husage]
    exact Or.inr ⟨selector, hselector, by omega⟩

/-- Only externally inherited selector usages can interact with an earlier configure
contribution. Fresh selectors are separated from all selectors allocated earlier. -/
theorem ConfigureSelectorSummary.CrossCompatible.of_externalAt
    {left right : ConfigureSelectorSummary} {boundary : ℕ}
    (hleft : left.Bounded boundary)
    (hexternal : left.CrossCompatible (right.externalAt boundary)) :
    left.CrossCompatible right := by
  rcases hleft with ⟨hleftGates, hleftLookups⟩
  rcases hexternal.facts with
    ⟨hleftRightGates, hrightLeftGates,
      hleftRightLookups, hrightLeftLookups⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.forall_iff_forall_mem]
    intro gate hgate
    rw [List.forall_iff_forall_mem]
    intro usage husage
    by_cases hexternalUsage :
        usage ∈ (right.externalAt boundary).lookups
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hleftRightGates gate hgate)
        usage hexternalUsage
    · have hfresh := right.lookup_fresh_of_not_mem_externalAt
          husage hexternalUsage
      unfold Selector.LookupSelectorsCompatible
      constructor
      · rw [List.forall_iff_forall_mem]
        intro selector hselector hequal
        have hselectorFresh := List.forall_iff_forall_mem.mp hfresh.2.1
          selector hselector
        have hgateBound :=
          List.forall_iff_forall_mem.mp hleftGates gate hgate
        omega
      · intro hequal
        have hmasterFresh := hfresh.1
        have hgateBound :=
          List.forall_iff_forall_mem.mp hleftGates gate hgate
        omega
  · rw [List.forall_iff_forall_mem]
    intro gate hgate
    rw [List.forall_iff_forall_mem]
    intro usage husage
    by_cases hexternalGate : gate ∈ (right.externalAt boundary).gates
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hrightLeftGates gate hexternalGate)
        usage husage
    · have hgateFresh := right.gate_fresh_of_not_mem_externalAt
          hgate hexternalGate
      have husageBound :=
        List.forall_iff_forall_mem.mp hleftLookups usage husage
      unfold Selector.LookupSelectorsCompatible
      constructor
      · rw [List.forall_iff_forall_mem]
        intro selector hselector hequal
        have hselectorBound := List.forall_iff_forall_mem.mp husageBound.2.1
          selector hselector
        omega
      · intro hequal
        have hmasterBound := husageBound.1
        omega
  · rw [List.forall_iff_forall_mem]
    intro source hsource
    rw [List.forall_iff_forall_mem]
    intro target htarget
    by_cases hexternalTarget :
        target ∈ (right.externalAt boundary).lookups
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hleftRightLookups source hsource)
        target hexternalTarget
    · have hsourceBound :=
        List.forall_iff_forall_mem.mp hleftLookups source hsource
      have htargetFresh := right.lookup_fresh_of_not_mem_externalAt
        htarget hexternalTarget
      unfold LookupSelectorUsage.SelectorsCompatible
      rw [List.forall_iff_forall_mem]
      intro selector hselector hauxiliary
      have hselectorBound :=
        List.forall_iff_forall_mem.mp hsourceBound.2.2 selector hselector
      have hselectorFresh :=
        List.forall_iff_forall_mem.mp htargetFresh.2.1 selector hauxiliary
      omega
  · rw [List.forall_iff_forall_mem]
    intro source hsource
    rw [List.forall_iff_forall_mem]
    intro target htarget
    by_cases hexternalSource :
        source ∈ (right.externalAt boundary).lookups
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hrightLeftLookups source hexternalSource)
        target htarget
    · have hsourceFresh := right.lookup_fresh_of_not_mem_externalAt
        hsource hexternalSource
      have htargetBound :=
        List.forall_iff_forall_mem.mp hleftLookups target htarget
      unfold LookupSelectorUsage.SelectorsCompatible
      rw [List.forall_iff_forall_mem]
      intro selector hselector hauxiliary
      have hselectorFresh :=
        List.forall_iff_forall_mem.mp hsourceFresh.2.2 selector hselector
      have hselectorBound :=
        List.forall_iff_forall_mem.mp htargetBound.2.1 selector hauxiliary
      omega

@[configure_selector_norm, keygen_norm]
theorem ConfigureDelta.selectorSummary_append
    (left right : ConfigureDelta F) :
    (left.append right).selectorSummary =
      left.selectorSummary.append right.selectorSummary := by
  simp [ConfigureDelta.selectorSummary, ConfigureSelectorSummary.append]

/-- Gate/lookup selector compatibility within one configure contribution. -/
def ConfigureDelta.LookupSelectorsCompatible
    (delta : ConfigureDelta F) : Prop :=
  Halo2.LookupSelectorsCompatible delta.gates delta.lookups

/-- The selector conditions needed when two already-lawful configure contributions
are appended. Keeping these cross terms explicit makes a large configure tree reduce
to small local obligations. -/
def ConfigureDelta.LookupSelectorsCrossCompatible
    (left right : ConfigureDelta F) : Prop :=
  (left.gates.Forall fun gate =>
      right.lookups.Forall (gate.LookupSelectorsCompatible ·)) ∧
  (right.gates.Forall fun gate =>
      left.lookups.Forall (gate.LookupSelectorsCompatible ·)) ∧
  (left.lookups.Forall fun source =>
      right.lookups.Forall source.SelectorsCompatible) ∧
  (right.lookups.Forall fun source =>
      left.lookups.Forall source.SelectorsCompatible)

theorem ConfigureDelta.LookupSelectorsCrossCompatible.ofSelectorSummary
    {left right : ConfigureDelta F}
    (hsummary : left.selectorSummary.CrossCompatible
      right.selectorSummary) :
    left.LookupSelectorsCrossCompatible right := by
  rcases hsummary.facts with ⟨hleftGates, hrightGates,
    hleftLookups, hrightLookups⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [ConfigureDelta.selectorSummary,
      Gate.LookupSelectorsCompatible, LookupArgument.selectorUsage] using
      hleftGates
  · simpa [ConfigureDelta.selectorSummary,
      Gate.LookupSelectorsCompatible, LookupArgument.selectorUsage] using
      hrightGates
  · simpa [ConfigureDelta.selectorSummary,
      LookupArgument.SelectorsCompatible,
      LookupArgument.selectorUsage] using hleftLookups
  · simpa [ConfigureDelta.selectorSummary,
      LookupArgument.SelectorsCompatible,
      LookupArgument.selectorUsage] using hrightLookups

@[simp] theorem ConfigureDelta.empty_lookupSelectorsCrossCompatible
    (delta : ConfigureDelta F) :
    ({} : ConfigureDelta F).LookupSelectorsCrossCompatible delta := by
  unfold ConfigureDelta.LookupSelectorsCrossCompatible
  constructor
  · trivial
  constructor
  · rw [List.forall_iff_forall_mem]
    intros
    trivial
  constructor
  · trivial
  · rw [List.forall_iff_forall_mem]
    intros
    trivial

@[simp] theorem ConfigureDelta.lookupSelectorsCrossCompatible_empty
    (delta : ConfigureDelta F) :
    delta.LookupSelectorsCrossCompatible ({} : ConfigureDelta F) := by
  unfold ConfigureDelta.LookupSelectorsCrossCompatible
  constructor
  · rw [List.forall_iff_forall_mem]
    intros
    trivial
  constructor
  · trivial
  constructor
  · rw [List.forall_iff_forall_mem]
    intros
    trivial
  · trivial

theorem ConfigureDelta.lookupSelectorsCompatible_append
    (left right : ConfigureDelta F)
    (hleft : left.LookupSelectorsCompatible)
    (hright : right.LookupSelectorsCompatible)
    (hcross : left.LookupSelectorsCrossCompatible right) :
    (left.append right).LookupSelectorsCompatible := by
  rcases hleft with ⟨hleftGates, hleftLookups⟩
  rcases hright with ⟨hrightGates, hrightLookups⟩
  rcases hcross with
    ⟨hleftRightGates, hrightLeftGates,
      hleftRightLookups, hrightLeftLookups⟩
  constructor
  · rw [ConfigureDelta.gates_append,
      List.forall_iff_forall_mem]
    intro gate hgate
    rw [ConfigureDelta.lookups_append,
      List.forall_iff_forall_mem]
    intro lookup hlookup
    rw [List.mem_append] at hgate hlookup
    rcases hgate with hgate | hgate <;>
      rcases hlookup with hlookup | hlookup
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hleftGates gate hgate)
        lookup hlookup
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hleftRightGates gate hgate)
        lookup hlookup
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hrightLeftGates gate hgate)
        lookup hlookup
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hrightGates gate hgate)
        lookup hlookup
  · rw [ConfigureDelta.lookups_append,
      List.forall_iff_forall_mem]
    intro source hsource
    rw [List.forall_iff_forall_mem]
    intro target htarget
    rw [List.mem_append] at hsource htarget
    rcases hsource with hsource | hsource <;>
      rcases htarget with htarget | htarget
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hleftLookups source hsource)
        target htarget
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hleftRightLookups source hsource)
        target htarget
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hrightLeftLookups source hsource)
        target htarget
    · exact List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hrightLookups source hsource)
        target htarget

/-- Selector allocation remains true when the available count grows. -/
theorem ConfigureDelta.SelectorsAllocated.mono
    {delta : ConfigureDelta F} {source target : ℕ}
    (hallocated : delta.SelectorsAllocated source)
    (hcount : source ≤ target) :
    delta.SelectorsAllocated target where
  gates := hallocated.gates.imp fun _ hgate => hgate.trans_le hcount
  lookupMasters :=
    hallocated.lookupMasters.imp fun _ hmaster => hmaster.trans_le hcount
  lookups := hallocated.lookups.trans hcount

/-- The empty configure contribution allocates no selectors. -/
theorem ConfigureDelta.SelectorsAllocated.empty (numSelectors : ℕ) :
    ({} : ConfigureDelta F).SelectorsAllocated numSelectors := by
  constructor
  · simp
  · simp
  · simp [lookupInputSelectorBound]

/-- Allocation laws compose across append-only configure deltas. -/
theorem ConfigureDelta.SelectorsAllocated.append
    {left right : ConfigureDelta F} {numSelectors : ℕ}
    (hleft : left.SelectorsAllocated numSelectors)
    (hright : right.SelectorsAllocated numSelectors) :
    (left.append right).SelectorsAllocated numSelectors where
  gates := by
    simpa only [ConfigureDelta.gates_append, List.forall_append] using
      And.intro hleft.gates hright.gates
  lookupMasters := by
    simpa only [ConfigureDelta.lookups_append, List.forall_append] using
      And.intro hleft.lookupMasters hright.lookupMasters
  lookups := by
    simp only [ConfigureDelta.lookups_append,
      lookupInputSelectorBound_append]
    exact max_le hleft.lookups hright.lookups

/-- Allocation bounds cover every selector represented in the reduced summary. -/
theorem ConfigureDelta.SelectorsAllocated.selectorsBounded
    {delta : ConfigureDelta F} {numSelectors : ℕ}
    (hallocated : delta.SelectorsAllocated numSelectors) :
    delta.SelectorsBounded numSelectors := by
  constructor
  · exact hallocated.gates
  · rw [List.forall_iff_forall_mem]
    intro argument hargument
    rw [List.forall_iff_forall_mem]
    intro selector hselector
    rw [LookupArgument.selectorIndices, List.mem_cons] at hselector
    rcases hselector with rfl | hauxiliary
    · exact List.forall_iff_forall_mem.mp hallocated.lookupMasters
        argument hargument
    · simp only [LookupArgument.auxiliarySelectorIndices,
        List.mem_filter, List.mem_flatMap] at hauxiliary
      rcases hauxiliary.1 with ⟨expression, hexpression, hselector⟩
      exact (expression.lt_selectorBound_of_mem_selectorIndices hselector).trans_le
        ((expression.selectorBound_le_lookupInputSelectorBound
          hargument hexpression).trans hallocated.lookups)

theorem ConfigureDelta.selectorSummary_bounded
    {delta : ConfigureDelta F} {bound : ℕ}
    (hbounded : delta.SelectorsBounded bound) :
    delta.selectorSummary.Bounded bound := by
  constructor
  · simpa [ConfigureDelta.selectorSummary] using hbounded.gates
  · rw [ConfigureDelta.selectorSummary, List.forall_map_iff,
      List.forall_iff_forall_mem]
    intro argument hargument
    have hargumentBound :=
      List.forall_iff_forall_mem.mp hbounded.lookups argument hargument
    refine ⟨?_, ?_, ?_⟩
    · exact List.forall_iff_forall_mem.mp hargumentBound
        argument.masterSelector.index argument.masterSelector_mem_selectorIndices
    · rw [List.forall_iff_forall_mem]
      intro selector hselector
      exact List.forall_iff_forall_mem.mp hargumentBound selector (by
        simp only [LookupArgument.selectorIndices, List.mem_cons]
        exact Or.inr hselector)
    · exact hargumentBound

@[simp] theorem ConfigureDelta.gates_queriedCells
    (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells cells).gates = [] := by
  unfold ConfigureDelta.queriedCells
  have aux :
      ∀ (remaining : List (Expression F Query)) (delta : ConfigureDelta F),
        (remaining.foldl
          (fun current cell =>
            current.append (ConfigureDelta.queriedCell cell))
          delta).gates = delta.gates := by
    intro remaining
    induction remaining with
    | nil =>
        intro delta
        rfl
    | cons cell remaining ih =>
        intro delta
        rw [List.foldl_cons, ih]
        cases cell with
        | var query =>
            cases query <;>
              simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
        | const
        | add
        | mul =>
            simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
  exact aux cells {}

@[simp] theorem ConfigureDelta.lookups_queriedCells
    (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells cells).lookups = [] := by
  unfold ConfigureDelta.queriedCells
  have aux :
      ∀ (remaining : List (Expression F Query)) (delta : ConfigureDelta F),
        (remaining.foldl
          (fun current cell =>
            current.append (ConfigureDelta.queriedCell cell))
          delta).lookups = delta.lookups := by
    intro remaining
    induction remaining with
    | nil =>
        intro delta
        rfl
    | cons cell remaining ih =>
        intro delta
        rw [List.foldl_cons, ih]
        cases cell with
        | var query =>
            cases query <;>
              simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
        | const
        | add
        | mul =>
            simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
  exact aux cells {}

@[simp] theorem ConfigureDelta.constants_queriedCells
    (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells cells).constants = [] := by
  unfold ConfigureDelta.queriedCells
  have aux :
      ∀ (remaining : List (Expression F Query)) (delta : ConfigureDelta F),
        (remaining.foldl
          (fun current cell =>
            current.append (ConfigureDelta.queriedCell cell))
          delta).constants = delta.constants := by
    intro remaining
    induction remaining with
    | nil =>
        intro delta
        rfl
    | cons cell remaining ih =>
        intro delta
        rw [List.foldl_cons, ih]
        cases cell with
        | var query =>
            cases query <;>
              simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
        | const
        | add
        | mul =>
            simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
  exact aux cells {}

@[simp] theorem Configure.delta_createGate_constants
    (gate : Gate F) (counts : ConfigureCounts) :
    ((createGate gate).delta counts).constants = [] := by
  simp [Configure.delta, createGate]

theorem ConfigureDelta.permutationRequests_queriedCells
    (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells cells).permutationRequests = [] := by
  unfold ConfigureDelta.queriedCells
  have aux :
      ∀ (remaining : List (Expression F Query)) (delta : ConfigureDelta F),
        (remaining.foldl
          (fun current cell =>
            current.append (ConfigureDelta.queriedCell cell))
          delta).permutationRequests = delta.permutationRequests := by
    intro remaining
    induction remaining with
    | nil =>
        intro delta
        rfl
    | cons cell remaining ih =>
        intro delta
        rw [List.foldl_cons, ih]
        cases cell with
        | var query =>
            cases query <;>
              simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
        | const
        | add
        | mul =>
            simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
  exact aux cells {}

theorem foldlTableDelta_gates
    (tables : List TableColumn) (delta : ConfigureDelta F) :
    (tables.foldl
      (fun current table =>
        current.append { fixedQueries := [(table.inner, 0)] })
      delta).gates = delta.gates := by
  induction tables generalizing delta with
  | nil => rfl
  | cons table tables ih =>
      rw [List.foldl_cons, ih]
      simp [ConfigureDelta.append]

theorem foldlTableDelta_lookups
    (tables : List TableColumn) (delta : ConfigureDelta F) :
    (tables.foldl
      (fun current table =>
        current.append { fixedQueries := [(table.inner, 0)] })
      delta).lookups = delta.lookups := by
  induction tables generalizing delta with
  | nil => rfl
  | cons table tables ih =>
      rw [List.foldl_cons, ih]
      simp [ConfigureDelta.append]

private theorem foldlTableDelta_constants
    (tables : List TableColumn) (delta : ConfigureDelta F) :
    (tables.foldl
      (fun current table =>
        current.append { fixedQueries := [(table.inner, 0)] })
      delta).constants = delta.constants := by
  induction tables generalizing delta with
  | nil => rfl
  | cons table tables ih =>
      rw [List.foldl_cons, ih]
      simp [ConfigureDelta.append]

@[simp] theorem Configure.delta_lookup_gates
    (queriedCells : List (Expression F Query))
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    ((lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors).delta counts).gates = [] := by
  unfold Configure.delta lookup
  simp [ConfigureDelta.fixedQueriesOfColumns, foldlTableDelta_gates]

@[simp] theorem Configure.delta_lookup_constants
    (queriedCells : List (Expression F Query))
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    ((lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors).delta counts).constants = [] := by
  unfold Configure.delta lookup
  simp [ConfigureDelta.fixedQueriesOfColumns, foldlTableDelta_constants]

@[simp, keygen_norm] theorem Configure.delta_enableConstant_gates
    (column : Column .fixed) (counts : ConfigureCounts) :
    ((enableConstant (F := F) column).delta counts).gates = [] :=
  rfl

@[simp, keygen_norm] theorem Configure.delta_enableConstant_lookups
    (column : Column .fixed) (counts : ConfigureCounts) :
    ((enableConstant (F := F) column).delta counts).lookups = [] :=
  rfl

@[simp] theorem Configure.lookupInputSelectorBound_delta_lookup
    (queriedCells : List (Expression F Query))
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    lookupInputSelectorBound
        ((lookup queriedCells masterSelector tableMap hqueries
          hnoSimpleSelectors).delta counts).lookups =
      ((tableMap.map Prod.fst).map Expression.selectorBound).foldr max 0 := by
  unfold Configure.delta lookup lookupInputSelectorBound
    LookupArgument.inputSelectorBound
  simp [ConfigureDelta.fixedQueriesOfColumns, foldlTableDelta_lookups]

end Halo2
