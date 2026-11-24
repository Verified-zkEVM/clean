import Midnight.SHA256.Configure
import Midnight.SHA256.SynthesisLayout
import Midnight.Chips.OperationsLawful
import Midnight.Chips.CopyLawful
import Midnight.Chips.SynthesisShapeLawful

/-! Closure of the actual source activation callback: enabling one selector emits
all its native Clean gates and lookup tuples, rather than an arbitrary subset. -/
namespace Midnight.SHA256.Admission
open Halo2 Chips.OperationsLawful
attribute [local irreducible] cleanGates cleanLookups Synthesis.schedule

private theorem localActivation_source (body : RegionOperations F) (selector row : Nat)
    (active : (selector, row) ∈ localActivations body) :
    ∃ operation ∈ body, operation.ActivatesSelectorAt selector row := by
  obtain ⟨index, source, operation, localRow, region, member, enabled, absolute⟩ :=
    (mem_activations_iff [0] [(0,body)] selector row).mp active
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp region)
  have same : row = localRow := by simpa using absolute
  subst localRow
  exact ⟨operation, member, enabled⟩

private theorem activation_index (s atRow selector row : Nat)
    (active : (selector, row) ∈ localActivations (activation s atRow)) :
    selector = s ∧ row = atRow := by
  obtain ⟨operation, member, enabled⟩ := localActivation_source _ _ _ active
  simp only [activation, List.mem_append, List.mem_map, List.mem_filter] at member
  rcases member with ⟨gate,⟨_,hs⟩,rfl⟩ | ⟨lookup,⟨_,_⟩,rfl⟩
  · have same : gate.selector.index = s := beq_iff_eq.mp hs
    simpa [RegionOperation.ActivatesSelectorAt, same, eq_comm] using enabled
  · simpa [RegionOperation.ActivatesSelectorAt, SelectorEnabledAtIndex, eq_comm] using enabled

theorem activation_closed (selector row : Nat) :
    ActivationClosed cleanGates cleanLookups (activation selector row) := by
  apply List.forall_iff_forall_mem.mpr
  rintro ⟨s,r⟩ member
  obtain ⟨hs,hr⟩ := activation_index selector row s r member
  subst s
  subst r
  constructor
  · apply List.forall_iff_forall_mem.mpr
    intro gate registered _ same
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨gate, List.mem_filter.mpr ⟨registered, beq_iff_eq.mpr same⟩, rfl⟩
  · apply List.forall_iff_forall_mem.mpr
    intro lookup registered same
    refine ⟨[⟨selector,false⟩], List.mem_append_right _ ?_⟩
    apply List.mem_map.mpr
    exact ⟨lookup, List.mem_filter.mpr ⟨registered, beq_iff_eq.mpr same⟩, rfl⟩

theorem activation_onlyEnables : Chips.SynthesisShapeLawful.OnlyEnables activation := by
  intro selector row
  apply List.forall_iff_forall_mem.mpr
  intro operation member
  simp only [activation, List.mem_append, List.mem_map, List.mem_filter] at member
  rcases member with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> trivial

private theorem localActivations_append (left right : RegionOperations F) :
    localActivations (left ++ right) = localActivations left ++ localActivations right := by
  simp [localActivations, Halo2.activations, List.flatMap_append]

private theorem activationClosed_append (left right : RegionOperations F)
    (hl : ActivationClosed cleanGates cleanLookups left)
    (hr : ActivationClosed cleanGates cleanLookups right) :
    ActivationClosed cleanGates cleanLookups (left ++ right) := by
  apply List.forall_iff_forall_mem.mpr
  intro active member
  rw [localActivations_append, List.mem_append] at member
  rcases member with member | member
  · have closed := List.forall_iff_forall_mem.mp hl active member
    constructor
    · exact closed.1.imp fun gate hgate hn hs =>
        List.mem_append_left right (hgate hn hs)
    · exact closed.2.imp fun lookup hlookup hs => by
        obtain ⟨enabled, member⟩ := hlookup hs
        exact ⟨enabled, List.mem_append_left right member⟩
  · have closed := List.forall_iff_forall_mem.mp hr active member
    constructor
    · exact closed.1.imp fun gate hgate hn hs =>
        List.mem_append_right left (hgate hn hs)
    · exact closed.2.imp fun lookup hlookup hs => by
        obtain ⟨enabled, member⟩ := hlookup hs
        exact ⟨enabled, List.mem_append_right left member⟩

theorem lowerRegion_activationClosed (instructions : List Chips.Synthesis.Instruction) :
    ActivationClosed cleanGates cleanLookups
      (Chips.SynthesisShapeLawful.lowerRegion activation instructions) := by
  induction instructions with
  | nil => simp [Chips.SynthesisShapeLawful.lowerRegion, ActivationClosed,
      localActivations, Halo2.activations]
  | cons instruction rest ih =>
    rw [Chips.SynthesisShapeLawful.lowerRegion, List.flatMap_cons]
    apply activationClosed_append _ _ ?_ ih
    cases instruction with
    | selector selector row => exact activation_closed selector row
    | advice column row | fixed column row value | copy left right =>
      simp [Chips.SynthesisShapeLawful.lowerInstruction, ActivationClosed,
        localActivations, Halo2.activations]

theorem lowerRegion_noConstants (instructions : List Chips.Synthesis.Instruction) :
    Chips.CopyLawful.RegionNoDeferredConstants
      (Chips.SynthesisShapeLawful.lowerRegion activation instructions) := by
  intro cell value member
  obtain ⟨instruction, _, lowered⟩ := List.mem_flatMap.mp member
  cases instruction with
  | selector selector row =>
    have enabled := List.forall_iff_forall_mem.mp
      (activation_onlyEnables selector row) _ lowered
    exact enabled
  | advice column row | fixed column row value | copy left right =>
    simp [Chips.SynthesisShapeLawful.lowerInstruction] at lowered

private theorem source_region (name : String) (body : RegionOperations F)
    (member : .region name body ∈ Synthesis.operations activation) :
    ∃ instructions : List Chips.Synthesis.Instruction,
      body = Chips.SynthesisShapeLawful.lowerRegion activation instructions := by
  rcases List.mem_append.mp member with lowered | table
  · obtain ⟨step, _, equality⟩ := List.mem_map.mp lowered
    cases step with
    | publicInput cell row => contradiction
    | region sourceName instructions =>
      obtain ⟨rfl,rfl⟩ := Operation.region.inj equality
      exact ⟨instructions.toList, rfl⟩
  · simp only [Synthesis.tableOperations, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, or_self] at table

theorem source_activationClosed (index : Nat) (body : RegionOperations F)
    (member : (index,body) ∈ (indexedRegions (Synthesis.operations activation) 0).1) :
    ActivationClosed cleanGates cleanLookups body := by
  obtain ⟨name, source⟩ := exists_region_mem_of_mem_indexedRegions _ _ member
  obtain ⟨instructions, rfl⟩ := source_region name body source
  exact lowerRegion_activationClosed instructions

theorem source_noConstants : Chips.CopyLawful.NoDeferredConstants (Synthesis.operations activation) := by
  intro name body member
  obtain ⟨instructions, rfl⟩ := source_region name body member
  exact lowerRegion_noConstants instructions

private theorem lowerRegion_noInstance (instructions : List Chips.Synthesis.Instruction) :
    ∀ cell column row, .constrainInstance cell column row ∉
      Chips.SynthesisShapeLawful.lowerRegion activation instructions := by
  intro cell column row member
  obtain ⟨instruction, _, lowered⟩ := List.mem_flatMap.mp member
  cases instruction with
  | selector selector atRow =>
    exact List.forall_iff_forall_mem.mp (activation_onlyEnables selector atRow) _ lowered
  | advice column row | fixed column row value | copy left right =>
    simp [Chips.SynthesisShapeLawful.lowerInstruction] at lowered

/-- The schedule's instance copies are all layouter-level, never inside a region. -/
theorem source_instanceCopies : (indexedRegions (Synthesis.operations activation) 0).1.Forall
    fun (region, body) => Chips.OperationsLawful.instanceCopiesLocal region body = true := by
  apply List.forall_iff_forall_mem.mpr
  rintro ⟨index, body⟩ member
  obtain ⟨name, source⟩ := exists_region_mem_of_mem_indexedRegions _ _ member
  obtain ⟨instructions, rfl⟩ := source_region name body source
  apply List.all_eq_true.mpr
  intro op present
  cases op with
  | constrainInstance cell column row => exact absurd present (lowerRegion_noInstance instructions cell column row)
  | _ => rfl

theorem lowerRegion_lookup_shape (instructions : List Chips.Synthesis.Instruction)
    (lookup : LookupArgument F) (enabled : List Selector) (row : Nat)
    (member : .enableLookup lookup enabled row ∈
      Chips.SynthesisShapeLawful.lowerRegion activation instructions) :
    enabled = [lookup.masterSelector.toSelector] := by
  obtain ⟨instruction, _, lowered⟩ := List.mem_flatMap.mp member
  cases instruction with
  | advice column row | fixed column row value | copy left right =>
    simp [Chips.SynthesisShapeLawful.lowerInstruction] at lowered
  | selector selector atRow =>
    simp only [Chips.SynthesisShapeLawful.lowerInstruction, activation, List.mem_append,
      List.mem_map, List.mem_filter] at lowered
    rcases lowered with ⟨gate,_,impossible⟩ | ⟨source,⟨_,same⟩,equal⟩
    · contradiction
    · obtain ⟨rfl,rfl,_⟩ := RegionOperation.enableLookup.inj equal
      have same : source.masterSelector.index = selector := beq_iff_eq.mp same
      simp only [← same, ComplexSelector.toSelector]

theorem source_lookup_shape (index : Nat) (body : RegionOperations F)
    (region : (index,body) ∈ (indexedRegions (Synthesis.operations activation) 0).1)
    (lookup : LookupArgument F) (enabled : List Selector) (row : Nat)
    (member : .enableLookup lookup enabled row ∈ body) :
    enabled = [lookup.masterSelector.toSelector] := by
  obtain ⟨name, source⟩ := exists_region_mem_of_mem_indexedRegions _ _ region
  obtain ⟨instructions, rfl⟩ := source_region name body source
  exact lowerRegion_lookup_shape instructions lookup enabled row member

end Midnight.SHA256.Admission
