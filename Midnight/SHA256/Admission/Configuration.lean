import Midnight.SHA256.Configure
import Midnight.SHA256.Admission.ConfigurationFacts
import Midnight.Chips.CertifiedCircuit

/-! Kernel-checked native configuration and its existing Clean semantic view.
This is one component of admission; it does not certify the operation layout. -/
namespace Midnight.SHA256.Admission
open Halo2 Midnight.Keygen
set_option Elab.async false
attribute [local irreducible] configured cleanGates cleanLookups

set_option maxRecDepth 100000 in
private theorem sourceState : configured.selectorFixedStart = none := by decide +kernel
set_option maxRecDepth 100000 in
private theorem noErrors : configured.errors = #[] := by decide +kernel
set_option maxRecDepth 100000 in
private theorem adviceQueries : QueryLayout.Allocated configured.numAdvice configured.adviceQueries := by decide +kernel
set_option maxRecDepth 100000 in
private theorem fixedQueries : QueryLayout.Allocated configured.numFixed configured.fixedQueries := by decide +kernel
set_option maxRecDepth 100000 in
private theorem instanceQueries : QueryLayout.Allocated configured.numInstance configured.instanceQueries := by decide +kernel

private theorem no_trash : configured.trashcans = #[] := by decide +kernel
private theorem adviceLayout : configured.adviceQueries = #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (0, 1), (1, 1), (2, 1), (5, 0), (6, 0), (7, 0), (3, -1), (4, -1), (0, -1),
  (1, -1), (3, 1), (4, 1), (6, -1), (6, 1), (2, -1), (7, -1), (5, -1), (5, 1), (7, 1)] := by decide +kernel

private theorem fixedLayout : configured.fixedQueries = #[(9, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (0, 0), (1, 0), (2, 0), (3, 0), (10, 0), (11, 0), (12, 0), (13, 0),
  (14, 0), (15, 0)] := by decide +kernel

private theorem instanceLayout : configured.instanceQueries = #[(0, 0), (1, 0)] := by decide +kernel

private theorem selectorCount : configured.numSelectors = 16 := by decide +kernel

private def registrationCS : CS :=
  { numSelectors := 16,
    adviceQueries := #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (0, 1), (1, 1), (2, 1), (5, 0), (6, 0), (7, 0), (3, -1), (4, -1), (0, -1),
  (1, -1), (3, 1), (4, 1), (6, -1), (6, 1), (2, -1), (7, -1), (5, -1), (5, 1), (7, 1)],
    fixedQueries := #[(9, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (0, 0), (1, 0), (2, 0), (3, 0), (10, 0), (11, 0), (12, 0), (13, 0),
  (14, 0), (15, 0)],
    instanceQueries := #[(0, 0), (1, 0)] }

private theorem registeredQuery : configured.RegistersQuery = registrationCS.RegistersQuery := by
  funext query
  cases query <;> simp only [CS.RegistersQuery, adviceLayout, fixedLayout, instanceLayout, registrationCS]

set_option maxRecDepth 100000 in
private theorem gateAllocation : configured.gates.toList.Forall
    (fun gate => gate.selectorUses.Forall (·.index < configured.numSelectors) ∧
      gate.queries.toList.Forall configured.RegistersQuery) := by
  rw [registeredQuery, selectorCount]
  decide +kernel

private theorem gatesLawful : configured.gateSpecs.Forall (GateSpec.Lawful configured) := by
  simp only [CS.gateSpecs, no_trash, Array.append_empty]
  apply List.forall_iff_forall_mem.mpr
  intro gate member
  have valid := List.all_eq_true.mp configured_gates_valid gate member
  have allocated := List.forall_iff_forall_mem.mp gateAllocation gate member
  exact gateLawful_of_valid _ _ valid allocated.1 allocated.2
set_option maxRecDepth 100000 in
private theorem lookupsLawful : configured.lookups.toList.Forall (BatchedLookup.Lawful configured) := by
  unfold BatchedLookup.Lawful Halo2.Expression.Registered
  rw [registeredQuery]
  decide +kernel
set_option maxRecDepth 100000 in
private theorem permutationLawful : configured.permutation.toList.Nodup ∧
    configured.permutation.toList.Forall configured.RegistersPermutation := by decide +kernel
set_option maxRecDepth 100000 in
private theorem trashComplex : configured.trashcans.toList.Forall (fun g => g.selector.simple = false) := by decide +kernel
set_option maxRecDepth 100000 in
private theorem trashNonempty : configured.trashcans.toList.Forall (fun g => 0 < g.constraints.size) := by decide +kernel
set_option maxRecDepth 100000 in
private theorem trashSelected : configured.trashcans.toList.Forall (fun g => g.raw = false) := by decide +kernel
set_option maxRecDepth 100000 in
private theorem selectorKinds : configured.selectorUses.Forall (fun q =>
    configured.selectorUses.Forall (fun r => q.index = r.index → q.simple = r.simple)) := by decide +kernel

set_option maxRecDepth 100000 in
private theorem constants : configured.ConstantsWellFormed := by decide +kernel

set_option maxRecDepth 100000 in
private theorem validated : configured.validate.isOk = true := by decide +kernel

theorem configuration : configured.WellFormed :=
  ⟨sourceState, noErrors, adviceQueries, fixedQueries, instanceQueries,
    gatesLawful, lookupsLawful, permutationLawful, trashComplex, trashNonempty,
    trashSelected, selectorKinds, constants, validated⟩

set_option maxRecDepth 100000 in
theorem minimumRows : configured.blindingFactors + 3 ≤ 2 ^ 13 := by decide +kernel

def checked : CS.Checked := ⟨configured, configuration⟩

/-- Every SHA gate is owned: none has Rust's every-row meaning. -/
theorem gatesOwned : configured.gateSpecs.all (fun g => !g.rows) = true := by
  have owned : configured.gates.toList.all (fun g => !g.rows) = true := by decide +kernel
  simpa only [CS.gateSpecs, no_trash, Array.append_empty] using owned

/-- Every SHA lookup is owned: none has Rust's every-row meaning. -/
theorem lookupsOwned : configured.lookups.toList.all (·.owned) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- SHA uses all its selectors, so it has no unused-selector handles. -/
theorem selectorsUsed : configured.unusedSelectors = [] := by decide +kernel

theorem gates : checked.toCleanDelta.gates = cleanGates := by
  have noHandles : checked.rowsHandles = [] := checked.rowsHandles_of_owned gatesOwned
  have noLookupHandles : checked.lookupHandles = [] := checked.lookupHandles_of_owned lookupsOwned
  have noUnusedHandles : checked.unusedHandles = [] := checked.unusedHandles_of_used selectorsUsed
  change checked.gateHandles ++ checked.rowsHandles ++ checked.lookupHandles ++ checked.unusedHandles = _
  rw [noHandles, noLookupHandles, noUnusedHandles, List.append_nil, List.append_nil, List.append_nil]
  unfold cleanGates
  dsimp only [checked, CS.Checked.gateHandles, CS.gateSpecs]
  have same : (configured.gates ++ configured.trashcans).toList = configured.gates.toList := by
    rw [no_trash, Array.append_empty]
  rw [List.attach_congr same, List.map_map]
  rfl

theorem lookups : checked.toCleanDelta.lookups = cleanLookups := by
  unfold cleanLookups
  rfl

theorem permutationColumns :
    (Chips.CertifiedCircuit.permutationColumns configured).map Halo2.Layout.ColRef.toAny =
      configured.permutation.toList := by
  unfold Chips.CertifiedCircuit.permutationColumns
  simp only [List.map_map]
  conv_rhs => rw [← List.map_id configured.permutation.toList]
  apply List.map_congr_left
  intro column _
  cases column with
  | mk kind index => cases kind <;> rfl

theorem counts : configured.counts = ⟨8, 16, 2, 16⟩ := by
  have checked : configured.numAdvice = 8 ∧ configured.numFixed = 16 ∧
      configured.numInstance = 2 ∧ configured.numSelectors = 16 := by decide +kernel
  unfold CS.counts
  rw [checked.1, checked.2.1, checked.2.2.1, checked.2.2.2]

theorem usableRows : (Chips.CertifiedCircuit.layoutConfig configured 13).usableRows = 8183 := by
  decide +kernel

theorem constantColumn : configured.constantColumn = none := by decide +kernel

theorem layoutConstant : (Chips.CertifiedCircuit.layoutConfig configured 13).constant = none :=
  constantColumn

end Midnight.SHA256.Admission
