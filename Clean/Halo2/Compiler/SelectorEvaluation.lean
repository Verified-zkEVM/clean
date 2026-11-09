import Clean.Halo2.Compiler.GateOperations
import Clean.Halo2.Keygen.GateProjection

/-! # Semantics of packed selectors in a row assignment -/

variable {F : Type} [FiniteField F]

namespace Halo2

set_option maxHeartbeats 20000

/-- Every selector-compression entry uses a valid, field-distinct root. -/
def SelectorRootsWellFormed (F : Type) [Field F] (map : SelCompressMap) : Prop :=
  ∀ {selector : ℕ} {compressed : SelCompress},
    map.lookup selector = some compressed →
      1 ≤ compressed.assignedRoot ∧
      compressed.assignedRoot ≤ compressed.combinationLen ∧
      compressed.combinationLen < ringChar F

/--
The packed fixed columns realize the compression map on every selector activation
derived from synthesis and placement.
-/
def RealizesSelectorActivations
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (environment : Environment F) : Prop :=
  ∀ {selector row : ℕ} {compressed : SelCompress},
    (selector, row) ∈ activationRows →
    map.lookup selector = some compressed →
      environment.fixed ⟨compressed.packedCol⟩ row =
        (compressed.assignedRoot : F)

/--
The selector-compression replacement is nonzero when its packed fixed cell holds
its assigned root.  The only field-specific premise is that the combination length
is below the field characteristic, making its small natural roots injective in `F`.
-/
theorem selectorScale_ne_zero_of_root
    (compressed : SelCompress) (valuation : Query → F)
    (hvalue : valuation (.fixed ⟨compressed.packedCol⟩ 0) =
      (compressed.assignedRoot : F))
    (hpositive : 1 ≤ compressed.assignedRoot)
    (hrootBound :
      compressed.assignedRoot ≤ compressed.combinationLen)
    (hlengthBound :
      compressed.combinationLen < ringChar F) :
    (selReplacement compressed).eval valuation ≠ 0 := by
  apply selReplacement_eval_of_root compressed valuation
    hvalue hpositive hrootBound
  intro left right hleft hright heq
  have hleftOrder : left < ringChar F := by
    omega
  have hrightOrder : right < ringChar F := by
    omega
  have hmod := (CharP.cast_eq_iff_mod_eq F (ringChar F)).mp heq
  simpa only [Nat.mod_eq_of_lt hleftOrder, Nat.mod_eq_of_lt hrightOrder] using hmod

/-- Environment spelling of `selectorScale_ne_zero_of_root`. -/
theorem selectorScale_ne_zero_of_environment
    (compressed : SelCompress) (environment : Environment F)
    (selectors : ℕ → F) (row : ℕ)
    (hvalue : environment.fixed ⟨compressed.packedCol⟩ row =
      (compressed.assignedRoot : F))
    (hpositive : 1 ≤ compressed.assignedRoot)
    (hrootBound :
      compressed.assignedRoot ≤ compressed.combinationLen)
    (hlengthBound :
      compressed.combinationLen < ringChar F) :
    (selReplacement compressed).eval
      (Query.eval environment selectors row) ≠ 0 := by
  apply selectorScale_ne_zero_of_root compressed
    (Query.eval environment selectors row)
    _ hpositive hrootBound hlengthBound
  simpa [Query.eval] using hvalue

/--
Circuit-derived activation placement and packed fixed data make the selector scale
nonzero at every extracted enabled gate.
-/
theorem selectorScale_ne_zero_of_enabledGate
    (map : SelCompressMap) (starts : List ℕ)
    (operations : Operations F) (i : RegionIndex)
    (environment : Environment F) (selectors : ℕ → F)
    (hroots : SelectorRootsWellFormed F map)
    (hfixed : RealizesSelectorActivations map
      (activations starts (indexedRegions operations i).1) environment)
    {enabled : EnabledGate F}
    (henabled : enabled ∈ operationEnabledGates operations i)
    {compressed : SelCompress}
    (hcompressed :
      map.lookup enabled.gate.selector.index = some compressed) :
    (selReplacement compressed).eval
      (Query.eval environment selectors
        (starts.getD enabled.region 0 + enabled.row)) ≠ 0 := by
  have hactivation :=
    mem_activations_of_mem_operationEnabledGate starts henabled
  have hvalue := hfixed hactivation hcompressed
  obtain ⟨hpositive, hrootBound, hlengthBound⟩ :=
    hroots hcompressed
  exact selectorScale_ne_zero_of_environment
    compressed environment selectors
    (starts.getD enabled.region 0 + enabled.row)
    hvalue hpositive hrootBound hlengthBound

end Halo2
