import Midnight.Chips.Usize

/-! Two conditions the key derivation checks beyond Rust's. Rust keeps the last of several writes
to one fixed cell (keygen.rs:116-174), while Clean's `assignFixed` and `loadTable` require every
write, so with two different writes to a cell Rust would key a circuit whose `Constraints` no
environment meets. And each deferred constant must sit, with its value, on an equality column
where the copy list puts it. Both are decided on the certified (`Nat`) layout, which the key's
(`Usize.layout`) must equal: they differ only if an offset or V1 area wraps. `keyed` is the
three together, which `deriveFromCertificate` checks before deriving a key. -/

deriving instance DecidableEq for Midnight.Chips.Layout.DerivedLayout

namespace Midnight.Chips.KeyChecks
open Halo2 Midnight.Keygen

/-- The certified layout's fixed writes, then its selector columns' 1s. -/
def writes (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) :
    List LayoutLawful.Write :=
  Layout.sourceFixedWrites ops (CertifiedCircuit.layoutConfig source k) planner ++
    LayoutLawful.selectorWrites source.numFixed
      (Layout.sourceActivations ops source.constantColumn planner)

/-- The certified layout's fixed matrix, selector columns included. -/
def matrix (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) :
    Array (Array Nat) :=
  (LayoutLawful.dense (2 ^ k) (source.numFixed + source.numSelectors)
    (writes source ops k planner)).toArray.map List.toArray

/-- A cell of a fixed matrix, 0 outside it. -/
def cell (fixed : Array (Array Nat)) (column row : Nat) : Nat :=
  (fixed[column]?.bind (·[row]?)).getD 0

/-- The certified layout, as `CertifiedLayout.toDerivedLayout` builds it, without the
certificate. -/
def certified (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) :
    Layout.DerivedLayout :=
  Layout.derivedLayout ops (CertifiedCircuit.permutationColumns source)
    (CertifiedCircuit.layoutConfig source k) planner

theorem toDerivedLayout_eq {source : CS} {ops : Operations F} {k : Nat}
    {planner : Layout.Planner} (cert : CertifiedCircuit.Certificate source ops k planner) :
    cert.toDerivedLayout = certified source ops k planner := rfl

/-- Every fixed write is what the matrix keeps for its cell, so no two writes to a cell differ
(`agree`). -/
def fixedConsistent (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) :
    Bool :=
  let fixed := matrix source ops k planner
  (writes source ops k planner).all fun w => cell fixed w.1 w.2.1 == w.2.2

/-- Every deferred constant has a position, on an equality column, whose fixed write is its
value. -/
def constantsPlaced (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) :
    Bool :=
  let fixed := Layout.sourceFixedWrites ops (CertifiedCircuit.layoutConfig source k) planner
  decide ((operationConstSites ops).length ≤ (planner.constants source.constantColumn ops).length)
    && ((operationConstSites ops).zip (planner.constants source.constantColumn ops)).all fun p =>
      p.2.1 == scalarNat p.1.2 &&
        decide ((⟨.fixed, p.2.2.1⟩ : AnyColumn) ∈
          (CertifiedCircuit.permutationColumns source).map Halo2.Layout.ColRef.toAny) &&
        decide ((p.2.2.1, p.2.2.2, p.2.1) ∈ fixed)

/-- The key's layout is the certified one, its fixed writes agree and its deferred constants are
placed. -/
def keyed (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) : Bool :=
  decide (Usize.layout source ops k planner = certified source ops k planner) &&
    fixedConsistent source ops k planner && constantsPlaced source ops k planner

theorem keyed_spec {source : CS} {ops : Operations F} {k : Nat} {planner : Layout.Planner}
    (h : keyed source ops k planner = true) :
    Usize.layout source ops k planner = certified source ops k planner ∧
      fixedConsistent source ops k planner = true ∧
        constantsPlaced source ops k planner = true := by
  simp only [keyed, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cell_toArray (L : List (List Nat)) (column row : Nat) :
    cell (L.toArray.map List.toArray) column row = (L.getD column []).getD row 0 := by
  simp only [cell, Array.getElem?_map, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  cases L[column]? <;> simp

section
variable {source : CS} {ops : Operations F} {k : Nat} {planner : Layout.Planner}

theorem cell_of_mem (h : fixedConsistent source ops k planner = true) {w : LayoutLawful.Write}
    (hw : w ∈ writes source ops k planner) :
    cell (matrix source ops k planner) w.1 w.2.1 = w.2.2 :=
  beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem agree (h : fixedConsistent source ops k planner = true) :
    Halo2.Layout.FixedAssignmentsAgree (writes source ops k planner) := by
  intro left right hl hr hc
  obtain ⟨h1, h2⟩ := Prod.mk.inj hc
  rw [← cell_of_mem h hl, ← cell_of_mem h hr, h1, h2]

private theorem foldl_insert_mem (L : List LayoutLawful.Write) (m : Std.HashMap (Nat × Nat) Nat)
    (c : Nat × Nat) (v : Nat)
    (h : (L.foldl (fun values (column, row, value) => values.insert (column, row) value) m)[c]? =
      some v) :
    (∃ v', m[c]? = some v') ∨ c ∈ L.map Halo2.Layout.FixedAssignment.cell := by
  induction L generalizing m with
  | nil => exact Or.inl ⟨v, h⟩
  | cons w rest ih =>
    obtain ⟨column, row, value⟩ := w
    rcases ih _ h with ⟨v', hv⟩ | hc
    · change (m.insert (column, row) value)[c]? = some v' at hv
      rw [Std.HashMap.getElem?_insert] at hv
      by_cases hb : ((column, row) == c) = true
      · right
        simp only [List.map_cons, List.mem_cons]
        exact Or.inl (beq_iff_eq.mp hb).symm
      · rw [ite_eq_right hb] at hv
        exact Or.inl ⟨v', hv⟩
    · exact Or.inr (List.mem_cons_of_mem _ hc)

theorem cell_mem_of_mem_dedup {L : List LayoutLawful.Write} {w : LayoutLawful.Write}
    (hw : w ∈ Halo2.Layout.dedupAssignments L) :
    w.cell ∈ L.map Halo2.Layout.FixedAssignment.cell := by
  unfold Halo2.Layout.dedupAssignments at hw
  obtain ⟨⟨c, v⟩, hmem, rfl⟩ := List.mem_map.mp hw
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hmem
  rcases foldl_insert_mem L ∅ c v hmem with ⟨v', hv⟩ | hc
  · simp at hv
  · exact hc

/-- A cell no write names is 0. -/
theorem cell_eq_zero {c r : Nat}
    (h : (c, r) ∉ (writes source ops k planner).map Halo2.Layout.FixedAssignment.cell) :
    cell (matrix source ops k planner) c r = 0 := by
  rw [matrix, cell_toArray, LayoutLawful.dense]
  by_cases hc : c < source.numFixed + source.numSelectors
  · by_cases hr : r < 2 ^ k
    · refine Halo2.Layout.denseFixedColumns_getD_getD_eq_zero_of_not_mem _ _ _ c r
        (fun hm => h ?_) hc hr
      obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
      rw [← he]
      exact cell_mem_of_mem_dedup hw
    · rw [List.getD_eq_default _ (0 : Nat)
        (by rw [Halo2.Layout.denseFixedColumns_getD_length _ _ _ _ hc]; omega)]
  · rw [List.getD_eq_default _ ([] : List Nat)
      (by rw [Halo2.Layout.denseFixedColumns_length]; omega)]
    simp

/-- A selector column is the indicator of its activations. -/
theorem selector_cell (cert : CertifiedCircuit.Certificate source ops k planner)
    (h : fixedConsistent source ops k planner = true) (q row : Nat) :
    cell (matrix source ops k planner) (source.numFixed + q) row =
      if (q, row) ∈ Layout.sourceActivations ops source.constantColumn planner then 1 else 0 := by
  split_ifs with ha
  · exact cell_of_mem h (w := (source.numFixed + q, row, 1))
      (List.mem_append_right _ (List.mem_map.mpr ⟨(q, row), ha, rfl⟩))
  · apply cell_eq_zero
    intro hm
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
    simp only [Halo2.Layout.FixedAssignment.cell, Prod.mk.injEq] at he
    rcases List.mem_append.mp hw with hw | hw
    · have : w.1 < source.numFixed := (cert.layout.fixedCertificate.sourceLawful.bounds w hw).1
      omega
    · obtain ⟨⟨q', r'⟩, hq, rfl⟩ := List.mem_map.mp hw
      simp only at he
      have : q' = q := by omega
      exact ha (by rw [← this, ← he.2]; exact hq)

end

end Midnight.Chips.KeyChecks
