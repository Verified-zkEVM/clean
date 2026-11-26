import Midnight.SHA256.Semantics.Lookup
import Clean.Halo2.Lemmas

/-! Table facts derived from the actual Clean load operations. In particular,
the three components of a spread lookup share one row; separate per-column
membership would be too weak. Unused usable rows are the loaded first row. -/

namespace Midnight.SHA256.Semantics
open Halo2

abbrev ColumnLoaded (env : Environment F) (column : Column .fixed) (values : List F) : Prop :=
  TableLoaded env ⟨column⟩ values

theorem ColumnLoaded.entries {env : Environment F} {column : Column .fixed} {values : List F}
    (loaded : ColumnLoaded env column values) :
    ∀ row : Nat, row < values.length → env.fixed column row = values[row]! :=
  loaded.1

theorem ColumnLoaded.fill {env : Environment F} {column : Column .fixed} {values : List F}
    (loaded : ColumnLoaded env column values) :
    values ≠ [] → ∀ row : Nat, values.length ≤ row → row < env.usableRows →
      env.fixed column row = values[0]! :=
  loaded.2

theorem loadSpread_columns {place : RegionIndex → Nat} {env : Environment F}
    (tag plain expanded : TableColumn) (i : RegionIndex)
    (h : Constraints place env ((loadSpread tag plain expanded).operations i) i) :
    ColumnLoaded env tag.inner (spreadRows.map fun row => (row.1 : F)) ∧
    ColumnLoaded env plain.inner (spreadRows.map fun row => (row.2.1 : F)) ∧
    ColumnLoaded env expanded.inner (spreadRows.map fun row => (row.2.2 : F)) := by
  simp only [loadSpread, circuit_norm] at h
  exact ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩

theorem loadRange_columns {place : RegionIndex → Nat} {env : Environment F}
    (tag value : TableColumn) (requested : List Nat) (i : RegionIndex)
    (h : Constraints place env ((loadRange tag value requested).operations i) i) :
    ColumnLoaded env tag.inner ((rangeRows requested).map fun row => (row.1 : F)) ∧
    ColumnLoaded env value.inner ((rangeRows requested).map fun row => (row.2 : F)) := by
  simp only [loadRange, circuit_norm] at h
  exact ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩

/-- Every usable row is either an explicit row or the shared first-row default. -/
theorem ColumnLoaded.projected_row {α : Type} {env : Environment F}
    {column : Column .fixed} {rows : List α} {project : α → F}
    (loaded : ColumnLoaded env column (rows.map project))
    (hne : rows ≠ []) (row : Nat) (hrow : row < env.usableRows) :
    env.fixed column row = project (rows[if row < rows.length then row else 0]'(by
      split <;> simp_all [List.length_pos_iff])) := by
  by_cases h : row < rows.length
  · simp only [ite_eq_left h]
    simpa [getElem!_pos, h] using loaded.entries row (by simpa using h)
  · simp only [ite_eq_right h]
    have hzero : 0 < rows.length := List.length_pos_iff.mpr hne
    have hmap : rows.map project ≠ [] := by simpa using hne
    simpa [getElem!_pos, hzero] using
      loaded.fill hmap row (by simpa using Nat.le_of_not_gt h) hrow

/-- A tuple is read from one row of the original table, never from three
independently chosen entries. This includes the default-filled suffix. -/
theorem triple_row_mem {α : Type} {env : Environment F}
    {c₀ c₁ c₂ : Column .fixed} {rows : List α} {p₀ p₁ p₂ : α → F}
    (h₀ : ColumnLoaded env c₀ (rows.map p₀))
    (h₁ : ColumnLoaded env c₁ (rows.map p₁))
    (h₂ : ColumnLoaded env c₂ (rows.map p₂))
    (hne : rows ≠ []) (row : Nat) (hrow : row < env.usableRows) :
    (env.fixed c₀ row, env.fixed c₁ row, env.fixed c₂ row) ∈
      rows.map (fun entry => (p₀ entry, p₁ entry, p₂ entry)) := by
  rw [h₀.projected_row hne row hrow, h₁.projected_row hne row hrow,
    h₂.projected_row hne row hrow]
  apply List.mem_map.mpr
  exact ⟨_, List.getElem_mem _, rfl⟩

/-- Conversely, every loaded source tuple occurs at a usable row when the
configured domain accommodates the table. This is the honest lookup direction. -/
theorem triple_mem_has_row {α : Type} {env : Environment F}
    {c₀ c₁ c₂ : Column .fixed} {rows : List α} {p₀ p₁ p₂ : α → F}
    (h₀ : ColumnLoaded env c₀ (rows.map p₀))
    (h₁ : ColumnLoaded env c₁ (rows.map p₁))
    (h₂ : ColumnLoaded env c₂ (rows.map p₂))
    (hsize : rows.length ≤ env.usableRows) {entry : α} (hentry : entry ∈ rows) :
    ∃ row : Nat, row < env.usableRows ∧
      env.fixed c₀ row = p₀ entry ∧ env.fixed c₁ row = p₁ entry ∧
      env.fixed c₂ row = p₂ entry := by
  obtain ⟨row, hrow, heq⟩ := List.mem_iff_getElem.mp hentry
  refine ⟨row, lt_of_lt_of_le hrow hsize, ?_, ?_, ?_⟩
  all_goals
    first
    | simpa [getElem!_pos, hrow, heq] using h₀.entries row (by simpa using hrow)
    | simpa [getElem!_pos, hrow, heq] using h₁.entries row (by simpa using hrow)
    | simpa [getElem!_pos, hrow, heq] using h₂.entries row (by simpa using hrow)

theorem spreadRows_nonempty : spreadRows ≠ [] := by
  have h : (0, 0, 0) ∈ spreadRows := by
    rw [mem_spreadRows_iff]
    simp [spreadWidths]
  intro heq
  simp [heq] at h

/-- Soundness-side ambient table fact, derived from the actual table loader. -/
theorem loadSpread_sound {place : RegionIndex → Nat} {env : Environment F}
    (tag plain expanded : TableColumn) (i : RegionIndex)
    (h : Constraints place env ((loadSpread tag plain expanded).operations i) i)
    (row : Nat) (hrow : row < env.usableRows) :
    SpreadLookup (env.fixed tag.inner row) (env.fixed plain.inner row)
      (env.fixed expanded.inner row) := by
  obtain ⟨ht, hp, hs⟩ := loadSpread_columns tag plain expanded i h
  exact triple_row_mem ht hp hs spreadRows_nonempty row hrow

/-- Completeness-side ambient table fact: all admitted tuples really occur in
the loaded usable prefix. The checked native layout enforces the stronger
strict table-length bound needed for its default-fill API call. -/
theorem loadSpread_complete {place : RegionIndex → Nat} {env : Environment F}
    (tag plain expanded : TableColumn) (i : RegionIndex)
    (h : Constraints place env ((loadSpread tag plain expanded).operations i) i)
    (hsize : spreadRows.length ≤ env.usableRows)
    {tagValue plainValue expandedValue : F}
    (hmember : SpreadLookup tagValue plainValue expandedValue) :
    ∃ row : Nat, row < env.usableRows ∧
      env.fixed tag.inner row = tagValue ∧ env.fixed plain.inner row = plainValue ∧
      env.fixed expanded.inner row = expandedValue := by
  obtain ⟨ht, hp, hs⟩ := loadSpread_columns tag plain expanded i h
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmember
  obtain ⟨row, hrow, htag, hplain, hexpanded⟩ :=
    triple_mem_has_row ht hp hs hsize hentry
  have et := congrArg (fun t : F × F × F => t.1) heq
  have ep := congrArg (fun t : F × F × F => t.2.1) heq
  have es := congrArg (fun t : F × F × F => t.2.2) heq
  exact ⟨row, hrow, htag.trans et, hplain.trans ep, hexpanded.trans es⟩

theorem mem_rangeRows_iff (requested : List Nat) (width value : Nat) :
    (width, value) ∈ rangeRows requested ↔
      width < requested.foldl max 0 + 1 ∧
      (width = 0 ∨ width ∈ requested) ∧ value < 2 ^ width := by
  simp [rangeRows, and_assoc]

theorem mem_byteRangeRows_iff (width value : Nat) :
    (width, value) ∈ byteRangeRows ↔
      (width = 0 ∧ value = 0) ∨ (width = 8 ∧ value < 256) := by
  rw [byteRangeRows, mem_rangeRows_iff]
  simp only [List.foldl_cons, List.foldl_nil, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨_, h | h, hv⟩ <;> subst width
    · left; constructor; rfl; simpa using hv
    · right; exact ⟨rfl, hv⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, hv⟩) <;> simp_all

def byteRangeFieldRows : List (F × F) :=
  byteRangeRows.map fun row => ((row.1 : F), (row.2 : F))

def ByteRangeLookup (tag value : F) : Prop := (tag, value) ∈ byteRangeFieldRows

theorem byteRangeLookup_iff (tag value : F) : ByteRangeLookup tag value ↔
    (tag = 0 ∧ value = 0) ∨ (tag = 8 ∧ value.val < 256) := by
  constructor
  · intro hm
    obtain ⟨⟨width, n⟩, hn, heq⟩ := List.mem_map.mp hm
    rcases (mem_byteRangeRows_iff _ _).mp hn with hz | hb
    · obtain ⟨rfl, rfl⟩ := hz
      left
      exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩
    · obtain ⟨rfl, hbound⟩ := hb
      right
      have ht := congrArg (fun t : F × F => t.1) heq
      have hv := congrArg (fun t : F × F => t.2.val) heq
      have hsmall : n < BLS12_381.scalarFieldSize :=
        hbound.trans (by norm_num [BLS12_381.scalarFieldSize])
      refine ⟨ht.symm, ?_⟩
      have hv' : value.val = n := by
        simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hsmall] using hv.symm
      rw [hv']
      exact hbound
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, hv⟩)
    · apply List.mem_map.mpr
      exact ⟨(0,0), (mem_byteRangeRows_iff _ _).mpr (Or.inl ⟨rfl,rfl⟩), by simp⟩
    · apply List.mem_map.mpr
      exact ⟨(8,value.val), (mem_byteRangeRows_iff _ _).mpr (Or.inr ⟨rfl,hv⟩), by simp⟩

theorem byteRangeLookup_eight (value : F) : ByteRangeLookup 8 value ↔ value.val < 256 := by
  rw [byteRangeLookup_iff]
  have hne : (8 : F) ≠ 0 := by decide +kernel
  simp [hne]

theorem byteRangeRows_nonempty : byteRangeRows ≠ [] := by
  have h : (0,0) ∈ byteRangeRows := (mem_byteRangeRows_iff _ _).mpr (Or.inl ⟨rfl,rfl⟩)
  intro heq
  simp [heq] at h

theorem loadByteRange_sound {place : RegionIndex → Nat} {env : Environment F}
    (tag value : TableColumn) (i : RegionIndex)
    (h : Constraints place env ((loadRange tag value [8]).operations i) i)
    (row : Nat) (hrow : row < env.usableRows) :
    ByteRangeLookup (env.fixed tag.inner row) (env.fixed value.inner row) := by
  obtain ⟨ht, hv⟩ := loadRange_columns tag value [8] i h
  have hm := triple_row_mem ht hv hv byteRangeRows_nonempty row hrow
  obtain ⟨entry, he, heq⟩ := List.mem_map.mp hm
  exact List.mem_map.mpr ⟨entry, he, congrArg (fun t : F × F × F => (t.1,t.2.1)) heq⟩

theorem loadByteRange_complete {place : RegionIndex → Nat} {env : Environment F}
    (tag value : TableColumn) (i : RegionIndex)
    (h : Constraints place env ((loadRange tag value [8]).operations i) i)
    (hsize : byteRangeRows.length ≤ env.usableRows)
    {tagValue plainValue : F} (hmember : ByteRangeLookup tagValue plainValue) :
    ∃ row : Nat, row < env.usableRows ∧
      env.fixed tag.inner row = tagValue ∧ env.fixed value.inner row = plainValue := by
  obtain ⟨ht, hv⟩ := loadRange_columns tag value [8] i h
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmember
  obtain ⟨row, hrow, htag, hvalue, _⟩ := triple_mem_has_row ht hv hv hsize hentry
  exact ⟨row, hrow, htag.trans (congrArg Prod.fst heq), hvalue.trans (congrArg Prod.snd heq)⟩

end Midnight.SHA256.Semantics
