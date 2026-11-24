import Mathlib.Algebra.Polynomial.Roots
import CompPoly.Univariate.ToPoly.Core
import CompPoly.Univariate.Raw.Proofs
import Midnight.Keygen.ConfigureLawful
import Midnight.Chips.CertifiedCircuit
import Clean.Halo2.Compiler.GateOperations
import Clean.Halo2.Keygen.CompressSelectors

/-! midnight-zk's additive selector (`Constraints::with_additive_selector`, `trash.rs`)
enforces `compress r cs - (1 - q) * trash = 0` on every row of the domain, for a challenge `r`,
the selector's fixed column `q` and a free column `trash`. Outside a small challenge set that is
the trashcan's constraints wherever `q = 1`; the challenge being uniform and drawn after the
witness (Fiat–Shamir) is assumed, not modelled. Rust draws one challenge for all trash
arguments, so the theorems take every trashcan at once. The identity covers all `2 ^ k` rows and
its rotations wrap (`Environment.wrap`). -/

namespace Midnight.Additive
open Polynomial
variable {F : Type} [Field F]

/-- Rust's Horner fold: the first constraint gets the highest challenge power. -/
def compress (r : F) (cs : List F) : F :=
  cs.foldl (fun acc c => acc * r + c) 0

/-- One row of Rust's trash argument at selector value `q`. -/
def rowConstraint (q r trash : F) (cs : List F) : Prop :=
  compress r cs - (1 - q) * trash = 0

/-- The constraint values as coefficients, the first one leading. -/
noncomputable def polynomial (cs : List F) : F[X] :=
  CompPoly.CPolynomial.Raw.toPoly (cs.reverse.toArray : CompPoly.CPolynomial.Raw F)

open CompPoly.CPolynomial in
theorem eval_polynomial (r : F) (cs : List F) : (polynomial cs).eval r = compress r cs := by
  rw [polynomial, Raw.eval_toPoly_eq_eval, ← Raw.evalHorner_eq_eval]
  simp [Raw.evalHorner, Raw.eval₂Horner, compress, List.foldr_reverse]

theorem coeff_polynomial (cs : List F) (n : ℕ) :
    (polynomial cs).coeff n = cs.reverse.getD n 0 := by
  simp [polynomial, CompPoly.CPolynomial.Raw.coeff_toPoly, CompPoly.CPolynomial.Raw.coeff,
    List.getD_eq_getElem?_getD]

theorem natDegree_polynomial_le (cs : List F) : (polynomial cs).natDegree ≤ cs.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_polynomial, List.getD_eq_default]
  simp only [List.length_reverse]
  omega

theorem polynomial_eq_zero_iff (cs : List F) : polynomial cs = 0 ↔ ∀ c ∈ cs, c = 0 := by
  constructor
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_reverse.mpr hc)
    have := congrArg (coeff · i) h
    rwa [coeff_polynomial, Polynomial.coeff_zero, List.getD_eq_getElem _ _ hi] at this
  · intro h
    ext n
    rw [coeff_polynomial, coeff_zero]
    rcases lt_or_ge n cs.reverse.length with hn | hn
    · rw [List.getD_eq_getElem _ _ hn]
      exact h _ (List.mem_reverse.mp (List.getElem_mem hn))
    · exact List.getD_eq_default _ _ hn

/-- At an active row the trash value drops out, and outside at most `length - 1`
challenges (the roots of `polynomial cs`) compression is equivalent to every value being zero. -/
theorem exists_small_exceptional_set (cs : List F) :
    ∃ bad : Finset F, bad.card ≤ cs.length - 1 ∧
      ∀ r ∉ bad, ∀ trash, (rowConstraint 1 r trash cs ↔ ∀ c ∈ cs, c = 0) := by
  classical
  refine ⟨(polynomial cs).roots.toFinset, (Multiset.toFinset_card_le _).trans
    ((card_roots' _).trans (natDegree_polynomial_le cs)), fun r hr trash => ?_⟩
  simp only [rowConstraint, sub_self, zero_mul, sub_zero, ← eval_polynomial]
  refine ⟨fun h => by_contra fun hne => hr ?_, fun h => by
    rw [(polynomial_eq_zero_iff cs).mpr h, eval_zero]⟩
  exact Multiset.mem_toFinset.mpr
    ((mem_roots (mt (polynomial_eq_zero_iff cs).mp hne)).mpr h)

/-- Rows below `n`: a row with `q ≠ 1` is met by `trash = compress r cs / (1 - q)`, so outside
at most `A.card * (m - 1)` challenges Rust's identity on every row is equivalent to all values
vanishing on the rows with `q = 1`, which lie in `A`. -/
theorem exists_small_exceptional_set_rows (n : ℕ) (A : Finset ℕ) (m : ℕ) (q : ℕ → F)
    (cs : ℕ → List F)
    (hA : ∀ row < n, q row = 1 → row ∈ A) (hm : ∀ row ∈ A, (cs row).length ≤ m) :
    ∃ bad : Finset F, bad.card ≤ A.card * (m - 1) ∧ ∀ r ∉ bad,
      ((∃ trash : ℕ → F, ∀ row < n, rowConstraint (q row) r (trash row) (cs row)) ↔
        ∀ row < n, q row = 1 → ∀ c ∈ cs row, c = 0) := by
  classical
  choose B hB good using fun row => exists_small_exceptional_set (cs row)
  refine ⟨A.biUnion B, ?_, fun r hr => ?_⟩
  · refine Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ (m - 1) ?_).trans ?_)
    · intro row hrow
      have := hm row hrow
      have := hB row
      omega
    · simp
  have hr row (hn : row < n) (h1 : q row = 1) : r ∉ B row := fun h =>
    hr (Finset.mem_biUnion.mpr ⟨row, hA row hn h1, h⟩)
  constructor
  · rintro ⟨trash, h⟩ row hn h1
    have := h row hn
    rw [h1] at this
    exact (good row r (hr row hn h1) (trash row)).mp this
  · intro h
    refine ⟨fun row => compress r (cs row) / (1 - q row), fun row hn => ?_⟩
    by_cases h1 : q row = 1
    · rw [h1]
      exact (good row r (hr row hn h1) _).mpr (h row hn h1)
    · have hne : 1 - q row ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      rw [rowConstraint, mul_comm, div_mul_cancel₀ _ hne, sub_self]

omit [Field F] in
/-- One challenge for several arguments: the exceptional sets add up. -/
theorem exists_small_exceptional_set_all {ι : Type} (L : List ι) (b : ι → ℕ)
    (P : ι → F → Prop) (Q : ι → Prop)
    (h : ∀ i ∈ L, ∃ bad : Finset F, bad.card ≤ b i ∧ ∀ r ∉ bad, (P i r ↔ Q i)) :
    ∃ bad : Finset F, bad.card ≤ (L.map b).sum ∧ ∀ r ∉ bad,
      ((∀ i ∈ L, P i r) ↔ ∀ i ∈ L, Q i) := by
  classical
  induction L with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons i L ih =>
    obtain ⟨B, hB, hi⟩ := h i (by simp)
    obtain ⟨C, hC, hL⟩ := ih fun j hj => h j (by simp [hj])
    refine ⟨B ∪ C, (Finset.card_union_le _ _).trans (by simp; omega), fun r hr => ?_⟩
    rw [Finset.mem_union, not_or] at hr
    simp only [List.forall_mem_cons]
    exact and_congr (hi r hr.1) (hL r hr.2)

end Midnight.Additive

namespace Midnight.Keygen
open Halo2

/-- Rust's witness: columns have `n` rows and rotations wrap, so cells are read modulo `n`. -/
def _root_.Halo2.Environment.wrap (env : Environment F) (n : ℕ) : Environment F :=
  { env with get := fun col row => env.get col (row % n) }

/-- The rows where Rust's fixed column for selector `idx` is 1
(`directly_convert_selectors_to_fixed`): keygen's activations, by any gate or lookup. -/
def selectorRows (idx : ℕ) (starts : List ℕ) (ops : Operations F) : Finset ℕ :=
  (selectorActivationRows (activations starts (indexedRegions ops 0).1) idx).toFinset

/-- Rust's fixed column for selector `idx`. -/
def selectorColumn (idx : ℕ) (starts : List ℕ) (ops : Operations F) (row : ℕ) : F :=
  if row ∈ selectorRows idx starts ops then 1 else 0

/-- What Rust's trash argument folds at `row`: the trashcan's constraints, any selector in them
read from its fixed column. -/
def GateSpec.rowValues (g : GateSpec) (env : Environment F) (starts : List ℕ) (ops : Operations F)
    (row : ℕ) : List F :=
  g.constraints.toList.map fun c => c.2.eval (Query.eval env (selectorColumn · starts ops row) row)

/-- One trashcan on the rows below `n`: outside `rows * (m - 1)` challenges Rust's identity
holds for some trash column iff the constraints vanish where the selector column is 1. -/
theorem GateSpec.trash_argument (g : GateSpec) (n : ℕ) (starts : List ℕ) (ops : Operations F)
    (env : Environment F) :
    ∃ bad : Finset F, bad.card ≤ (selectorRows g.selector.index starts ops).card *
        (g.constraints.size - 1) ∧ ∀ r ∉ bad,
      ((∃ trash : ℕ → F, ∀ row < n, Additive.rowConstraint
          (selectorColumn g.selector.index starts ops row) r (trash row)
          (g.rowValues env starts ops row)) ↔
        ∀ row < n, row ∈ selectorRows g.selector.index starts ops →
          ∀ v ∈ g.rowValues env starts ops row, v = 0) := by
  have hcol row : selectorColumn g.selector.index starts ops row = 1 ↔
      row ∈ selectorRows g.selector.index starts ops := by
    unfold selectorColumn
    split_ifs with h <;> simp [h]
  obtain ⟨bad, hcard, hbad⟩ := Additive.exists_small_exceptional_set_rows n
    (selectorRows g.selector.index starts ops) g.constraints.size
    (selectorColumn g.selector.index starts ops) (g.rowValues env starts ops)
    (fun row _ h => (hcol row).mp h) (fun row _ => by simp [GateSpec.rowValues])
  exact ⟨bad, hcard, fun r hr => (hbad r hr).trans (by simp only [hcol])⟩

/-- Every trashcan of `c` on Rust's `2 ^ k` rows under one challenge. -/
theorem CS.Checked.additive_selector (c : CS.Checked) (k : ℕ) (starts : List ℕ)
    (ops : Operations F) (env : Environment F) :
    ∃ bad : Finset F, bad.card ≤ (c.raw.trashcans.toList.map fun g =>
        (selectorRows g.selector.index starts ops).card * (g.constraints.size - 1)).sum ∧
      ∀ r ∉ bad,
        ((∀ g ∈ c.raw.trashcans.toList, ∃ trash : ℕ → F, ∀ row < 2 ^ k,
          Additive.rowConstraint (selectorColumn g.selector.index starts ops row) r (trash row)
            (g.rowValues (env.wrap (2 ^ k)) starts ops row)) ↔
        ∀ g ∈ c.raw.trashcans.toList, ∀ row < 2 ^ k,
          row ∈ selectorRows g.selector.index starts ops →
            ∀ v ∈ g.rowValues (env.wrap (2 ^ k)) starts ops row, v = 0) :=
  Additive.exists_small_exceptional_set_all _ _ _ _ fun g _ =>
    g.trash_argument (2 ^ k) starts ops (env.wrap (2 ^ k))

/-- A trashcan whose body queries selectors (`rows`): `q * c` vanishing on every row, as
`RowGatesHold` states it, is each `c` vanishing where the selector column is 1. -/
theorem GateSpec.rowsHold_iff (g : GateSpec) (hraw : g.raw = false) (n : ℕ) (starts : List ℕ)
    (ops : Operations F) (env : Environment F) :
    (∀ row < n, ∀ p ∈ g.polynomials.toList,
        p.eval (Query.eval env (selectorColumn · starts ops row) row) = 0) ↔
      ∀ row < n, row ∈ selectorRows g.selector.index starts ops →
        ∀ v ∈ g.rowValues env starts ops row, v = 0 := by
  refine forall₂_congr fun row _ => ?_
  simp only [GateSpec.polynomials, GateSpec.rowValues, hraw, Bool.false_eq_true, ↓reduceIte,
    Array.toList_map, List.forall_mem_map]
  by_cases hrow : row ∈ selectorRows g.selector.index starts ops <;>
    simp [selectorColumn, hrow, querySelector, Expression.eval, Query.eval, Prod.forall]

theorem CS.Checked.trash_lawful (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) : g.Lawful c.raw :=
  List.forall_iff_forall_mem.mp c.lawful.gates g (by simp [CS.gateSpecs, hg])

theorem CS.Checked.trash_selected (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) : g.raw = false :=
  List.forall_iff_forall_mem.mp c.lawful.trashSelected g hg

/-- A trashcan that is not `rows` has selector-free constraints. -/
theorem CS.Checked.trash_free (c : CS.Checked) {g : GateSpec} (hg : g ∈ c.raw.trashcans.toList)
    (hrows : g.rows = false) : ∀ p ∈ g.constraints.toList, p.2.SelectorFree := by
  intro p hp
  have h := ((List.forall_iff_forall_mem.mp (c.trash_lawful hg).2.2) p hp).1
  simp only [hrows, Bool.false_or, GateSpec.bodyValid, c.trash_selected hg, Bool.false_eq_true,
    ↓reduceIte] at h
  exact (Expression.free_iff _).mp h

/-- The Clean gate a trashcan contributes to `toCleanDelta`: its constraints under the selector,
or for a `rows` trashcan a handle stating nothing. -/
def CS.Checked.trashGate (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) : Gate F :=
  g.toClean (c.trash_lawful hg).valid

theorem CS.Checked.trashGate_mem (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) : c.trashGate hg ∈ c.toCleanDelta.gates := by
  show c.trashGate hg ∈ c.gateHandles ++ c.rowsHandles ++ c.lookupHandles ++ c.unusedHandles
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  unfold gateHandles
  exact List.mem_map.mpr ⟨⟨g, by simp [CS.gateSpecs, hg]⟩, List.mem_attach _ _, rfl⟩

theorem CS.Checked.trashGate_selector (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) : (c.trashGate hg).selector = g.selector := by
  unfold trashGate GateSpec.toClean
  split <;> (try split) <;> rfl

theorem CS.Checked.trashGate_constraints (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) (hrows : g.rows = false) :
    (c.trashGate hg).constraints = g.constraints.toList.map fun (name, p) =>
      { name := name, poly := querySelector g.selector * p } := by
  unfold trashGate GateSpec.toClean
  split
  · rename_i h
    simp [hrows] at h
  · split
    · rename_i h
      simp [c.trash_selected hg] at h
    · rfl

theorem CS.Checked.trashGate_satisfied_iff (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) (hrows : g.rows = false) (starts : List ℕ)
    (ops : Operations F) (place : RegionIndex → ℕ) (env : Environment F)
    (e : EnabledGate F) (he : e.gate = c.trashGate hg) :
    e.Satisfied place env ↔ ∀ v ∈ g.rowValues env starts ops (place e.region + e.row), v = 0 := by
  obtain ⟨gate, region, row⟩ := e
  subst he
  have free := c.trash_free hg hrows
  simp only [EnabledGate.Satisfied, c.trashGate_constraints hg hrows, c.trashGate_selector hg,
    GateSpec.rowValues, List.forall_iff_forall_mem, List.forall_mem_map]
  refine forall₂_congr fun ⟨name, p⟩ hp => ?_
  simp only [querySelector, Expression.eval, Query.eval, ↓reduceIte, one_mul]
  exact Iff.of_eq (congrArg (· = 0) (Expression.eval_eq_of_selectorFree p (free _ hp) _ _
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)))

theorem CS.Checked.mem_selectorRows (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) (starts : List ℕ) {ops : Operations F}
    {e : EnabledGate F} (he : e ∈ operationEnabledGates ops 0) (hgate : e.gate = c.trashGate hg) :
    starts.getD e.region 0 + e.row ∈ selectorRows g.selector.index starts ops := by
  have := mem_activations_of_mem_operationEnabledGate starts he
  rw [hgate, c.trashGate_selector hg] at this
  simpa [selectorRows, mem_selectorActivationRows_iff] using this

/-- A trashcan's constraints where its selector column is 1 give Clean's gate at each of its
activations, all below `n` (`Certificate.activation_lt`). -/
theorem CS.Checked.trashGate_satisfied (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) (hrows : g.rows = false) {n : ℕ} {starts : List ℕ}
    {ops : Operations F} {env : Environment F}
    (hacts : ∀ a ∈ activations starts (indexedRegions ops 0).1, a.2 < n)
    (h : ∀ row < n, row ∈ selectorRows g.selector.index starts ops →
      ∀ v ∈ g.rowValues env starts ops row, v = 0) :
    ∀ e ∈ operationEnabledGates ops 0, e.gate = c.trashGate hg →
      e.Satisfied (starts.getD · 0) env := by
  intro e he hgate
  refine (c.trashGate_satisfied_iff hg hrows starts ops _ env e hgate).mpr
    (h _ ?_ (c.mem_selectorRows hg starts he hgate))
  exact hacts _ (mem_activations_of_mem_operationEnabledGate starts he)

theorem mem_regionEnabledGates {gate : Gate F} {row : ℕ} (i : RegionIndex)
    {body : RegionOperations F} (h : .enableGate gate row ∈ body) :
    ⟨gate, i, row⟩ ∈ regionEnabledGates i body := by
  induction body with
  | nil => simp at h
  | cons op rest ih =>
    rcases List.mem_cons.mp h with rfl | hrest
    · simp [regionEnabledGates]
    · cases op <;> simp only [regionEnabledGates, List.mem_cons] <;>
        first | exact Or.inr (ih hrest) | exact ih hrest

theorem mem_operationEnabledGates {ops : Operations F} {i index : ℕ} {body : RegionOperations F}
    {gate : Gate F} {row : ℕ} (hreg : (index, body) ∈ (indexedRegions ops i).1)
    (h : .enableGate gate row ∈ body) : ⟨gate, index, row⟩ ∈ operationEnabledGates ops i := by
  induction ops generalizing i with
  | nil => simp [indexedRegions] at hreg
  | cons op rest ih =>
    cases op with
    | region name b =>
      simp only [indexedRegions, List.mem_cons, Prod.mk.injEq] at hreg
      simp only [operationEnabledGates, List.mem_append]
      rcases hreg with ⟨rfl, rfl⟩ | hreg
      · exact Or.inl (mem_regionEnabledGates _ h)
      · exact Or.inr (ih hreg)
    | constrainInstance _ _ _ => exact ih hreg
    | loadTable _ _ => exact ih hreg

/-- A certified layout places every selector activation below its usable rows, so below `2 ^ k`. -/
theorem _root_.Midnight.Chips.CertifiedCircuit.Certificate.activation_lt {source : CS}
    {ops : Operations F} {k : ℕ} {planner : Chips.Layout.Planner}
    (cert : Chips.CertifiedCircuit.Certificate source ops k planner) :
    ∀ a ∈ activations (planner.starts source.constantColumn ops) (indexedRegions ops 0).1,
      a.2 < 2 ^ k := fun a ha =>
  lt_of_lt_of_le (cert.layout.fixedCertificate.activationBounds a ha).2
    cert.layout.fixedCertificate.usable_le_rows

/-- On a certified layout every row where a trashcan's selector column is 1, whoever enables
the selector there, enables the trashcan's gate (`OperationsLawful.ActivationClosed`). -/
theorem CS.Checked.selectorRows_enabled (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) (hrows : g.rows = false) {ops : Operations F} {k : ℕ}
    {planner : Chips.Layout.Planner} (cert : Chips.CertifiedCircuit.Certificate c.raw ops k planner) :
    ∀ row ∈ selectorRows g.selector.index (planner.starts c.raw.constantColumn ops) ops,
      ∃ e ∈ operationEnabledGates ops 0, e.gate = c.trashGate hg ∧
        (planner.starts c.raw.constantColumn ops).getD e.region 0 + e.row = row := by
  intro row hrow
  simp only [selectorRows, List.mem_toFinset, mem_selectorActivationRows_iff] at hrow
  obtain ⟨index, body, op, localRow, hreg, hop, hact, rfl⟩ :=
    (mem_activations_iff _ _ _ _).mp hrow
  have hloc : (g.selector.index, localRow) ∈ Chips.OperationsLawful.localActivations body :=
    (mem_activations_iff _ _ _ _).mpr
      ⟨0, body, op, localRow, List.mem_singleton_self _, hop, hact, by simp⟩
  obtain ⟨-, -, closed⟩ := List.forall_iff_forall_mem.mp cert.operations.regions _ hreg
  obtain ⟨hgates, -⟩ := List.forall_iff_forall_mem.mp closed _ hloc
  have hen : Chips.OperationsLawful.GateEnabled body (c.trashGate hg) localRow :=
    List.forall_iff_forall_mem.mp hgates (c.trashGate hg) (c.trashGate_mem hg)
      (by
        rw [c.trashGate_constraints hg hrows]
        intro hnil
        have hpos := List.forall_iff_forall_mem.mp c.lawful.trashNonempty g hg
        have := congrArg List.length hnil
        simp only [List.length_map, Array.length_toList, List.length_nil] at this
        omega)
      (by rw [c.trashGate_selector hg])
  exact ⟨⟨c.trashGate hg, index, localRow⟩, mem_operationEnabledGates hreg hen, rfl, rfl⟩

/-- On a certified layout a trashcan that is not `rows` holds where its selector column is 1
iff Clean's gate holds at each of its activations. -/
theorem CS.Checked.trashGate_satisfied_iff_rows (c : CS.Checked) {g : GateSpec}
    (hg : g ∈ c.raw.trashcans.toList) (hrows : g.rows = false) {ops : Operations F} {k : ℕ}
    {planner : Chips.Layout.Planner} (cert : Chips.CertifiedCircuit.Certificate c.raw ops k planner)
    (env : Environment F) :
    (∀ row < 2 ^ k, row ∈ selectorRows g.selector.index (planner.starts c.raw.constantColumn ops) ops →
        ∀ v ∈ g.rowValues env (planner.starts c.raw.constantColumn ops) ops row, v = 0) ↔
      ∀ e ∈ operationEnabledGates ops 0, e.gate = c.trashGate hg →
        e.Satisfied ((planner.starts c.raw.constantColumn ops).getD · 0) env := by
  refine ⟨c.trashGate_satisfied hg hrows cert.activation_lt, fun h row _ hrow => ?_⟩
  obtain ⟨e, he, hgate, rfl⟩ := c.selectorRows_enabled hg hrows cert row hrow
  exact (c.trashGate_satisfied_iff hg hrows _ ops _ env e hgate).mp (h e he hgate)

/-- `additive_selector` on a certified layout: outside `bad`, Rust's check is Clean's meaning of
every trashcan on `env.wrap (2 ^ k)`, its gate at each activation (`ActivationClosed` enables a
gate or lookup sharing the selector with it), or for a `rows` trashcan each polynomial on every
row with selectors read from their columns (`RowGatesHold`'s shape, at `env.wrap` rather than its
Simple-placement valuation). -/
theorem CS.Checked.additive_selector_clean (c : CS.Checked) {ops : Operations F} {k : ℕ}
    {planner : Chips.Layout.Planner} (cert : Chips.CertifiedCircuit.Certificate c.raw ops k planner)
    (env : Environment F) :
    let starts := planner.starts c.raw.constantColumn ops
    ∃ bad : Finset F, bad.card ≤ (c.raw.trashcans.toList.map fun g =>
        (selectorRows g.selector.index starts ops).card * (g.constraints.size - 1)).sum ∧
      ∀ r ∉ bad,
        ((∀ g ∈ c.raw.trashcans.toList, ∃ trash : ℕ → F, ∀ row < 2 ^ k,
          Additive.rowConstraint (selectorColumn g.selector.index starts ops row) r
            (trash row) (g.rowValues (env.wrap (2 ^ k)) starts ops row)) ↔
        ∀ g (hg : g ∈ c.raw.trashcans.toList),
          (g.rows = false → ∀ e ∈ operationEnabledGates ops 0, e.gate = c.trashGate hg →
            e.Satisfied (starts.getD · 0) (env.wrap (2 ^ k))) ∧
          (g.rows = true → ∀ row < 2 ^ k, ∀ p ∈ g.polynomials.toList,
            p.eval (Query.eval (env.wrap (2 ^ k)) (selectorColumn · starts ops row) row) = 0)) := by
  intro starts
  obtain ⟨bad, hcard, h⟩ := c.additive_selector k starts ops env
  refine ⟨bad, hcard, fun r hr => (h r hr).trans (forall₂_congr fun g hg => ?_)⟩
  cases hrows : g.rows
  · exact (c.trashGate_satisfied_iff_rows hg hrows cert (env.wrap (2 ^ k))).trans
      ⟨fun h => ⟨fun _ => h, fun h => absurd h (by simp)⟩, fun h => h.1 rfl⟩
  · exact (g.rowsHold_iff (c.trash_selected hg) (2 ^ k) starts ops (env.wrap (2 ^ k))).symm.trans
      ⟨fun h => ⟨fun h => absurd h (by simp), fun _ => h⟩, fun h => h.2 rfl⟩

end Midnight.Keygen
