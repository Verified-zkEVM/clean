import Clean.Utils.PermutationConstruction
import Clean.Halo2.Compiler.CopyLayout
import Clean.Halo2.Compiler.PermutationRows
import Clean.Halo2.Keygen.Layout
import Mathlib.Tactic.IntervalCases

/-! # Correctness of executable permutation assembly

The array mapping implements cycle merging in source order. Its auxiliary union-find
representatives agree exactly on cycles; union-by-size does not change the mapping.
-/

variable {F : Type} [FiniteField F]

namespace Halo2.Layout.Asm

open Equiv

/-- The rectangular shape invariant of the assembly's cell arrays. -/
def Shaped (numCols n : ℕ) (a : Array (Array (ℕ × ℕ))) : Prop :=
  a.size = numCols ∧ ∀ i, (h : i < a.size) → a[i].size = n

/-- Simulation between an assembly state and an abstract cell permutation: the shape of
both cell arrays, `mapping` acting as the permutation, every `aux` entry an in-cycle,
self-rooted representative, and `aux` entries agreeing exactly on cycles. -/
structure Sim {numCols n : ℕ} (a : Asm) (π : Perm (FlatCell numCols n)) : Prop where
  map_shape : Shaped numCols n a.mapping
  aux_shape : Shaped numCols n a.aux
  map_eq : ∀ c : FlatCell numCols n,
    getPair a.mapping c.pair = (π c).pair
  aux_rep : ∀ c : FlatCell numCols n, ∃ r : FlatCell numCols n,
    getPair a.aux c.pair = r.pair ∧ π.SameCycle c r ∧
      getPair a.aux r.pair = r.pair
  aux_eq_iff : ∀ c d : FlatCell numCols n,
    (getPair a.aux c.pair = getPair a.aux d.pair ↔ π.SameCycle c d)

/-- `repoint` never touches `mapping`. -/
theorem repoint_mapping (a : Asm) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    (repoint a fuel i tgt stop).mapping = a.mapping := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [repoint]
      split
      · rfl
      · exact ih _ _

/-- `repoint` never touches `sizes`. -/
theorem repoint_sizes (a : Asm) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    (repoint a fuel i tgt stop).sizes = a.sizes := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [repoint]
      split
      · rfl
      · exact ih _ _

theorem Shaped.setPair {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) (p : ℕ × ℕ) (v : ℕ × ℕ) :
    Shaped numCols n (setPair a p v) := by
  obtain ⟨hsize, hrow⟩ := h
  refine ⟨by simpa [Asm.setPair] using hsize, ?_⟩
  intro i hi
  simp only [Asm.setPair, Array.size_modify] at hi
  by_cases hip : p.1 = i
  · subst hip
    simp [Asm.setPair, Array.getElem_modify_self, hrow]
  · simp [Asm.setPair, Array.getElem_modify_of_ne hip, hrow]

/-- Reading back the just-written cell (the write position must be in shape). -/
theorem getPair_setPair_self {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) {p : ℕ × ℕ} (hp1 : p.1 < numCols) (hp2 : p.2 < n)
    (v : ℕ × ℕ) :
    getPair (setPair a p v) p = v := by
  obtain ⟨hsize, hrow⟩ := h
  have hp1' : p.1 < a.size := hsize ▸ hp1
  simp [getPair, setPair,
    Array.size_modify, hp1', Array.getElem_modify_self,
    Array.set!, Array.getElem_setIfInBounds_self, hrow _ hp1', hp2]

/-- Reading any other cell is unaffected by the write. -/
theorem getPair_setPair_ne {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) {p q : ℕ × ℕ} (hpq : q ≠ p) (v : ℕ × ℕ) :
    getPair (setPair a p v) q = getPair a q := by
  obtain ⟨hsize, hrow⟩ := h
  by_cases h1 : q.1 = p.1
  · have h2 : q.2 ≠ p.2 := fun h2 => hpq (Prod.ext_iff.mpr ⟨h1, h2⟩)
    by_cases hq1 : q.1 < a.size
    · have hp1 : p.1 < a.size := h1 ▸ hq1
      simp [getPair, setPair, Array.getElem!_eq_getD, Array.getD,
        Array.size_modify, h1, Array.getElem_modify_self,
        Array.set!, Array.size_setIfInBounds, hp1]
      split
      · exact Array.getElem_setIfInBounds_ne (by assumption) (Ne.symm h2)
      · rfl
    · simp [getPair, setPair, Array.getElem!_eq_getD, Array.getD,
        Array.size_modify, hq1]
  · simp [getPair, setPair, Array.getElem!_eq_getD, Array.getD,
      Array.size_modify, Array.getElem_modify_of_ne (fun h => h1 h.symm)]

/-- `repoint` preserves the aux shape. -/
theorem Shaped.repoint {numCols n : ℕ} {a : Asm}
    (h : Shaped numCols n a.aux) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    Shaped numCols n (Asm.repoint a fuel i tgt stop).aux := by
  induction fuel generalizing a i with
  | zero => exact h
  | succ fuel ih =>
      simp only [Asm.repoint]
      split
      · exact h.setPair i tgt
      · exact ih (h.setPair i tgt) _

/-- The effect of one `repoint` walk: with `mapping` acting as `π`, the walk from
`start` (with stop `stop`, the first later return of the orbit) re-points exactly the
orbit segment `π ^ t · start, t < s`, and leaves every other `aux` entry unchanged. -/
theorem getPair_repoint_aux {numCols n : ℕ} {a : Asm} {π : Perm (FlatCell numCols n)}
    (hshape : Shaped numCols n a.aux)
    (hmap : ∀ c : FlatCell numCols n, getPair a.mapping c.pair = (π c).pair)
    (s : ℕ) (start stop : FlatCell numCols n) (tgt : ℕ × ℕ)
    (hs : (π ^ s) start = stop) (hs1 : 1 ≤ s)
    (hmin : ∀ t, 0 < t → t < s → (π ^ t) start ≠ stop)
    (fuel : ℕ) (hfuel : s ≤ fuel)
    (d : FlatCell numCols n) :
    getPair (repoint a fuel start.pair tgt stop.pair).aux d.pair =
      if ∃ t, t < s ∧ (π ^ t) start = d then tgt else getPair a.aux d.pair := by
  induction s generalizing a start fuel with
  | zero => exact absurd hs1 (by omega)
  | succ s' ih =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
        ⟨fuel - 1, by omega⟩
      have hnext : getPair a.mapping start.pair = (π start).pair := hmap start
      by_cases hzero : s' = 0
      · -- one step: the walk immediately returns to `stop`
        subst hzero
        have hstop : π start = stop := by
          simpa [pow_one] using hs
        simp only [repoint, hnext, hstop]
        rw [if_pos (by simp)]
        by_cases hd : d = start
        · subst hd
          rw [if_pos ⟨0, by simp, rfl⟩]
          exact getPair_setPair_self hshape d.1.isLt d.2.isLt tgt
        · rw [if_neg ?_, getPair_setPair_ne hshape ?_ tgt]
          · exact fun h => hd (FlatCell.pair_injective h)
          · rintro ⟨t, ht, hteq⟩
            interval_cases t
            exact hd (by simpa using hteq.symm)
      · -- the walk continues: `π start ≠ stop`, recurse along the orbit
        have hs'1 : 1 ≤ s' := by omega
        have hne : π start ≠ stop := by
          simpa [pow_one] using hmin 1 (by omega) (by omega)
        have hnepair : ((π start).pair == stop.pair) = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun h => hne (FlatCell.pair_injective h)
        simp only [repoint, hnext, hnepair]
        rw [if_neg (by simp)]
        have hs'' : (π ^ s') (π start) = stop := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ]
          exact hs
        have hmin'' : ∀ t, 0 < t → t < s' → (π ^ t) (π start) ≠ stop := by
          intro t ht hts habs
          refine hmin (t + 1) (by omega) (by omega) ?_
          rw [pow_succ, Equiv.Perm.mul_apply]
          exact habs
        have hrec := ih (a := { a with aux := setPair a.aux start.pair tgt })
          (hshape.setPair start.pair tgt) hmap (π start) hs'' hs'1 hmin'' f (by omega)
        rw [hrec]
        by_cases hd : d = start
        · subst hd
          have hrhs : ∃ t, t < s' + 1 ∧ (π ^ t) d = d := ⟨0, by simp⟩
          rw [if_pos hrhs]
          split
          · rfl
          · exact getPair_setPair_self hshape d.1.isLt d.2.isLt tgt
        · have hpairne : d.pair ≠ start.pair :=
            fun h => hd (FlatCell.pair_injective h)
          have hcond : (∃ t, t < s' ∧ (π ^ t) (π start) = d) ↔
              (∃ t, t < s' + 1 ∧ (π ^ t) start = d) := by
            constructor
            · rintro ⟨t, ht, hteq⟩
              refine ⟨t + 1, by omega, ?_⟩
              rw [pow_succ, Equiv.Perm.mul_apply]
              exact hteq
            · rintro ⟨t, ht, hteq⟩
              match t with
              | 0 => exact absurd (by simpa using hteq.symm) hd
              | t + 1 =>
                  refine ⟨t, by omega, ?_⟩
                  rw [pow_succ, Equiv.Perm.mul_apply] at hteq
                  exact hteq
          rw [getPair_setPair_ne hshape hpairne tgt]
          by_cases hc : ∃ t, t < s' + 1 ∧ (π ^ t) start = d
          · rw [if_pos hc, if_pos (hcond.mpr hc)]
          · rw [if_neg hc, if_neg (fun h => hc (hcond.mp h))]

/-- The walk reads only `mapping` and writes only `aux`, so a `sizes` update commutes
away. -/
theorem repoint_aux_sizes {a : Asm} (sz : Array (Array ℕ)) (fuel : ℕ)
    (i tgt stop : ℕ × ℕ) :
    (repoint { a with sizes := sz }
        fuel i tgt stop).aux =
      (repoint a fuel i tgt stop).aux := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [repoint]
      split
      · rfl
      · exact ih (a := { a with aux := setPair a.aux i tgt }) _

/-- The mapping component of a merge: the two-entry swap over the untouched mapping. -/
theorem merge_mapping (a : Asm) (fuel : ℕ) (lp rp : ℕ × ℕ) :
    (merge a fuel lp rp).mapping =
      setPair (setPair a.mapping lp (getPair a.mapping rp)) rp
        (getPair a.mapping lp) := by
  simp only [merge, repoint_mapping]

/-- The aux component of a merge: the re-pointing walk over the untouched aux, from and
to the absorbed representative, targeting the surviving one. -/
theorem merge_aux (a : Asm) (fuel : ℕ) (lp rp : ℕ × ℕ) :
    (merge a fuel lp rp).aux =
      (repoint a fuel
        (if getNat a.sizes (getPair a.aux lp) < getNat a.sizes (getPair a.aux rp)
          then getPair a.aux lp else getPair a.aux rp)
        (if getNat a.sizes (getPair a.aux lp) < getNat a.sizes (getPair a.aux rp)
          then getPair a.aux rp else getPair a.aux lp)
        (if getNat a.sizes (getPair a.aux lp) < getNat a.sizes (getPair a.aux rp)
          then getPair a.aux lp else getPair a.aux rp)).aux := by
  simp only [merge, repoint_aux_sizes]

/-- One assembly `copy` simulates one abstract merge step, with walk fuel covering any
cycle length. -/
theorem Sim.copy {numCols n : ℕ} {a : Asm} {π : Perm (FlatCell numCols n)}
    (sim : Sim a π) (l r : FlatCell numCols n) :
    Sim (Asm.copy a (n * numCols)
        l.pair.1 l.pair.2 r.pair.1 r.pair.2)
      (PermConstruction.step π (l, r)) := by
  classical
  obtain ⟨L, hL, hLcyc, hLroot⟩ := sim.aux_rep l
  obtain ⟨R, hR, hRcyc, hRroot⟩ := sim.aux_rep r
  have hpl : ((l.pair.1, l.pair.2) : ℕ × ℕ) = l.pair := rfl
  have hpr : ((r.pair.1, r.pair.2) : ℕ × ℕ) = r.pair := rfl
  rw [Asm.copy, PermConstruction.step]
  by_cases hsame : π.SameCycle l r
  · have heq : getPair a.aux l.pair = getPair a.aux r.pair :=
      (sim.aux_eq_iff l r).mpr hsame
    rw [if_pos hsame, if_pos (by simpa [hpl, hpr] using heq)]
    exact sim
  · have hbeq : ¬ (getPair a.aux (l.pair.1, l.pair.2) ==
        getPair a.aux (r.pair.1, r.pair.2)) = true := by
      simp only [hpl, hpr, beq_iff_eq]
      exact fun h => hsame ((sim.aux_eq_iff l r).mp h)
    rw [if_neg hsame, if_neg hbeq]
    -- representative cells and their source cells, by the size comparison
    set RC : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then L else R with hRC
    set LC : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then R else L with hLC
    set u : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then l else r with hu
    set v : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then r else l with hv
    have hRCpair : (if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
        getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2))
        then getPair a.aux (l.pair.1, l.pair.2)
        else getPair a.aux (r.pair.1, r.pair.2)) = RC.pair := by
      rw [hRC]; split <;> simp [hpl, hpr, hL, hR]
    have hLCpair : (if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
        getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2))
        then getPair a.aux (r.pair.1, r.pair.2)
        else getPair a.aux (l.pair.1, l.pair.2)) = LC.pair := by
      rw [hLC]; split <;> simp [hpl, hpr, hL, hR]
    have hRCcyc : π.SameCycle u RC := by
      rw [hRC, hu]; split <;> assumption
    have hLCcyc : π.SameCycle v LC := by
      rw [hLC, hv]; split <;> assumption
    have hLCroot : getPair a.aux LC.pair = LC.pair := by
      rw [hLC]; split <;> assumption
    have hvrep : getPair a.aux v.pair = LC.pair := by
      rw [hv, hLC]; split <;> assumption
    have huv : ¬ π.SameCycle u v := by
      rw [hu, hv]
      split
      · exact hsame
      · exact fun h => hsame h.symm
    have hRCLC : ¬ π.SameCycle RC LC :=
      fun h => huv (hRCcyc.trans (h.trans hLCcyc.symm))
    obtain ⟨sN, ⟨hs1, hsret⟩, hsle, hsmin⟩ := π.exists_minimal_return RC
    have hsle : sN ≤ numCols * n := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using hsle
    -- the aux component after the merge, cycle by cycle
    have haux2 : ∀ d : FlatCell numCols n,
        getPair (merge a (n * numCols)
            (l.pair.1, l.pair.2) (r.pair.1, r.pair.2)).aux d.pair =
          if π.SameCycle RC d then LC.pair else getPair a.aux d.pair := by
      intro d
      rw [merge_aux, hRCpair, hLCpair]
      rw [getPair_repoint_aux sim.aux_shape sim.map_eq sN RC RC LC.pair
        hsret hs1 hsmin (n * numCols)
        (le_trans hsle (le_of_eq (Nat.mul_comm _ _))) d]
      by_cases hcyc : π.SameCycle RC d
      · rw [if_pos ((Equiv.Perm.sameCycle_iff_exists_pow_lt hs1 hsret d).mp hcyc), if_pos hcyc]
      · rw [if_neg (fun h => hcyc ((Equiv.Perm.sameCycle_iff_exists_pow_lt hs1 hsret d).mpr h)),
          if_neg hcyc]
    have hlr : l ≠ r := fun h => hsame (h ▸ Equiv.Perm.SameCycle.refl π l)
    have hlrpair : l.pair ≠ r.pair := fun h => hlr (FlatCell.pair_injective h)
    have hmerge : ∀ c d : FlatCell numCols n,
        (π * Equiv.swap l r).SameCycle c d ↔ PermConstruction.MergeRel π l r c d :=
      PermConstruction.sameCycle_mul_swap hsame
    have huvlr : (u = l ∧ v = r) ∨ (u = r ∧ v = l) := by
      rw [hu, hv]
      split
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    -- membership in the absorbed cycle relates through the merge to the surviving one
    have hMergeOfRC : ∀ {e : FlatCell numCols n}, π.SameCycle RC e →
        ∀ {f : FlatCell numCols n}, π.SameCycle v f →
        PermConstruction.MergeRel π l r e f := by
      intro e he f hf
      have heu : π.SameCycle e u := he.symm.trans hRCcyc.symm
      have hfv : π.SameCycle f v := hf.symm
      rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
      · exact Or.inr (Or.inl ⟨hul ▸ heu, hvr ▸ hfv⟩)
      · exact Or.inr (Or.inr ⟨hur ▸ heu, hvl ▸ hfv⟩)
    have hMergeElim : ∀ {e f : FlatCell numCols n},
        PermConstruction.MergeRel π l r e f → π.SameCycle RC e →
        ¬ π.SameCycle RC f → π.SameCycle v f := by
      intro e f hm he hf
      rcases hm with hm | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (he.trans hm) hf
      · -- e ~ l, f ~ r
        rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
        · exact hvr ▸ h2.symm
        · exact absurd ((((hur ▸ hRCcyc : π.SameCycle r RC).trans he).trans h1).symm)
            hsame
      · -- e ~ r, f ~ l
        rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
        · exact absurd (((hul ▸ hRCcyc : π.SameCycle l RC).trans he).trans h1) hsame
        · exact hvl ▸ h2.symm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- mapping shape: two writes over the untouched mapping
      rw [merge_mapping]
      exact (sim.map_shape.setPair _ _).setPair _ _
    · -- aux shape: one walk over the untouched aux
      rw [merge_aux]
      exact Shaped.repoint sim.aux_shape _ _ _ _
    · -- the mapping acts as the merged permutation
      intro c
      rw [merge_mapping, hpl, hpr]
      have hswap : (π * Equiv.swap l r) c = π (Equiv.swap l r c) :=
        Equiv.Perm.mul_apply _ _ _
      by_cases hcr : c = r
      · subst hcr
        rw [getPair_setPair_self (sim.map_shape.setPair _ _) c.1.isLt c.2.isLt,
          sim.map_eq l, hswap, Equiv.swap_apply_right]
      · have hcrpair : c.pair ≠ r.pair := fun h => hcr (FlatCell.pair_injective h)
        rw [getPair_setPair_ne (sim.map_shape.setPair _ _) hcrpair]
        by_cases hcl : c = l
        · subst hcl
          rw [getPair_setPair_self sim.map_shape c.1.isLt c.2.isLt,
            sim.map_eq r, hswap, Equiv.swap_apply_left]
        · have hclpair : c.pair ≠ l.pair := fun h => hcl (FlatCell.pair_injective h)
          rw [getPair_setPair_ne sim.map_shape hclpair, sim.map_eq c, hswap,
            Equiv.swap_apply_of_ne_of_ne hcl hcr]
    · -- every cell keeps an in-cycle, self-rooted representative
      intro c
      by_cases hc : π.SameCycle RC c
      · refine ⟨LC, by rw [haux2 c, if_pos hc], ?_, ?_⟩
        · exact (hmerge c LC).mpr (hMergeOfRC hc hLCcyc)
        · rw [haux2 LC, if_neg hRCLC]
          exact hLCroot
      · obtain ⟨rep, hrep, hrepcyc, hreproot⟩ := sim.aux_rep c
        refine ⟨rep, by rw [haux2 c, if_neg hc]; exact hrep,
          (hmerge c rep).mpr (Or.inl hrepcyc), ?_⟩
        have hrc : ¬ π.SameCycle RC rep := fun h => hc (h.trans hrepcyc.symm)
        rw [haux2 rep, if_neg hrc]
        exact hreproot
    · -- aux entries agree exactly on merged cycles
      intro c d
      rw [haux2 c, haux2 d, hmerge c d]
      by_cases hc : π.SameCycle RC c <;> by_cases hd : π.SameCycle RC d
      · rw [if_pos hc, if_pos hd]
        exact ⟨fun _ => Or.inl (hc.symm.trans hd), fun _ => rfl⟩
      · rw [if_pos hc, if_neg hd]
        constructor
        · intro h
          have hdv : π.SameCycle d v :=
            (sim.aux_eq_iff d v).mp (by rw [hvrep, ← h])
          exact hMergeOfRC hc hdv.symm
        · intro hm
          have hdv : π.SameCycle v d := hMergeElim hm hc hd
          have : getPair a.aux d.pair = getPair a.aux v.pair :=
            (sim.aux_eq_iff d v).mpr hdv.symm
          rw [this, hvrep]
      · rw [if_neg hc, if_pos hd]
        constructor
        · intro h
          have hcv : π.SameCycle c v :=
            (sim.aux_eq_iff c v).mp (by rw [hvrep, h])
          exact PermConstruction.mergeRel_symm (hMergeOfRC hd hcv.symm)
        · intro hm
          have hcv : π.SameCycle v c :=
            hMergeElim (PermConstruction.mergeRel_symm hm) hd hc
          have : getPair a.aux c.pair = getPair a.aux v.pair :=
            (sim.aux_eq_iff c v).mpr hcv.symm
          rw [this, hvrep]
      · rw [if_neg hc, if_neg hd, sim.aux_eq_iff c d]
        constructor
        · exact fun h => Or.inl h
        · intro hm
          rcases hm with hm | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hm
          · rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
            · exact absurd (h1.trans (hul ▸ hRCcyc)).symm hc
            · exact absurd (h2.trans (hur ▸ hRCcyc)).symm hd
          · rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
            · exact absurd (h2.trans (hul ▸ hRCcyc)).symm hd
            · exact absurd (h1.trans (hur ▸ hRCcyc)).symm hc

/-- The fresh assembly simulates the identity permutation. -/
theorem Sim.new (numCols n : ℕ) :
    Sim (numCols := numCols) (n := n)
      (Asm.new n numCols) 1 := by
  have hget : ∀ c : FlatCell numCols n,
      getPair ((Array.range numCols).map
        (fun i => initCol i n)) c.pair = c.pair := by
    intro c
    simp [getPair,
      initCol,
      FlatCell.pair, c.1.isLt, c.2.isLt]
  have hshape : Shaped numCols n ((Array.range numCols).map
      (fun i => initCol i n)) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    simp only [Array.size_map, Array.size_range] at hi
    simp [initCol]
  have hgetm : ∀ c : FlatCell numCols n,
      getPair (Asm.new n numCols).mapping c.pair =
        c.pair := fun c => hget c
  have hgeta : ∀ c : FlatCell numCols n,
      getPair (Asm.new n numCols).aux c.pair =
        c.pair := fun c => hget c
  refine ⟨hshape, hshape, ?_, ?_, ?_⟩
  · intro c
    simpa using hgetm c
  · intro c
    exact ⟨c, hgeta c, Equiv.Perm.SameCycle.refl 1 c, hgeta c⟩
  · intro c d
    rw [hgeta c, hgeta d]
    constructor
    · intro h
      rw [Equiv.Perm.sameCycle_one]
      exact FlatCell.pair_injective h
    · intro h
      rw [Equiv.Perm.sameCycle_one] at h
      rw [h]

/-- The simulation survives a whole copy fold. -/
theorem Sim.foldl {numCols n : ℕ}
    (copies : List (FlatCell numCols n × FlatCell numCols n))
    {a : Asm} {π : Perm (FlatCell numCols n)} (sim : Sim a π) :
    Sim (copies.foldl (fun st p =>
        Asm.copy st (n * numCols)
          p.1.pair.1 p.1.pair.2 p.2.pair.1 p.2.pair.2) a)
      (copies.foldl PermConstruction.step π) := by
  induction copies generalizing a π with
  | nil => exact sim
  | cons p rest ih => exact ih (sim.copy p.1 p.2)

/-- **The executable keygen assembly is the abstract replay**: on every cell, the final
`mapping` is the action of `PermConstruction.replay` over the same copies. -/
theorem runAssembly_getPair {numCols n : ℕ}
    (copies : List (FlatCell numCols n × FlatCell numCols n))
    (c : FlatCell numCols n) :
    getPair (runAssembly n numCols
        (copies.map fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2))) c.pair =
      ((PermConstruction.replay copies) c).pair := by
  rw [runAssembly]
  rw [List.foldl_map]
  rw [PermConstruction.replay_eq_foldl]
  exact (Sim.foldl copies (Sim.new numCols n)).map_eq c

variable [FieldDomainParams F]

/-- A generated σ-table entry is the δ/ω name of the replayed permutation's image cell:
the executable pipeline reads the assembly mapping at `(column, row)`, and the mapping's
action is the abstract replay. -/
theorem permutationRows_getD_eq {k numCols n : ℕ} (cs : ConstraintSystem F) (ops : Operations F)
    (hcount : numCols = (permColsOf cs).length) (hsize : n = 2 ^ k)
    (copies' : List (FlatCell numCols n × FlatCell numCols n))
    (hcopies : V1.copyList (permColsOf cs)
        (FloorPlanner.V1.starts ops) ops
        (constantCopyEntries cs ops) =
      copies'.map fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2))
    (g : Fin numCols) (j : Fin n) :
    ((permutationRows k cs ops).getD (g : ℕ) []).getD (j : ℕ) 0 =
      FieldDomainParams.delta ^ ((PermConstruction.replay copies' (g, j)).1 : ℕ) *
        FieldDomainParams.omega k ^ ((PermConstruction.replay copies' (g, j)).2 : ℕ) := by
  subst numCols n
  have hmap' : ((runAssembly (2 ^ k)
      (permColsOf cs).length (copies'.map fun p =>
        (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)))[(g : ℕ)]!)[(j : ℕ)]! =
      (PermConstruction.replay copies' (g, j)).pair :=
    runAssembly_getPair copies' (g, j)
  simp only [permutationRows]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range g.isLt, List.getElem?_range j.isLt,
    Option.map_some, Option.getD_some]
  rw [hcopies, hmap']
  simp only [FlatCell.pair]
  rw [deltaPowersArr_getElem! _
      (PermConstruction.replay copies' (g, j)).1.isLt,
    omegaPowersArr_getElem! _
      (PermConstruction.replay copies' (g, j)).2.isLt]

end Halo2.Layout.Asm
