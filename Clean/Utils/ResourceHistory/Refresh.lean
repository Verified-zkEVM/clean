module

public import Clean.Utils.ResourceHistory.Ranked

/-! # Elimination of administrative resource refreshes

A refresh consumes a record and emits an observation-equal record at a later version.
Such rows can maintain bounded-difference timestamp checks for resources that are
otherwise untouched for long periods.

Elimination retains every real access with its successor unchanged, rewrites predecessors
to observation-equal records at no later versions, and preserves boundary balance.
Include resource identity in the observation function, as well as architectural value.
The theorem retains occurrence correspondence through `Multiset.Rel`. -/

@[expose] public section

namespace Utils.ResourceHistory.Refresh

universe u v

variable {α : Type u} {β : Type v}

section Defs

variable (value : α → β) (time : α → ℕ)

/-- A touch survives elimination with its push unchanged and its pull rewritten to a value-equal
record at a no-later time. -/
def EdgeRewrite (orig rewr : α × α) : Prop :=
  rewr.2 = orig.2 ∧ value rewr.1 = value orig.1 ∧ time rewr.1 ≤ time orig.1

/-- A boundary pull survives elimination rewritten to a value-equal record at a no-later time. -/
def RecordRewrite (orig rewr : α) : Prop :=
  value rewr = value orig ∧ time rewr ≤ time orig

/-- A refresh touch: the pushed record has the pulled record's value at a strictly later time. -/
def IsRefresh (r : α × α) : Prop :=
  value r.1 = value r.2 ∧ time r.1 < time r.2

end Defs

/-- **Refresh elimination.** From a balanced touch multiset split into plain touches `N` and
refreshes `R`, produce a refresh-free balanced multiset: the plain touches survive `EdgeRewrite`-
related (push unchanged, pull value-equal at a no-later time), the boundary pulls survive
`RecordRewrite`-related, and the boundary pushes `init` are untouched. -/
theorem eliminate [DecidableEq α] (value : α → β) (time : α → ℕ) (init : Multiset α) :
    ∀ (n : ℕ) (R N : Multiset (α × α)) (fin : Multiset α), R.card = n →
    (∀ r ∈ R, IsRefresh value time r) →
    init + (N + R).map Prod.snd = fin + (N + R).map Prod.fst →
    ∃ (N' : Multiset (α × α)) (fin' : Multiset α),
      init + N'.map Prod.snd = fin' + N'.map Prod.fst ∧
      Multiset.Rel (EdgeRewrite value time) N N' ∧
      Multiset.Rel (RecordRewrite value time) fin fin'
  | 0, R, N, fin, hcard, _, balanced => by
      rw [Multiset.card_eq_zero.mp hcard, add_zero] at balanced
      exact ⟨N, fin, balanced,
        Multiset.rel_refl_of_refl_on fun e _ => ⟨rfl, rfl, le_refl _⟩,
        Multiset.rel_refl_of_refl_on fun a _ => ⟨rfl, le_refl _⟩⟩
  | n + 1, R, N, fin, hcard, hrefresh, balanced => by
      -- Pop one refresh `r`; its pushed record `r.2` is pulled somewhere other than by `r` itself.
      have hR0 : R ≠ 0 := by
        intro h
        rw [h] at hcard
        exact absurd hcard.symm (Nat.succ_ne_zero n)
      obtain ⟨r, hrR⟩ := Multiset.exists_mem_of_ne_zero hR0
      obtain ⟨hval, htime⟩ := hrefresh r hrR
      have hne : r.1 ≠ r.2 := fun h => absurd htime (by rw [h]; exact lt_irrefl _)
      set S := R.erase r with hS
      have hconsS : r ::ₘ S = R := Multiset.cons_erase hrR
      have hcardS : S.card = n := by
        have := congrArg Multiset.card hconsS
        rw [Multiset.card_cons] at this
        omega
      have hrefreshS : ∀ r' ∈ S, IsRefresh value time r' := fun r' hr' =>
        hrefresh r' (Multiset.mem_of_le (Multiset.erase_le r R) hr')
      -- The shifted balance with `r`'s own contributions isolated.
      have hbal : init + (r.2 ::ₘ (N + S).map Prod.snd) =
          fin + (r.1 ::ₘ (N + S).map Prod.fst) := by
        have := balanced
        rw [← hconsS, show N + (r ::ₘ S) = r ::ₘ (N + S) from by
            rw [Multiset.add_cons]] at this
        simp only [Multiset.map_cons] at this
        exact this
      -- `r.2` is pulled: it appears on the pull side minus `r`'s own pull.
      have hmem : r.2 ∈ fin + (N + S).map Prod.fst := by
        have hin : r.2 ∈ fin + (r.1 ::ₘ (N + S).map Prod.fst) := by
          rw [← hbal]
          exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self _ _))
        rcases Multiset.mem_add.mp hin with h | h
        · exact Multiset.mem_add.mpr (Or.inl h)
        · rcases Multiset.mem_cons.mp h with h | h
          · exact absurd h.symm hne
          · exact Multiset.mem_add.mpr (Or.inr h)
      -- Cancel `r.2` on both sides of a cons-shaped balance.
      have cancel : ∀ {s t : Multiset α}, r.2 ::ₘ s = r.2 ::ₘ t → s = t :=
        fun h => (Multiset.cons_inj_right _).mp h
      rcases Multiset.mem_add.mp hmem with hfin | hpull
      · -- The boundary pulls `r.2`: rewrite that boundary pull down to `r.1`.
        have hbalA : init + (N + S).map Prod.snd =
            (r.1 ::ₘ fin.erase r.2) + (N + S).map Prod.fst := by
          apply cancel
          calc r.2 ::ₘ (init + (N + S).map Prod.snd)
              = init + (r.2 ::ₘ (N + S).map Prod.snd) := by rw [Multiset.add_cons]
            _ = fin + (r.1 ::ₘ (N + S).map Prod.fst) := hbal
            _ = (r.2 ::ₘ fin.erase r.2) + (r.1 ::ₘ (N + S).map Prod.fst) := by
                rw [Multiset.cons_erase hfin]
            _ = r.2 ::ₘ ((r.1 ::ₘ fin.erase r.2) + (N + S).map Prod.fst) := by
                rw [Multiset.cons_add, Multiset.cons_add, Multiset.add_cons,
                  Multiset.cons_swap]
        obtain ⟨N', fin', bal', relN, relF⟩ :=
          eliminate value time init n S N (r.1 ::ₘ fin.erase r.2) hcardS hrefreshS hbalA
        -- Strengthen the rewritten head `r.1 ↦ f'` to `r.2 ↦ f'` through the refresh.
        obtain ⟨f', finRest', hf', relRest, hfin'⟩ := Multiset.rel_cons_left.mp relF
        refine ⟨N', fin', bal', relN, ?_⟩
        rw [← Multiset.cons_erase hfin, hfin']
        exact Multiset.Rel.cons ⟨hf'.1.trans hval, hf'.2.trans htime.le⟩ relRest
      · -- A touch pulls `r.2`: rewrite its pull to `r.1`; if it is itself a refresh, fuse.
        rcases Multiset.mem_add.mp (by
            rw [Multiset.map_add] at hpull; exact hpull) with hN | hR
        · -- A plain touch `e ∈ N` pulls `r.2`.
          obtain ⟨e, heN, he1⟩ := Multiset.mem_map.mp hN
          have hbalB : init + ((r.1, e.2) ::ₘ N.erase e + S).map Prod.snd =
              fin + ((r.1, e.2) ::ₘ N.erase e + S).map Prod.fst := by
            simp only [Multiset.cons_add, Multiset.map_cons]
            apply cancel
            calc r.2 ::ₘ (init + (e.2 ::ₘ ((N.erase e + S).map Prod.snd)))
                = init + (r.2 ::ₘ (N + S).map Prod.snd) := by
                  rw [show (N + S).map Prod.snd = e.2 ::ₘ (N.erase e + S).map Prod.snd from by
                    rw [← Multiset.cons_erase heN, Multiset.cons_add, Multiset.map_cons,
                      Multiset.erase_cons_head],
                    Multiset.add_cons, Multiset.add_cons, Multiset.cons_swap]
                  rw [Multiset.add_cons, Multiset.cons_swap]
              _ = fin + (r.1 ::ₘ (N + S).map Prod.fst) := hbal
              _ = r.2 ::ₘ (fin + (r.1 ::ₘ ((N.erase e + S).map Prod.fst))) := by
                  rw [show (N + S).map Prod.fst = r.2 ::ₘ (N.erase e + S).map Prod.fst from by
                    rw [← Multiset.cons_erase heN, Multiset.cons_add, Multiset.map_cons, he1,
                      Multiset.erase_cons_head],
                    Multiset.add_cons, Multiset.add_cons, Multiset.cons_swap]
                  rw [Multiset.add_cons]
          obtain ⟨N', fin', bal', relN, relF⟩ :=
            eliminate value time init n S ((r.1, e.2) ::ₘ N.erase e) fin hcardS hrefreshS hbalB
          -- Strengthen the rewritten head `(r.1, e.2) ↦ x'` to `e ↦ x'` through the refresh.
          obtain ⟨x', rest', hx', relRest, hN'⟩ := Multiset.rel_cons_left.mp relN
          refine ⟨N', fin', bal', ?_, relF⟩
          rw [← Multiset.cons_erase heN, hN']
          exact Multiset.Rel.cons
            ⟨hx'.1, hx'.2.1.trans (hval.trans (congrArg value he1).symm),
              hx'.2.2.trans (htime.le.trans (le_of_eq (congrArg time he1).symm))⟩ relRest
        · -- Another refresh `e ∈ S` pulls `r.2`: fuse the two refreshes into `(r.1, e.2)`.
          obtain ⟨e, heS, he1⟩ := Multiset.mem_map.mp hR
          obtain ⟨hvalE, htimeE⟩ := hrefreshS e heS
          have hbalB : init + (N + ((r.1, e.2) ::ₘ S.erase e)).map Prod.snd =
              fin + (N + ((r.1, e.2) ::ₘ S.erase e)).map Prod.fst := by
            rw [show N + ((r.1, e.2) ::ₘ S.erase e) = (r.1, e.2) ::ₘ (N + S.erase e) from
              Multiset.add_cons _ _ _]
            simp only [Multiset.map_cons]
            apply cancel
            calc r.2 ::ₘ (init + (e.2 ::ₘ ((N + S.erase e).map Prod.snd)))
                = init + (r.2 ::ₘ (N + S).map Prod.snd) := by
                  rw [show (N + S).map Prod.snd = e.2 ::ₘ (N + S.erase e).map Prod.snd from by
                    rw [← Multiset.cons_erase heS, Multiset.add_cons, Multiset.map_cons,
                      Multiset.erase_cons_head],
                    Multiset.add_cons, Multiset.add_cons, Multiset.cons_swap]
                  rw [Multiset.add_cons, Multiset.cons_swap]
              _ = fin + (r.1 ::ₘ (N + S).map Prod.fst) := hbal
              _ = r.2 ::ₘ (fin + (r.1 ::ₘ ((N + S.erase e).map Prod.fst))) := by
                  rw [show (N + S).map Prod.fst = r.2 ::ₘ (N + S.erase e).map Prod.fst from by
                    rw [← Multiset.cons_erase heS, Multiset.add_cons, Multiset.map_cons, he1,
                      Multiset.erase_cons_head],
                    Multiset.add_cons, Multiset.add_cons, Multiset.cons_swap]
                  rw [Multiset.add_cons]
          have hcard' : ((r.1, e.2) ::ₘ S.erase e).card = n := by
            have := congrArg Multiset.card (Multiset.cons_erase heS)
            rw [Multiset.card_cons] at this
            rw [Multiset.card_cons]
            omega
          have hrefresh' : ∀ r' ∈ (r.1, e.2) ::ₘ S.erase e, IsRefresh value time r' := by
            intro r' hr'
            rcases Multiset.mem_cons.mp hr' with rfl | hr'
            · exact ⟨hval.trans ((congrArg value he1).symm.trans hvalE),
                htime.trans (lt_of_eq_of_lt (congrArg time he1).symm htimeE)⟩
            · exact hrefreshS r' (Multiset.mem_of_le (Multiset.erase_le e S) hr')
          exact eliminate value time init n ((r.1, e.2) ::ₘ S.erase e) N fin
            hcard' hrefresh' hbalB

end Utils.ResourceHistory.Refresh
