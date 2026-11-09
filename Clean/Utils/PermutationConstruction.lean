import Mathlib.GroupTheory.Perm.Cycle.Factors

/-! # Building permutation cycles from equality pairs

Each new pair joins its endpoints' cycles. The resulting cycles are exactly the
equivalence closure of the input pairs. Replaying the reversed recursive build
processes the pairs in declaration order.
-/

open Equiv Equiv.Perm

namespace PermConstruction

variable {α : Type*} [DecidableEq α]

/-- The relation obtained from `π`'s cycle relation by merging the cycle of `a` with the cycle of `b`
(see `mergeRel_equivalence`: it is an equivalence relation). -/
def MergeRel (π : Perm α) (a b x y : α) : Prop :=
  π.SameCycle x y ∨ (π.SameCycle x a ∧ π.SameCycle y b) ∨ (π.SameCycle x b ∧ π.SameCycle y a)

omit [DecidableEq α] in
theorem mergeRel_refl (π : Perm α) (a b x : α) : MergeRel π a b x x :=
  Or.inl (SameCycle.refl π x)

omit [DecidableEq α] in
theorem mergeRel_symm {π : Perm α} {a b x y : α} (h : MergeRel π a b x y) :
    MergeRel π a b y x := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨h2, h1⟩)
  · exact Or.inr (Or.inl ⟨h2, h1⟩)

omit [DecidableEq α] in
theorem mergeRel_trans {π : Perm α} {a b x y z : α}
    (hxy : MergeRel π a b x y) (hyz : MergeRel π a b y z) : MergeRel π a b x z := by
  rcases hxy with hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (Or.inl ⟨hxy.trans hya, hzb⟩)
    · exact Or.inr (Or.inr ⟨hxy.trans hyb, hza⟩)
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨_, hza⟩
    · exact Or.inr (Or.inl ⟨hxa, hyz.symm.trans hyb⟩)
    · exact Or.inl (hxa.trans ((hya.symm.trans hyb).trans hzb.symm))
    · exact Or.inl (hxa.trans hza.symm)
  · rcases hyz with hyz | ⟨_, hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inr (Or.inr ⟨hxb, hyz.symm.trans hya⟩)
    · exact Or.inl (hxb.trans hzb.symm)
    · exact Or.inl (hxb.trans ((hya.symm.trans hyb).symm.trans hza.symm))

omit [DecidableEq α] in
theorem mergeRel_equivalence (π : Perm α) (a b : α) : Equivalence (MergeRel π a b) :=
  ⟨mergeRel_refl π a b, mergeRel_symm, mergeRel_trans⟩

/-- One step of `π * swap a b` stays within the merged relation. -/
theorem mergeRel_step (π : Perm α) (a b x : α) :
    MergeRel π a b x ((π * swap a b) x) := by
  have fwd : ∀ z : α, π.SameCycle z (π z) := fun z => ⟨1, by simp⟩
  rw [Perm.mul_apply]
  rcases eq_or_ne x a with rfl | hxa
  · rw [swap_apply_left]
    exact Or.inr (Or.inl ⟨SameCycle.refl π x, (fwd b).symm⟩)
  · rcases eq_or_ne x b with rfl | hxb
    · rw [swap_apply_right]
      exact Or.inr (Or.inr ⟨SameCycle.refl π x, (fwd a).symm⟩)
    · rw [swap_apply_of_ne_of_ne hxa hxb]
      exact Or.inl (fwd x)

/-- **Subset direction (unconditional).** Every `π * swap a b` cycle is contained in the merge of
`π`'s cycles at `a` and `b`: the new permutation never connects more than the merge allows. Proved by
showing the merged relation is closed along the `π * swap a b` orbit (it is an equivalence containing
each one-step pair, `mergeRel_step`). -/
theorem sameCycle_mul_swap_subset {π : Perm α} {a b x y : α}
    (h : (π * swap a b).SameCycle x y) : MergeRel π a b x y := by
  have key : ∀ (n : ℤ) (x : α), MergeRel π a b x (((π * swap a b) ^ n) x) := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; simpa using mergeRel_refl π a b x
    | succ i ih =>
        intro x
        have hstep : ((π * swap a b) ^ ((i : ℤ) + 1)) x
            = ((π * swap a b) ^ (i : ℤ)) ((π * swap a b) x) := by
          rw [zpow_add, zpow_one, Perm.mul_apply]
        rw [hstep]
        exact mergeRel_trans (mergeRel_step π a b x) (ih ((π * swap a b) x))
    | pred i ih =>
        intro x
        have hstep : ((π * swap a b) ^ (-(i : ℤ) - 1)) x
            = ((π * swap a b) ^ (-(i : ℤ))) (((π * swap a b)⁻¹) x) := by
          rw [show (-(i : ℤ) - 1) = (-(i : ℤ)) + (-1) from by ring, zpow_add, zpow_neg_one,
            Perm.mul_apply]
        rw [hstep]
        have hb := mergeRel_step π a b (((π * swap a b)⁻¹) x)
        have hpiv : (π * swap a b) (((π * swap a b)⁻¹) x) = x := by simp
        rw [hpiv] at hb
        exact mergeRel_trans (mergeRel_symm hb) (ih ((π * swap a b)⁻¹ x))
  obtain ⟨n, rfl⟩ := h
  exact key n x

/-- **The orbit walk.** Under `g = π * swap a b`, iterating from `a` follows `b`'s `π`-cycle: as long
as we stay strictly inside the first `p` steps of `b`'s orbit — where `π^k b` avoids both `a` (it is in
`b`'s orbit, disjoint from `a`'s, hypothesis `hnotA`) and `b` itself (not yet returned, hypothesis
`hltb`) — the transposition is invisible and `g^[k+1] a = π^[k+1] b`. Pure orbit arithmetic; no
finiteness needed. -/
theorem iterate_mul_swap_apply_eq_of_lt {π : Perm α} {a b : α} {p : ℕ}
    (hnotA : ∀ k : ℕ, (⇑π)^[k] b ≠ a)
    (hltb : ∀ k : ℕ, 0 < k → k < p → (⇑π)^[k] b ≠ b) :
    ∀ k : ℕ, k < p → (⇑(π * swap a b))^[k + 1] a = (⇑π)^[k + 1] b := by
  have hga : (⇑(π * swap a b)) a = (⇑π) b := by rw [Perm.mul_apply, swap_apply_left]
  have hgz : ∀ z : α, z ≠ a → z ≠ b → (⇑(π * swap a b)) z = (⇑π) z := by
    intro z hza hzb; rw [Perm.mul_apply, swap_apply_of_ne_of_ne hza hzb]
  intro k
  induction k with
  | zero =>
      intro _
      simp only [zero_add, Function.iterate_one]
      exact hga
  | succ k ih =>
      intro hkp
      have hk : k < p := Nat.lt_of_succ_lt hkp
      have hA : (⇑π)^[k + 1] b ≠ a := hnotA (k + 1)
      have hB : (⇑π)^[k + 1] b ≠ b := hltb (k + 1) (Nat.succ_pos k) hkp
      calc (⇑(π * swap a b))^[k + 1 + 1] a
          = (⇑(π * swap a b)) ((⇑(π * swap a b))^[k + 1] a) := Function.iterate_succ_apply' _ _ _
        _ = (⇑(π * swap a b)) ((⇑π)^[k + 1] b) := by rw [ih hk]
        _ = (⇑π) ((⇑π)^[k + 1] b) := hgz _ hA hB
        _ = (⇑π)^[k + 1 + 1] b := (Function.iterate_succ_apply' _ _ _).symm

/-- **The merge witness (the one finiteness-using fact).** If `a` and `b` lie in different cycles of
`π`, then composing with the transposition `(a b)` puts them in the same cycle. We walk `b`'s `π`-cycle
(`iterate_mul_swap_apply_eq_of_lt`) for its full period `p = minimalPeriod π b`, reaching
`π^[p] b = b` from `a` in `p` steps. -/
theorem sameCycle_mul_swap_self [Fintype α] {π : Perm α} {a b : α} (hab : ¬ π.SameCycle a b) :
    (π * swap a b).SameCycle a b := by
  -- `π^[k] b` is never `a` (same cycle as `b`, which differs from `a`'s cycle)
  have hnotA : ∀ k : ℕ, (⇑π)^[k] b ≠ a := by
    intro k hk
    have hsc : π.SameCycle b a := ⟨(k : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]; exact hk⟩
    exact hab hsc.symm
  set p := Function.minimalPeriod (⇑π) b with hp
  -- `b` is a periodic point (finite group), with minimal period `p`
  have hper : Function.IsPeriodicPt (⇑π) (orderOf π) b := by
    show (⇑π)^[orderOf π] b = b
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]; rfl
  have hpb : (⇑π)^[p] b = b := Function.iterate_minimalPeriod
  have hppos : 0 < p := Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos π) hper
  have hltb : ∀ k : ℕ, 0 < k → k < p → (⇑π)^[k] b ≠ b := by
    intro k hk0 hkp h0
    exact Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hk0.ne' hkp h0
  -- walk `b`'s cycle for a full period: `g^[p] a = π^[p] b = b`
  have hreach : (⇑(π * swap a b))^[p] a = b := by
    have hw := iterate_mul_swap_apply_eq_of_lt hnotA hltb (p - 1) (by omega)
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1] at hw
    rw [hw, hpb]
  exact ⟨(p : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]; exact hreach⟩

/-- **Monotonicity.** When `a`, `b` are in different `π`-cycles, composing with `(a b)` only *merges*
cycles — it never splits one — so every `π`-cycle relation survives in `π * swap a b`. Proved by
running the (unconditional) subset lemma backwards through `π = (π * swap a b) * swap a b`. -/
theorem sameCycle_mul_swap_mono [Fintype α] {π : Perm α} {a b : α} (hab : ¬ π.SameCycle a b)
    {u v : α} (huv : π.SameCycle u v) : (π * swap a b).SameCycle u v := by
  have hab' : (π * swap a b).SameCycle a b := sameCycle_mul_swap_self hab
  have hsub : ((π * swap a b) * swap a b).SameCycle u v := by
    rwa [mul_assoc, swap_mul_self, mul_one]
  rcases sameCycle_mul_swap_subset hsub with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · exact h1.trans (hab'.trans h2.symm)
  · exact h1.trans (hab'.symm.trans h2.symm)

/-- **Cycle-merge lemma.** Composing `π` with the transposition `(a b)`, when `a` and `b` are in
different `π`-cycles, merges those two cycles and leaves all others unchanged:
`(π * swap a b).SameCycle x y ↔ MergeRel π a b x y`. (If `a`, `b` were in the *same* cycle, the same
composition would split it — this is the "Broken alternatives" of the design doc.) -/
theorem sameCycle_mul_swap [Fintype α] {π : Perm α} {a b : α} (hab : ¬ π.SameCycle a b)
    (x y : α) :
    (π * swap a b).SameCycle x y ↔ MergeRel π a b x y := by
  refine ⟨sameCycle_mul_swap_subset, fun h => ?_⟩
  have hab' : (π * swap a b).SameCycle a b := sameCycle_mul_swap_self hab
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact sameCycle_mul_swap_mono hab h
  · exact (sameCycle_mul_swap_mono hab h1).trans (hab'.trans (sameCycle_mul_swap_mono hab h2).symm)
  · exact (sameCycle_mul_swap_mono hab h1).trans
      (hab'.symm.trans (sameCycle_mul_swap_mono hab h2).symm)

/-! ## The construction algorithm (union-find fold over copy constraints) -/

variable [Fintype α]

/-- One copy constraint `(a, b)`: merge the cycles of `a` and `b`, unless they are already in the same
cycle (the disjoint-set "already connected" check — essential: composing with `(a b)` when `a`, `b` are
already in one cycle would *split* it, undoing constraints). -/
def step (π : Perm α) (ab : α × α) : Perm α :=
  if π.SameCycle ab.1 ab.2 then π else π * swap ab.1 ab.2

/-- Run the algorithm over a list of copy constraints, starting from the identity permutation (every
cell its own 1-cycle). Constraint order does not affect the final cycle *partition* — it is the
equivalence closure either way (`sameCycle_build_iff`) — though it does affect the exact permutation. -/
def build : List (α × α) → Perm α
  | [] => 1
  | ab :: rest => step (build rest) ab

/-- **Every declared copy constraint ends up in one cycle.** (The soundness-relevant direction: each
`a ≡ b` the circuit asked for is enforced by `σ`.) -/
theorem sameCycle_build_of_mem (cs : List (α × α)) : ∀ p ∈ cs, (build cs).SameCycle p.1 p.2 := by
  induction cs with
  | nil => intro p hp; simp at hp
  | cons ab rest ih =>
      obtain ⟨a, b⟩ := ab
      intro p hp
      show (step (build rest) (a, b)).SameCycle p.1 p.2
      unfold step
      rcases List.mem_cons.mp hp with rfl | hpr
      · by_cases hsc : (build rest).SameCycle a b
        · rw [if_pos hsc]; exact hsc
        · rw [if_neg hsc]; exact sameCycle_mul_swap_self hsc
      · have hp' := ih p hpr
        by_cases hsc : (build rest).SameCycle a b
        · rw [if_pos hsc]; exact hp'
        · rw [if_neg hsc]; exact sameCycle_mul_swap_mono hsc hp'

/-- **No spurious merges.** Two cells share a `build cs` cycle only if the copy constraints force it. -/
theorem eqvGen_of_sameCycle_build : ∀ (cs : List (α × α)) {x y : α},
    (build cs).SameCycle x y → Relation.EqvGen (fun u v => (u, v) ∈ cs) x y := by
  intro cs
  induction cs with
  | nil =>
      intro x y h
      have h1 : (1 : Perm α).SameCycle x y := h
      rw [sameCycle_one] at h1
      subst h1
      exact Relation.EqvGen.refl x
  | cons ab rest ih =>
      obtain ⟨a, b⟩ := ab
      intro x y h
      have mono : ∀ {u v : α}, Relation.EqvGen (fun u v => (u, v) ∈ rest) u v →
          Relation.EqvGen (fun u v => (u, v) ∈ (a, b) :: rest) u v :=
        fun huv => Relation.EqvGen.mono (fun _ _ hm => List.mem_cons_of_mem _ hm) huv
      have hab_link : Relation.EqvGen (fun u v => (u, v) ∈ (a, b) :: rest) a b :=
        Relation.EqvGen.rel a b List.mem_cons_self
      have E : Equivalence (Relation.EqvGen (fun u v => (u, v) ∈ (a, b) :: rest)) :=
        Relation.EqvGen.is_equivalence _
      change (step (build rest) (a, b)).SameCycle x y at h
      unfold step at h
      by_cases hsc : (build rest).SameCycle a b
      · rw [if_pos hsc] at h
        exact mono (ih h)
      · rw [if_neg hsc] at h
        rcases (sameCycle_mul_swap hsc x y).mp h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mono (ih h1)
        · exact E.trans (mono (ih h1)) (E.trans hab_link (E.symm (mono (ih h2))))
        · exact E.trans (mono (ih h1)) (E.trans (E.symm hab_link) (E.symm (mono (ih h2))))

/-- **Correctness of the construction.** The cycles of the permutation built from a list of copy
constraints are exactly the equality-constraint classes: two cells are in the same cycle iff the
constraints (reflexively, symmetrically, transitively) force them equal. -/
theorem sameCycle_build_iff (cs : List (α × α)) (x y : α) :
    (build cs).SameCycle x y ↔ Relation.EqvGen (fun u v => (u, v) ∈ cs) x y := by
  refine ⟨eqvGen_of_sameCycle_build cs, fun h => ?_⟩
  -- `SameCycle (build cs)` contains every constraint pair (`sameCycle_build_of_mem`), and `EqvGen`
  -- is the least such equivalence, so it is contained in `SameCycle (build cs)`.
  induction h with
  | rel u v huv => exact sameCycle_build_of_mem cs (u, v) huv
  | refl u => exact SameCycle.refl _ u
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2

/-- Replay the mathematical keygen permutation in the source copy-list order.

`build` consumes its list from right to left, so reversing here makes the first
declared copy the first cycle merge.  The concrete array/union-find replay can be compared with
this permutation once its finite cell decoding is available. -/
def replay
    {cell : Type*} [DecidableEq cell] [Fintype cell]
    (copies : List (cell × cell)) : Equiv.Perm cell :=
  build copies.reverse

/-- Every copy processed by the generic keygen replay belongs to one resulting permutation cycle. -/
theorem sameCycle_replay_of_mem
    {cell : Type*} [DecidableEq cell] [Fintype cell]
    (copies : List (cell × cell)) {left right : cell}
    (hcopy : (left, right) ∈ copies) :
    (replay copies).SameCycle left right :=
  sameCycle_build_of_mem copies.reverse (left, right)
    (List.mem_reverse.mpr hcopy)

/-- The replayed cycles are exactly the equivalence closure of the declared copies. -/
theorem sameCycle_replay_iff
    {cell : Type*} [DecidableEq cell] [Fintype cell]
    (copies : List (cell × cell)) (left right : cell) :
    (replay copies).SameCycle left right ↔
      Relation.EqvGen (fun a b => (a, b) ∈ copies) left right := by
  simpa only [replay, List.mem_reverse] using
    sameCycle_build_iff copies.reverse left right

/--
A predicate containing both endpoints of every replayed copy is preserved by
the resulting permutation. This supplies the generic active-row closure fact
needed when restricting a full-domain keygen permutation.
-/
theorem replay_preserves
    {cell : Type*} [DecidableEq cell] [Fintype cell]
    (copies : List (cell × cell)) (predicate : cell → Prop)
    (hcopies : ∀ pair ∈ copies,
      predicate pair.1 ∧ predicate pair.2)
    (cell : cell) (hcell : predicate cell) :
    predicate (replay copies cell) := by
  have hedge : ∀ {left right},
      (left, right) ∈ copies →
        (predicate left ↔ predicate right) := by
    intro left right hpair
    obtain ⟨hleft, hright⟩ := hcopies (left, right) hpair
    exact ⟨fun _ => hright, fun _ => hleft⟩
  have hclosure : ∀ {left right},
      Relation.EqvGen (fun a b => (a, b) ∈ copies) left right →
        (predicate left ↔ predicate right) := by
    intro left right hrelation
    induction hrelation with
    | rel left right hpair =>
        exact hedge hpair
    | refl value =>
        exact Iff.rfl
    | symm left right _ ih =>
        exact ih.symm
    | trans left middle right _ _ ih₁ ih₂ =>
        exact ih₁.trans ih₂
  have hsame :
      (replay copies).SameCycle cell
        (replay copies cell) := by
    exact ⟨(1 : ℤ), by simp⟩
  exact
    (hclosure
      ((sameCycle_replay_iff copies _ _).mp hsame)).mp
        hcell

/-- The abstract replay is the copy-order fold of the merge step. -/
theorem replay_eq_foldl {cell : Type*} [DecidableEq cell] [Fintype cell]
    (copies : List (cell × cell)) :
    replay copies = copies.foldl step 1 := by
  have hbuild : ∀ l : List (cell × cell),
      build l = l.foldr (fun ab π => step π ab) 1 := by
    intro l
    induction l with
    | nil => rfl
    | cons ab rest ih => simp [build, ih]
  rw [replay, hbuild, List.foldr_reverse]

end PermConstruction

namespace Equiv.Perm

/-- Every cell has a first return time under a permutation of a finite type, bounded by
the type's cardinality. -/
theorem exists_minimal_return {α : Type*} [Fintype α] (π : Perm α)
    (rep : α) :
    ∃ s, (1 ≤ s ∧ (π ^ s) rep = rep) ∧ s ≤ Fintype.card α ∧
      ∀ t, 0 < t → t < s → (π ^ t) rep ≠ rep := by
  classical
  have hex : ∃ t, 1 ≤ t ∧ (π ^ t) rep = rep := by
    refine ⟨orderOf π, orderOf_pos π, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  let s := Nat.find hex
  have hfind := Nat.find_spec hex
  have hmin : ∀ t, 0 < t → t < s → (π ^ t) rep ≠ rep := by
    intro t ht hts habs
    exact Nat.find_min hex hts ⟨ht, habs⟩
  refine ⟨s, hfind, ?_, hmin⟩
  -- `t ↦ π ^ t rep` is injective below the first return, so `s` is at most the cell count
  have hinj : Set.InjOn (fun t => (π ^ t) rep) (Finset.range s) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    by_contra hne
    -- w.l.o.g. x < y; then `π ^ (y - x) rep = rep` strictly before `s`
    rcases Nat.lt_or_ge x y with hlt | hge
    · have : (π ^ (y - x)) rep = rep := by
        apply (Equiv.injective (π ^ x))
        rw [← mul_apply, ← pow_add]
        rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
        exact hxy.symm
      exact hmin (y - x) (by omega) (by omega) this
    · have hlt' : y < x := by omega
      have : (π ^ (x - y)) rep = rep := by
        apply (Equiv.injective (π ^ y))
        rw [← mul_apply, ← pow_add]
        rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt')]
        exact hxy
      exact hmin (x - y) (by omega) (by omega) this
  have hcard := Finset.card_le_card_of_injOn (fun t => (π ^ t) rep)
    (fun x _ => Finset.mem_univ _) hinj
  simpa using hcard

/-- Below the first return time, the orbit segment of a cell is exactly its cycle. -/
theorem sameCycle_iff_exists_pow_lt {α : Type*} [Fintype α] {π : Perm α}
    {rep : α} {s : ℕ} (hs1 : 1 ≤ s) (hs : (π ^ s) rep = rep)
    (d : α) :
    π.SameCycle rep d ↔ ∃ t, t < s ∧ (π ^ t) rep = d := by
  classical
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
    have hq : ∀ q, (π ^ (s * q)) rep = rep := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih =>
          rw [Nat.mul_succ, pow_add, mul_apply, hs]
          exact ih
    refine ⟨i % s, Nat.mod_lt _ (by omega), ?_⟩
    conv_rhs => rw [← hi, ← Nat.mod_add_div i s]
    rw [pow_add, mul_apply, hq]
  · rintro ⟨t, _, rfl⟩
    exact ⟨(t : ℤ), by simp⟩

end Equiv.Perm
