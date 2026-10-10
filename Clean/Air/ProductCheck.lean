module

public import Clean.Air.Balance
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-!
## Integer multiplicities and the product check

Over a field of characteristic `2`, multiplicities read in the field cannot tell a push from a pull,
since `-1 = 1`. Taking the multiplicity ring `M = ℤ` instead makes balance an exact identity of
multisets in any characteristic: the messages pushed, each as often as its positive multiplicity,
are the messages pulled, each as often as its negative one (`balancedInteractions_iff_pushed_eq_pulled`).

Proof systems check such an identity through a product of linear factors, one per message,
at a message fingerprint. This file proves the algebra that makes that check sound, independently
of the characteristic: equal products as polynomials force equal multisets, given an injective
fingerprint into an integral domain (`balancedInteractions_of_fingerprintProduct_eq`), and a
multiplicity committed as bits `m = ∑ b_k 2^k` contributes the factor `P^m` as the product of
the leaves `1 + b_k (P^(2^k) - 1)` (`prod_one_add_bit_mul_pow_two_pow_sub_one`).
The random evaluation of the polynomials is the cryptographic step and is not modelled here.
-/

open Polynomial

variable {F : Type} [DecidableEq F]

/-- The messages an interaction list pushes, each as often as its positive multiplicity. -/
def pushedMessages (interactions : List (Interaction F ℤ)) : Multiset (Array F) :=
  (interactions.map fun i => Multiset.replicate i.mult.toNat i.msg).sum

/-- The messages an interaction list pulls, each as often as its negative multiplicity. -/
def pulledMessages (interactions : List (Interaction F ℤ)) : Multiset (Array F) :=
  (interactions.map fun i => Multiset.replicate (-i.mult).toNat i.msg).sum

lemma balanceOf_eq_count_pushed_sub_count_pulled (interactions : List (Interaction F ℤ)) (msg : Array F) :
    balanceOf interactions msg =
      ((pushedMessages interactions).count msg : ℤ) - (pulledMessages interactions).count msg := by
  induction interactions with
  | nil => simp [balanceOf, pushedMessages, pulledMessages]
  | cons i is ih =>
    rw [balanceOf_cons, ih]
    simp only [pushedMessages, pulledMessages, List.map_cons, List.sum_cons, Multiset.count_add,
      Multiset.count_replicate] at ih ⊢
    split_ifs <;> push_cast <;> omega

/-- Over the integers, balance is the identity of the pushed and pulled multisets. -/
theorem balancedInteractions_iff_pushed_eq_pulled (interactions : List (Interaction F ℤ)) :
    BalancedInteractions interactions ↔ pushedMessages interactions = pulledMessages interactions := by
  simp only [BalancedInteractions, ringChar.eq_zero, or_true, true_and,
    balanceOf_eq_count_pushed_sub_count_pulled, sub_eq_zero, Nat.cast_inj, Multiset.ext]

/--
The fingerprint product of a multiset: one monic linear factor `X - φ a` per element.
Here `φ` maps a message to a fingerprint in a commutative ring `R`, for example a polynomial ring
in formal challenge variables.
-/
noncomputable def fingerprintProduct {α R : Type} [CommRing R] (φ : α → R) (s : Multiset α) : R[X] :=
  (s.map fun a => X - C (φ a)).prod

/-- Multisets with equal images under a map injective on their elements are equal. -/
theorem Multiset.eq_of_map_eq_of_injOn {α β : Type} [DecidableEq α] {φ : α → β} {s t : Multiset α}
    (injOn : Set.InjOn φ {a | a ∈ s + t}) (h : s.map φ = t.map φ) : s = t := by
  induction s using Multiset.induction_on generalizing t with
  | empty =>
    rw [Multiset.map_zero, eq_comm, Multiset.map_eq_zero] at h
    exact h.symm
  | cons a s ih =>
    have a_mem : φ a ∈ t.map φ := h ▸ Multiset.mem_map_of_mem φ (Multiset.mem_cons_self a s)
    obtain ⟨ b, b_mem, b_eq ⟩ := Multiset.mem_map.mp a_mem
    have b_eq_a : b = a := injOn (by simp [b_mem]) (by simp) b_eq
    subst b_eq_a
    rw [← Multiset.cons_erase b_mem, Multiset.map_cons, Multiset.map_cons, Multiset.cons_inj_right] at h
    rw [← Multiset.cons_erase b_mem, ih _ h]
    intro x x_mem y y_mem
    apply injOn
    · simp only [Set.mem_ofPred_eq, Multiset.mem_add, Multiset.mem_cons] at x_mem ⊢
      rcases x_mem with x_mem | x_mem
      · exact Or.inl (Or.inr x_mem)
      · exact Or.inr (Multiset.mem_of_mem_erase x_mem)
    · simp only [Set.mem_ofPred_eq, Multiset.mem_add, Multiset.mem_cons] at y_mem ⊢
      rcases y_mem with y_mem | y_mem
      · exact Or.inl (Or.inr y_mem)
      · exact Or.inr (Multiset.mem_of_mem_erase y_mem)

/--
A product identity is a multiset identity: equal fingerprint products force equal multisets,
provided the fingerprint separates their elements.
-/
theorem eq_of_fingerprintProduct_eq {α R : Type} [DecidableEq α] [CommRing R] [IsDomain R] {φ : α → R}
    {s t : Multiset α} (injOn : Set.InjOn φ {a | a ∈ s + t})
    (h : fingerprintProduct φ s = fingerprintProduct φ t) : s = t := by
  have roots_eq := congrArg Polynomial.roots h
  have map_factors : ∀ u : Multiset α, (u.map fun a => X - C (φ a)) = (u.map φ).map fun b => X - C b := by
    intro u
    rw [Multiset.map_map]
    rfl
  simp only [fingerprintProduct, map_factors, roots_multiset_prod_X_sub_C] at roots_eq
  exact Multiset.eq_of_map_eq_of_injOn injOn roots_eq

omit [DecidableEq F] in
lemma mem_pushedMessages {interactions : List (Interaction F ℤ)} {msg : Array F} :
    msg ∈ pushedMessages interactions → ∃ i ∈ interactions, i.msg = msg := by
  induction interactions with
  | nil => simp [pushedMessages]
  | cons i is ih =>
    simp only [pushedMessages, List.map_cons, List.sum_cons, Multiset.mem_add, Multiset.mem_replicate] at ih ⊢
    rintro (⟨ _, rfl ⟩ | msg_mem)
    · exact ⟨ i, List.mem_cons_self .., rfl ⟩
    · obtain ⟨ j, j_mem, rfl ⟩ := ih msg_mem
      exact ⟨ j, List.mem_cons_of_mem _ j_mem, rfl ⟩

omit [DecidableEq F] in
lemma mem_pulledMessages {interactions : List (Interaction F ℤ)} {msg : Array F} :
    msg ∈ pulledMessages interactions → ∃ i ∈ interactions, i.msg = msg := by
  induction interactions with
  | nil => simp [pulledMessages]
  | cons i is ih =>
    simp only [pulledMessages, List.map_cons, List.sum_cons, Multiset.mem_add, Multiset.mem_replicate] at ih ⊢
    rintro (⟨ _, rfl ⟩ | msg_mem)
    · exact ⟨ i, List.mem_cons_self .., rfl ⟩
    · obtain ⟨ j, j_mem, rfl ⟩ := ih msg_mem
      exact ⟨ j, List.mem_cons_of_mem _ j_mem, rfl ⟩

omit [DecidableEq F] in
lemma fingerprintProduct_pushedMessages {R : Type} [CommRing R] (φ : Array F → R)
    (interactions : List (Interaction F ℤ)) :
    fingerprintProduct φ (pushedMessages interactions) =
      (interactions.map fun i => (X - C (φ i.msg))^i.mult.toNat).prod := by
  induction interactions with
  | nil => simp [fingerprintProduct, pushedMessages]
  | cons i is ih =>
    simp only [fingerprintProduct, pushedMessages, List.map_cons, List.sum_cons, Multiset.map_add,
      Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate, List.prod_cons] at ih ⊢
    rw [ih]

omit [DecidableEq F] in
lemma fingerprintProduct_pulledMessages {R : Type} [CommRing R] (φ : Array F → R)
    (interactions : List (Interaction F ℤ)) :
    fingerprintProduct φ (pulledMessages interactions) =
      (interactions.map fun i => (X - C (φ i.msg))^(-i.mult).toNat).prod := by
  induction interactions with
  | nil => simp [fingerprintProduct, pulledMessages]
  | cons i is ih =>
    simp only [fingerprintProduct, pulledMessages, List.map_cons, List.sum_cons, Multiset.map_add,
      Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate, List.prod_cons] at ih ⊢
    rw [ih]

/--
The product check is sound and complete as a polynomial identity: with a fingerprint into an integral
domain that separates the messages of the interactions, the pushed and pulled fingerprint products
agree exactly when the interactions balance.
-/
theorem balancedInteractions_iff_fingerprintProduct_eq {R : Type} [CommRing R] [IsDomain R]
    {φ : Array F → R} {interactions : List (Interaction F ℤ)}
    (injOn : Set.InjOn φ {msg | ∃ i ∈ interactions, i.msg = msg}) :
    BalancedInteractions interactions ↔
      (interactions.map fun i => (X - C (φ i.msg))^i.mult.toNat).prod =
        (interactions.map fun i => (X - C (φ i.msg))^(-i.mult).toNat).prod := by
  rw [balancedInteractions_iff_pushed_eq_pulled, ← fingerprintProduct_pushedMessages,
    ← fingerprintProduct_pulledMessages]
  refine ⟨ congrArg _, eq_of_fingerprintProduct_eq (injOn.mono ?_) ⟩
  intro msg msg_mem
  simp only [Set.mem_ofPred_eq, Multiset.mem_add] at msg_mem ⊢
  rcases msg_mem with msg_mem | msg_mem
  · exact mem_pushedMessages msg_mem
  · exact mem_pulledMessages msg_mem

theorem balancedInteractions_of_fingerprintProduct_eq {R : Type} [CommRing R] [IsDomain R]
    {φ : Array F → R} {interactions : List (Interaction F ℤ)}
    (injOn : Set.InjOn φ {msg | ∃ i ∈ interactions, i.msg = msg})
    (h : (interactions.map fun i => (X - C (φ i.msg))^i.mult.toNat).prod =
      (interactions.map fun i => (X - C (φ i.msg))^(-i.mult).toNat).prod) :
    BalancedInteractions interactions :=
  (balancedInteractions_iff_fingerprintProduct_eq injOn).mpr h

/-! ### Multiplicities committed as bits -/

/-- A leaf of bit `b` at weight `2^k` is `P` raised to `b*2^k`. -/
lemma one_add_bit_mul_pow_two_pow_sub_one {R : Type} [CommRing R] (P : R) (k b : ℕ) (hb : b ≤ 1) :
    1 + (b : R)*(P^2^k - 1) = P^(b*2^k) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp

/--
The leaves of a multiplicity committed as bits multiply to the factor raised to that multiplicity:
`∏_k (1 + b_k (P^(2^k) - 1)) = P^(∑_k b_k 2^k)` when every `b_k` is `0` or `1`.
-/
theorem prod_one_add_bit_mul_pow_two_pow_sub_one {R : Type} [CommRing R] (P : R) (n : ℕ)
    (bits : ℕ → ℕ) (bits_le : ∀ k < n, bits k ≤ 1) :
    ∏ k ∈ Finset.range n, (1 + (bits k : R)*(P^2^k - 1)) = P^(∑ k ∈ Finset.range n, bits k*2^k) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro k hk
  exact one_add_bit_mul_pow_two_pow_sub_one P k (bits k) (bits_le k (Finset.mem_range.mp hk))
