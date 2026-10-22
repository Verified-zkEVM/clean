module

public import CleanCompStark.KeccakAir.Bridgeable

/-!
# The degrees of the Keccak-f AIR

Plonky3's `degree_multiple` and CompStark's `degBound` of a lowered constraint are a weight of the
Clean constraint it comes from (`weight`): every cell has a weight, a constant `0`, a sum the
larger of its terms' and a product the sum of its factors'. Lowering takes the selector off a
gated constraint and multiplies the body by CompStark's selector, which keeps the weight
(`gateConstraint_weight`).

The weights of the constraints of a window are the constraints of the cells' weights (`Deg`,
`isHom_weight`); `simp` bounds them family by family (`weights_le`): with cells of weight `a`
and the transition selector of weight `b`, every constraint weighs at most `max (3 a) (b + 2 a)`,
and the parity constraints weigh `3 a` (`exists_weight_eq`).
-/

@[expose] public section

namespace CleanCompStark.KeccakAir
open Air.Flat Air.Flat.WitnessGeneration Backends _root_.KeccakAir

/-! ### Weights of expressions -/

section Weight
variable {F : Type}

/-- The weight of an expression, cell `j` weighing `wv j`: a constant weighs `0`, a sum the larger
of its terms, a product the sum of its factors. -/
def weight (wv : ℕ → ℕ) : Expression F → ℕ
  | .var v => wv v.index
  | .const _ => 0
  | .add a b => max (weight wv a) (weight wv b)
  | .mul a b => weight wv a + weight wv b

/-- The weight of a gate's selector cell, for rows of `w` cells. -/
def gateWeight (w : ℕ) (wv : ℕ → ℕ) : Gate → ℕ
  | .everyRow => 0
  | .firstRow => wv (2 * w)
  | .lastRow => wv (2 * w + 1)
  | .transition => wv (2 * w + 2)

lemma weight_congr (wv wv' : ℕ → ℕ) :
    ∀ x : Expression F, (∀ j ∈ expressionCells x, wv j = wv' j) → weight wv x = weight wv' x
  | .var v, h => h v.index (by simp [expressionCells])
  | .const _, _ => rfl
  | .add a b, h | .mul a b, h => by
    simp only [expressionCells, List.mem_append] at h
    simp only [weight, weight_congr wv wv' a fun j hj => h j (Or.inl hj),
      weight_congr wv wv' b fun j hj => h j (Or.inr hj)]

/-- Splitting the selector off a product keeps its weight. -/
theorem weight_of_splitSelector {w : ℕ} (wv : ℕ → ℕ) :
    ∀ {x body : Expression F} {gate : Gate}, splitSelector w x = some (gate, body) →
      weight wv x = gateWeight w wv gate + weight wv body
  | .var _, _, _, h | .const _, _, _, h | .add _ _, _, _, h => by simp [splitSelector] at h
  | .mul left right, body, gate, h => by
    have hcell {y : Expression F} {g : Gate} (hy : selectorGate? w y = some g) :
        weight wv y = gateWeight w wv g := by
      obtain ⟨cell, hcell, rfl⟩ := selectorGate?_eq_some hy
      cases g <;> simp only [Gate.selectorCell, Option.some.injEq, reduceCtorEq] at hcell <;>
        simp only [weight, gateWeight, hcell]
    simp only [splitSelector] at h
    split at h
    · rename_i hleft
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [weight, hcell hleft]
    · rename_i hright
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [weight, hcell hright]
      omega
    · split at h
      · rename_i hsplit
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [weight, weight_of_splitSelector wv hsplit]
        omega
      · obtain ⟨⟨gate', right'⟩, hsplit, heq⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [weight, weight_of_splitSelector wv hsplit]
        omega

/-- A constraint of a window that `gateConstraint` splits: its body reads cells of the rows, and
its weight is its selector's and its body's. -/
theorem gateConstraint_weight {w : ℕ} {x : Expression F} {g : GatedConstraint F}
    (hcells : ∀ j ∈ expressionCells x, j < 2 * w + 3) (h : gateConstraint (some w) x = some g) :
    Plain w g.body ∧ ∀ wv, weight wv x = gateWeight w wv g.gate + weight wv g.body := by
  simp only [gateConstraint] at h
  split at h
  · rename_i hreads
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun j hj => ?_, fun _ => by simp only [gateWeight, Nat.zero_add]⟩
    simp only [Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq,
      not_and, not_lt] at hreads
    have := hcells j hj
    have := hreads j hj
    omega
  · obtain ⟨⟨gate, body⟩, hsplit, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rename_i hreads
      refine ⟨fun j hj => ?_, fun wv => weight_of_splitSelector wv hsplit⟩
      simp only [Bool.not_eq_true, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq,
        not_and, not_lt] at hreads
      have := hcells j (cells_subset_of_splitSelector hsplit j hj)
      have := hreads j hj
      omega

end Weight

/-! ### Weights as values of the constraints -/

/-- Weights, with `max` as sum and difference and `+` as product; numerals weigh `0`. -/
structure Deg where
  val : ℕ

namespace Deg

instance : Add Deg := ⟨fun a b => ⟨max a.val b.val⟩⟩
instance : Sub Deg := ⟨fun a b => ⟨max a.val b.val⟩⟩
instance : Mul Deg := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance {n : ℕ} : OfNat Deg n := ⟨⟨0⟩⟩

@[simp] lemma val_add (a b : Deg) : (a + b).val = max a.val b.val := rfl
@[simp] lemma val_sub (a b : Deg) : (a - b).val = max a.val b.val := rfl
@[simp] lemma val_mul (a b : Deg) : (a * b).val = a.val + b.val := rfl
@[simp] lemma val_one : (1 : Deg).val = 0 := rfl
@[simp] lemma val_two : (2 : Deg).val = 0 := rfl
@[simp] lemma val_four : (4 : Deg).val = 0 := rfl

@[simp] lemma val_boolCheck (x : Deg) : (boolCheck x).val = 2 * x.val := by
  simp only [boolCheck, val_mul, val_sub, val_one, Nat.max_zero]
  omega

@[simp] lemma val_xor (x y : Deg) : (_root_.KeccakAir.xor x y).val = x.val + y.val := by
  simp only [_root_.KeccakAir.xor, val_add, val_sub, val_mul, val_two, Nat.zero_add]
  omega

@[simp] lemma val_andn (x y : Deg) : (andn x y).val = x.val + y.val := by
  simp only [andn, val_mul, val_sub, val_one, Nat.zero_max]

lemma val_horner_le (bit : Fin 16 → Deg) (c : ℕ) (h : ∀ k, (bit k).val ≤ c) :
    ∀ n, (horner bit n).val ≤ c
  | 0 => h 15
  | n + 1 => by
    simp only [horner, val_add, val_mul, val_two, Nat.zero_add, Nat.max_le]
    exact ⟨val_horner_le bit c h n, h _⟩

lemma val_limbOf_le (bit : Fin 64 → Deg) (limb : Fin 4) (c : ℕ) (h : ∀ z, (bit z).val ≤ c) :
    (limbOf bit limb).val ≤ c :=
  val_horner_le _ c (fun _ => h _) 15

@[simp] lemma val_limbOf_const (d : Deg) (limb : Fin 4) : (limbOf (fun _ => d) limb).val = d.val :=
  le_antisymm (val_limbOf_le _ limb _ fun _ => le_rfl) (by
    have h (n : ℕ) : d.val ≤ (horner (fun _ => d) n).val := by
      induction n with
      | zero => exact le_rfl
      | succ n ih => simp only [horner, val_add, val_mul, val_two, Nat.zero_add]; omega
    exact h 15)

lemma val_iotaBit_le {α : Type} (flags : Vector α 24) (a : ℕ) (bit : Deg) (z : Fin 64) :
    (iotaBit (flags.map fun _ => (⟨a⟩ : Deg)) bit z).val ≤ a + bit.val := by
  have hfold (rounds : List (Fin 24)) (sum : Deg) (hsum : sum.val ≤ a) :
      (rounds.foldl (fun sum (r : Fin 24) => sum + (flags.map fun _ => (⟨a⟩ : Deg))[r]) sum).val
        ≤ a := by
    induction rounds generalizing sum with
    | nil => exact hsum
    | cons r rounds ih =>
      rw [List.foldl_cons]
      exact ih _ (by simp only [val_add, getElem_map_fin]; omega)
  unfold iotaBit
  split
  · omega
  · rename_i r rs _
    have := hfold rs ((flags.map fun _ => (⟨a⟩ : Deg))[r])
      (by simp only [getElem_map_fin]; exact le_rfl)
    simp only [val_xor]
    omega

end Deg

section Hom
variable {F : Type} [FiniteField F]

/-- Weighing commutes with the operations of the constraints. -/
lemma isHom_weight (wv : ℕ → ℕ) : IsHom fun x : Expression F => (⟨weight wv x⟩ : Deg) :=
  ⟨fun _ _ => rfl, fun x y => by
    show (⟨max (weight wv x) (0 + weight wv y)⟩ : Deg) = ⟨max (weight wv x) (weight wv y)⟩
    rw [Nat.zero_add], fun _ _ => rfl, rfl, rfl, rfl⟩

end Hom

/-- The weights of a window whose rows' cells weigh `a`, its first- and last-row selectors `a` and
its transition selector `b`. -/
def degWindow {α : Type} (current next : Row α) (a b : ℕ) : Window Row Deg where
  current := current.map fun _ => ⟨a⟩
  next := next.map fun _ => ⟨a⟩
  isFirstRow := ⟨a⟩
  isLastRow := ⟨a⟩
  isTransition := ⟨b⟩

/-- ι's constraints weigh at most `2 a`. -/
lemma iota_weights_le {α : Type} (current next : Row α) (a b : ℕ) :
    ∀ d ∈ iotaConstraints (degWindow current next a b), d.val ≤ 2 * a := by
  simp only [iotaConstraints, degWindow, List.mem_append, List.mem_map, List.mem_finRange,
    true_and, Row.map_aPrimePrime00Bits, Row.map_aPrimePrimeLimb,
    Row.map_aPrimePrimePrime00Limbs, Row.map_stepFlags, getElem_map_fin]
  rintro d ((⟨z, rfl⟩ | ⟨limb, rfl⟩) | ⟨limb, rfl⟩)
  · simp only [Deg.val_boolCheck, le_refl]
  · simp only [Deg.val_sub, Nat.max_le]
    exact ⟨Deg.val_limbOf_le _ _ _ fun _ => show a ≤ 2 * a by omega, show a ≤ 2 * a by omega⟩
  · simp only [Deg.val_sub, Nat.max_le]
    refine ⟨Deg.val_limbOf_le _ _ _ fun z => ?_, by omega⟩
    have := Deg.val_iotaBit_le current.stepFlags a ⟨a⟩ z
    simp only at this
    omega

/-- **Every constraint of a window weighs at most `max (3 a) (b + 2 a)`**, its rows' cells weighing
`a`, its first- and last-row selectors `a` and its transition selector `b`. -/
theorem weights_le {α : Type} (current next : Row α) (a b : ℕ) :
    ∀ d ∈ constraints (degWindow current next a b), d.val ≤ max (3 * a) (b + 2 * a) := by
  have hiota := iota_weights_le current next a b
  simp only [constraints, List.mem_append, or_imp, forall_and]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, fun d hd => (hiota d hd).trans (by omega)⟩,
    ?_⟩ <;>
  simp only [degWindow, roundFlagConstraints, preimageConstraints, exportConstraints,
    thetaColumnConstraints, thetaConstraints, parityConstraints, chiConstraints,
    outputConstraints, transitionInPermutation, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_flatMap, Row.map_stepFlags, Row.map_exportFlag, Row.map_preimageLimb, Row.map_aLimb,
    Row.map_cBit, Row.map_cPrimeBit, Row.map_aPrimeBit, Row.map_aPrimePrimeLimb, Row.map_b,
    Row.map_aPrimePrimePrimeLimb, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map,
    Deg.val_sub, Deg.val_mul, Deg.val_one, Deg.val_boolCheck, or_imp, forall_and,
    forall_exists_index, and_imp, forall_eq, implies_true, List.not_mem_nil, false_imp_iff] <;>
  (and_intros <;> intros <;> subst_vars <;> (try simp only [Deg.val_add, Deg.val_sub, Deg.val_mul,
    Deg.val_one, Deg.val_two, Deg.val_four, Deg.val_boolCheck, Deg.val_xor, Deg.val_andn,
    Deg.val_limbOf_const]) <;> omega)

/-- The parity constraints weigh `3 a`. -/
theorem exists_weight_eq {α : Type} (current next : Row α) (a b : ℕ) :
    ∃ d ∈ constraints (degWindow current next a b), d.val = 3 * a := by
  refine ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨0, List.mem_finRange 0,
      List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩⟩)))), ?_⟩
  simp only [degWindow, Row.map_aPrimeBit, Row.map_cPrimeBit, Deg.val_mul, Deg.val_sub,
    Deg.val_add, Deg.val_two, Deg.val_four]
  omega

/-- A window has `3182` constraints. -/
theorem length_constraints {α : Type} [Add α] [Sub α] [Mul α] [OfNat α 1] [OfNat α 2] [OfNat α 4]
    (window : Window Row α) : (constraints window).length = 3182 := by
  simp [constraints, roundFlagConstraints, preimageConstraints, exportConstraints,
    thetaColumnConstraints, thetaConstraints, parityConstraints, chiConstraints, iotaConstraints,
    outputConstraints]

end CleanCompStark.KeccakAir
