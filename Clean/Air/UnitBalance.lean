module

public import Clean.Air.Balance

/-! # Exact message balance for unit transitions

Typed unit-message permutations follow from `BalancedInteractions` and its characteristic
bound. The converse establishes field balance from exact conservation. Disabled physical
slots can be removed for logical matching while retaining the original capacity obligation. -/

@[expose] public section

/-- Removing disabled interactions preserves balance and weakens its characteristic count bound. -/
theorem BalancedInteractions.filter_nonzero {F : Type} [FiniteField F] [DecidableEq F]
    {interactions : List (Interaction F)} (balanced : BalancedInteractions interactions) :
    BalancedInteractions (interactions.filter fun interaction => decide (interaction.mult ≠ 0)) := by
  refine ⟨balanced.1.imp (lt_of_le_of_lt (List.length_filter_le ..)) id, ?_⟩
  intro message
  have zero : balanceOf (interactions.filter fun interaction => decide (interaction.mult = 0)) message = 0 :=
    balanceOf_eq_of_const_zero (fun _ member => of_decide_eq_true (List.mem_filter.mp member).2)
  have split := balanceOf_eq_add_filter (interactions := interactions) (msg := message) (· = 0)
  rw [balanced.2, zero, zero_add] at split
  exact split.symm

namespace Channel

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {Message : TypeMap} [ProvableType Message]

/-- The actual unit interactions of a boundary and a list of transitions. -/
def transitionLedger {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (edge : Row → Message F × Message F) :
    List (Interaction F) :=
  [channel.pushedValue initial, channel.pulledValue final] ++
    rows.flatMap (fun row => [channel.pulledValue (edge row).1,
      channel.pushedValue (edge row).2])

private theorem balanceOf_pushes (channel : Channel F Message) (messages : List (Message F))
    (msg : Array F) :
    balanceOf (messages.map channel.pushedValue) msg =
      ((messages.map (fun value => (toElements value).toArray)).count msg : F) := by
  have compare (a : Array F) : decide (a = msg) = (a == msg) := by
    apply Bool.eq_iff_iff.mpr
    simp
  rw [balanceOf_eq_of_const_mult' (mult := (1 : F)) (fun _ member => by
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member; rfl), one_mul]
  congr 1
  simp only [List.countP_map, List.count_eq_countP, Function.comp_def, pushedValue, compare]

private theorem balanceOf_pulls (channel : Channel F Message) (messages : List (Message F))
    (msg : Array F) :
    balanceOf (messages.map channel.pulledValue) msg =
      - ((messages.map (fun value => (toElements value).toArray)).count msg : F) := by
  have compare (a : Array F) : decide (a = msg) = (a == msg) := by
    apply Bool.eq_iff_iff.mpr
    simp
  rw [balanceOf_eq_of_const_mult' (mult := (-1 : F)) (fun _ member => by
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member; rfl), neg_one_mul]
  congr 1
  simp only [List.countP_map, List.count_eq_countP, Function.comp_def, pulledValue, compare]

omit [DecidableEq F] in
/-- Collecting unit transition pairs preserves every interaction occurrence. -/
theorem pairedLedger_perm {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (edge : Row → Message F × Message F) :
    (rows.flatMap (fun row => [channel.pulledValue (edge row).1,
      channel.pushedValue (edge row).2])).Perm
      ((rows.map (fun row => channel.pushedValue (edge row).2)) ++
       (rows.map (fun row => channel.pulledValue (edge row).1))) := by
  induction rows with
  | nil => exact .refl _
  | cons row rest ih =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.nil_append]
    exact ((ih.cons _).cons _).trans
      ((List.Perm.swap _ _ _).trans (List.perm_middle.symm.cons _))

omit [DecidableEq F] in
/-- Collecting unit pushes and pulls changes only the order of the real interaction list. -/
theorem transitionLedger_perm {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (edge : Row → Message F × Message F) :
    (channel.transitionLedger initial final rows edge).Perm
      (((initial :: rows.map (fun row => (edge row).2)).map channel.pushedValue) ++
       ((final :: rows.map (fun row => (edge row).1)).map channel.pulledValue)) := by
  unfold transitionLedger
  have split := channel.pairedLedger_perm rows edge
  have reordered := (split.cons (channel.pulledValue final) |>.cons (channel.pushedValue initial)).trans
    (List.perm_middle.symm.cons _)
  simp only [List.map_cons, List.map_map, Function.comp_def, List.cons_append, List.nil_append] at reordered ⊢
  exact reordered

/-- Unit field balance is exactly a permutation of typed messages, subject to Clean's own
non-overflow condition. This applies in arbitrary characteristic, including characteristic zero. -/
theorem balanced_unit_iff (channel : Channel F Message) (produced consumed : List (Message F)) :
    BalancedInteractions (produced.map channel.pushedValue ++ consumed.map channel.pulledValue) ↔
      (produced.length + consumed.length < ringChar F ∨ ringChar F = 0) ∧
        produced.Perm consumed := by
  have encode_injective : Function.Injective (fun value : Message F => (toElements value).toArray) := by
    intro a b equal
    have vectors := Vector.toArray_inj.mp equal
    have decoded := congrArg fromElements vectors
    simp only [ProvableType.fromElements_toElements] at decoded
    exact decoded
  constructor
  · intro balanced
    have bound : produced.length + consumed.length < ringChar F ∨ ringChar F = 0 := by
      have bound := balanced.1
      simp only [List.length_append, List.length_map] at bound
      exact bound
    refine ⟨bound, (List.map_perm_map_iff encode_injective).mp ?_⟩
    rw [List.perm_iff_count]
    intro msg
    have zero := balanced.2 msg
    rw [balanceOf_append, balanceOf_pushes, balanceOf_pulls, ← sub_eq_add_neg,
      sub_eq_zero] at zero
    rcases bound with bound | zeroChar
    · have aBound : (produced.map (fun value => (toElements value).toArray)).count msg < ringChar F := by
        apply lt_of_le_of_lt List.count_le_length
        simp only [List.length_map]
        omega
      have bBound : (consumed.map (fun value => (toElements value).toArray)).count msg < ringChar F := by
        apply lt_of_le_of_lt List.count_le_length
        simp only [List.length_map]
        omega
      exact (Lean.Grind.IsCharP.natCast_eq_iff_of_lt (ringChar F) aBound bBound).mp zero
    · rw [CharP.ringChar_zero_iff_CharZero] at zeroChar
      exact Nat.cast_injective zero
  · rintro ⟨bound, perm⟩
    refine ⟨by simp only [List.length_append, List.length_map]; exact bound, ?_⟩
    intro msg
    rw [balanceOf_append, balanceOf_pushes, balanceOf_pulls,
      (perm.map (fun value => (toElements value).toArray)).count_eq msg, add_neg_cancel]

/-- A closed unit-transition ledger has exactly the same produced and consumed typed messages. -/
theorem pairedLedger_balanced_iff {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (edge : Row → Message F × Message F) :
    BalancedInteractions (rows.flatMap (fun row =>
      [channel.pulledValue (edge row).1, channel.pushedValue (edge row).2])) ↔
      (2 * rows.length < ringChar F ∨ ringChar F = 0) ∧
        (rows.map (fun row => (edge row).2)).Perm (rows.map (fun row => (edge row).1)) := by
  have perm := channel.pairedLedger_perm rows edge
  have transport : BalancedInteractions (rows.flatMap (fun row =>
      [channel.pulledValue (edge row).1, channel.pushedValue (edge row).2])) ↔
      BalancedInteractions ((rows.map (fun row => channel.pushedValue (edge row).2)) ++
        (rows.map (fun row => channel.pulledValue (edge row).1))) :=
    ⟨fun valid => balancedInteractions_of_perm valid perm,
      fun valid => balancedInteractions_of_perm valid perm.symm⟩
  rw [transport]
  have characterization := channel.balanced_unit_iff
    (rows.map fun row => (edge row).2) (rows.map fun row => (edge row).1)
  simp only [List.map_map, Function.comp_def, List.length_map] at characterization
  rw [two_mul]
  exact characterization

/-- A balanced transition ledger yields the endpoint permutation needed by a ranked walk. -/
theorem transitionLedger_balanced_iff {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (edge : Row → Message F × Message F) :
    BalancedInteractions (channel.transitionLedger initial final rows edge) ↔
      (2 * (rows.length + 1) < ringChar F ∨ ringChar F = 0) ∧
        (initial :: rows.map (fun row => (edge row).2)).Perm
          (final :: rows.map (fun row => (edge row).1)) := by
  have perm := transitionLedger_perm channel initial final rows edge
  have transport : BalancedInteractions (channel.transitionLedger initial final rows edge) ↔
      BalancedInteractions (((initial :: rows.map (fun row => (edge row).2)).map channel.pushedValue) ++
        ((final :: rows.map (fun row => (edge row).1)).map channel.pulledValue)) :=
    ⟨fun valid => balancedInteractions_of_perm valid perm,
      fun valid => balancedInteractions_of_perm valid perm.symm⟩
  rw [transport, balanced_unit_iff]
  simp only [List.length_cons, List.length_map, two_mul]

/-- A binary-gated producer inventory and unit consumers agree on complete typed messages.
Disabled physical rows may remain in the original ledger and its count bound. -/
theorem gated_unit_perm_of_balanced {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (gate : Row → F) (message : Row → Message F) (consumed : List (Message F))
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1)
    (balanced : BalancedInteractions
      (rows.map (fun row => channel.pushedIfValue (gate row) (message row)) ++
        consumed.map channel.pulledValue)) :
    ((rows.filter fun row => decide (gate row = 1)).map message).Perm consumed := by
  have producers :
      ((rows.map fun row => channel.pushedIfValue (gate row) (message row)).filter
        fun interaction => decide (interaction.mult ≠ 0)) =
      (rows.filter fun row => decide (gate row = 1)).map (fun row => channel.pushedValue (message row)) := by
    clear balanced
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      have tail := ih (fun other member => binary other (List.mem_cons_of_mem _ member))
      rcases binary row (List.mem_cons_self ..) with equal | equal <;>
        simp only [List.map_cons, List.filter_cons, pushedIfValue, equal, ne_eq,
          not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          zero_ne_one, one_ne_zero, not_false_eq_true, decide_true, List.map_cons,
          pushedValue]
      · exact tail
      · exact congrArg (List.cons _) tail
  have consumers : ((consumed.map channel.pulledValue).filter
      fun interaction => decide (interaction.mult ≠ 0)) = consumed.map channel.pulledValue := by
    apply List.filter_eq_self.mpr
    intro interaction member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    simp [pulledValue]
  have selected := balanced.filter_nonzero
  rw [List.filter_append, producers, consumers] at selected
  apply ((channel.balanced_unit_iff _ consumed).mp ?_).2
  simp only [List.map_map, Function.comp_def]
  exact selected

end Channel
