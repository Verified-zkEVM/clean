import Clean.Ironwood.Poseidon.Rounds

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `Pow5Chip::permute` (lines 228-266): ONE region `"permute state"`; load the initial
  state (copy_advice ×3 at row 0), then `half_full_rounds = 4` full-round rows, then
  `half_partial_rounds = 28` partial-round rows (each two source rounds,
  `round = 4 + 2r`), then 4 more full-round rows (`round = 60 + r`). 37 rows total; the
  final state is read at row 36.

`Spec` is the donor's `Permute.value` (the 4+28+4 `Fin.foldl` schedule,
`Clean/Orchard/Poseidon/Pow5.lean`), at the ported P128Pow5T3 round constants.
-/

namespace Halo2.Ironwood.Poseidon

open Halo2.Ironwood (Fp)
open Orchard.Poseidon
open Orchard.Poseidon.Permute (State)
open Orchard.Poseidon.Permute.P128Pow5T3 (mds mdsInv roundConstants)

-- contract bridges for the round chunks
private theorem fullRound_spec_eq (r : ℕ) :
    (fullRound r).Spec = fun _ out w =>
      out = FullRound.value (FullRound.params roundConstants mds r) w := rfl

private theorem fullRound_assumptions_eq (r : ℕ) :
    (fullRound r).Assumptions = fun _ => True := rfl

private theorem fullRound_envAssumptions_eq (r : ℕ) (cfg : Config)
    (env : Placed Environment Fp) :
    (fullRound r).EnvAssumptions cfg env = True := rfl

private theorem fullRound_extract_eq (r : ℕ) (cfg : Config) (offset : ℕ)
    (input : Var unit Fp) (self : RegionIndex) (env : Placed Environment Fp) :
    (fullRound r).extract cfg offset input self env
      = eval env (stateRow cfg offset self) := rfl

private theorem partialRound_spec_eq (r : ℕ) :
    (partialRound r).Spec = fun _ out w =>
      out = PartialRounds.value (PartialRounds.paramsP128 roundConstants r) w := rfl

private theorem partialRound_assumptions_eq (r : ℕ) :
    (partialRound r).Assumptions = fun _ => True := rfl

private theorem partialRound_envAssumptions_eq (r : ℕ) (cfg : Config)
    (env : Placed Environment Fp) :
    (partialRound r).EnvAssumptions cfg env = True := rfl

private theorem partialRound_extract_eq (r : ℕ) (cfg : Config) (offset : ℕ)
    (input : Var unit Fp) (self : RegionIndex) (env : Placed Environment Fp) :
    (partialRound r).extract cfg offset input self env
      = eval env (stateRow cfg offset self) := rfl

private theorem fullRound_proverAssumptions_eq (r : ℕ) (input : ProverValue unit Fp)
    (w : State Fp) (hint : ProverHint Fp) :
    (fullRound r).ProverAssumptions input w hint = True := rfl

private theorem partialRound_proverAssumptions_eq (r : ℕ) (input : ProverValue unit Fp)
    (w : State Fp) (hint : ProverHint Fp) :
    (partialRound r).ProverAssumptions input w hint = True := rfl

private theorem fullRound_output_eq (r : ℕ) (cfg : Config) (o : ℕ)
    (input : Var unit Fp) (self : RegionIndex) :
    (fullRound r).output cfg o input self = stateRow cfg (o + 1) self := rfl

private theorem partialRound_output_eq (r : ℕ) (cfg : Config) (o : ℕ)
    (input : Var unit Fp) (self : RegionIndex) :
    (partialRound r).output cfg o input self = stateRow cfg (o + 1) self := rfl

/-- Chain a per-row step family into a `Fin.foldl` (the donor `Permute.value` shape). -/
private theorem foldl_of_steps (f : ℕ → State Fp → State Fp) (st : ℕ → State Fp)
    (base : ℕ) : ∀ n : ℕ,
    (∀ i : ℕ, i < n → st (base + i + 1) = f i (st (base + i))) →
    st (base + n) = Fin.foldl n (fun s (i : Fin n) => f ↑i s) (st base)
  | 0, _ => by simp
  | n + 1, h => by
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← foldl_of_steps f st base n (fun i hi => h i (by omega)),
      show base + (n + 1) = base + n + 1 from rfl]
    exact h n (by omega)

/-- Rust `Pow5Chip::permute`'s region body (`pow5.rs:235-265`): load the state, 4 full
rounds, 28 double partial rounds, 4 full rounds. `Spec`: the outgoing state is the donor
`Permute.value` of the incoming one. -/
def permuteRegion : FormalRegionCircuit Fp Config Config State State where
  configure := pure

  synthesize cfg offset (input : Var State Fp) := do
    -- Pow5State::load (pow5.rs:536-550)
    let _c0 ← copyAdvice input.x0 (cfg.state 0) offset
    let _c1 ← copyAdvice input.x1 (cfg.state 1) offset
    let _c2 ← copyAdvice input.x2 (cfg.state 2) offset
    RegionCircuit.forRange' offset 1 4 (fun r o => do
      let _ ← (fullRound r).call cfg o ()
      pure ())
    RegionCircuit.forRange' (offset + 4) 1 28 (fun r o => do
      let _ ← (partialRound (4 + 2 * r)).call cfg o ()
      pure ())
    RegionCircuit.forRange' (offset + 32) 1 4 (fun r o => do
      let _ ← (fullRound (60 + r)).call cfg o ()
      pure ())
    readStateRow cfg (offset + 36)

  Spec input output _ := output = Permute.value roundConstants input

  ProverSpec input output _ _ := output = Permute.value roundConstants input

  soundness := by
    circuit_proof_start
    obtain ⟨hcp0, hcp1, hcp2, hfullA, hpart, hfullB⟩ := hc
    simp only [fullRound_envAssumptions_eq, fullRound_assumptions_eq, fullRound_spec_eq,
      fullRound_extract_eq, fullRound_output_eq, partialRound_envAssumptions_eq,
      partialRound_assumptions_eq, partialRound_spec_eq, partialRound_extract_eq,
      partialRound_output_eq, ProvableStruct.eval_cells_eq_eval, forall_const,
      mul_one] at hfullA hpart hfullB
    -- the row-value family
    set st : ℕ → State Fp := fun k =>
      ProvableStruct.eval env.place env.env (stateRow cfg (offset + k) self) with hst
    -- per-phase step facts on the family
    have hstepA : ∀ i : ℕ, i < 4 →
        st (0 + i + 1) = FullRound.value (FullRound.params roundConstants mds i)
          (st (0 + i)) := by
      intro i hi
      have h := hfullA ⟨i, hi⟩
      simp only [hst, Nat.zero_add]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepB : ∀ i : ℕ, i < 28 →
        st (4 + i + 1) = PartialRounds.value
          (PartialRounds.paramsP128 roundConstants (4 + 2 * i)) (st (4 + i)) := by
      intro i hi
      have h := hpart ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepC : ∀ i : ℕ, i < 4 →
        st (32 + i + 1) = FullRound.value
          (FullRound.params roundConstants mds (60 + i)) (st (32 + i)) := by
      intro i hi
      have h := hfullB ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    -- endpoints
    have h0 : st 0 = { x0 := input_x0, x1 := input_x1, x2 := input_x2 } := by
      simp only [hst, Nat.add_zero]
      rw [show (ProvableStruct.eval env.place env.env (stateRow cfg offset self)
          : State Fp)
        = { x0 := env.env.advice (cfg.state 0) ((env.place self + offset : ℕ) : ℤ),
            x1 := env.env.advice (cfg.state 1) ((env.place self + offset : ℕ) : ℤ),
            x2 := env.env.advice (cfg.state 2) ((env.place self + offset : ℕ) : ℤ) }
        from by with_unfolding_all rfl]
      rw [hcp0, hcp1, hcp2]
    have h36 : st 36 = { x0 := output_x0, x1 := output_x1, x2 := output_x2 } := h_output
    -- assemble the three folds
    have hA := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds i)) st 0 4 hstepA
    have hB := foldl_of_steps
      (fun i => PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i)))
      st 4 28 hstepB
    have hC := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds (60 + i))) st 32 4
      hstepC
    rw [← h36, ← h0]
    show st (32 + 4) = Permute.value roundConstants (st 0)
    rw [hC, show (32 : ℕ) = 4 + 28 from rfl, hB, show (4 : ℕ) = 0 + 4 from rfl, hA]
    rfl

  completeness := by
    circuit_proof_start
    obtain ⟨hw0, hw1, hw2, hwA, hwB, hwC⟩ := hwit
    -- per-chunk derived contracts (verifier-view Spec is all we need for the chain)
    have hdA := fun i : Fin 4 => (SubcircuitRw.region_completeness_derived
      (fullRound ↑i) cfg (offset + ↑i * 1) self env.place env.env () (hwA i)
      trivial trivial trivial).1
    have hdB := fun i : Fin 28 => (SubcircuitRw.region_completeness_derived
      (partialRound (4 + 2 * ↑i)) cfg (offset + 4 + ↑i * 1) self env.place env.env ()
      (hwB i) trivial trivial trivial).1
    have hdC := fun i : Fin 4 => (SubcircuitRw.region_completeness_derived
      (fullRound (60 + ↑i)) cfg (offset + 32 + ↑i * 1) self env.place env.env ()
      (hwC i) trivial trivial trivial).1
    simp only [fullRound_spec_eq, fullRound_extract_eq, fullRound_output_eq,
      partialRound_spec_eq, partialRound_extract_eq, partialRound_output_eq,
      ProvableStruct.eval_cells_eq_eval, mul_one] at hdA hdB hdC
    -- the row-value family (verifier view of the honest environment)
    set st : ℕ → State Fp := fun k =>
      ProvableStruct.eval env.place env.env.toEnvironment (stateRow cfg (offset + k) self)
      with hst
    have hstepA : ∀ i : ℕ, i < 4 →
        st (0 + i + 1) = FullRound.value (FullRound.params roundConstants mds i)
          (st (0 + i)) := by
      intro i hi
      have h := hdA ⟨i, hi⟩
      simp only [hst, Nat.zero_add]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepB : ∀ i : ℕ, i < 28 →
        st (4 + i + 1) = PartialRounds.value
          (PartialRounds.paramsP128 roundConstants (4 + 2 * i)) (st (4 + i)) := by
      intro i hi
      have h := hdB ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    have hstepC : ∀ i : ℕ, i < 4 →
        st (32 + i + 1) = FullRound.value
          (FullRound.params roundConstants mds (60 + i)) (st (32 + i)) := by
      intro i hi
      have h := hdC ⟨i, hi⟩
      simp only [hst, Nat.add_assoc]
      simp only [Nat.add_assoc] at h
      exact h
    have h0 : st 0 = { x0 := input_x0, x1 := input_x1, x2 := input_x2 } := by
      simp only [hst, Nat.add_zero]
      rw [show (ProvableStruct.eval env.place env.env.toEnvironment
          (stateRow cfg offset self) : State Fp)
        = { x0 := env.env.advice (cfg.state 0) ((env.place self + offset : ℕ) : ℤ),
            x1 := env.env.advice (cfg.state 1) ((env.place self + offset : ℕ) : ℤ),
            x2 := env.env.advice (cfg.state 2) ((env.place self + offset : ℕ) : ℤ) }
        from by with_unfolding_all rfl]
      rw [hw0, hw1, hw2, h_input.1, h_input.2.1, h_input.2.2]
    have h36 : st 36 = { x0 := output_x0, x1 := output_x1, x2 := output_x2 } := h_output
    have hA := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds i)) st 0 4 hstepA
    have hB := foldl_of_steps
      (fun i => PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i)))
      st 4 28 hstepB
    have hC := foldl_of_steps
      (fun i => FullRound.value (FullRound.params roundConstants mds (60 + i))) st 32 4
      hstepC
    refine ⟨⟨hw0, hw1, hw2, ?_, ?_, ?_⟩, ?_⟩
    · intro i
      have hleaf := SubcircuitRw.region_completeness_leaf_placed (fullRound ↑i) cfg
        (offset + ↑i * 1) self env () (hwA i)
      rw [fullRound_envAssumptions_eq, fullRound_assumptions_eq,
        fullRound_proverAssumptions_eq] at hleaf
      exact hleaf ⟨trivial, trivial, trivial⟩
    · intro i
      have hleaf := SubcircuitRw.region_completeness_leaf_placed
        (partialRound (4 + 2 * ↑i)) cfg (offset + 4 + ↑i * 1) self env () (hwB i)
      rw [partialRound_envAssumptions_eq, partialRound_assumptions_eq,
        partialRound_proverAssumptions_eq] at hleaf
      exact hleaf ⟨trivial, trivial, trivial⟩
    · intro i
      have hleaf := SubcircuitRw.region_completeness_leaf_placed (fullRound (60 + ↑i))
        cfg (offset + 32 + ↑i * 1) self env () (hwC i)
      rw [fullRound_envAssumptions_eq, fullRound_assumptions_eq,
        fullRound_proverAssumptions_eq] at hleaf
      exact hleaf ⟨trivial, trivial, trivial⟩
    rw [← h36, ← h0]
    show st (32 + 4) = Permute.value roundConstants (st 0)
    rw [hC, show (32 : ℕ) = 4 + 28 from rfl, hB, show (4 : ℕ) = 0 + 4 from rfl, hA]
    rfl

end Halo2.Ironwood.Poseidon
