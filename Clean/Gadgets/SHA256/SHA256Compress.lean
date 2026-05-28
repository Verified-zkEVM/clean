import Clean.Gadgets.SHA256.SHA256Round
import Clean.Gadgets.SHA256.SHA256Schedule
import Clean.Gadgets.SHA256.Add32
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

instance fact_p_gt_2_of_2_pow_33 : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^33 := by decide
  exact h.trans (Fact.out (p := p > 2^33)))

namespace Gadgets.SHA256

/-!
# SHA-256 Compression

Applies 64 rounds of the SHA-256 compression function and then adds the original
state to produce the final output (the Davies–Meyer construction).

This file builds two `FormalCircuit`s:
  * `SHA256Rounds.circuit`     — the 64-round inner loop
  * `CompressBlock.circuit`    — message schedule + 64 rounds + Davies-Meyer
-/

/-!
## FormalCircuit for 64-round compression loop
-/

namespace SHA256Rounds

structure Inputs (F : Type) where
  state : SHA256State F
  schedule : SHA256Schedule F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  Circuit.foldlRange 64 input.state (fun s i =>
    SHA256Round.circuit ⟨s, constWord32 Specs.SHA256.K[i].toNat, input.schedule[i]⟩)

/-- The variable-level state after `k` rounds. Used as the explicit `output` for the
    SHA256Rounds elaborated instance, mirroring how Keccak Permutation provides `stateVar`. -/
def stateVar (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) :
    ℕ → Var SHA256State (F p)
  | 0 => input_var_state
  | k + 1 =>
    let prev := stateVar i₀ input_var_state k
    #v[Vector.mapRange 32 fun j => var { index := i₀ + k * 455 + 389 + j },
       prev[0], prev[1], prev[2],
       Vector.mapRange 32 fun j => var { index := i₀ + k * 455 + 422 + j },
       prev[4], prev[5], prev[6]]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 64, Normalized input.schedule[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Compress (input.state.map valueBits) (input.schedule.map valueBits)
  ∧ ∀ i : Fin 8, Normalized out[i]

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 33)] in
/-- Generic version of `output_eq`: for any bound `k`, the `Fin.foldl k` over our round body
    equals `stateVar i₀ input_var_state k`. -/
private lemma fin_foldl_eq_stateVar (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) (k : ℕ) :
    Fin.foldl k
      (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
        #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 389 + i_1 },
           acc[0], acc[1], acc[2],
           Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 422 + i_1 },
           acc[4], acc[5], acc[6]]) input_var_state =
      stateVar i₀ input_var_state k := by
  induction k with
  | zero => simp [stateVar, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last]
    rw [stateVar]
    rw [show Fin.foldl k
        (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
          #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 455 + 389 + i_1 },
             acc[0], acc[1], acc[2],
             Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 455 + 422 + i_1 },
             acc[4], acc[5], acc[6]]) input_var_state =
        Fin.foldl k
          (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
            #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 389 + i_1 },
               acc[0], acc[1], acc[2],
               Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 422 + i_1 },
               acc[4], acc[5], acc[6]]) input_var_state from rfl, ih]

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 64` equals `stateVar i₀ input_var_state k`.

    Uses `SHA256State (Expression (F p))` for the accumulator type (not the
    `Var SHA256State (F p)` alias) so the lemma's pattern matches `h_holds`
    syntactically — `rw` can't see through the alias. -/
private lemma foldlAcc_eq_stateVar (i₀ : ℕ)
    (input_var_state : SHA256State (Expression (F p)))
    (input_var_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 64) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀ (Vector.finRange 64)
      (fun s (i : Fin 64) => subcircuit SHA256Round.circuit
        { state := s,
          k := constWord32 (Specs.SHA256.K[i.val]'i.isLt).toNat,
          w := input_var_schedule[i.val]'i.isLt })
      input_var_state ⟨k, h⟩ =
        stateVar i₀ input_var_state k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar _ _ _

omit [Fact (p > 2 ^ 33)] in
/-- Helper: `constWord32 n` evaluated is always normalized (bits are 0 or 1). -/
private lemma normalized_constWord32 (env : Environment (F p)) (n : ℕ) :
    Normalized (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) := by
  intro i
  have h : (n / 2^i.val % 2 : ℕ) = 0 ∨ (n / 2^i.val % 2 : ℕ) = 1 := by omega
  rcases h with h | h
  · left
    simp [constWord32, Expression.eval, h]
  · right
    simp [constWord32, Expression.eval, h]

/-- valueBits of `constWord32 n` equals `n` modulo `2^32`. -/
private lemma valueBits_constWord32 (env : Environment (F p)) (n : ℕ) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) = n % 2^32 := by
  simp only [valueBits, constWord32]
  have h2 : ∀ i : Fin 32, ((n / 2^i.val % 2 : ℕ) : F p).val = n / 2^i.val % 2 := by
    intro i
    have hp : 2^33 < p := Fact.out
    have hle : (n / 2^i.val % 2 : ℕ) ≤ 1 := by omega
    have hlt : (n / 2^i.val % 2 : ℕ) < p := by omega
    exact ZMod.val_natCast_of_lt hlt
  have heq : (∑ i : Fin 32, (Vector.map (Expression.eval env)
        (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F p))))[i].val * 2^i.val)
      = ∑ i : Fin 32, (n / 2^i.val % 2) * 2^i.val := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [show (Vector.map (Expression.eval env)
          (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F p))))[i] =
        ((n / 2^i.val % 2 : ℕ) : F p) from by
      simp [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]]
    rw [h2 i]
  rw [heq]
  -- Standard bit-decomposition: ∑ i < 32, (n / 2^i % 2) * 2^i = n % 2^32
  have key : ∀ (m : ℕ), ∑ i : Fin m, (n / 2^i.val % 2) * 2^i.val = n % 2^m := by
    intro m
    induction m with
    | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, pow_zero, Nat.mod_one]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ih, Nat.mod_pow_succ]
      ring
  exact key 32

/-- For `n < 2^32`, valueBits of `constWord32 n` is `n`. -/
private lemma valueBits_constWord32_of_lt (env : Environment (F p)) {n : ℕ} (h : n < 2^32) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) = n := by
  rw [valueBits_constWord32, Nat.mod_eq_of_lt h]

/-- The value-level state at the end of round `k`. -/
private def valStateAfterRound (input_state : Vector ℕ 8)
    (input_schedule : Vector ℕ 64) : ℕ → Vector ℕ 8
  | 0 => input_state
  | k + 1 =>
    if h : k < 64 then
      let prev := valStateAfterRound input_state input_schedule k
      Specs.SHA256.sha256Round prev (Specs.SHA256.K[k]'h).toNat (input_schedule[k]'h)
    else
      valStateAfterRound input_state input_schedule k

/-- `sha256Compress` equals our `valStateAfterRound` at index 64. -/
private lemma sha256Compress_eq_valStateAfterRound
    (input_state : Vector ℕ 8) (input_schedule : Vector ℕ 64) :
    Specs.SHA256.sha256Compress input_state input_schedule =
      valStateAfterRound input_state input_schedule 64 := by
  simp only [Specs.SHA256.sha256Compress]
  suffices h : ∀ k (hk : k ≤ 64),
      Fin.foldl k
        (fun s (i : Fin k) =>
          Specs.SHA256.sha256Round s
            (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat
            (input_schedule[i.val]'(by have := i.isLt; omega))) input_state =
        valStateAfterRound input_state input_schedule k by
    have := h 64 (le_refl 64)
    convert this using 1
  intro k hk
  induction k with
  | zero => simp [valStateAfterRound, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valStateAfterRound]
    rw [dif_pos (by omega : k < 64)]
    have hk' : k ≤ 64 := by omega
    specialize ih hk'
    rw [show Fin.foldl k
          (fun s (i : Fin k) =>
            Specs.SHA256.sha256Round s
              (Specs.SHA256.K[i.castSucc.val]'(by have := i.isLt; omega)).toNat
              (input_schedule[i.castSucc.val]'(by have := i.isLt; omega))) input_state =
        Fin.foldl k
          (fun s (i : Fin k) =>
            Specs.SHA256.sha256Round s
              (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat
              (input_schedule[i.val]'(by have := i.isLt; omega))) input_state from rfl, ih]
    simp [Fin.val_last]

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit_with {
    output input i₀ := stateVar i₀ input.state 64
  } using by
    simp only [circuit_norm]
    intros
    apply fin_foldl_eq_stateVar

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  rw [sha256Compress_eq_valStateAfterRound]
  -- Inductive invariant. We phrase normalization as `eval env ((stateVar k)[i])`
  -- (indexing INSIDE eval) which has type `fields 32 (F p) = Vector (F p) 32`
  -- and works smoothly with `Normalized` since the type alias issue is sidestepped.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 64),
      Vector.map valueBits (eval env (stateVar i₀ input_var_state k)) =
        valStateAfterRound (Vector.map valueBits input_state)
          (Vector.map valueBits input_schedule) k ∧
      (∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env ((stateVar i₀ input_var_state k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [stateVar, valStateAfterRound]; rw [h_input_state]
      · intro j hj
        simp only [stateVar]
        rw [getElem_eval_vector, h_input_state]
        exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 64 := by omega
      have hk'' : k < 64 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      specialize h_holds ⟨k, hk''⟩
      rw [foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule k hk''] at h_holds
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_holds
      have h2 : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) Specs.SHA256.K[k].toNat)) := normalized_constWord32 env _
      have h3 : Normalized (Vector.map (Expression.eval env) input_var_schedule[k]) := by
        rw [show Vector.map (Expression.eval env) input_var_schedule[k]
              = eval env (input_var_schedule[k]'hk'') from (CircuitType.eval_var_fields env _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, hk''⟩
      -- Provide the IH-derived normalization assumption via a tactic that bridges
      -- via `getElem_eval_vector`.
      have h_spec := h_holds ⟨by
        intro i
        have h := ih_norm i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨h_value, h_norm⟩ := h_spec
      rw [stateVar, valStateAfterRound, dif_pos hk'']
      refine ⟨?_, ?_⟩
      · -- Value equality: h_value gives the LHS = sha256Round (...)
        rw [h_value, ih_val,
          valueBits_constWord32_of_lt env Specs.SHA256.K[k].toNat_lt,
          show Vector.map (Expression.eval env) input_var_schedule[k]
            = eval env (input_var_schedule[k]'hk'') from (CircuitType.eval_var_fields env _).symm,
          getElem_eval_vector, h_input_schedule,
          show (Vector.map valueBits input_schedule)[k]'hk''
            = valueBits (input_schedule[k]'hk'') from Vector.getElem_map _ _]
      · -- Normalization for round k+1.
        intro j hj
        -- h_norm gives Normalized (eval env <new state>)[↑i_1] for i_1 : Fin 8.
        -- We need Normalized (eval env <new state>[j]'hj).
        rw [getElem_eval_vector]
        exact h_norm ⟨j, hj⟩
  obtain ⟨h_val_64, h_norm_64⟩ := h_inv 64 (le_refl 64)
  refine ⟨⟨h_val_64, ?_⟩, ?_⟩
  · intro i
    rw [← getElem_eval_vector]
    exact h_norm_64 i.val i.isLt
  · intro _
    left; rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  -- Inductive invariant: at every round k, the state going in is normalized.
  -- This requires us to know the output of each round k is normalized — which
  -- follows from h_env when we provide the antecedents.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 64),
      ∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env.toEnvironment ((stateVar i₀ input_var_state k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [stateVar]
      rw [getElem_eval_vector, h_input_state]
      exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 64 := by omega
      have hk'' : k < 64 := by omega
      specialize h_env ⟨k, hk''⟩
      rw [foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule k hk''] at h_env
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_env
      have h2 : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) Specs.SHA256.K[k].toNat)) := normalized_constWord32 _ _
      have h3 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_schedule[k]) := by
        rw [show Vector.map (Expression.eval env.toEnvironment) input_var_schedule[k]
              = eval env.toEnvironment (input_var_schedule[k]'hk'') from
            (CircuitType.eval_var_fields _ _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, hk''⟩
      have h_spec := h_env ⟨by
        intro i
        have h := ih hk' i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨_, h_norm⟩ := h_spec
      intro j hj
      rw [stateVar]
      rw [getElem_eval_vector]
      exact h_norm ⟨j, hj⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h := h_inv i.val (le_of_lt i.isLt) j.val j.isLt
    rw [← foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule i.val i.isLt] at h
    rw [getElem_eval_vector] at h
    have heq : (⟨i.val, i.isLt⟩ : Fin 64) = i := Fin.ext rfl
    rw [heq] at h
    exact h
  · exact normalized_constWord32 _ _
  · rw [show Vector.map (Expression.eval env.toEnvironment) input_var_schedule[i.val]
          = eval env.toEnvironment (input_var_schedule[i.val]'i.isLt) from
        (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input_schedule]
    exact h_sched_norm i

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end SHA256Rounds

/-!
## FormalCircuit for full block compression (messageSchedule + 64 rounds + Davies-Meyer)
-/

namespace CompressBlock

structure Inputs (F : Type) where
  state : SHA256State F
  block : SHA256Block F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let w ← MessageSchedule.circuit input.block
  let state' ← SHA256Rounds.circuit ⟨input.state, w⟩
  Circuit.mapFinRange 8 fun (i : Fin 8) =>
    Add32.circuit ⟨input.state[i], state'[i]⟩

-- TODO AUTOELAB fails with whnf timeout
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main where
  localLength _ := 48 * 227 + 64 * 455 + 8 * 33
  localLength_eq input offset := by
    simp only [main, circuit_norm, MessageSchedule.circuit,
      SHA256Rounds.circuit, SHA256Rounds.elaborated, Add32.circuit]
  output input i0 :=
    Vector.mapFinRange 8 fun i =>
      varFromOffset (fields 32) (i0 + 48 * 227 + 64 * 455 + i.val * 33)
  output_eq input offset := by
    simp only [main, circuit_norm, MessageSchedule.circuit,
      SHA256Rounds.circuit, SHA256Rounds.elaborated, Add32.circuit]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]
  channelsLawful := by
    simp only [main, circuit_norm, MessageSchedule.circuit,
      SHA256Rounds.circuit, SHA256Rounds.elaborated, Add32.circuit]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 16, Normalized input.block[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.compressBlock (input.state.map valueBits) (input.block.map valueBits)
  ∧ ∀ i : Fin 8, Normalized out[i]

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [MessageSchedule.circuit, MessageSchedule.Spec, MessageSchedule.Assumptions,
    SHA256Rounds.circuit, SHA256Rounds.Spec, SHA256Rounds.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched, h_rounds, h_add⟩ := h_holds
  have h_sched_full := h_sched h_block_norm
  have h_sched_val := fun i => (h_sched_full i).1
  have h_sched_norm := fun i => (h_sched_full i).2
  have h_rounds_full := h_rounds ⟨h_state_norm, h_sched_norm⟩
  have h_rounds_val := h_rounds_full.1
  have h_rounds_norm := h_rounds_full.2
  -- Per-position antecedents for h_add (lifted via getElem_eval_vector / eval_var_fields)
  have h_state_a : ∀ i : Fin 8,
      Normalized (Vector.map (Expression.eval env) input_var_state[i.val]) := by
    intro i
    rw [← CircuitType.eval_var_fields, getElem_eval_vector, h_input_state]
    exact h_state_norm i
  have h_state_b : ∀ i : Fin 8,
      Normalized (Vector.map (Expression.eval env)
        (SHA256Rounds.stateVar (i₀ + 48 * 227) input_var_state 64)[i.val]) := by
    intro i
    have := h_rounds_norm i
    rw [← getElem_eval_vector, CircuitType.eval_var_fields] at this
    exact this
  -- Bridge: Vector.map valueBits of evaluated message schedule = Specs.SHA256.messageSchedule
  have h_sched_map :
      Vector.map valueBits (eval env (MessageSchedule.main input_var_block i₀).1)
        = Specs.SHA256.messageSchedule (Vector.map valueBits input_block) := by
    ext j hj
    simp only [Vector.getElem_map]
    exact h_sched_val ⟨j, hj⟩
  -- Per-position value equation: bridging valueBits of var-output to value-level state.
  have h_val_eq : ∀ i : Fin 8,
      valueBits (Vector.map (Expression.eval env) input_var_state[i.val])
        = valueBits input_state[i.val] := by
    intro i
    rw [← CircuitType.eval_var_fields, getElem_eval_vector, h_input_state]
  have h_rounds_eq : ∀ i : Fin 8,
      valueBits (Vector.map (Expression.eval env)
        (SHA256Rounds.stateVar (i₀ + 48 * 227) input_var_state 64)[i.val])
        = (Specs.SHA256.sha256Compress (input_state.map valueBits)
            (Specs.SHA256.messageSchedule (input_block.map valueBits)))[i.val]'i.isLt := by
    intro i
    rw [← CircuitType.eval_var_fields, getElem_eval_vector]
    have := congrArg (fun v => v[i.val]'i.isLt) h_rounds_val
    simp only [Vector.getElem_map] at this
    rw [this, h_sched_map]
  -- Helper to convert `eval env <mapFinRange>[i]` to the per-position var form.
  have h_index : ∀ (i : ℕ) (hi : i < 8),
      (eval env ((Vector.mapFinRange 8 fun (j : Fin 8) ↦
              Vector.mapRange 32 fun i_1 ↦
                var { index := i₀ + 48 * 227 + 64 * 455 + j.val * 33 + i_1 }) :
            Var SHA256State (F p)))[i]'hi
          = Vector.map (Expression.eval env)
              (Vector.mapRange 32 fun i_1 ↦
                var (F := F p) { index := i₀ + 48 * 227 + 64 * 455 + i * 33 + i_1 }) := by
    intro i hi
    rw [← getElem_eval_vector, CircuitType.eval_var_fields, Vector.getElem_mapFinRange]
  simp_all only [implies_true, and_self, forall_const, and_true]
  -- Value equality
  simp only [Specs.SHA256.compressBlock]
  ext i hi
  have ⟨h_val, _⟩ := h_add ⟨i, hi⟩
  simp only at h_val
  rw [Vector.getElem_map, h_index i hi, h_val,
      Vector.getElem_mapFinRange]
  simp only [_root_.add32, circuit_norm]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [MessageSchedule.circuit, MessageSchedule.Spec, MessageSchedule.Assumptions,
    SHA256Rounds.circuit, SHA256Rounds.Spec, SHA256Rounds.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched_impl, h_rounds_impl, _⟩ := h_env
  -- Extract directly from h_sched_impl/h_rounds_impl applied to assumptions.
  have h_sched_full := h_sched_impl h_block_norm
  have h_sched_norm := fun i => (h_sched_full i).2
  have h_rounds_full := h_rounds_impl ⟨h_state_norm, h_sched_norm⟩
  have h_rounds_norm := h_rounds_full.2
  refine ⟨h_block_norm, ⟨h_state_norm, h_sched_norm⟩, ?_⟩
  intro i
  refine ⟨?_, ?_⟩
  · -- Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[i.val])
    rw [← CircuitType.eval_var_fields, getElem_eval_vector, h_input_state]
    exact h_state_norm i
  · -- Normalized (Vector.map (Expression.eval env.toEnvironment) (stateVar ...)[i.val])
    have := h_rounds_norm i
    rw [← getElem_eval_vector, CircuitType.eval_var_fields] at this
    exact this

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlock
end Gadgets.SHA256
end
