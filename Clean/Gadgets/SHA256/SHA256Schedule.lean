import Clean.Gadgets.SHA256.LowerSigma0
import Clean.Gadgets.SHA256.LowerSigma1
import Clean.Gadgets.SHA256.Add32
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

namespace Gadgets.SHA256

/-!
# SHA-256 Message Schedule

Expands a 16-word block into a 64-word message schedule.

For i in 16..63:
  w[i] = σ₁(w[i−2]) + w[i−7] + σ₀(w[i−15]) + w[i−16]  (mod 2^32)

Per step, `scheduleStep` creates:
  - lowerSigma1: 2 × xor32 = 2 × 32 = 64 witness variables
  - lowerSigma0: 2 × xor32 = 64 witness variables
  - 3 × add32    = 3 × 33  = 99 witness variables
  Total: 64 + 64 + 99 = 227 variables per step.
-/


/-- One step of the message schedule: compute w[j] for j = i.val + 16. -/
private def scheduleStep (w : SHA256Schedule (Expression (F p))) (i : Fin 48) :
    Circuit (F p) (SHA256Schedule (Expression (F p))) := do
  let j := i.val + 16
  let s1   ← LowerSigma1.circuit (w.get ⟨j - 2,  by omega⟩)
  let s0   ← LowerSigma0.circuit (w.get ⟨j - 15, by omega⟩)
  let sum0 ← Add32.circuit ⟨s1, w.get ⟨j - 7, by omega⟩⟩
  let sum1 ← Add32.circuit ⟨sum0, s0⟩
  let wj   ← Add32.circuit ⟨sum1, w.get ⟨j - 16, by omega⟩⟩
  return w.set (⟨j, by omega⟩ : Fin 64) wj

private def constantLength :
    Circuit.ConstantLength (fun (x : SHA256Schedule (Expression (F p)) × Fin 48) => scheduleStep x.1 x.2) where
  localLength := 227
  localLength_eq _ _ := by
    simp [circuit_norm, scheduleStep, LowerSigma1.circuit, LowerSigma0.circuit, Add32.circuit]

/-- Expand a 16-word block into a 64-word message schedule.
    Each word is a `Var (fields 32) (F p)` (32-bit boolean vector, LSB first). -/
def messageSchedule (block : SHA256Block (Expression (F p))) :
    Circuit (F p) (SHA256Schedule (Expression (F p))) := do
  -- Initialise: first 16 words from block, next 48 as zero placeholders.
  let zero32 : Var (fields 32) (F p) := Vector.replicate 32 (0 : Expression (F p))
  let init : SHA256Schedule (Expression (F p)) := block.append (Vector.replicate 48 zero32)
  -- Expand indices 16..63 one at a time.
  -- Pass ConstantLength explicitly because the default tactic times out on this complex body.
  Circuit.foldlRange 48 init (fun w i => scheduleStep w i) constantLength

namespace MessageSchedule

def main (block : SHA256Block (Expression (F p))) : Circuit (F p) (SHA256Schedule (Expression (F p))) :=
  messageSchedule block

def Assumptions (block : SHA256Block (F p)) : Prop :=
  ∀ i : Fin 16, Normalized block[i]

def Spec (block : SHA256Block (F p)) (sched : SHA256Schedule (F p)) : Prop :=
  let block_val : Vector ℕ 16 := block.map valueBits
  let expected := Specs.SHA256.messageSchedule block_val
  ∀ i : Fin 64, valueBits sched[i] = expected[i] ∧ Normalized sched[i]

/-- Variable-level schedule after `k` expansion steps. Used as the explicit description
    of the foldlRange accumulator, mirroring `SHA256Rounds.stateVar`. -/
def varSchedule (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p))) :
    ℕ → SHA256Schedule (Expression (F p))
  | 0 =>
    Vector.append input_var_block
      (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))
  | k + 1 =>
    if h : k < 48 then
      (varSchedule i₀ input_var_block k).set
        (k + 16) (varFromOffset (fields 32) (i₀ + k * 227 + 194)) (by omega)
    else
      varSchedule i₀ input_var_block k

/-- Value-level schedule after `k` expansion steps. -/
private def valSchedule (input_block : Vector ℕ 16) : ℕ → Vector ℕ 64
  | 0 => Vector.mapFinRange 64 fun i => if h : i.val < 16 then input_block.get ⟨i.val, h⟩ else 0
  | k + 1 =>
    if h : k < 48 then
      let prev := valSchedule input_block k
      let wj := _root_.add32
        (_root_.add32 (Specs.SHA256.lowerSigma1 prev[k + 16 - 2]) prev[k + 16 - 7])
        (_root_.add32 (Specs.SHA256.lowerSigma0 prev[k + 16 - 15]) prev[k + 16 - 16])
      prev.set (k + 16) wj (by omega)
    else
      valSchedule input_block k

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 33)] in
/-- `Specs.SHA256.messageSchedule` equals our `valSchedule` at index 48. -/
private lemma messageSchedule_eq_valSchedule (input_block : Vector ℕ 16) :
    Specs.SHA256.messageSchedule input_block = valSchedule input_block 48 := by
  simp only [Specs.SHA256.messageSchedule]
  -- Generic step body, independent of the foldl bound, so the IH on `k` matches
  -- the new occurrence in `Fin.foldl_succ_last`.
  set body : Vector ℕ 64 → ℕ → Vector ℕ 64 := fun w n =>
    if h : n < 48 then
      have hj   : n + 16     < 64 := by omega
      let wj := _root_.add32
        (_root_.add32 (Specs.SHA256.lowerSigma1 w[n + 16 - 2]) w[n + 16 - 7])
        (_root_.add32 (Specs.SHA256.lowerSigma0 w[n + 16 - 15]) w[n + 16 - 16])
      w.set (n + 16) wj hj
    else w with hbody_def
  set init : Vector ℕ 64 :=
    Vector.mapFinRange 64 fun i => if h : i.val < 16 then input_block.get ⟨i.val, h⟩ else 0
  -- Rephrase RHS bodies in terms of `body`.
  have hspec : Fin.foldl 48 (fun w (i : Fin 48) =>
      w.set (i.val + 16)
        (_root_.add32 (_root_.add32 (Specs.SHA256.lowerSigma1 w[i.val + 16 - 2]) w[i.val + 16 - 7])
          (_root_.add32 (Specs.SHA256.lowerSigma0 w[i.val + 16 - 15]) w[i.val + 16 - 16]))
        (by have := i.isLt; omega)) init =
      Fin.foldl 48 (fun w (i : Fin 48) => body w i.val) init := by
    congr 1; funext w i
    have hi : i.val < 48 := i.isLt
    simp only [hbody_def, dif_pos hi]
  rw [hspec]
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k (fun w (i : Fin k) => body w i.val) init =
        valSchedule input_block k by
    have h48 := h 48 (le_refl 48)
    convert h48 using 1
  intro k hk
  induction k with
  | zero => simp [valSchedule, Fin.foldl_zero, init]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valSchedule]
    have hk' : k ≤ 48 := by omega
    specialize ih hk'
    rw [show (fun w (i : Fin k) => body w i.castSucc.val) =
           (fun w (i : Fin k) => body w i.val) from rfl, ih]
    simp only [Fin.val_last, hbody_def, dif_pos (show k < 48 from by omega)]

/-- The output of `scheduleStep w i` at offset `n` is `w.set (i.val + 16) (varFromOffset ...)`. -/
private lemma scheduleStep_output (w : SHA256Schedule (Expression (F p))) (i : Fin 48) (n : ℕ) :
    (scheduleStep w i).output n =
      w.set (i.val + 16) (varFromOffset (fields 32) (n + 194)) (by omega) := by
  simp [scheduleStep, circuit_norm, LowerSigma1.circuit, LowerSigma0.circuit, Add32.circuit]

/-- The localLength of `scheduleStep w i` is 227. -/
private lemma scheduleStep_localLength (w : SHA256Schedule (Expression (F p))) (i : Fin 48) (n : ℕ) :
    (scheduleStep w i).localLength n = 227 := by
  simp [circuit_norm, scheduleStep, LowerSigma1.circuit, LowerSigma0.circuit, Add32.circuit]

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 48` equals `varSchedule i₀ input_var k`. -/
private lemma foldlAcc_eq_varSchedule (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p)))
    (k : ℕ) (h : k < 48) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 48)
      (fun w (i : Fin 48) => scheduleStep w i)
      (Vector.append input_var_block (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p)))))
      ⟨k, h⟩ =
        varSchedule i₀ input_var_block k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk : k < 48 := by omega
    specialize ih hk
    rw [Fin.foldl_succ_last, varSchedule, dif_pos hk]
    rw [show Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            (scheduleStep acc ⟨i.castSucc.val, by have := i.isLt; omega⟩).output
              (i₀ + i.castSucc.val *
                (scheduleStep acc ⟨i.castSucc.val, by have := i.isLt; omega⟩).localLength))
            _ =
        Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            (scheduleStep acc ⟨i.val, by have := i.isLt; omega⟩).output
              (i₀ + i.val *
                (scheduleStep acc ⟨i.val, by have := i.isLt; omega⟩).localLength))
            _ from rfl, ih]
    simp only [Fin.val_last]
    rw [scheduleStep_output, scheduleStep_localLength]

/-- The 48-step `Fin.foldl` of the variable-level schedule body equals `varSchedule 48`. -/
private lemma finFoldl_eq_varSchedule_48 (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p))) :
    Fin.foldl 48
      (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin 48) =>
        (scheduleStep acc i (i₀ + i.val * 227)).1)
      (Vector.append input_var_block
        (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
      varSchedule i₀ input_var_block 48 := by
  -- Prove a more general statement by induction on `k ≤ 48`, where we cast Fin k to Fin 48.
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k
        (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
          (scheduleStep acc ⟨i.val, by have := i.isLt; omega⟩ (i₀ + i.val * 227)).1)
        (Vector.append input_var_block
          (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
        (show Vector (fields 32 (Expression (F p))) (16 + 48) from
          varSchedule i₀ input_var_block k) by
    have := h 48 (le_refl 48)
    convert this using 2
  intro k hk
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk' : k ≤ 48 := by omega
    have hk'' : k < 48 := by omega
    specialize ih hk'
    rw [Fin.foldl_succ_last]
    rw [show Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            (scheduleStep acc ⟨i.castSucc.val, by have := i.isLt; omega⟩ (i₀ + i.castSucc.val * 227)).1)
            _ =
        Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            (scheduleStep acc ⟨i.val, by have := i.isLt; omega⟩ (i₀ + i.val * 227)).1)
            _ from rfl, ih]
    simp only [Fin.val_last]
    rw [varSchedule, dif_pos hk'']
    -- (scheduleStep w i).output n = (scheduleStep w i n).1
    change (scheduleStep _ ⟨k, hk''⟩).output (i₀ + k * 227) = _
    rw [scheduleStep_output]

/-- The soundness inductive invariant. Given the constraints `h_holds` hold for every step,
    the variable-level schedule at step `k` matches the value-level schedule and is normalized. -/
private lemma soundness_inv (i₀ : ℕ) (input_var : SHA256Block (Expression (F p)))
    (env : Environment (F p)) (input : SHA256Block (F p))
    (h_input : eval env input_var = input)
    (h_assumptions : ∀ i : Fin 16, Normalized input[i])
    (h_holds : ∀ (i : Fin 48),
      Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0,
          lookup := fun l => l.Soundness env,
          interact := fun i ↦ i.Guarantees env,
          subcircuit := fun {m} s => s.Assumptions env → s.Spec env }
        (scheduleStep
          (Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 48) (fun w i ↦ scheduleStep w i)
            (Vector.append input_var (Vector.replicate 48 (Vector.replicate 32 0))) i)
          i (i₀ + ↑i * 227)).2) :
    ∀ (k : ℕ) (_ : k ≤ 48),
      (∀ (j : ℕ) (hj : j < 64),
        valueBits (eval env ((varSchedule i₀ input_var k)[j]'hj)) =
          (valSchedule (input.map valueBits) k)[j]'hj) ∧
      (∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env ((varSchedule i₀ input_var k)[j]'hj))) := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [varSchedule, valSchedule]
      by_cases hj16 : j < 16
      · -- j < 16: the slot is `input_var[j]`, eval gives `input[j]`.
        change valueBits (eval env (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
        rw [Vector.getElem_append_left hj16]
        simp only [Vector.getElem_mapFinRange, hj16, dif_pos]
        rw [show (Vector.map valueBits input).get ⟨j, hj16⟩ =
              (Vector.map valueBits input)[j]'hj16 from rfl]
        rw [Vector.getElem_map]
        congr 1
        rw [getElem_eval_vector, h_input]
      · -- j ≥ 16: the slot is `Vector.replicate 32 0`, both sides equal 0.
        change valueBits (eval env (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
        have hj' : j < 16 + 48 := by omega
        rw [show (input_var ++ Vector.replicate 48
              (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
            (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
            from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
        rw [Vector.getElem_replicate]
        simp only [Vector.getElem_mapFinRange, hj16, dif_neg, not_false_eq_true]
        -- LHS: valueBits (eval env (Vector.replicate 32 0)) = 0
        have h_eval_repl :
            eval env (Vector.replicate 32 (0 : Expression (F p))) =
              Vector.replicate 32 (0 : F p) := by
          rw [CircuitType.eval_var_fields]
          rw [Vector.map_replicate]
          rfl
        unfold valueBits
        rw [h_eval_repl]
        simp [Vector.getElem_replicate]
    · intro j hj
      simp only [varSchedule]
      by_cases hj16 : j < 16
      · change Normalized (eval env (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        rw [Vector.getElem_append_left hj16]
        -- eval env input_var[j] = input[j]
        have h_ev : eval env (input_var[j]'hj16) = input[j]'hj16 := by
          rw [getElem_eval_vector, h_input]
        rw [h_ev]
        exact h_assumptions ⟨j, hj16⟩
      · change Normalized (eval env (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        have hj' : j < 16 + 48 := by omega
        rw [show (input_var ++ Vector.replicate 48
              (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
            (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
            from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
        rw [Vector.getElem_replicate]
        have h_eval_repl :
            eval env (Vector.replicate 32 (0 : Expression (F p))) =
              Vector.replicate 32 (0 : F p) := by
          rw [CircuitType.eval_var_fields]
          rw [Vector.map_replicate]
          rfl
        rw [h_eval_repl]
        intro i
        left
        simp [Vector.getElem_replicate]
  | succ k ih =>
    have hk' : k ≤ 48 := by omega
    have hk'' : k < 48 := by omega
    obtain ⟨ih_val, ih_norm⟩ := ih hk'
    have h_step := h_holds ⟨k, hk''⟩
    rw [foldlAcc_eq_varSchedule i₀ input_var k hk''] at h_step
    -- Unfold scheduleStep at h_step.
    simp only [scheduleStep, circuit_norm, LowerSigma1.circuit, LowerSigma0.circuit,
      Add32.circuit, LowerSigma1.Assumptions, LowerSigma1.Spec,
      LowerSigma0.Assumptions, LowerSigma0.Spec, Add32.Assumptions, Add32.Spec, and_imp] at h_step
    obtain ⟨c_sig1, c_sig0, c_sum0, c_sum1, c_wj⟩ := h_step
    -- Establish normalization of indexed positions via IH.
    -- Convert `Vector.get x ⟨i, h⟩` to `x[i]` for our IH lemmas.
    have h_eval_get : ∀ (x : SHA256Schedule (Expression (F p))) (i : ℕ) (h : i < 64),
        Vector.map (Expression.eval env) (Vector.get x ⟨i, h⟩) = eval env (x[i]'h) := by
      intros x i h
      rw [show Vector.get x ⟨i, h⟩ = x[i]'h from rfl,
          CircuitType.eval_var_fields]
    have h_norm_m2 : Normalized (eval env ((varSchedule i₀ input_var k)[k + 16 - 2]'(by omega))) :=
      ih_norm (k + 16 - 2) (by omega)
    have h_norm_m7 : Normalized (eval env ((varSchedule i₀ input_var k)[k + 16 - 7]'(by omega))) :=
      ih_norm (k + 16 - 7) (by omega)
    have h_norm_m15 : Normalized (eval env ((varSchedule i₀ input_var k)[k + 16 - 15]'(by omega))) :=
      ih_norm (k + 16 - 15) (by omega)
    have h_norm_m16 : Normalized (eval env ((varSchedule i₀ input_var k)[k + 16 - 16]'(by omega))) :=
      ih_norm (k + 16 - 16) (by omega)
    -- Apply specs in order: sig1, sig0, sum0, sum1, wj.
    rw [h_eval_get] at c_sig1
    obtain ⟨v_sig1, n_sig1⟩ := c_sig1 h_norm_m2
    rw [h_eval_get] at c_sig0
    obtain ⟨v_sig0, n_sig0⟩ := c_sig0 h_norm_m15
    rw [h_eval_get] at c_sum0
    obtain ⟨v_sum0, n_sum0⟩ := c_sum0 n_sig1 h_norm_m7
    obtain ⟨v_sum1, n_sum1⟩ := c_sum1 n_sum0 n_sig0
    rw [h_eval_get] at c_wj
    obtain ⟨v_wj, n_wj⟩ := c_wj n_sum1 h_norm_m16
    -- Now compose values: wj's value should equal valSchedule's k+16 slot.
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [varSchedule, valSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self]
        -- RHS: the wj of the spec.
        -- LHS: valueBits (eval env (varFromOffset (fields 32) (i₀ + k * 227 + 194)))
        rw [show (i₀ + k * 227 + 194 : ℕ) = i₀ + k * 227 + 64 + 64 + 33 + 33 from by ring]
        rw [show (varFromOffset (fields 32)
              (i₀ + k * 227 + 64 + 64 + 33 + 33) : Vector (Expression (F p)) 32) =
            (Vector.mapRange 32 fun i ↦ (var { index := i₀ + k * 227 + 64 + 64 + 33 + 33 + i } : Expression (F p)))
            from by
          simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
        rw [CircuitType.eval_var_fields, v_wj, v_sum1, v_sig0, v_sum0, v_sig1,
          ih_val (k + 16 - 7) (by omega), ih_val (k + 16 - 16) (by omega),
          ih_val (k + 16 - 2) (by omega), ih_val (k + 16 - 15) (by omega)]
        -- RHS uses `set ... [k+16]` which is the new wj_spec.
        rw [Vector.getElem_set_self]
        -- Both sides should be `(sig1 + x-7 + sig0 + x-16) % 2^32` after unfolding add32.
        show _ = (_root_.add32 (_root_.add32 _ _) (_root_.add32 _ _) : ℕ)
        unfold _root_.add32
        -- Reduce to nat-mod equality.
        omega
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih_val j hj
    · intro j hj
      simp only [varSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self]
        rw [show (i₀ + k * 227 + 194 : ℕ) = i₀ + k * 227 + 64 + 64 + 33 + 33 from by ring]
        rw [show (varFromOffset (fields 32)
              (i₀ + k * 227 + 64 + 64 + 33 + 33) : Vector (Expression (F p)) 32) =
            (Vector.mapRange 32 fun i ↦ (var { index := i₀ + k * 227 + 64 + 64 + 33 + 33 + i } : Expression (F p)))
            from by
          simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
        rw [CircuitType.eval_var_fields]
        exact n_wj
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih_norm j hj

instance elaborated : ElaboratedCircuit (F p) SHA256Block SHA256Schedule main := by
  elaborate_circuit_with {
    output input i₀ := varSchedule i₀ input 48
  } using by
    simp only [circuit_norm, ← finFoldl_eq_varSchedule_48]
    intros
    congr

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [messageSchedule]
  simp only [show ∀ (w : SHA256Schedule (Expression (F p))) (i : Fin 48) (n : ℕ),
    Operations.localLength (scheduleStep w i n).2 = 227 from scheduleStep_localLength]
    at h_holds ⊢
  -- Use the inductive invariant at k = 48.
  have h_invk :=
    soundness_inv i₀ input_var env input h_input h_assumptions h_holds 48 (le_refl 48)
  obtain ⟨h_val_48, h_norm_48⟩ := h_invk
  refine ⟨?_, ?_⟩
  · intro i
    have h_bridge :
        (eval env (varSchedule i₀ input_var 48))[i.val] =
          eval env ((varSchedule i₀ input_var 48)[i.val]'i.isLt) := by
      exact (getElem_eval_vector
        (α := fields 32) (n := 64) env (varSchedule i₀ input_var 48) i.val i.isLt).symm
    refine ⟨?_, ?_⟩
    · rw [h_bridge, messageSchedule_eq_valSchedule]
      exact h_val_48 i.val i.isLt
    · rw [h_bridge]
      exact h_norm_48 i.val i.isLt
  · -- Requirements: scheduleStep's channelsWithRequirements is empty (only R1CS subcircuits).
    intro i
    simp [scheduleStep, circuit_norm, LowerSigma0.circuit, LowerSigma1.circuit, Add32.circuit]

theorem completeness : Completeness (F p) (Input := SHA256Block) (Output := SHA256Schedule) main Assumptions := by
  circuit_proof_start [messageSchedule]
  simp only [show ∀ (w : SHA256Schedule (Expression (F p))) (i : Fin 48) (n : ℕ),
    Operations.localLength (scheduleStep w i n).2 = 227 from scheduleStep_localLength]
    at h_env ⊢
  -- Inductive invariant: at every step k, every slot of varSchedule i₀ input_var k is Normalized.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 48),
      ∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env.toEnvironment ((varSchedule i₀ input_var k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [varSchedule]
      by_cases hj16 : j < 16
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        rw [Vector.getElem_append_left hj16]
        have h_ev : eval env.toEnvironment (input_var[j]'hj16) = input[j]'hj16 := by
          rw [getElem_eval_vector, h_input]
        rw [h_ev]
        exact h_assumptions ⟨j, hj16⟩
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        have hj' : j < 16 + 48 := by omega
        rw [show (input_var ++ Vector.replicate 48
              (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
            (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
            from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
        rw [Vector.getElem_replicate]
        have h_eval_repl :
            eval env.toEnvironment (Vector.replicate 32 (0 : Expression (F p))) =
              Vector.replicate 32 (0 : F p) := by
          rw [CircuitType.eval_var_fields]
          rw [Vector.map_replicate]
          rfl
        rw [h_eval_repl]
        intro i
        left
        simp [Vector.getElem_replicate]
    | succ k ih =>
      have hk' : k ≤ 48 := by omega
      have hk'' : k < 48 := by omega
      specialize ih hk'
      have h_step := h_env ⟨k, hk''⟩
      rw [foldlAcc_eq_varSchedule i₀ input_var k hk''] at h_step
      -- Simplify h_step to get the chain.
      simp only [scheduleStep, circuit_norm, LowerSigma1.circuit, LowerSigma0.circuit,
        Add32.circuit, LowerSigma1.Assumptions, LowerSigma1.Spec,
        LowerSigma0.Assumptions, LowerSigma0.Spec, Add32.Assumptions, Add32.Spec, and_imp]
        at h_step
      -- We need to show Normalized at slot j for varSchedule (k+1).
      obtain ⟨c_sig1, c_sig0, c_sum0, c_sum1, c_wj⟩ := h_step
      have h_eval_get : ∀ (x : SHA256Schedule (Expression (F p))) (i : ℕ) (h : i < 64),
          Vector.map (Expression.eval env.toEnvironment) (Vector.get x ⟨i, h⟩) =
            eval env.toEnvironment (x[i]'h) := by
        intros x i h
        rw [show Vector.get x ⟨i, h⟩ = x[i]'h from rfl,
            CircuitType.eval_var_fields]
      have h_norm_m2 := ih (k + 16 - 2) (by omega)
      have h_norm_m7 := ih (k + 16 - 7) (by omega)
      have h_norm_m15 := ih (k + 16 - 15) (by omega)
      have h_norm_m16 := ih (k + 16 - 16) (by omega)
      rw [h_eval_get] at c_sig1
      obtain ⟨_, n_sig1⟩ := c_sig1 h_norm_m2
      rw [h_eval_get] at c_sig0
      obtain ⟨_, n_sig0⟩ := c_sig0 h_norm_m15
      rw [h_eval_get] at c_sum0
      obtain ⟨_, n_sum0⟩ := c_sum0 n_sig1 h_norm_m7
      obtain ⟨_, n_sum1⟩ := c_sum1 n_sum0 n_sig0
      rw [h_eval_get] at c_wj
      obtain ⟨_, n_wj⟩ := c_wj n_sum1 h_norm_m16
      intro j hj
      simp only [varSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self]
        rw [show (i₀ + k * 227 + 194 : ℕ) = i₀ + k * 227 + 64 + 64 + 33 + 33 from by ring]
        rw [show (varFromOffset (fields 32)
              (i₀ + k * 227 + 64 + 64 + 33 + 33) : Vector (Expression (F p)) 32) =
            (Vector.mapRange 32 fun i ↦ (var { index := i₀ + k * 227 + 64 + 64 + 33 + 33 + i } : Expression (F p)))
            from by
          simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
        rw [CircuitType.eval_var_fields]
        exact n_wj
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih j hj
  -- The goal is to provide the chain of assumptions for each step.
  intro i
  have hk : i.val < 48 := i.isLt
  have hk' : i.val ≤ 48 := le_of_lt hk
  -- Get normalization of state at step i.
  have ih := h_inv i.val hk'
  -- Apply h_env at step i and unfold.
  have h_env_i := h_env i
  rw [foldlAcc_eq_varSchedule i₀ input_var i.val hk] at h_env_i
  -- Unfold scheduleStep & subcircuit Assumptions / Spec / and_imp at h_env_i.
  simp only [scheduleStep, circuit_norm, LowerSigma1.circuit, LowerSigma0.circuit,
    Add32.circuit, LowerSigma1.Assumptions, LowerSigma1.Spec,
    LowerSigma0.Assumptions, LowerSigma0.Spec, Add32.Assumptions, Add32.Spec, and_imp]
    at h_env_i
  -- The goal is also structured this way.
  rw [foldlAcc_eq_varSchedule i₀ input_var i.val hk]
  simp only [scheduleStep, circuit_norm, LowerSigma1.circuit, LowerSigma0.circuit,
    Add32.circuit, LowerSigma1.Assumptions,
    LowerSigma0.Assumptions, Add32.Assumptions]
  -- Now we need to provide the chain of normalized assumptions.
  -- Extract the chain from h_env_i.
  obtain ⟨e_sig1, e_sig0, e_sum0, e_sum1, e_wj⟩ := h_env_i
  have h_eval_get : ∀ (x : SHA256Schedule (Expression (F p))) (i : ℕ) (h : i < 64),
      Vector.map (Expression.eval env.toEnvironment) (Vector.get x ⟨i, h⟩) =
        eval env.toEnvironment (x[i]'h) := by
    intros x i h
    rw [show Vector.get x ⟨i, h⟩ = x[i]'h from rfl,
        CircuitType.eval_var_fields]
  have h_norm_m2 := ih (i.val + 16 - 2) (by omega)
  have h_norm_m7 := ih (i.val + 16 - 7) (by omega)
  have h_norm_m15 := ih (i.val + 16 - 15) (by omega)
  have h_norm_m16 := ih (i.val + 16 - 16) (by omega)
  rw [h_eval_get] at e_sig1
  obtain ⟨_, n_sig1⟩ := e_sig1 h_norm_m2
  rw [h_eval_get] at e_sig0
  obtain ⟨_, n_sig0⟩ := e_sig0 h_norm_m15
  rw [h_eval_get] at e_sum0
  obtain ⟨_, n_sum0⟩ := e_sum0 n_sig1 h_norm_m7
  obtain ⟨_, n_sum1⟩ := e_sum1 n_sum0 n_sig0
  -- The goal is the chain of ProverAssumptions = R1CS Assumptions = Normalized.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_eval_get]; exact h_norm_m2
  · rw [h_eval_get]; exact h_norm_m15
  · rw [h_eval_get]; exact ⟨n_sig1, h_norm_m7⟩
  · exact ⟨n_sum0, n_sig0⟩
  · rw [h_eval_get]; exact ⟨n_sum1, h_norm_m16⟩

def circuit : FormalCircuit (F p) SHA256Block SHA256Schedule where
  main; elaborated; Assumptions; Spec; soundness;
  completeness := by simp only [completeness]

end MessageSchedule
end Gadgets.SHA256
end
