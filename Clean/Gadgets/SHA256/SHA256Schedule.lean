import Clean.Gadgets.SHA256.LowerSigma0
import Clean.Gadgets.SHA256.LowerSigma1
import Clean.Gadgets.SHA256.Add32
import Clean.Gadgets.SHA256.AddMod32
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Gadgets.SHA256

private instance fact_four_le_eight : Fact ((4 : ℕ) ≤ 8) := ⟨by norm_num⟩

/-!
# SHA-256 Message Schedule

Expands a 16-word block into a 64-word message schedule.

For i in 16..63:
  w[i] = σ₁(w[i−2]) + w[i−7] + σ₀(w[i−15]) + w[i−16]  (mod 2^32)

Per step, `scheduleStep` creates:
  - lowerSigma1: carry-save xor3 = 32 witness variables
  - lowerSigma0: carry-save xor3 = 32 witness variables
  - 1 × addMod32 (4 operands) = 35 witness variables (32 result bits + 3 carry bits)
  Total: 32 + 32 + 35 = 99 variables per step.
-/

private abbrev Schedule := Vector (Var (fields 32) (F p)) 64

/-- One step of the message schedule: compute w[j] for j = i.val + 16. -/
private def scheduleStep (w : Schedule (p := p)) (i : Fin 48) :
    Circuit (F p) (Schedule (p := p)) := do
  let j := i.val + 16
  let s1   ← subcircuit LowerSigma1.circuit (w.get ⟨j - 2,  by omega⟩)
  let s0   ← subcircuit LowerSigma0.circuit (w.get ⟨j - 15, by omega⟩)
  let wj   ← AddMod32.circuit (n := 4)
    #v[s1, w.get ⟨j - 7, by omega⟩, s0, w.get ⟨j - 16, by omega⟩]
  return w.set (⟨j, by omega⟩ : Fin 64) wj

private instance :
    Circuit.ConstantLength (fun (x : Schedule (p := p) × Fin 48) => scheduleStep x.1 x.2) where
  localLength := 99
  localLength_eq _ _ := by
    simp [circuit_norm, scheduleStep, LowerSigma1.circuit, LowerSigma0.circuit,
      AddMod32.circuit, AddMod32.elaborated]

/-- Expand a 16-word block into a 64-word message schedule.
    Each word is a `Var (fields 32) (F p)` (32-bit boolean vector, LSB first). -/
@[irreducible] def messageSchedule (block : Vector (Var (fields 32) (F p)) 16) :
    Circuit (F p) (Schedule (p := p)) := do
  -- Initialise: first 16 words from block, next 48 as zero placeholders.
  let zero32 : Var (fields 32) (F p) := Vector.replicate 32 (0 : Expression (F p))
  let init : Schedule (p := p) := block.append (Vector.replicate 48 zero32)
  -- Expand indices 16..63 one at a time.
  -- Pass ConstantLength explicitly because the default tactic times out on this complex body.
  Circuit.foldlRange 48 init (fun w i => scheduleStep w i) ⟨99, fun _ _ => by
    simp [circuit_norm, scheduleStep, LowerSigma1.circuit, LowerSigma0.circuit,
      AddMod32.circuit, AddMod32.elaborated]⟩

namespace MessageSchedule

def main (block : Var SHA256Block (F p)) : Circuit (F p) (Var SHA256Schedule (F p)) :=
  messageSchedule block

instance elaborated : ElaboratedCircuit (F p) SHA256Block SHA256Schedule where
  main := main
  localLength _ := 48 * 99
  localLength_eq _ _ := by
    unfold main messageSchedule
    simp [circuit_norm, scheduleStep,
      LowerSigma1.circuit, LowerSigma0.circuit, AddMod32.circuit, AddMod32.elaborated]
  subcircuitsConsistent _ _ := by
    unfold main messageSchedule
    simp +arith [circuit_norm, scheduleStep,
      LowerSigma1.circuit, LowerSigma0.circuit, AddMod32.circuit, AddMod32.elaborated]
  channelsLawful := by
    intro block i0
    unfold main messageSchedule
    simp [circuit_norm, scheduleStep,
      LowerSigma1.circuit, LowerSigma0.circuit, AddMod32.circuit, AddMod32.elaborated]

def Assumptions (block : SHA256Block (F p)) : Prop :=
  ∀ i : Fin 16, Normalized block[i]

def Spec (block : SHA256Block (F p)) (sched : SHA256Schedule (F p)) : Prop :=
  let block_val : Vector ℕ 16 := block.map valueBits
  let expected := Specs.SHA256.messageSchedule block_val
  ∀ i : Fin 64, valueBits sched[i] = expected[i] ∧ Normalized sched[i]

/-- A single 4-operand modular reduction equals two nested binary reductions. -/
private lemma add4_mod (a b c d M : ℕ) :
    (a + b + c + d) % M = ((a + b) % M + (c + d) % M) % M := by
  conv_lhs => rw [show a + b + c + d = (a + b) + (c + d) from by ring]
  rw [Nat.add_mod]

omit [Fact (p > 2 ^ 35)] in
/-- The evaluation of a 4-element variable vector, elementwise. -/
private lemma eval_v4 (env : Environment (F p)) (a b c d : Var (fields 32) (F p)) :
    (eval env (#v[a, b, c, d] : Var (ProvableVector (fields 32) 4) (F p)) :
      ProvableVector (fields 32) 4 (F p)) =
      #v[Vector.map (Expression.eval env) a, Vector.map (Expression.eval env) b,
         Vector.map (Expression.eval env) c, Vector.map (Expression.eval env) d] := by
  rw [eval_vector]
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    · rename_i hi
      simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      exact (ProvableType.getElem_eval_fields env _ _ hi).symm

omit [Fact (p > 2 ^ 35)] in
/-- `AddMod32.Assumptions` of a 4-operand vector unfolds to four `Normalized` facts. -/
private lemma addMod32_assum_iff (env : Environment (F p))
    (a b c d : Var (fields 32) (F p)) :
    (∀ j : Fin 4, Normalized ((eval env (#v[a, b, c, d] :
        Var (ProvableVector (fields 32) 4) (F p)) :
        ProvableVector (fields 32) 4 (F p))[j])) ↔
      Normalized (Vector.map (Expression.eval env) a) ∧
      Normalized (Vector.map (Expression.eval env) b) ∧
      Normalized (Vector.map (Expression.eval env) c) ∧
      Normalized (Vector.map (Expression.eval env) d) := by
  rw [eval_v4]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨ha, hb, hc, hd⟩ j
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
    · exact hd

omit [Fact (p > 2 ^ 35)] in
/-- `opsValueSum` of a 4-operand vector expands to four `valueBits` summands. -/
private lemma addMod32_opsValueSum (env : Environment (F p))
    (a b c d : Var (fields 32) (F p)) :
    opsValueSum (eval env (#v[a, b, c, d] :
        Var (ProvableVector (fields 32) 4) (F p)) :
        ProvableVector (fields 32) 4 (F p)) =
      valueBits (Vector.map (Expression.eval env) a) +
      valueBits (Vector.map (Expression.eval env) b) +
      valueBits (Vector.map (Expression.eval env) c) +
      valueBits (Vector.map (Expression.eval env) d) := by
  unfold opsValueSum
  rw [eval_v4, Fin.sum_univ_four]
  norm_num [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]

/-- Variable-level schedule after `k` expansion steps. Used as the explicit description
    of the foldlRange accumulator, mirroring `SHA256Rounds.stateVar`. -/
private def varSchedule (i₀ : ℕ) (input_var_block : Var SHA256Block (F p)) :
    ℕ → Schedule (p := p)
  | 0 =>
    Vector.append input_var_block
      (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))
  | k + 1 =>
    if h : k < 48 then
      (varSchedule i₀ input_var_block k).set
        (k + 16) (varFromOffset (fields 32) (i₀ + k * 99 + 64)) (by omega)
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

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
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
private lemma scheduleStep_output (w : Schedule (p := p)) (i : Fin 48) (n : ℕ) :
    (scheduleStep w i).output n =
      w.set (i.val + 16) (varFromOffset (fields 32) (n + 64)) (by omega) := by
  simp [scheduleStep, circuit_norm, LowerSigma1.circuit, LowerSigma0.circuit, AddMod32.circuit]

/-- The localLength of `scheduleStep w i` is 99. -/
private lemma scheduleStep_localLength (w : Schedule (p := p)) (i : Fin 48) (n : ℕ) :
    (scheduleStep w i).localLength n = 99 := by
  simp [circuit_norm, scheduleStep, LowerSigma1.circuit, LowerSigma0.circuit, AddMod32.circuit]

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 48` equals `varSchedule i₀ input_var k`. -/
private lemma foldlAcc_eq_varSchedule (i₀ : ℕ) (input_var_block : Var SHA256Block (F p))
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
          (fun (acc : Schedule (p := p)) (i : Fin k) =>
            (scheduleStep acc ⟨i.castSucc.val, by have := i.isLt; omega⟩).output
              (i₀ + i.castSucc.val *
                (scheduleStep acc ⟨i.castSucc.val, by have := i.isLt; omega⟩).localLength))
            _ =
        Fin.foldl k
          (fun (acc : Schedule (p := p)) (i : Fin k) =>
            (scheduleStep acc ⟨i.val, by have := i.isLt; omega⟩).output
              (i₀ + i.val *
                (scheduleStep acc ⟨i.val, by have := i.isLt; omega⟩).localLength))
            _ from rfl, ih]
    simp only [Fin.val_last]
    rw [scheduleStep_output, scheduleStep_localLength]

/-- The 48-step `Fin.foldl` of the variable-level schedule body equals `varSchedule 48`. -/
private lemma finFoldl_eq_varSchedule_48 (i₀ : ℕ) (input_var_block : Var SHA256Block (F p)) :
    Fin.foldl 48
      (fun (acc : Vector (fields 32 (Expression (F p))) (16 + 48)) (i : Fin 48) =>
        (scheduleStep (show Schedule (p := p) from acc) i (i₀ + i.val * 99)).1)
      (Vector.append input_var_block
        (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
      (show Vector (fields 32 (Expression (F p))) (16 + 48) from
        varSchedule i₀ input_var_block 48) := by
  -- Prove a more general statement by induction on `k ≤ 48`, where we cast Fin k to Fin 48.
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k
        (fun (acc : Vector (fields 32 (Expression (F p))) (16 + 48)) (i : Fin k) =>
          (scheduleStep (show Schedule (p := p) from acc)
            ⟨i.val, by have := i.isLt; omega⟩ (i₀ + i.val * 99)).1)
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
          (fun (acc : Vector (fields 32 (Expression (F p))) (16 + 48)) (i : Fin k) =>
            (scheduleStep (show Schedule (p := p) from acc)
              ⟨i.castSucc.val, by have := i.isLt; omega⟩
              (i₀ + i.castSucc.val * 99)).1)
            _ =
        Fin.foldl k
          (fun (acc : Vector (fields 32 (Expression (F p))) (16 + 48)) (i : Fin k) =>
            (scheduleStep (show Schedule (p := p) from acc)
              ⟨i.val, by have := i.isLt; omega⟩
              (i₀ + i.val * 99)).1)
            _ from rfl, ih]
    simp only [Fin.val_last]
    rw [varSchedule, dif_pos hk'']
    -- (scheduleStep w i).output n = (scheduleStep w i n).1
    change (scheduleStep _ ⟨k, hk''⟩).output (i₀ + k * 99) = _
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
          i (i₀ + ↑i * 99)).2) :
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
      LowerSigma1.Assumptions, LowerSigma1.Spec,
      LowerSigma0.Assumptions, LowerSigma0.Spec] at h_step
    obtain ⟨c_sig1, c_sig0, c_wj⟩ := h_step
    -- Establish normalization of indexed positions via IH.
    -- Convert `Vector.get x ⟨i, h⟩` to `x[i]` for our IH lemmas.
    have h_eval_get : ∀ (x : Schedule (p := p)) (i : ℕ) (h : i < 64),
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
    -- Apply LowerSigma specs first.
    rw [h_eval_get] at c_sig1
    obtain ⟨v_sig1, n_sig1⟩ := c_sig1 h_norm_m2
    rw [h_eval_get] at c_sig0
    obtain ⟨v_sig0, n_sig0⟩ := c_sig0 h_norm_m15
    -- Apply the 4-operand AddMod32 spec.
    simp only [AddMod32.circuit, AddMod32.Assumptions, AddMod32.Spec,
      addMod32_assum_iff, addMod32_opsValueSum] at c_wj
    obtain ⟨v_wj, n_wj⟩ := c_wj ⟨n_sig1, by rw [h_eval_get]; exact h_norm_m7,
      n_sig0, by rw [h_eval_get]; exact h_norm_m16⟩
    -- `v_wj`/`n_wj` refer to the output, which equals `varFromOffset (i₀+k*99+64)`.
    simp only [AddMod32.elaborated] at v_wj n_wj
    -- Now compose values: wj's value should equal valSchedule's k+16 slot.
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [varSchedule, valSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self]
        rw [show (i₀ + k * 99 + 64 : ℕ) = i₀ + k * 99 + 32 + 32 from by ring]
        rw [CircuitType.eval_var_fields, v_wj]
        rw [v_sig1, v_sig0]
        rw [Vector.getElem_set_self]
        have e7 : Vector.map (Expression.eval env)
            ((varSchedule i₀ input_var k).get ⟨k + 16 - 7, by omega⟩) =
            eval env ((varSchedule i₀ input_var k)[k + 16 - 7]'(by omega)) := h_eval_get _ _ _
        have e16 : Vector.map (Expression.eval env)
            ((varSchedule i₀ input_var k).get ⟨k + 16 - 16, by omega⟩) =
            eval env ((varSchedule i₀ input_var k)[k + 16 - 16]'(by omega)) := h_eval_get _ _ _
        rw [e7, e16, ih_val (k + 16 - 7) (by omega), ih_val (k + 16 - 16) (by omega),
          ih_val (k + 16 - 2) (by omega), ih_val (k + 16 - 15) (by omega)]
        -- Both sides equal `(sig1 + w7 + sig0 + w16) % 2^32`.
        show (_ + _ + _ + _) % 2^32 =
          (_root_.add32 (_root_.add32 _ _) (_root_.add32 _ _) : ℕ)
        unfold _root_.add32
        rw [add4_mod]
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih_val j hj
    · intro j hj
      simp only [varSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self]
        rw [show (i₀ + k * 99 + 64 : ℕ) = i₀ + k * 99 + 32 + 32 from by ring]
        rw [CircuitType.eval_var_fields]
        exact n_wj
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih_norm j hj

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  unfold messageSchedule at h_holds ⊢
  simp only [circuit_norm] at h_holds ⊢
  simp only [show ∀ (w : Schedule (p := p)) (i : Fin 48) (n : ℕ),
    Operations.localLength (scheduleStep w i n).2 = 99 from scheduleStep_localLength]
    at h_holds ⊢
  have h_eq := finFoldl_eq_varSchedule_48 i₀ input_var
  simp only [h_eq]
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
    simp [scheduleStep, circuit_norm, LowerSigma0.circuit, LowerSigma1.circuit, AddMod32.circuit]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  unfold messageSchedule at h_env ⊢
  simp only [circuit_norm] at h_env ⊢
  simp only [show ∀ (w : Schedule (p := p)) (i : Fin 48) (n : ℕ),
    Operations.localLength (scheduleStep w i n).2 = 99 from scheduleStep_localLength]
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
        LowerSigma1.Assumptions, LowerSigma1.Spec,
        LowerSigma0.Assumptions, LowerSigma0.Spec]
        at h_step
      -- We need to show Normalized at slot j for varSchedule (k+1).
      obtain ⟨c_sig1, c_sig0, c_wj⟩ := h_step
      have h_eval_get : ∀ (x : Schedule (p := p)) (i : ℕ) (h : i < 64),
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
      simp only [AddMod32.circuit, AddMod32.Assumptions, AddMod32.Spec,
        addMod32_assum_iff] at c_wj
      obtain ⟨_, n_wj⟩ := c_wj ⟨n_sig1, by rw [h_eval_get]; exact h_norm_m7,
        n_sig0, by rw [h_eval_get]; exact h_norm_m16⟩
      simp only [AddMod32.elaborated] at n_wj
      intro j hj
      simp only [varSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self]
        rw [show (i₀ + k * 99 + 64 : ℕ) = i₀ + k * 99 + 32 + 32 from by ring]
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
    LowerSigma1.Assumptions, LowerSigma1.Spec,
    LowerSigma0.Assumptions, LowerSigma0.Spec]
    at h_env_i
  -- The goal is also structured this way.
  rw [foldlAcc_eq_varSchedule i₀ input_var i.val hk]
  simp only [scheduleStep, circuit_norm, LowerSigma1.circuit, LowerSigma0.circuit,
    AddMod32.circuit, LowerSigma1.Assumptions,
    LowerSigma0.Assumptions, AddMod32.Assumptions]
  -- Now we need to provide the chain of normalized assumptions.
  -- Extract the chain from h_env_i.
  obtain ⟨e_sig1, e_sig0, -⟩ := h_env_i
  have h_eval_get : ∀ (x : Schedule (p := p)) (i : ℕ) (h : i < 64),
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
  -- Provide: LowerSigma1.Assumptions, LowerSigma0.Assumptions, then the 4-operand assumption.
  refine ⟨?_, ?_, ?_⟩
  · rw [h_eval_get]; exact h_norm_m2
  · rw [h_eval_get]; exact h_norm_m15
  · refine (addMod32_assum_iff env.toEnvironment _ _ _ _).mpr ⟨n_sig1, ?_, n_sig0, ?_⟩
    · rw [h_eval_get]; exact h_norm_m7
    · rw [h_eval_get]; exact h_norm_m16

def circuit : FormalCircuit (F p) SHA256Block SHA256Schedule where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end MessageSchedule
end Gadgets.SHA256
end
