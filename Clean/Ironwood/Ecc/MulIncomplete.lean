import Clean.Halo2.Tactics.ContractBridges
import Clean.Ironwood.Ecc.MulIncompleteRound

/-! The double-and-add loop and bundle over the round gadget (`MulIncompleteRound.lean`). -/

namespace Halo2.Ironwood.Ecc.MulIncomplete

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc (DoubleAndAddRow)
open Halo2.Ironwood.Ecc.Mul (kBits kNat tQNat)
open Halo2.Ironwood.Ecc.Mul.Incomplete.DoubleAndAdd
  (accScalar zRunValue stepPoint accVal lambdaCellsValue rowLambdaValue
   accScalar_two_le accScalar_le pow254_lt_card)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-! ## The double-and-add bundle

`incomplete::Config::<{n+1}>::double_and_add` (`CircuitVersion::AnchoredBase`): the edges —
start copies, the `q_mul_1` boundary, the final `q_mul_3` row — around the `loop` bundle.
Instantiated at `n = 124` (`hi`) and `n = 125` (`lo`), window offset `w`. -/

-- `cellAt`/`cellVec` (naming cells at fixed rows) now live in the framework (`Basic.lean`).

-- contract bridges for the `round` child (opened by the loop's proofs)
derive_contract_bridges roundC (i : ℕ) := round i

/-! ## The loop bundle

The interior rounds (`q_mul_2` rows) as one formal circuit: `n` rounds of the `round`
bundle at consecutive offsets. The entering neighborhood is positional (`Witness`), the
exit neighborhood and the interstitial running sums are the output. The round-to-round
induction lives in this bundle's proofs and nowhere else. -/

structure LoopOut (n : ℕ) (F : Type) where
  -- The last round's output state, consumed positionally by the caller's final `q_mul_3` row.
  exit : State F
  -- The `n` interstitial running sums.
  zs : Vector F n
deriving ProvableStruct

/-- `accScalar` only reads bits below the round count. -/
private theorem accScalar_ext (m : ℕ) (b b' : ℕ → Bool) :
    ∀ r, (∀ j, j < r → b j = b' j) → accScalar m b r = accScalar m b' r := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ v ih =>
    intro h
    show 2 * accScalar m b v + (if b v then 1 else 0) * 2 - 1 = _
    rw [ih (fun j hj => h j (by omega)), h v (by omega)]
    rfl

/-- The loop's row family: the neighborhood state at each round offset. -/
private def rowFam (cfg : Config) (pl : RegionIndex → ℕ) (e : ProverEnvironment Fp)
    (self : RegionIndex) (offset : ℕ) : ℕ → State Fp := fun r =>
  { z := e.advice cfg.z ((pl self + (offset + r) : ℕ) : ℤ),
    xA := e.advice cfg.xA ((pl self + (offset + r + 1) : ℕ) : ℤ),
    lambda1 := e.advice cfg.lambda1 ((pl self + (offset + r + 1) : ℕ) : ℤ),
    lambda2 := e.advice cfg.lambda2 ((pl self + (offset + r + 1) : ℕ) : ℤ),
    base := { x := e.advice cfg.xP ((pl self + (offset + r + 1) : ℕ) : ℤ),
              y := e.advice cfg.yP ((pl self + (offset + r + 1) : ℕ) : ℤ) } }

/-- The loop induction over an abstract row family: `n` constrained steps fold the
accumulator to `accScalar` and propagate the base. -/
private theorem loop_fold {n : ℕ} (st : ℕ → State Fp) (bits : ℕ → Bool)
    (hb : ∀ i : Fin n, (st (i.val + 1)).base = (st i.val).base)
    (hacc : ∀ i : Fin n, ∀ m' : ℕ, (st i.val).base.OnCurve →
      (st i.val).acc = m' • (st i.val).base → 2 ≤ m' → 2 * m' + 1 < PALLAS_SCALAR_CARD →
      (st (i.val + 1)).acc
        = (2 * m' + (if bits i.val then 1 else 0) * 2 - 1) • (st i.val).base)
    (m : ℕ) (hOn : (st 0).base.OnCurve) (hacc0 : (st 0).acc = m • (st 0).base)
    (h2 : 2 ≤ m) (hbudget : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254) :
    (st n).acc = accScalar m bits n • (st 0).base ∧ (st n).base = (st 0).base := by
  suffices hinv : ∀ r, r ≤ n →
      (st r).base = (st 0).base ∧ (st r).acc = accScalar m bits r • (st 0).base by
    obtain ⟨hbase, hacc⟩ := hinv n le_rfl
    exact ⟨hacc, hbase⟩
  intro r hr
  induction r with
  | zero => exact ⟨rfl, hacc0⟩
  | succ v ih =>
    obtain ⟨ihb, iha⟩ := ih (by omega)
    have hv : v < n := by omega
    -- bounds on the accumulated multiplier
    have hMle : accScalar m bits v ≤ 2 ^ v * (m + 1) - 1 := accScalar_le bits v
    have hM2 : 2 ≤ accScalar m bits v := accScalar_two_le h2 bits v
    have hpow : 2 ^ v * (m + 1) ≤ 2 ^ (n + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hMbound : 2 * accScalar m bits v + 1 < PALLAS_SCALAR_CARD := by
      have h254 := pow254_lt_card
      have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
      omega
    have hstep := hacc ⟨v, hv⟩ (accScalar m bits v)
      (by rw [ihb]; exact hOn) (by rw [iha, ihb]) hM2 hMbound
    refine ⟨(hb ⟨v, hv⟩).trans ihb, ?_⟩
    rw [hstep, ihb]
    rfl

def loop (n w : ℕ) : FormalRegionCircuit Fp Config Config (Unconstrained field) (LoopOut n) where
  configure := pure

  synthesize cfg offset (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) := do
    RegionCircuit.forRange' offset 1 n (fun r o => do
      let _ ← (round (w + r)).call cfg o alpha)
    let exit ← readState cfg (offset + n)
    let zs ← cellVec cfg.z (fun j => offset + 1 + j) n
    return { exit, zs }

  Witness := State
  extract cfg offset _ self env := eval env (reads cfg offset self)

  -- `n` constrained double-and-add steps: some bit sequence enters the running sums, and —
  -- for an in-range entering accumulator `[m]·base` — the exit accumulator is
  -- `[accScalar m bits n]·base` over the propagated base.
  Spec _ out ws :=
    ∃ bits : ℕ → Bool,
      zChain ws.z out.zs bits ∧
      ∀ m : ℕ, ws.base.OnCurve → ws.acc = m • ws.base →
        2 ≤ m → 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254 →
        out.exit.acc = accScalar m bits n • ws.base ∧ out.exit.base = ws.base

  -- honest entry: the neighborhood is the honest row for an accumulator multiple with
  -- budget for all `n` rounds.
  ProverAssumptions alpha ws _ :=
    ∃ m : ℕ, ws.Honest m (kBitsWindow alpha 0 w) ∧ 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254

  ProverSpec alpha out ws _ :=
    out.exit = ws.iter (bitsFrom alpha w) n ∧
    ∀ j : Fin n, out.zs[j] = (ws.iter (bitsFrom alpha w) (j.val + 1)).z

  soundness := by
    circuit_proof_start2 [zChain, reads, round, mul_one]
    choose k hk using region_0
    obtain ⟨⟨hez, hexA, hel1, hel2, hebase⟩, hzs⟩ := output_eq
    -- the z column per-index, off the vector output equation
    have h_output_zs : ∀ (j : ℕ) (hj : j < n),
        env.advice cfg.z ((place self + (offset + 1 + j) : ℕ) : ℤ) = output_zs[j] := by
      intro j hj
      rw [← hzs]
      simp [circuit_norm]
    refine ⟨fun j => if h : j < n then k ⟨j, h⟩ else false, ?_, ?_⟩
    · -- the running-sum chain, from the per-round z-steps
      intro j
      rw [show (fun t => if h : t < n then k ⟨t, h⟩ else false) (j : ℕ) = k j from by
        simp [j.isLt]]
      have hz := (hk j).1
      rw [show offset + ↑j + 1 = offset + 1 + ↑j from by omega,
        h_output_zs ↑j j.isLt] at hz
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · rw [dif_pos h0]
        rw [show offset + ↑j = offset from by omega] at hz
        exact hz
      · rw [dif_neg (by omega)]
        rw [show offset + ↑j = offset + 1 + (↑j - 1) from by omega,
          h_output_zs (↑j - 1) (by omega)] at hz
        exact hz
    · -- the accumulator fold
      intro m hOn hacc0 h2m hbudget
      rw [← hez, ← hexA, ← hel1, ← hel2, ← hebase]
      have hfold := loop_fold
        (fun r => { z := env.advice cfg.z ((place self + (offset + r) : ℕ) : ℤ),
                    xA := env.advice cfg.xA ((place self + (offset + r + 1) : ℕ) : ℤ),
                    lambda1 := env.advice cfg.lambda1
                      ((place self + (offset + r + 1) : ℕ) : ℤ),
                    lambda2 := env.advice cfg.lambda2
                      ((place self + (offset + r + 1) : ℕ) : ℤ),
                    base := { x := env.advice cfg.xP
                                ((place self + (offset + r + 1) : ℕ) : ℤ),
                              y := env.advice cfg.yP
                                ((place self + (offset + r + 1) : ℕ) : ℤ) } })
        (fun j => if h : j < n then k ⟨j, h⟩ else false)
        (fun i => by
          have hbp := (hk i).2.1
          beta_reduce
          rw [show offset + (↑i + 1) + 1 = offset + ↑i + 2 from by omega,
            show offset + (↑i + 1) = offset + ↑i + 1 from by omega]
          exact congrArg₂ Point.mk hbp.1 hbp.2 ▸ rfl)
        (fun i => by
          beta_reduce
          rw [dif_pos i.isLt]
          have ha := (hk i).2.2
          rw [show offset + (↑i + 1) + 1 = offset + ↑i + 2 from by omega,
            show offset + (↑i + 1) = offset + ↑i + 1 from by omega]
          exact ha)
        m (by simpa using hOn) (by simpa using hacc0) h2m hbudget
      simpa using hfold
  completeness := by
    circuit_proof_start2 [reads]
    obtain ⟨m, hH0, hbudget⟩ := prover_assumptions
    obtain ⟨⟨hez, hexA, hel1, hel2, hebase⟩, hzs⟩ := output_eq
    -- the z column per-index, off the vector output equation
    have h_output_zs : ∀ (j : ℕ) (hj : j < n),
        env.advice cfg.z ((place self + (offset + 1 + j) : ℕ) : ℤ) = output_zs[j] := by
      intro j hj
      rw [← hzs]
      simp [circuit_norm]
    -- the per-round witness equations, as steps of the row family
    have hsteps : ∀ i : Fin n,
        (rowFam cfg place env self offset) (i.val + 1)
          = ((rowFam cfg place env self offset) i.val).step
            (bitsFrom input w i.val) (bitsFrom input w (i.val + 1)) := by
      intro i
      have hw := region_0 i
      rw [Halo2.SubcircuitRw.FormalRegionCircuit.extendsWitnesses_call] at hw
      simp only [roundC_synthesize_eq, circuit_norm, mul_one, reads, input_eq] at hw
      obtain ⟨hz, hxa, hl1, hl2, hxp, hyp⟩ := hw
      simp only [rowFam, bitsFrom]
      rw [show offset + (↑i + 1) = offset + ↑i + 1 from by omega,
        show offset + ↑i + 1 + 1 = offset + ↑i + 2 from by omega,
        hz, hxa, hl1, hl2, hxp, hyp]
      rfl
    have hIter := iter_of_steps (rowFam cfg place env self offset)
      (bitsFrom input w) hsteps
    have hHall := honest_of_steps (rowFam cfg place env self offset)
      (bitsFrom input w) hsteps m
      (by simp only [rowFam, bitsFrom, Nat.add_zero]; exact hH0) hbudget
    refine ⟨?_, ?_, ?_⟩
    · -- each round's constraints, via the engine leaf and the chained honesty
      intro i
      have hleaf := Halo2.SubcircuitRw.region_completeness_leaf_placed (round (w + ↑i)) cfg
        (offset + ↑i * 1) self (⟨place, env⟩ : Placed ProverEnvironment Fp) input_var
        (region_0 i)
      rw [roundC_envAssumptions_eq, roundC_assumptions_eq, roundC_proverAssumptions_eq,
        roundC_extract_eq] at hleaf
      refine hleaf ⟨trivial, trivial, accScalar m (bitsFrom input w) ↑i, ?_⟩
      have hH := hHall ↑i i.isLt.le
      simp only [rowFam, bitsFrom] at hH
      simp only [reads, mul_one]
      provable_type_simp
      simp only [circuit_norm, input_eq]
      exact hH
    · -- the exit state is the iterated step
      rw [← hez, ← hexA, ← hel1, ← hel2, ← hebase]
      have hn := hIter n le_rfl
      simp only [rowFam] at hn
      simpa using hn
    · -- the interstitial running sums are the iterated z's
      intro j
      rw [← h_output_zs ↑j j.isLt]
      have hj := hIter (↑j + 1) (by omega)
      simp only [rowFam] at hj
      rw [show offset + 1 + ↑j = offset + (↑j + 1) from by omega]
      exact congrArg State.z hj

/-- The loop's output variable: exit neighborhood + interstitial z cells (rfl). -/
@[circuit_norm]
theorem loop_output (n w : ℕ) (cfg : Config) (o : ℕ) (iv : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (self : RegionIndex) :
    (loop n w).output cfg o iv self
      = { exit := reads cfg (o + n) self,
          zs := Vector.ofFn (fun j => AssignedCell.of self (o + 1 + j) cfg.z) } := rfl

/-- What `numBits` constrained double-and-add rounds guarantee: some bit sequence enters the
running sums, and an in-range accumulator `[m]·base` exits as `[accScalar m bits numBits]·base`. -/
def RoundInvariant (numBits : ℕ) (z : Fp) (base acc : Point Fp)
    (output : Output numBits Fp) (bits : ℕ → Bool) : Prop :=
  zChain z output.zs bits ∧
  ∀ m : ℕ, acc = m • base → 2 ≤ m → 2 ^ (numBits + 1) * (m + 1) ≤ 2 ^ 254 →
    output.acc = accScalar m bits numBits • base

/-- Honest witnesses for the init row's slopes (round 0's λ's), from the input cells. -/
def initLambdaWit (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) (base acc : Point (AssignedCell Fp)) (w : ℕ)
    (f : Halo2.Ironwood.Ecc.Mul.Incomplete.DoubleAndAdd.LambdaCells Fp → Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[f (lambdaCellsValue (readCell env base.x) (readCell env base.y)
    (readCell env acc.x) (readCell env acc.y) (bitWit alpha w env))]

@[circuit_norm]
theorem initLambdaWit_eval (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) (base acc : Point (AssignedCell Fp))
    (w : ℕ) (f : Halo2.Ironwood.Ecc.Mul.Incomplete.DoubleAndAdd.LambdaCells Fp → Fp)
    (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((initLambdaWit alpha base acc w f).eval env)[j]
      = f (lambdaCellsValue (readCell env base.x) (readCell env base.y)
          (readCell env acc.x) (readCell env acc.y) (bitWit alpha w env)) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [initLambdaWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

def double_and_add (n : ℕ) (w : ℕ) :
    FormalRegionCircuit Fp
      (Column .advice × Column .advice × Column .advice × Column .advice ×
        Column .advice × Column .advice)
      Config Inputs (Output (n + 1)) where
  configure := fun (z, xA, xP, yP, lambda1, lambda2) =>
    configure z xA xP yP lambda1 lambda2

  synthesize cfg offset (input : Var Inputs Fp) := do
    -- start copies (Rust execution order), materializing round 0's neighborhood
    let _z ← copyAdvice input.z cfg.z offset
    let _xA ← copyAdvice input.acc.x cfg.xA (offset + 1)
    let _yA ← copyAdvice input.acc.y cfg.lambda1 offset
    let _xP ← copyAdvice input.base.x cfg.xP (offset + 1)
    let _yP ← copyAdvice input.base.y cfg.yP (offset + 1)
    let _l1 ← assignAdvice cfg.lambda1 (offset + 1)
      (initLambdaWit input.alpha input.base input.acc w (·.lambda1))
    let _l2 ← assignAdvice cfg.lambda2 (offset + 1)
      (initLambdaWit input.alpha input.base input.acc w (·.lambda2))
    (qMul1Gate cfg).enable offset
    -- the interior rounds
    let _lp ← (loop n w).call cfg offset input.alpha
    -- the final `q_mul_3` round on the exit neighborhood
    let ex ← readState cfg (offset + n)
    (qMul3Gate cfg).enable (offset + n + 1)
    let _zl ← assignAdvice cfg.z (offset + n + 1) (stepWit input.alpha ex (w + n) (·.z))
    let _xf ← assignAdvice cfg.xA (offset + n + 2) (stepWit input.alpha ex (w + n) (·.xA))
    let yf ← assignAdvice cfg.lambda1 (offset + n + 2) (readWit ex State.stepY)
    let xf ← cellAt cfg.xA (offset + n + 2)
    let zs ← cellVec cfg.z (fun j => offset + 1 + j) (n + 1)
    return { acc := { x := xf, y := yf }, zs }

  -- base is a non-identity on-curve point (Rust exceptional-case check).
  Assumptions input := (show Point Fp from input.base).OnCurve

  Spec input output _ :=
    ∃ bits : ℕ → Bool,
      RoundInvariant (n + 1) input.z input.base input.acc output bits

  -- honest-prover precondition: the accumulator is a small positive multiple of the base
  -- in the exceptional-case-free range.
  ProverAssumptions input _ _ :=
    (show Point Fp from input.base).OnCurve ∧ ∃ m : ℕ,
      (show Point Fp from input.acc) = m • (show Point Fp from input.base) ∧ 2 ≤ m ∧
      2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254

  -- honest bits are derived from the scalar cell.
  ProverSpec input output _ _ :=
    RoundInvariant (n + 1) input.z input.base input.acc output (bitsFrom input.alpha w)

  soundness := by
    circuit_proof_start2 [qMul1Gate, qMul3Gate, forLoopPolys, yA, xRExpr, reads, RoundInvariant,
      loop]
    obtain ⟨⟨hax, hay⟩, hzs⟩ := output_eq
    -- the z column per-index, off the vector output equation
    have h_output_zs : ∀ (j : ℕ) (hj : j < n + 1),
        env.advice cfg.z ((place self + (offset + 1 + j) : ℕ) : ℤ) = output_zs[j] := by
      intro j hj
      rw [← hzs]
      simp [circuit_norm]
    -- re-concretize the loop witness: this proof's fold helpers speak the advice rows
    simp only [← wit_lp_eq] at lp_spec
    obtain ⟨bits, hchain, hfold⟩ := lp_spec
    obtain ⟨hb3, hg13, hs3, hg23⟩ := region_6
    obtain ⟨kl, hzl, hstepl⟩ := sound_last_step hb3 hg13 hs3 hg23
    refine ⟨fun j => if j < n then bits j else kl, ?_, ?_⟩
    · -- the running-sum chain
      intro j
      simp only [Fin.getElem_fin]
      rcases Nat.lt_or_ge j.val n with hjn | hjn
      · have hcj := hchain ⟨j.val, hjn⟩
        simp only [circuit_norm] at hcj
        rw [h_output_zs j.val (by omega)] at hcj
        simp only [show (fun t => if t < n then bits t else kl) (j.val : ℕ) = bits j.val from by
          simp [hjn]]
        rcases Nat.eq_zero_or_pos j.val with h0 | hpos
        · rw [dif_pos h0]
          rw [dif_pos h0, region_0] at hcj
          exact hcj
        · rw [dif_neg (by omega)]
          rw [dif_neg (by omega), h_output_zs (j.val - 1) (by omega)] at hcj
          exact hcj
      · -- the last round
        have hjeq : j.val = n := by omega
        have hz' := hzl
        rw [show offset + n + 1 = offset + 1 + n from by omega,
          h_output_zs n (by omega)] at hz'
        simp only [hjeq]
        rw [if_neg (show ¬ n < n by omega)]
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          rw [dif_pos rfl]
          simp only [Nat.add_zero] at hz'
          rw [region_0] at hz'
          exact hz'
        · rw [dif_neg (by omega)]
          rw [show offset + n = offset + 1 + (n - 1) from by omega,
            h_output_zs (n - 1) (by omega)] at hz'
          exact hz'
    · -- the accumulator
      intro m hacc h2m hbudget
      have hbOn : ({ x := input_base_x, y := input_base_y } : Point Fp).OnCurve := assumptions
      have hentry := hfold m
        (by rw [region_3, region_4]; exact hbOn)
        (by
          simp only [State.acc, State.yA2, State.xR]
          have hy : (env.advice cfg.lambda1 ((place self + (offset + 1) : ℕ) : ℤ)
                + env.advice cfg.lambda2 ((place self + (offset + 1) : ℕ) : ℤ))
              * (env.advice cfg.xA ((place self + (offset + 1) : ℕ) : ℤ)
                - (env.advice cfg.lambda1 ((place self + (offset + 1) : ℕ) : ℤ)
                    * env.advice cfg.lambda1 ((place self + (offset + 1) : ℕ) : ℤ)
                  - env.advice cfg.xA ((place self + (offset + 1) : ℕ) : ℤ)
                  - env.advice cfg.xP ((place self + (offset + 1) : ℕ) : ℤ)))
              * (2 : Fp)⁻¹ = input_acc_y := by
            linear_combination region_2 - region_5
          rw [hy, region_1, region_3, region_4]
          exact hacc)
        h2m hbudget
      obtain ⟨hexit_acc, hexit_base⟩ := hentry
      simp only [State.acc, State.yA2, State.xR] at hexit_acc
      rw [region_3, region_4] at hexit_acc
      have h2n : 2 ≤ accScalar m bits n := accScalar_two_le h2m bits n
      have hMle : accScalar m bits n ≤ 2 ^ n * (m + 1) - 1 := accScalar_le bits n
      have hp : 2 ^ n * (m + 1) ≤ 2 ^ (n + 1) * (m + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hMb : 2 * accScalar m bits n + 1 < PALLAS_SCALAR_CARD := by
        have h254 := pow254_lt_card
        have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
        omega
      simp only [Halo2.Ironwood.Point.mk.injEq] at hexit_base
      obtain ⟨hbx, hby⟩ := hexit_base
      rw [region_3] at hbx
      rw [region_4] at hby
      rw [hbx] at hexit_acc
      have hlast := hstepl (accScalar m bits n)
        (by rw [hbx, hby]; exact hbOn)
        (by rw [hbx, hby]; exact hexit_acc)
        h2n hMb
      rw [hbx, hby] at hlast
      rw [hlast]
      congr 1
      have hext : accScalar m (fun j => if j < n then bits j else kl) n
          = accScalar m bits n :=
        accScalar_ext m _ bits n (fun j hj => by simp [hj])
      symm
      show accScalar m (fun j => if j < n then bits j else kl) (n + 1) = _
      show 2 * accScalar m (fun j => if j < n then bits j else kl) n
          + (if (if n < n then bits n else kl) then 1 else 0) * 2 - 1 = _
      rw [hext, if_neg (show ¬ n < n by omega)]

  completeness := by
    circuit_proof_start2 [qMul1Gate, qMul3Gate, forLoopPolys, yA, xRExpr, reads, RoundInvariant,
      loop]
    obtain ⟨hbOn, m, haccm, h2m, hbudget⟩ := prover_assumptions
    obtain ⟨hia, ⟨hibx, hiby⟩, ⟨hiax, hiay⟩, hiz⟩ := input_eq
    obtain ⟨-, hzs⟩ := output_eq
    -- the z column per-index, off the vector output equation
    have h_output_zs : ∀ (j : ℕ) (hj : j < n + 1),
        env.advice cfg.z ((place self + (offset + 1 + j) : ℕ) : ℤ) = output_zs[j] := by
      intro j hj
      rw [← hzs]
      simp [circuit_norm]
    -- the init λ witnesses, over the honest multiple's coordinates
    have hacx : input_acc_x = (m • Point.mk input_base_x input_base_y).x :=
      congrArg Point.x haccm
    have hacy : input_acc_y = (m • Point.mk input_base_x input_base_y).y :=
      congrArg Point.y haccm
    simp only [readCell, circuit_norm, hibx, hiby, hiax, hiay] at region_5 region_6
    have hl1m := region_5
    have hl2m := region_6
    rw [hacx, hacy] at hl1m hl2m
    -- the entering neighborhood is the honest row for `[m]·base`
    have hH0 : (State.mk (env.advice cfg.z ((place self + offset : ℕ) : ℤ))
        (env.advice cfg.xA ((place self + (offset + 1) : ℕ) : ℤ))
        (env.advice cfg.lambda1 ((place self + (offset + 1) : ℕ) : ℤ))
        (env.advice cfg.lambda2 ((place self + (offset + 1) : ℕ) : ℤ))
        (Point.mk (env.advice cfg.xP ((place self + (offset + 1) : ℕ) : ℤ))
          (env.advice cfg.yP ((place self + (offset + 1) : ℕ) : ℤ)))).Honest
        m (kBitsWindow input_alpha 0 w) := by
      have h4 : 2 ^ 2 * (m + 1) ≤ 2 ^ (n + 2) * (m + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h254 := pow254_lt_card
      refine ⟨?_, h2m, by omega, ?_, ?_, ?_⟩
      · show (Point.mk _ _).OnCurve
        rw [region_3, region_4]
        exact hbOn
      · show env.advice cfg.xA _ = _
        rw [region_1, region_3, region_4]
        exact hacx
      · show env.advice cfg.lambda1 _ = _
        rw [region_3, region_4]
        exact hl1m
      · show env.advice cfg.lambda2 _ = _
        rw [region_3, region_4]
        exact hl2m
    -- re-concretize the loop-witness contract: this proof's helpers speak advice rows
    simp only [← wit_lp_eq] at h_spec_0
    obtain ⟨hSpec, hPS1, hPS2⟩ := h_spec_0 ⟨m, hH0, hbudget⟩
    -- step/iter value shapes (definitional)
    have hstepz : ∀ (s : State Fp) (k k' : Bool),
        (s.step k k').z = 2 * s.z + (if k then 1 else 0) := fun _ _ _ => rfl
    have hiterz : ∀ (s : State Fp) (bf : ℕ → Bool) (r : ℕ),
        (s.iter bf (r + 1)).z = 2 * (s.iter bf r).z + (if bf r then 1 else 0) :=
      fun _ _ _ => rfl
    -- honesty chains to every round, including the exit row
    have hHiter := honest_of_steps
      (fun r => (State.mk (env.advice cfg.z ((place self + offset : ℕ) : ℤ))
        (env.advice cfg.xA ((place self + (offset + 1) : ℕ) : ℤ))
        (env.advice cfg.lambda1 ((place self + (offset + 1) : ℕ) : ℤ))
        (env.advice cfg.lambda2 ((place self + (offset + 1) : ℕ) : ℤ))
        (Point.mk (env.advice cfg.xP ((place self + (offset + 1) : ℕ) : ℤ))
          (env.advice cfg.yP ((place self + (offset + 1) : ℕ) : ℤ)))).iter
        (bitsFrom input_alpha w) r)
      (bitsFrom input_alpha w) (fun i => rfl) m
      (by simpa [bitsFrom] using hH0) hbudget
    have hHn := hHiter n le_rfl
    beta_reduce at hHn
    rw [← hPS1] at hHn
    simp only [bitsFrom] at hHn
    -- the final row's gate identities, from exit-row honesty
    have hlg := last_gates (k' := kBitsWindow input_alpha 0 (w + n + 1)) hHn
    -- the per-round chain over the raw cells, in `bitsFrom` form
    have hcell : ∀ j : Fin n,
        env.advice cfg.z ((place self + (offset + 1 + j.val) : ℕ) : ℤ)
          = 2 * (if h : j.val = 0
              then env.advice cfg.z ((place self + offset : ℕ) : ℤ)
              else env.advice cfg.z ((place self + (offset + 1 + (j.val - 1)) : ℕ) : ℤ))
            + (if bitsFrom input_alpha w j.val then 1 else 0) := by
      intro j
      rw [hPS2 j, hiterz]
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · rw [dif_pos h0, h0]
        rfl
      · rw [dif_neg (by omega)]
        have hprev := hPS2 ⟨j.val - 1, by omega⟩
        rw [show j.val - 1 + 1 = j.val from by omega] at hprev
        rw [hprev]
    -- the running-sum chain of the bundle's output
    have hzc : zChain input_z output_zs (bitsFrom input_alpha w) := by
      intro j
      simp only [Fin.getElem_fin]
      rcases Nat.lt_or_ge j.val n with hjn | hjn
      · have hc := hcell ⟨j.val, hjn⟩
        rw [h_output_zs j.val (by omega)] at hc
        rcases Nat.eq_zero_or_pos j.val with h0 | hpos
        · rw [dif_pos h0]
          rw [dif_pos h0, region_0] at hc
          exact hc
        · rw [dif_neg (show ¬ j.val = 0 by omega)]
          rw [dif_neg (show ¬ j.val = 0 by omega), h_output_zs (j.val - 1) (by omega)] at hc
          exact hc
      · have hjeq : j.val = n := by omega
        have hz' := region_7
        rw [hstepz, show offset + n + 1 = offset + 1 + n from by omega,
          h_output_zs n (by omega)] at hz'
        simp only [hjeq]
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          rw [dif_pos rfl]
          simp only [Nat.add_zero] at hz'
          rw [region_0] at hz'
          exact hz'
        · rw [dif_neg (show ¬ n = 0 by omega)]
          rw [show offset + n = offset + 1 + (n - 1) from by omega,
            h_output_zs (n - 1) (by omega)] at hz'
          exact hz'
    -- the init row in value form is also honest, giving the witnessed y_a's identity
    have hHV : (State.mk input_z input_acc_x
        ((lambdaCellsValue input_base_x input_base_y input_acc_x input_acc_y
          (kBitsWindow input_alpha 0 w)).lambda1)
        ((lambdaCellsValue input_base_x input_base_y input_acc_x input_acc_y
          (kBitsWindow input_alpha 0 w)).lambda2)
        (Point.mk input_base_x input_base_y)).Honest m (kBitsWindow input_alpha 0 w) := by
      have h4 : 2 ^ 2 * (m + 1) ≤ 2 ^ (n + 2) * (m + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h254 := pow254_lt_card
      refine ⟨hbOn, h2m, by omega, hacx, ?_, ?_⟩
      · show (lambdaCellsValue _ _ _ _ _).lambda1 = _
        rw [hacx, hacy]
      · show (lambdaCellsValue _ _ _ _ _).lambda2 = _
        rw [hacx, hacy]
    have hyv := honest_yA2 hHV
    simp only [State.yA2, State.xR] at hyv
    rw [← hacy] at hyv
    have h2 : (2 : Fp) ≠ 0 := by decide
    have hyv2 := congrArg (· * (2 : Fp)⁻¹) hyv
    beta_reduce at hyv2
    rw [show (2 : Fp) * input_acc_y * (2 : Fp)⁻¹ = input_acc_y from by
      rw [mul_comm (2 : Fp) input_acc_y, mul_assoc, mul_inv_cancel₀ h2, mul_one]] at hyv2
    -- the final row's cells are `w.step`/`stepY` values (`last_gates`' spelling)
    simp only [region_7, region_8, region_9]
    refine ⟨⟨region_0, region_1, region_2, region_3, region_4, ?_, ⟨m, ?_, hbudget⟩,
      hlg.1, hlg.2.1, hlg.2.2.1, hlg.2.2.2⟩, hzc, ?_⟩
    · -- the `q_mul_1` boundary: the witnessed init y_a is the accumulator's y
      simp only [region_1, region_2, region_3, region_5, region_6]
      linear_combination -hyv2
    · -- the loop's honest entry (the obligation speaks the minted witness atom)
      exact wit_lp_eq ▸ hH0
    · -- the accumulator fold, for any in-range multiple entering the region:
      -- replay the constraints (loop spec + final-row identities), which hold
      -- for the honest witness and quantify over every multiple
      intro m' hacc' h2' hbud'
      obtain ⟨bits', hchain', hfold'⟩ := hSpec
      have hexit := hfold' m'
        (by show (Point.mk _ _).OnCurve
            rw [region_3, region_4]
            exact hbOn)
        (by simp only [State.acc, State.yA2, State.xR]
            rw [region_1, region_3, region_4, region_5, region_6, hyv2]
            exact hacc')
        h2' hbud'
      simp only [Halo2.Ironwood.Point.mk.injEq] at hexit
      obtain ⟨hexAcc, hbpx, hbpy⟩ := hexit
      have hbx := hbpx.trans region_3
      have hby := hbpy.trans region_4
      -- the loop's bit sequence is the honest one below `n`
      have hbits : ∀ j : Fin n, bits' j.val = bitsFrom input_alpha w j.val := by
        intro j
        have e1 := hchain' j
        simp only [circuit_norm] at e1
        have e2 := hcell j
        have hif : (if bits' j.val then (1 : Fp) else 0)
            = if bitsFrom input_alpha w j.val then 1 else 0 := by
          linear_combination e2 - e1
        rcases hb1 : bits' j.val <;> rcases hb2 : bitsFrom input_alpha w j.val
        · rfl
        · rw [hb1, hb2] at hif
          simp at hif
        · rw [hb1, hb2] at hif
          simp at hif
        · rfl
      rw [accScalar_ext m' bits' _ n (fun j hj => hbits ⟨j, hj⟩)] at hexAcc
      -- the final row's step, from its constraints
      obtain ⟨kl, hklz, hstepl⟩ := sound_last_step hlg.1 hlg.2.1 hlg.2.2.1 hlg.2.2.2
      have hkl : kl = kBitsWindow input_alpha 0 (w + n) := by
        have h1 := hklz
        rw [hstepz] at h1
        have hif : (if kl then (1 : Fp) else 0)
            = if kBitsWindow input_alpha 0 (w + n) then 1 else 0 := by
          linear_combination -h1
        rcases hb1 : kl <;> rcases hb2 : kBitsWindow input_alpha 0 (w + n)
        · rfl
        · rw [hb1, hb2] at hif
          simp at hif
        · rw [hb1, hb2] at hif
          simp at hif
        · rfl
      have hM2 : 2 ≤ accScalar m' (bitsFrom input_alpha w) n := accScalar_two_le h2' _ n
      have hMle := accScalar_le (m := m') (bitsFrom input_alpha w) n
      have hp : 2 ^ n * (m' + 1) ≤ 2 ^ (n + 1) * (m' + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hMb : 2 * accScalar m' (bitsFrom input_alpha w) n + 1 < PALLAS_SCALAR_CARD := by
        have h254 := pow254_lt_card
        have hsplit : 2 ^ (n + 2) * (m' + 1) = 2 * (2 ^ (n + 1) * (m' + 1)) := by ring
        omega
      simp only [State.acc, State.yA2, State.xR] at hexAcc
      rw [← hbpx, ← hbpy] at hexAcc
      have hlast := hstepl (accScalar m' (bitsFrom input_alpha w) n)
        (by show (Point.mk _ _).OnCurve
            rw [hbx, hby]
            exact hbOn)
        hexAcc hM2 hMb
      rw [hkl, hbx, hby] at hlast
      rw [hbx, hby]
      exact hlast

end Halo2.Ironwood.Ecc.MulIncomplete
