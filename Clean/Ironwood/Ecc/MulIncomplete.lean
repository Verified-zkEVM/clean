import Clean.Ironwood.Ecc.MulIncompleteRound

/-! The double-and-add loop and bundle over the round gadget (`MulIncompleteRound.lean`). -/

namespace Halo2.Ironwood.Ecc.MulIncomplete

open Orchard (Point)
open Orchard.Ecc (DoubleAndAddRow)
open Orchard.Ecc.Mul (kBits kNat tQNat)
open Orchard.Ecc.Mul.Incomplete.DoubleAndAdd
  (accScalar zRunValue stepPoint accVal lambdaCellsValue rowLambdaValue
   accScalar_two_le accScalar_le pow254_lt_card)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-! ## The per-bit round loop

One round per scalar bit (`RegionCircuit.forRange'`), addressing cells by *absolute* region-local
rows, so the rounds are independent of each other.

Row layout (relative to the ambient `offset`):
- row `offset`      : starting `z` copy (`z` col) and starting `y_a` copy (`λ₁` col).
- row `offset + 1`  : starting `x_a` copy (`x_a` col); loop row 0 begins here.
- loop row `r` (`0 ≤ r ≤ n`) at `offset + 1 + r`: assign `z, x_p, y_p, λ₁, λ₂` and next-row `x_a`.
- row `offset + 1 + (n + 1)` : the witnessed final `y_a` (`λ₁` col).

Selectors: `q_mul_1` at `offset`; `q_mul_2` at `offset + 1 .. offset + n`; `q_mul_3` at
`offset + 1 + n`. -/

/-- One double-and-add round at loop index `r`. Assigns the five per-row cells and the next-row
`x_a`, and enables the round's selector (`q_mul_2` interior, `q_mul_3` last). On the first loop row
(`r = 0`) `x_p`/`y_p` are copied from `base` (`CircuitVersion::AnchoredBase`); `q_mul_2` constancy
propagates the anchor. Absolute rows make each round independent of the others. -/
def roundOld (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (offset n r : ℕ) : RegionCircuit Fp Unit := do
  let row := offset + 1 + r
  let _z ← assignAdvice cfg.z row (zWit input ebits r)
  -- x_p / y_p: anchored copy of `base` on the first loop row, plain assignment otherwise
  if r = 0 then
    let _xP ← copyAdvice input.base.x cfg.xP row
    let _yP ← copyAdvice input.base.y cfg.yP row
  else
    let _xP ← assignAdvice cfg.xP row (.ofFExpr (.expr input.base.x))
    let _yP ← assignAdvice cfg.yP row (.ofFExpr (.expr input.base.y))
  let _l1 ← assignAdvice cfg.lambda1 row (l1Wit input ebits r)
  let _l2 ← assignAdvice cfg.lambda2 row (l2Wit input ebits r)
  let _xANext ← assignAdvice cfg.xA (row + 1) (xANextWit input ebits r)
  -- the round's selector: q_mul_2 on interior rows, q_mul_3 on the last
  if r = n then
    (qMul3Gate cfg).enable row
  else
    (qMul2Gate cfg).enable row

/-- The double-and-add loop: `numRounds` independent rounds, round `r` at row `offset + 1 + r`. -/
def loop (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint) (offset n numRounds : ℕ) :
    RegionCircuit Fp Unit :=
  RegionCircuit.forRange' (offset + 1) 1 numRounds
    (fun r _row => roundOld cfg input ebits offset n r)

/-- Read the assigned cell at a known region-local row/column (no op emitted), so `synthesize` can
name the output cells that live at fixed rows rather than being threaded through the loop. -/
def cellAt (col : Column .advice) (row : ℕ) : RegionCircuit Fp (AssignedCell Fp) :=
  fun self => (.of self row col, [])

@[circuit_norm]
theorem operations_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).operations self = [] := rfl

@[circuit_norm]
theorem output_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).output self = .of self row col := rfl

/-- Name a vector of cells at fixed region-local rows (no op emitted) — the vector-valued analogue
of `cellAt`, for the `Output.zs` running-sum cells. Returns `Vector.ofFn` so its `output` is `rfl`. -/
def cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) :
    RegionCircuit Fp (Vector (AssignedCell Fp) len) :=
  fun self => (Vector.ofFn (fun i => AssignedCell.of self (rows i) col), [])

@[circuit_norm]
theorem operations_cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) (self : RegionIndex) :
    (cellVec col rows len).operations self = [] := rfl

@[circuit_norm]
theorem output_cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) (self : RegionIndex) :
    (cellVec col rows len).output self
      = Vector.ofFn (fun i => AssignedCell.of self (rows i) col) := rfl

/-! ## Loop-shaped standalone lemmas

The z-chain and accumulator invariants, extracted per round from the framework
`forRange'_constraints` / `forRange'_extendsWitnesses` split and folded by a value induction over
rounds. Once the per-row row facts are cleaned, the chain induction is exactly the donor's
`soundness_aux`/`accVal_eq_nsmul` (imported). The region packs six cells per loop row
(`z, x_p, y_p, λ₁, λ₂, x_a'`) after three starting-copy rows, read via the `adv` accessor below. -/

/-- Env reader: advice value of column `col` at region-local row `row` in region `self`. -/
def adv (cfg_col : Column .advice) (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment Fp) (row : ℕ) : Fp :=
  env.advice cfg_col ((place self + row : ℕ) : ℤ)

section LoopFacts

variable (cfg : Config) (input : Inputs (AssignedCell Fp))
  (ebits : Placed ProverEnvironment Fp → BitsHint)
  (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset : ℕ)

/-- The per-row cell readers, as abbreviations over `adv` at the round's absolute row. -/
private def XAr (r : ℕ) : Fp := adv cfg.xA place self env (offset + 1 + r)
private def XPr (r : ℕ) : Fp := adv cfg.xP place self env (offset + 1 + r)
private def YPr (r : ℕ) : Fp := adv cfg.yP place self env (offset + 1 + r)
private def L1r (r : ℕ) : Fp := adv cfg.lambda1 place self env (offset + 1 + r)
private def L2r (r : ℕ) : Fp := adv cfg.lambda2 place self env (offset + 1 + r)
/-- The `z` running-sum reader at the round's row, and its predecessor (the `z` cell one
row earlier: for `r = 0` the start-copy at `offset`, otherwise the previous round's `z`). -/
private def Zr (r : ℕ) : Fp := adv cfg.z place self env (offset + 1 + r)
private def Zpr (r : ℕ) : Fp := adv cfg.z place self env (offset + r)
/-- The bit read off the running sum at round `r`: `k_r = z_r − 2·z_{r−1}`. -/
private def Kr (r : ℕ) : Fp := Zr cfg place self env offset r - Zpr cfg place self env offset r * 2
/-- The derived `Y_A` of row `r` (`(λ₁+λ₂)(x_A − x_R)`); at `r = n+1` we instead read the
witnessed doubled final `y` from the `λ₁` column at `offset+1+(n+1)`. -/
private def YADr (n r : ℕ) : Fp :=
  if r = n + 1 then 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1))
  else (L1r cfg place self env offset r + L2r cfg place self env offset r) *
    (XAr cfg place self env offset r -
      (L1r cfg place self env offset r * L1r cfg place self env offset r
        - XAr cfg place self env offset r - XPr cfg place self env offset r))

-- TODO this kind of stuff could be handled in a cleaner way by defining a circuit bundle for `round` (the loop body)
/-- **Cleaned per-round gate facts.** From the loop's `Constraints`, each round `r ≤ n` yields the
four `forLoopPolys` facts (booleanity, gradient_1, secant_line, gradient_2), plus the `x_p`/`y_p`
constancy on interior rounds (`r ≠ n`). -/
private theorem loop_gate_facts (n : ℕ)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    ∀ r, r < n + 1 →
      -- booleanity of the bit
      (IsBool (Kr cfg place self env offset r)) ∧
      -- gradient_1 (×2 form)
      (2 * L1r cfg place self env offset r *
          (XAr cfg place self env offset r - XPr cfg place self env offset r)
        + 2 * ((Kr cfg place self env offset r * 2 - 1) * YPr cfg place self env offset r)
        = YADr cfg place self env offset n r) ∧
      -- secant_line
      (L2r cfg place self env offset r * L2r cfg place self env offset r
        = XAr cfg place self env offset (r + 1)
          + (L1r cfg place self env offset r * L1r cfg place self env offset r
              - XAr cfg place self env offset r - XPr cfg place self env offset r)
          + XAr cfg place self env offset r) ∧
      -- gradient_2
      (2 * L2r cfg place self env offset r *
          (XAr cfg place self env offset r - XAr cfg place self env offset (r + 1))
        = YADr cfg place self env offset n r + YADr cfg place self env offset n (r + 1)) ∧
      -- x_p / y_p constancy on interior rounds
      (r ≠ n → XPr cfg place self env offset r = XPr cfg place self env offset (r + 1)
        ∧ YPr cfg place self env offset r = YPr cfg place self env offset (r + 1)) := by
  -- the framework split: `Constraints (loop) ↔ ∀ r : Fin (n+1), <round r's constraints>`
  simp only [loop, circuit_norm, roundOld] at hLoop
  intro r hr
  have hrle : r ≤ n := by omega
  -- round `r`'s own constraints (the `forRange'` body ignores its base-row arg; `round` recomputes)
  have hRound := hLoop ⟨r, hr⟩
  -- `2 ≠ 0` clears the `TWO_INV = 2⁻¹` in the VK-faithful `y_a`.
  have h2 : (2 : Fp) ≠ 0 := by decide
  -- YADr at `r` is always the derived form (since `r ≤ n < n+1`)
  have hYADr : YADr cfg place self env offset n r
      = (L1r cfg place self env offset r + L2r cfg place self env offset r) *
        (XAr cfg place self env offset r -
          (L1r cfg place self env offset r * L1r cfg place self env offset r
            - XAr cfg place self env offset r - XPr cfg place self env offset r)) := by
    rw [YADr, if_neg (by omega)]
  -- YADr at `r+1`: derived when `r ≠ n`, the witnessed doubled final `y` when `r = n`.
  have hYADr1n : YADr cfg place self env offset n (n + 1)
      = 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1)) := by rw [YADr, if_pos rfl]
  have hYADr1i : r ≠ n → YADr cfg place self env offset n (r + 1)
      = (L1r cfg place self env offset (r + 1) + L2r cfg place self env offset (r + 1)) *
        (XAr cfg place self env offset (r + 1) -
          (L1r cfg place self env offset (r + 1) * L1r cfg place self env offset (r + 1)
            - XAr cfg place self env offset (r + 1) - XPr cfg place self env offset (r + 1))) :=
    fun h => by rw [YADr, if_neg (by omega)]
  simp only [XAr, XPr, YPr, L1r, L2r, Zr, Zpr, Kr, adv] at hYADr hYADr1n hYADr1i ⊢
  -- split on `r = 0` (anchored copy) first
  by_cases hr0 : r = 0
  · -- first loop row: `x_p`/`y_p` are copies of `base`
    subst hr0
    by_cases hrn : (0 : ℕ) = n
    · -- single-round circuit: `q_mul_3` on row 0
      subst hrn
      rw [hYADr, hYADr1n]
      simp only [circuit_norm, qMul3Gate, forLoopPolys, yA, xRExpr] at hRound
      obtain ⟨_hxpc, _hypc, hbool, hg1, hsec, hg2⟩ := hRound
      refine ⟨?_, ?_, ?_, ?_, by intro h; exact absurd rfl h⟩
      · rcases mul_eq_zero.mp hbool with h | h
        · exact Or.inl (by linear_combination h)
        -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
        · exact Or.inr (by linear_combination -h)
      · linear_combination (norm := (field_simp; ring_nf)) 2 * hg1
      · linear_combination hsec
      · linear_combination (norm := (field_simp; ring)) 2 * hg2
    · -- interior first row: `q_mul_2` on row 0
      rw [hYADr, hYADr1i hrn]
      simp only [circuit_norm, qMul2Gate, forLoopPolys, yA, xRExpr,
        if_neg hrn] at hRound
      obtain ⟨_hxpc, _hypc, hxpk, hypk, hbool, hg1, hsec, hg2⟩ := hRound
      refine ⟨?_, ?_, ?_, ?_,
        fun _ => ⟨by linear_combination hxpk, by linear_combination hypk⟩⟩
      · rcases mul_eq_zero.mp hbool with h | h
        · exact Or.inl (by linear_combination h)
        -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
        · exact Or.inr (by linear_combination -h)
      · linear_combination (norm := (field_simp; ring_nf)) 2 * hg1
      · linear_combination hsec
      · linear_combination (norm := (field_simp; ring)) 2 * hg2
  · -- non-first loop row: `x_p`/`y_p` are plain assignments
    by_cases hrn : r = n
    · -- last round: `q_mul_3`
      subst hrn
      rw [hYADr, hYADr1n]
      simp only [circuit_norm, qMul3Gate, forLoopPolys, yA, xRExpr,
        if_neg hr0] at hRound
      obtain ⟨hbool, hg1, hsec, hg2⟩ := hRound
      refine ⟨?_, ?_, ?_, ?_, by intro h; exact absurd rfl h⟩
      · rcases mul_eq_zero.mp hbool with h | h
        · exact Or.inl (by linear_combination h)
        -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
        · exact Or.inr (by linear_combination -h)
      · linear_combination (norm := (field_simp; ring)) 2 * hg1
      · linear_combination hsec
      · linear_combination (norm := (field_simp; ring_nf)) 2 * hg2
    · -- interior round: `q_mul_2`
      rw [hYADr, hYADr1i hrn]
      simp only [circuit_norm, qMul2Gate, forLoopPolys, yA, xRExpr,
        if_neg hr0, if_neg hrn] at hRound
      obtain ⟨hxpk, hypk, hbool, hg1, hsec, hg2⟩ := hRound
      refine ⟨?_, ?_, ?_, ?_,
        fun _ => ⟨by linear_combination hxpk, by linear_combination hypk⟩⟩
      · rcases mul_eq_zero.mp hbool with h | h
        · exact Or.inl (by linear_combination h)
        -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
        · exact Or.inr (by linear_combination -h)
      · linear_combination (norm := (field_simp; ring)) 2 * hg1
      · linear_combination hsec
      · linear_combination (norm := (field_simp; ring_nf)) 2 * hg2

/-- **Round-0 anchor copies.** Round 0 copies `x_p`/`y_p` at `offset + 1` from the base point
(`CircuitVersion::AnchoredBase`), so the loop's `Constraints` pin them to `base.x`/`base.y`. -/
private theorem loop_anchor (n : ℕ)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    adv cfg.xP place self env (offset + 1) = input.base.x.eval place env ∧
    adv cfg.yP place self env (offset + 1) = input.base.y.eval place env := by
  simp only [loop, circuit_norm] at hLoop
  have hRound := hLoop ⟨0, by omega⟩
  simp only [roundOld, circuit_norm, adv] at hRound ⊢
  exact ⟨hRound.1, hRound.2.1⟩

end LoopFacts

/-- **Accumulator soundness.** If the loop constraints hold, `P` is on-curve, and the starting
accumulator reads `[m]P` (with `m` in the exceptional-case-free range), then after `n + 1` rounds
the final `x_a`/`y_a` cells give `[accScalar m bits' (n+1)] • P`, for the constraint-forced bit
sequence `bits'`. Routes the cleaned round facts into the donor's `soundness_aux`; independent of
the witness bit family `ebits`. -/
theorem loop_acc_sound (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint) (bits' : BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset n : ℕ)
    (P : Point Fp) (hP : P.OnCurve)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (hxA0 : adv cfg.xA place self env (offset + 1) = (m • P).x)
    (hyA0 : adv cfg.lambda1 place self env offset = (m • P).y)
    (hxPBase : adv cfg.xP place self env (offset + 1) = P.x)
    (hyPBase : adv cfg.yP place self env (offset + 1) = P.y)
    (hbit : ∀ r, r ≤ n →
      adv cfg.z place self env (offset + 1 + r) - adv cfg.z place self env (offset + r) * 2
        = (if bits' r then 1 else 0))
    -- the `q_mul_1` gate: the derived `Y_A` of loop row 0 equals twice the copied starting `y_a`.
    (hInit :
      (adv cfg.lambda1 place self env (offset + 1) + adv cfg.lambda2 place self env (offset + 1)) *
        (adv cfg.xA place self env (offset + 1) -
          (adv cfg.lambda1 place self env (offset + 1) * adv cfg.lambda1 place self env (offset + 1)
            - adv cfg.xA place self env (offset + 1) - adv cfg.xP place self env (offset + 1)))
        = 2 * adv cfg.lambda1 place self env offset)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    adv cfg.xA place self env (offset + 1 + n + 1)
      = ((accScalar m bits' (n + 1)) • P).x
    ∧ 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1))
      = 2 * ((accScalar m bits' (n + 1)) • P).y := by
  have hfacts := loop_gate_facts cfg input ebits place self env offset n hLoop
  -- the per-row cell readers as `ℕ → Fp` functions, in `soundness_aux`'s shape
  set XA := fun r => adv cfg.xA place self env (offset + 1 + r) with hXA
  set XP := fun r => adv cfg.xP place self env (offset + 1 + r) with hXP
  set YP := fun r => adv cfg.yP place self env (offset + 1 + r) with hYP
  set L1 := fun r => adv cfg.lambda1 place self env (offset + 1 + r) with hL1
  set L2 := fun r => adv cfg.lambda2 place self env (offset + 1 + r) with hL2
  -- `YAD r` is the derived `Y_A` for `r ≤ n`, and `2·(witnessed final y)` at `r = n+1`
  set YAD := fun r => if r = n + 1 then 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1))
    else (L1 r + L2 r) * (XA r - (L1 r * L1 r - XA r - XP r)) with hYAD
  -- base-point constancy along the rows (from the `q_mul_2` constancy checks + the anchor)
  have hconst : ∀ r, r ≤ n → XP r = P.x ∧ YP r = P.y := by
    intro r
    induction r with
    | zero => intro _; exact ⟨by rw [hXP]; simpa using hxPBase, by rw [hYP]; simpa using hyPBase⟩
    | succ v ih =>
      intro hv
      obtain ⟨hx, hy⟩ := ih (by omega)
      obtain ⟨_, _, _, _, hconstv⟩ := hfacts v (by omega)
      obtain ⟨hcx, hcy⟩ := hconstv (by omega)
      simp only [XPr, YPr] at hcx hcy
      refine ⟨?_, ?_⟩
      · simp only [hXP] at hx ⊢; rw [← hcx]; exact hx
      · simp only [hYP] at hy ⊢; rw [← hcy]; exact hy
  have haux := Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.soundness_aux n P hP m h2 hbound
    XA XP YP L1 L2 YAD bits' ?hxA0 ?hYAD0 ?hyad ?hxp ?hyp ?hg1 ?hsec ?hg2
  case hxA0 => rw [hXA]; simpa using hxA0
  case hYAD0 =>
    -- `YAD 0 = (L1 0 + L2 0)(XA 0 - x_R 0)`; the `q_mul_1` gate (`hInit`) forces it to
    -- `2·(λ₁ at offset)`, and the starting-cell copy `hyA0` reads that as `(m•P).y`.
    simp only [hYAD, if_neg (show ¬(0 = n + 1) by omega), hXA, hL1, hL2, hXP, Nat.add_zero]
    rw [hInit, hyA0]
  case hyad =>
    intro r hr; simp only [hYAD, if_neg (show ¬(r = n + 1) by omega)]
  case hxp => exact fun r hr => (hconst r hr).1
  case hyp => exact fun r hr => (hconst r hr).2
  case hg1 =>
    intro r hr
    obtain ⟨_, hg1, _, _, _⟩ := hfacts r (by omega)
    have hk := hbit r hr
    -- `hg1 : 2·L1·(XA−XP) + 2·((Kr·2−1)·YP) = YADr r`; `Kr r = if bits' r then 1 else 0` by `hbit`.
    simp only [XAr, XPr, YPr, L1r, L2r, Kr, Zr, Zpr, YADr, if_neg (by omega : ¬(r = n + 1))] at hg1
    simp only [hYAD, if_neg (show ¬(r = n + 1) by omega), hXA, hXP, hYP, hL1, hL2]
    rw [show adv cfg.z place self env (offset + 1 + r)
          - adv cfg.z place self env (offset + r) * 2 = (if bits' r then 1 else 0) from hk] at hg1
    linear_combination hg1
  case hsec =>
    intro r hr
    obtain ⟨_, _, hsec, _, _⟩ := hfacts r (by omega)
    simp only [XAr, XPr, L1r, L2r] at hsec
    simp only [hXA, hXP, hL1, hL2]
    linear_combination hsec
  case hg2 =>
    intro r hr
    obtain ⟨_, _, _, hg2, _⟩ := hfacts r (by omega)
    simp only [XAr, XPr, L1r, L2r, YADr] at hg2
    -- `hg2`'s RHS is `YADr r + YADr (r+1)`; the `r+1` branch is derived when `r < n+1`,
    -- the witnessed-final form when `r+1 = n+1`.
    by_cases hrn : r + 1 = n + 1
    · simp only [hYAD, if_pos hrn, if_neg (show ¬(r = n + 1) by omega), hXA, hXP, hL1, hL2]
      simp only [if_pos hrn, if_neg (show ¬(r = n + 1) by omega)] at hg2
      linear_combination hg2
    · simp only [hYAD, if_neg hrn, if_neg (show ¬(r = n + 1) by omega), hXA, hXP, hL1, hL2]
      simp only [if_neg hrn, if_neg (show ¬(r = n + 1) by omega)] at hg2
      linear_combination hg2
  refine ⟨?_, ?_⟩
  · have h := haux.1; rw [hXA] at h; simpa using h
  · have h := haux.2
    simp only [hYAD, if_pos rfl] at h
    linear_combination h

/-- **z-chain soundness.** Under the loop constraints and the starting `z` copy, each running-sum
cell satisfies `z_r = 2·z_{r-1} + k_r` with `k_r ∈ {0,1}` — the `Spec`'s running-sum conjunct,
forced by each round's `bool_check` gate. -/
theorem loop_zchain_sound (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset n : ℕ)
    (hz0 : adv cfg.z place self env offset = input.z.eval place env)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    ∃ bits' : BitsHint,
      -- per-round bit-match (the shape `loop_acc_sound.hbit` consumes)
      (∀ r, r ≤ n → adv cfg.z place self env (offset + 1 + r)
        - adv cfg.z place self env (offset + r) * 2 = (if bits' r then 1 else 0)) ∧
      adv cfg.z place self env (offset + 1)
        = 2 * input.z.eval place env + (if bits' 0 then 1 else 0) ∧
      ∀ r : Fin n, adv cfg.z place self env (offset + 1 + (r.val + 1))
        = 2 * adv cfg.z place self env (offset + 1 + r.val)
          + (if bits' (r.val + 1) then 1 else 0) := by
  have hfacts := loop_gate_facts cfg input ebits place self env offset n hLoop
  -- the bit read off the running sum at each round, decided into a `BitsHint`
  refine ⟨fun j => decide (adv cfg.z place self env (offset + 1 + j)
      = 2 * adv cfg.z place self env (offset + j) + 1), ?_, ?_, ?_⟩
  · -- the `hbit` per-round match: from each round's `bool_check` (`IsBool (Kr …)`).
    intro r hr
    have hb := (hfacts r (by omega)).1
    simp only [Kr, Zr, Zpr] at hb ⊢
    split_ifs with hd
    · rw [decide_eq_true_eq] at hd
      rcases hb with h | h
      · exact absurd hd (fun hc => one_ne_zero (α := Fp) (by linear_combination h - hc))
      · linear_combination h
    · rcases hb with h | h
      · linear_combination h
      · exact absurd (by rw [decide_eq_true_eq]; linear_combination h) hd
  · -- round 0: `z`-prev is the start-copy `adv z offset = input.z.eval`
    have hb := (hfacts 0 (by omega)).1
    simp only [Kr, Zr, Zpr, Nat.add_zero] at hb ⊢
    split_ifs with hd
    · rw [decide_eq_true_eq] at hd
      rcases hb with h | h
      · exact absurd hd (fun hc => one_ne_zero (α := Fp) (by linear_combination h - hc))
      · linear_combination h + 2 * hz0
    · rcases hb with h | h
      · linear_combination h + 2 * hz0
      · exact absurd (by rw [decide_eq_true_eq]; linear_combination h) hd
  · intro r
    have hb := (hfacts (r.val + 1) (by omega)).1
    simp only [Kr, Zr, Zpr] at hb ⊢
    -- the round's `z`-prev cell is at `offset + (r+1)`; the goal spells it `offset + 1 + r`
    rw [show offset + 1 + r.val = offset + (r.val + 1) from by omega]
    split_ifs with hd
    · rw [decide_eq_true_eq] at hd
      rcases hb with h | h
      · exact absurd hd (by intro hc; exact one_ne_zero (α := Fp) (by linear_combination h - hc))
      · linear_combination h
    · rcases hb with h | h
      · linear_combination h
      · exact absurd (by rw [decide_eq_true_eq]; linear_combination h) hd

/-- **Honest row values (completeness).** The honest `ExtendsWitnesses` pins every row's
`z`/`x_p`/`y_p`/`λ₁`/`λ₂`/`x_a(next)` cell to the donor's honest value
(`zRunValue`/`rowLambdaValue`/`accVal`). Stated in the raw `input.*.eval` spelling because a round's
gate reads cells witnessed by *other* rounds. -/
private theorem loop_row_values (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset n : ℕ)
    (hW : RegionOperations.ExtendsWitnesses place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    ∀ r, r < n + 1 →
      adv cfg.z place self env.toEnvironment (offset + 1 + r)
          = zRunValue (input.z.eval place env.toEnvironment) (ebits ⟨place, env⟩) r ∧
      adv cfg.xP place self env.toEnvironment (offset + 1 + r)
          = input.base.x.eval place env.toEnvironment ∧
      adv cfg.yP place self env.toEnvironment (offset + 1 + r)
          = input.base.y.eval place env.toEnvironment ∧
      adv cfg.lambda1 place self env.toEnvironment (offset + 1 + r)
          = (rowLambdaValue (input.base.x.eval place env.toEnvironment)
              (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
              (input.yA.eval place env.toEnvironment) (ebits ⟨place, env⟩) r).lambda1 ∧
      adv cfg.lambda2 place self env.toEnvironment (offset + 1 + r)
          = (rowLambdaValue (input.base.x.eval place env.toEnvironment)
              (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
              (input.yA.eval place env.toEnvironment) (ebits ⟨place, env⟩) r).lambda2 ∧
      adv cfg.xA place self env.toEnvironment (offset + 1 + (r + 1))
          = (accVal (input.base.x.eval place env.toEnvironment)
              (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
              (input.yA.eval place env.toEnvironment) (ebits ⟨place, env⟩) (r + 1)).1 := by
  simp only [loop, circuit_norm] at hW
  intro r hr
  have hWround := hW ⟨r, hr⟩
  simp only [adv, show offset + 1 + (r + 1) = offset + 1 + r + 1 from by omega]
  by_cases hr0 : r = 0 <;>
    [ simp only [roundOld, hr0, circuit_norm, zWit, l1Wit, l2Wit, xANextWit, readCell,
        reduceIte] at hWround ⊢;
      simp only [roundOld, circuit_norm, zWit, l1Wit, l2Wit, xANextWit, readCell,
        if_neg hr0] at hWround ⊢ ] <;>
    exact ⟨hWround.1, hWround.2.1, hWround.2.2.1, hWround.2.2.2.1,
      hWround.2.2.2.2.1, hWround.2.2.2.2.2.1⟩

/-- **Completeness loop lemma.** The honest `ExtendsWitnesses` pins every cell to the donor's honest
value, and the loaded round gates then hold. Routes into the donor's `honest_step`/`accVal_eq_nsmul`.

Three cells a round's gate reads live *outside* the loop's own ops; their honest values are the
hypotheses `hz0` (start-`z` copy), `hxA0cell` (start-`x_a` copy), and `hyAF` (witnessed final
`y_a`). -/
theorem loop_constraints_complete (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset n : ℕ)
    (bits : BitsHint) (hbits : bits = ebits ⟨place, env⟩)
    (P : Point Fp) (hP : P.OnCurve)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (hxA0 : input.xA.eval place env.toEnvironment = (m • P).x)
    (hyA0 : input.yA.eval place env.toEnvironment = (m • P).y)
    (hxPBase : input.base.x.eval place env.toEnvironment = P.x)
    (hyPBase : input.base.y.eval place env.toEnvironment = P.y)
    (hz0 : adv cfg.z place self env.toEnvironment offset = input.z.eval place env.toEnvironment)
    (hxA0cell : adv cfg.xA place self env.toEnvironment (offset + 1)
      = input.xA.eval place env.toEnvironment)
    (hyAF : adv cfg.lambda1 place self env.toEnvironment (offset + 1 + (n + 1))
      = (accVal (input.base.x.eval place env.toEnvironment)
          (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
          (input.yA.eval place env.toEnvironment) bits (n + 1)).2)
    (hWit : RegionOperations.ExtendsWitnesses place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((loop cfg input ebits offset n (n + 1)).operations self) := by
  -- honest accumulator in point coordinates: `accVal … r = (accScalar r • P)`
  have hAV : ∀ r, r ≤ n + 1 →
      accVal P.x P.y (input.xA.eval place env.toEnvironment)
          (input.yA.eval place env.toEnvironment) bits r
        = ((accScalar m bits r • P).x, (accScalar m bits r • P).y) := by
    rw [hxA0, hyA0]
    exact Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.accVal_eq_nsmul hP bits h2 n hbound
  -- per-row `honest_step` bound (the accumulator's scalar stays in the scalar-field range)
  have hMbound : ∀ r, r ≤ n → 2 * accScalar m bits r + 1 < PALLAS_SCALAR_CARD := by
    intro r hr
    have hMle := accScalar_le (m := m) bits r
    have hpow : 2 ^ r * (m + 1) ≤ 2 ^ (n + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h254 := pow254_lt_card
    have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
    have hpos : 0 < 2 ^ r * (m + 1) := by positivity
    omega
  -- the honest row lambda cells in point coordinates
  have hRL : ∀ r, r ≤ n + 1 →
      rowLambdaValue P.x P.y (input.xA.eval place env.toEnvironment)
          (input.yA.eval place env.toEnvironment) bits r
        = lambdaCellsValue P.x P.y (accScalar m bits r • P).x (accScalar m bits r • P).y (bits r) := by
    intro r hr; simp only [rowLambdaValue, hAV r hr]
  -- the honest running-sum step in subtraction form
  have hZB : ∀ (z : Fp) (r : ℕ), zRunValue z bits r
      - (if r = 0 then z else zRunValue z bits (r - 1)) * 2 = (if bits r then 1 else 0) := by
    intro z r
    rcases r with _ | r'
    · rw [if_pos rfl]
      show 2 * z + (if bits 0 then 1 else 0) - z * 2 = _
      rcases Bool.dichotomy (bits 0) with hb | hb <;> rw [hb] <;> norm_num <;> ring
    · rw [if_neg (Nat.succ_ne_zero r'), Nat.add_sub_cancel]
      show 2 * zRunValue z bits r' + (if bits (r' + 1) then 1 else 0)
        - zRunValue z bits r' * 2 = _
      rcases Bool.dichotomy (bits (r' + 1)) with hb | hb <;> rw [hb] <;> norm_num <;> ring
  -- the witnessed final `y_a`, in point coordinates
  have hyAF' : adv cfg.lambda1 place self env.toEnvironment (offset + 1 + (n + 1))
      = (accScalar m bits (n + 1) • P).y := by
    rw [hyAF, hxPBase, hyPBase, hAV (n + 1) le_rfl]
  -- **global** honest cell values (`loop_row_values`), rewritten to `P`-coordinates. Needed
  -- because a round's gate reads cells (`z`-predecessor, next-row `x_p`/`y_p`/`x_a`) witnessed
  -- by *other* rounds.
  have hRowVals : ∀ r, r < n + 1 →
        adv cfg.z place self env.toEnvironment (offset + 1 + r)
            = zRunValue (input.z.eval place env.toEnvironment) bits r ∧
        adv cfg.xP place self env.toEnvironment (offset + 1 + r) = P.x ∧
        adv cfg.yP place self env.toEnvironment (offset + 1 + r) = P.y ∧
        adv cfg.lambda1 place self env.toEnvironment (offset + 1 + r)
            = (rowLambdaValue P.x P.y (input.xA.eval place env.toEnvironment)
                (input.yA.eval place env.toEnvironment) bits r).lambda1 ∧
        adv cfg.lambda2 place self env.toEnvironment (offset + 1 + r)
            = (rowLambdaValue P.x P.y (input.xA.eval place env.toEnvironment)
                (input.yA.eval place env.toEnvironment) bits r).lambda2 ∧
        adv cfg.xA place self env.toEnvironment (offset + 1 + (r + 1))
            = (accVal P.x P.y (input.xA.eval place env.toEnvironment)
                (input.yA.eval place env.toEnvironment) bits (r + 1)).1 := by
    intro r hr
    obtain ⟨h1', h2', h3', h4', h5', h6'⟩ :=
      loop_row_values cfg input ebits place self env offset n hWit r hr
    rw [← hbits] at h1' h4' h5' h6'
    rw [hxPBase] at h2'; rw [hyPBase] at h3'
    rw [hxPBase, hyPBase] at h4' h5' h6'
    exact ⟨h1', h2', h3', h4', h5', h6'⟩
  -- discharge each round's gate constraints from the global honest cells (`hRowVals`) + `honest_step`
  simp only [loop, circuit_norm]
  intro rr
  obtain ⟨k, hkb⟩ := rr
  · -- `2 ≠ 0` clears the `TWO_INV = 2⁻¹` in the VK-faithful `y_a`.
    have hp2 : (2 : Fp) ≠ 0 := by decide
    have hkn : k ≤ n := by omega
    -- honest_step at row `k` (accumulator scalar `M := accScalar m bits k`)
    obtain ⟨hHSg1, hHSyad, hHSxnext, hHSg2⟩ :=
      Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.honest_step hP bits
        (accScalar_two_le h2 bits k) (hMbound k hkn) k
    -- fold honest_step's raw `2M + 2k − 1` scalar into `accScalar m bits (k+1)` (definitional)
    rw [show (2 * accScalar m bits k + (if bits k then 1 else 0) * 2 - 1)
        = accScalar m bits (k + 1) from rfl] at hHSxnext hHSg2
    -- the conditionally-negated per-bit `y` (donor `hSy`)
    have hSy : (stepPoint P (bits k)).y = ((if bits k then 1 else 0) * 2 - 1) * P.y := by
      unfold stepPoint
      rcases Bool.dichotomy (bits k) with hb | hb <;> rw [hb]
      · show (-P).y = _; rw [Orchard.Point.neg_y]; norm_num
      · show P.y = _; norm_num
    -- honest cell values of row `k`, in point coordinates
    obtain ⟨hVz, hVxp, hVyp, hVl1, hVl2, hVxa⟩ := hRowVals k (by omega)
    rw [hRL k (by omega)] at hVl1 hVl2
    simp only [accVal, hAV k (by omega)] at hVxa
    rw [hHSxnext] at hVxa
    -- `xANext`'s defining identity (the row engine's `x_R` form), donor `hXdef`
    have hXnext' : (accScalar m bits (k + 1) • P).x
        = (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
            (bits k)).lambda2
          * (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
              (bits k)).lambda2
          - (accScalar m bits k • P).x
          - ((lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
                (bits k)).lambda1
              * (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
                  (bits k)).lambda1
              - (accScalar m bits k • P).x - P.x) := hHSxnext.symm.trans rfl
    -- `hHSg2` with `xANext` in point form
    rw [show (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
        (bits k)).xANext = (accScalar m bits (k + 1) • P).x from hHSxnext] at hHSg2
    -- current-row `x_a` (row 0: the start copy; row `k ≥ 1`: round `k−1`'s next-`x_a` witness)
    have hVXcur : adv cfg.xA place self env.toEnvironment (offset + 1 + k)
        = (accScalar m bits k • P).x := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa [accScalar] using hxA0cell.trans hxA0
      · have h := (hRowVals (k - 1) (by omega)).2.2.2.2.2
        rw [show k - 1 + 1 = k from by omega] at h
        rw [h, hAV k (by omega)]
    -- the honest `z`-step at row `k` (`z_k − 2·z_{k−1} = bit k`)
    have hZprev : adv cfg.z place self env.toEnvironment (offset + k)
        = (if k = 0 then input.z.eval place env.toEnvironment
            else zRunValue (input.z.eval place env.toEnvironment) bits (k - 1)) := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa using hz0
      · rw [if_neg (by omega), show offset + k = offset + 1 + (k - 1) from by omega]
        exact (hRowVals (k - 1) (by omega)).1
    have hZstep : adv cfg.z place self env.toEnvironment (offset + 1 + k)
        - adv cfg.z place self env.toEnvironment (offset + k) * 2 = (if bits k then 1 else 0) := by
      rw [hVz, hZprev]
      have := hZB (input.z.eval place env.toEnvironment) k
      rcases Nat.eq_zero_or_pos k with rfl | hkpos <;> simpa using this
    -- expose the raw `env.advice` spellings the reduced gate polys use
    simp only [adv] at hVxp hVyp hVl1 hVl2 hVxa hVXcur hZstep hyAF'
    by_cases hrn : k = n
    · -- ── last round: `q_mul_3` (`Y_A(next)` = 2·witnessed final `y_a`; no constancy checks) ──
      subst hrn
      by_cases hr0 : k = 0
      · -- single-round circuit: anchor copies + `q_mul_3` at row 0
        subst hr0
        simp only [Nat.add_zero] at hVxp hVyp hVl1 hVl2 hVXcur hZstep
        simp only [roundOld, circuit_norm, qMul3Gate, forLoopPolys, yA, xRExpr]
        rw [hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 2 = offset + 1 + (0 + 1) from by omega, hVxa, hyAF']
        refine ⟨hxPBase.symm, hyPBase.symm, ?_, ?_, ?_, ?_⟩
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad
      · -- last row of a longer run: `q_mul_3` only
        simp only [roundOld, circuit_norm, qMul3Gate, forLoopPolys, yA, xRExpr,
          if_neg hr0]
        rw [hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 1 + k + 1 = offset + 1 + (k + 1) from by omega, hVxa, hyAF']
        refine ⟨?_, ?_, ?_, ?_⟩
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad
    · -- ── interior round: `q_mul_2` (constancy checks; `Y_A(next)` derived at row `k+1`) ──
      -- next row's honest cells (in-loop, from `hRowVals (k+1)`), in point coordinates
      obtain ⟨_, hVxp1, hVyp1, hVl1', hVl2', _⟩ :=
        hRowVals (k + 1) (by omega)
      rw [hRL (k + 1) (by omega)] at hVl1' hVl2'
      -- honest_step at row `k+1` — its `Y_A` identity pins the next row's derived `Y_A`
      obtain ⟨_, hHSyad1, _, _⟩ :=
        Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.honest_step hP bits
          (accScalar_two_le h2 bits (k + 1)) (hMbound (k + 1) (by omega)) (k + 1)
      simp only [adv] at hVxp1 hVyp1 hVl1' hVl2'
      by_cases hr0 : k = 0
      · subst hr0
        simp only [Nat.add_zero] at hVxp hVyp hVl1 hVl2 hVXcur hZstep
        simp only [roundOld, circuit_norm, qMul2Gate, forLoopPolys, yA, xRExpr,
          if_neg hrn]
        rw [hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 2 = offset + 1 + (0 + 1) from by omega, hVxa,
          hVxp1, hVyp1, hVl1', hVl2']
        refine ⟨hxPBase.symm, hyPBase.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · ring
        · ring
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad + hHSyad1
      · simp only [roundOld, circuit_norm, qMul2Gate, forLoopPolys, yA, xRExpr,
          if_neg hrn, if_neg hr0]
        rw [hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 1 + k + 1 = offset + 1 + (k + 1) from by omega, hVxa,
          hVxp1, hVyp1, hVl1', hVl2']
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · ring
        · ring
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad + hHSyad1

/-! ## The bundle contract

`Spec` exposes the round invariant; `Assumptions`/`ProverAssumptions` are the donor's
incomplete-addition preconditions (base on-curve; `A = [m]P`, `2 ≤ m`, `2^{n+2}(m+1) ≤ 2^{254}`).

There is NO prover-side `bits` parameter: the working scalar's bits are derived from the scalar cell
`input.alpha` (`kBits (alpha value) (w + ·)`), with `w` the window offset (0 for `hi`, 125 for
`lo`). The verifier-facing `Spec` existentially quantifies a matching bit sequence; `ProverSpec`
pins the honest one. -/

/-- The scalar-mul incomplete-phase round predicate: the running-sum chain and, for any
`A = [m]P` in range, the output accumulator is the double-and-add result. -/
def RoundInvariant (n : ℕ) (input : Inputs Fp) (output : Output (n + 1) Fp)
    (bits : BitsHint) : Prop :=
  let base : Point Fp := input.base
  (output.zs[0] = 2 * input.z + (if bits 0 then 1 else 0) ∧
    ∀ b : Fin n, output.zs[b.val + 1] =
      2 * output.zs[b.val] + (if bits (b.val + 1) then 1 else 0)) ∧
  ∀ (m : ℕ),
    -- TODO weird to use Point.ofCoords here, input/output should just contain entire points
    Point.ofCoords (input.xA, input.yA) = m • base →
    2 ≤ m → 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254 →
    Point.ofCoords (output.xA, output.yA) = (accScalar m bits (n + 1)) • base

/-! ## The gadget bundle

`incomplete::Config::double_and_add` (`CircuitVersion::AnchoredBase`), at `n = 124` (`hi`) and
`n = 125` (`lo`). Parameterized by the window offset `w`; soundness does not depend on the prover. -/

def double_and_add (n : ℕ) (w : ℕ) :
    FormalRegionCircuit Fp
      (Column .advice × Column .advice × Column .advice × Column .advice ×
        Column .advice × Column .advice)
      Config Inputs (Output (n + 1)) where
  configure := fun (z, xA, xP, yP, lambda1, lambda2) =>
    configure z xA xP yP lambda1 lambda2

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    -- starting copies
    let _z ← copyAdvice input.z cfg.z offset
    let _yA ← copyAdvice input.yA cfg.lambda1 offset
    let _xA ← copyAdvice input.xA cfg.xA (offset + 1)
    -- q_mul_1 at `offset` (outside the loop rows); the per-round selectors are enabled inside `round`
    (qMul1Gate cfg).enable offset
    -- the per-bit round loop; bits derived from the scalar cell (`bitsOf input w`), not a prover hint
    loop cfg input (bitsOf input w) offset n (n + 1)
    -- the witnessed final y_a
    let _yAFinal ← assignAdvice cfg.lambda1 (offset + 1 + (n + 1))
      (yAFinalWit n input (bitsOf input w))
    -- name the output cells at fixed absolute rows (`cellAt`/`cellVec` emit no op)
    let xAOut ← cellAt cfg.xA (offset + 1 + n + 1)
    let yAOut ← cellAt cfg.lambda1 (offset + 1 + (n + 1))
    let zsOut ← cellVec cfg.z (fun r => offset + 1 + r) (n + 1)
    return { xA := xAOut, yA := yAOut, zs := zsOut }

  -- base is a non-identity on-curve point (exceptional cases subsumed by the range condition)
  Assumptions input := input.base.OnCurve

  Spec input output _ :=
    ∃ bits : BitsHint, RoundInvariant n input output bits

  -- base on-curve; accumulator `[m]P` in the exceptional-case-free range
  ProverAssumptions input _ _ :=
    input.base.OnCurve ∧ ∃ m : ℕ,
      Point.ofCoords (input.xA, input.yA) = m • input.base ∧
      2 ≤ m ∧ 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254

  -- honest bits derived from the scalar cell: `kBits alpha (w + ·)`
  ProverSpec input output _ _ :=
    RoundInvariant n input output (kBitsWindow input.alpha w)

  -- ══ Soundness ══
  -- Read the output cells off the env, then feed the cleaned facts into `loop_zchain_sound`
  -- (running-sum chain) and `loop_acc_sound` (accumulator = `accScalar`).
  soundness := by
    circuit_proof_start [qMul1Gate, yA, xRExpr, RoundInvariant]
    -- fold the framework cell form (`env.advice col ↑(place self + row)`) to the loop lemmas' `adv`
    -- TODO this is ridiculous. we should have a nice normal form and use it
    have hadv : ∀ (col : Column .advice) (row : ℕ),
        env.env.advice col ((env.place self + row : ℕ) : ℤ) = adv col env.place self env.env row :=
      fun _ _ => rfl
    simp only [hadv] at h_output_xA h_output_yA h_output_zs hc
    obtain ⟨hCopyZ, hCopyYA, hCopyXA, hQMul1, hLoop⟩ := hc
    -- reconstruct the input record so the loop lemmas' `input` matches `hLoop`
    set inp : Inputs (AssignedCell Fp) :=
      { alpha := input_var_alpha, base := { x := input_var_base_x, y := input_var_base_y },
        xA := input_var_xA, yA := input_var_yA, z := input_var_z } with hinp
    -- the `input.*.eval` cell reads, resolved to the input values via `h_input`
    obtain ⟨hIalpha, ⟨hBx, hBy⟩, hIxA, hIyA, hIz⟩ := h_input
    -- z-chain + per-round bit match from `loop_zchain_sound` (its `bits'` is the witness)
    obtain ⟨bits', hbit, hz0chain, hzchain⟩ :=
      loop_zchain_sound cfg inp (bitsOf inp w) env.place self env.env offset n hCopyZ hLoop
    refine ⟨bits', ?_, ?_⟩
    · -- running-sum chain conjunct of `RoundInvariant`
      refine ⟨?_, ?_⟩
      · -- z_0 = 2·input.z + bit 0
        have hz0 := h_output_zs 0 (by omega)
        rw [Nat.add_zero] at hz0
        rw [hz0] at hz0chain
        simpa only [hinp, AssignedCell.eval, hIz] using hz0chain
      · intro b
        have h := hzchain b
        rw [h_output_zs (b.val + 1) (by omega), h_output_zs b.val (by omega)] at h
        exact h
    · -- accumulator conjunct: route `loop_acc_sound` into `Point.ofCoords`
      intro m hm h2 hbound
      -- the anchor copies pin `x_p`/`y_p` at `offset + 1` to `base.x`/`base.y`
      obtain ⟨hAnchorX, hAnchorY⟩ := loop_anchor cfg inp (bitsOf inp w) env.place self env.env offset n
        hLoop
      simp only [hinp, AssignedCell.eval, hBx, hBy] at hAnchorX hAnchorY
      -- the accumulator hypothesis `ofCoords (xA, yA) = m • base` ⇒ coordinate equalities
      have hAccX : input_xA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x :=
        congrArg Point.x hm
      have hAccY : input_yA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
        congrArg Point.y hm
      have hacc := loop_acc_sound cfg inp (bitsOf inp w) bits' env.place self env.env offset n
        { x := input_base_x, y := input_base_y } hA m h2 hbound
        (by rw [hCopyXA]; simp only [hIxA]; exact hAccX)
        (by rw [hCopyYA]; simp only [hIyA]; exact hAccY)
        hAnchorX hAnchorY hbit
        -- q_mul_1 is now `y_a_witnessed − Y_A(next)·TWO_INV = 0` (VK-faithful, `.scaled 2⁻¹`);
        -- clear the `2⁻¹` (via `2·2⁻¹ = 1`) to recover `Y_A(next) = 2·y_a_witnessed` (`hInit`).
        (by
          have hinv : (2 : Fp) * (2 : Fp)⁻¹ = 1 := mul_inv_cancel₀ (by decide : (2 : Fp) ≠ 0)
          linear_combination (-2 : Fp) * hQMul1
            - (adv cfg.lambda1 env.place self env.env (offset + 1) +
                adv cfg.lambda2 env.place self env.env (offset + 1)) *
              (adv cfg.xA env.place self env.env (offset + 1) -
                (adv cfg.lambda1 env.place self env.env (offset + 1) *
                    adv cfg.lambda1 env.place self env.env (offset + 1)
                  - adv cfg.xA env.place self env.env (offset + 1)
                  - adv cfg.xP env.place self env.env (offset + 1))) * hinv)
        hLoop
      obtain ⟨hx, hy2⟩ := hacc
      -- reconstruct the output point from its coordinates
      have hy : adv cfg.lambda1 env.place self env.env (offset + 1 + (n + 1))
          = (accScalar m bits' (n + 1) • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
        mul_left_cancel₀ Orchard.two_ne_zero hy2
      rw [h_output_xA] at hx
      rw [h_output_yA] at hy
      rw [hx, hy]
      -- `ofCoords (p.x, p.y) = p`
      rfl

  -- ══ Completeness ══
  -- Mirrors `soundness`: pin the start copies and the final `y_a` from their witnesses, discharge
  -- the loop via `loop_constraints_complete` and `q_mul_1` via `honest_step`'s row-0 `Y_A` identity,
  -- and read `RoundInvariant` off the honest row values (`loop_row_values`) + `accVal_eq_nsmul`.
  completeness := by
    circuit_proof_start
      [yAFinalWit, readCell,
       -- gate defs: normalize the `q_mul_1` gate constraint at the goal
       qMul1Gate, yA, xRExpr]
    obtain ⟨hWz, hWyA, hWxA, hWloop, hWyF⟩ := hwit
    -- reconstruct the input record so the loop lemmas' `input` matches `hWloop`
    set inp : Inputs (AssignedCell Fp) :=
      { alpha := input_var_alpha, base := { x := input_var_base_x, y := input_var_base_y },
        xA := input_var_xA, yA := input_var_yA, z := input_var_z } with hinp
    obtain ⟨hIalpha, ⟨hBx, hBy⟩, hIxA, hIyA, hIz⟩ := h_input
    obtain ⟨hPbase, m, hm, h2m, hbnd⟩ := hPA
    -- the honest bit sequence, derived from the scalar cell and equal to the witnessed family
    set bits : BitsHint := kBitsWindow input_alpha w with hbitsdef
    have hbits : bits = bitsOf inp w ⟨env.place, env.env⟩ :=
      congrArg (fun a => kBitsWindow a w) hIalpha.symm
    rw [← hbits] at hWyF
    have hAccX : input_xA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x :=
      congrArg Point.x hm
    have hAccY : input_yA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
      congrArg Point.y hm
    -- the honest row values (the loop witnesses), folded onto the honest `bits` via `hbits`
    have hRows := loop_row_values cfg inp (bitsOf inp w) env.place self env.env offset n hWloop
    simp only [← hbits] at hRows
    -- (`h_output_*` are already in the raw `env.advice` cell form the induction consumes)
    -- the scalar-field bound at row 0 (`2m + 1 < |scalar field|`), from the range assumption
    have hMb0 : 2 * m + 1 < PALLAS_SCALAR_CARD := by
      have h254 := pow254_lt_card
      have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
      have hpow : m + 1 ≤ 2 ^ (n + 1) * (m + 1) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    -- `honest_step` at row 0: its `Y_A` identity is exactly the `q_mul_1` gate
    have hHS0yad : 2 * (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y
        = ((lambdaCellsValue input_base_x input_base_y
              (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
              (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda1
            + (lambdaCellsValue input_base_x input_base_y
                (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
                (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda2)
          * ((m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
            - ((lambdaCellsValue input_base_x input_base_y
                  (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
                  (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda1
                * (lambdaCellsValue input_base_x input_base_y
                    (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
                    (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda1
                - (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x - input_base_x)) :=
      (Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.honest_step hPbase bits h2m hMb0 0).2.1
    -- row-0 honest cells, resolved to the destructured input values and point coordinates
    obtain ⟨_, hR0xp, _, hR0l1, hR0l2, _⟩ := hRows 0 (by omega)
    simp only [hinp, adv, AssignedCell.eval, hBx, hBy, hIxA, hIyA, Nat.add_zero,
      rowLambdaValue, accVal] at hR0xp hR0l1 hR0l2
    rw [hAccX, hAccY] at hR0l1 hR0l2
    refine ⟨⟨hWz, hWyA, hWxA, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · -- ── the `q_mul_1` gate: `y_a(copied) = Y_A(row 0)·TWO_INV`, the honest-row `Y_A` identity ──
      rw [hWyA, hIyA, hAccY, hR0l1, hR0l2, hWxA, hIxA, hAccX, hR0xp]
      -- VK-faithful gate carries `.scaled … TWO_INV`; clear it (needs `2 ≠ 0`).
      have hp2 : (2 : Fp) ≠ 0 := by decide
      field_simp
      linear_combination hHS0yad
    · -- ── the loop's `Constraints`: `loop_constraints_complete` on the honest start values ──
      exact loop_constraints_complete cfg inp (bitsOf inp w) env.place self env.env offset n
        bits hbits { x := input_base_x, y := input_base_y } hPbase m h2m hbnd
        (by simp only [hinp, AssignedCell.eval, hIxA]; exact hAccX)
        (by simp only [hinp, AssignedCell.eval, hIyA]; exact hAccY)
        (by simp only [hinp, AssignedCell.eval, hBx])
        (by simp only [hinp, AssignedCell.eval, hBy])
        (by simp only [adv, hinp, AssignedCell.eval]; exact hWz)
        (by simp only [adv, hinp, AssignedCell.eval]; exact hWxA)
        (by simp only [adv, hinp, AssignedCell.eval]; exact hWyF)
        hWloop
    · -- ── `RoundInvariant`, z-chain conjunct, round 0 ──
      have h := (hRows 0 (by omega)).1
      simp only [hinp, adv, AssignedCell.eval, hIz] at h
      rw [h_output_zs 0 (by omega)] at h
      exact h
    · -- ── z-chain conjunct, interior rounds ──
      intro b
      have h1 := (hRows (b.val + 1) (by omega)).1
      have h0 := (hRows b.val (by omega)).1
      simp only [hinp, adv, AssignedCell.eval, hIz] at h1 h0
      rw [h_output_zs (b.val + 1) (by omega)] at h1
      rw [h_output_zs b.val (by omega)] at h0
      rw [h1, h0]
      rfl
    · -- ── `RoundInvariant`, accumulator conjunct: `accVal_eq_nsmul` on the output cells ──
      intro m' hm' h2' hbnd'
      have hAccX' : input_xA = (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).x :=
        congrArg Point.x hm'
      have hAccY' : input_yA = (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
        congrArg Point.y hm'
      -- the honest accumulator after `n + 1` rounds, in point coordinates (ascribed; definitional)
      have hAV' : accVal input_base_x input_base_y
            (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
            (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).y bits (n + 1)
          = ((accScalar m' bits (n + 1) • ({ x := input_base_x, y := input_base_y } : Point Fp)).x,
             (accScalar m' bits (n + 1) • ({ x := input_base_x, y := input_base_y } : Point Fp)).y) :=
        Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.accVal_eq_nsmul hPbase bits h2' n hbnd'
          (n + 1) le_rfl
      -- output `x_a`: the last round's next-`x_a` witness
      have hx := (hRows n (by omega)).2.2.2.2.2
      simp only [hinp, adv, AssignedCell.eval, hBx, hBy, hIxA, hIyA] at hx
      rw [hAccX', hAccY', hAV'] at hx
      -- output `y_a`: the witnessed final `y_a`
      rw [hBx, hBy, hIxA, hIyA, hAccX', hAccY', hAV'] at hWyF
      rw [show offset + 1 + (n + 1) = offset + 1 + n + 1 from by omega] at hx
      rw [h_output_xA] at hx
      rw [h_output_yA] at hWyF
      rw [hx, hWyF]
      rfl

end Halo2.Ironwood.Ecc.MulIncomplete
