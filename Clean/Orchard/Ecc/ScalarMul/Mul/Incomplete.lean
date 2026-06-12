import Clean.Orchard.Ecc.ScalarMul.Defs
import Clean.Orchard.Sinsemilla
import Clean.Orchard.Sinsemilla.HashToPoint
import Clean.Orchard.Specs.Sinsemilla

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/incomplete.rs`.
-/

namespace Orchard.Ecc.ScalarMul.Mul.Incomplete

/- The Rust gate uses `y_a = Y_A / 2`. These constraints multiply those
   equations by `2`, avoiding a division operation while preserving the Pallas
   gate's zero set. -/
def yADouble {K : Type} [Add K] [Sub K] [Mul K] (row : Sinsemilla.DoubleAndAddRow K) : K :=
  Sinsemilla.DoubleAndAdd.yA row

namespace Init

structure Row (F : Type) where
  yAWitnessed : F
  next : Sinsemilla.DoubleAndAddRow F
deriving ProvableStruct

def poly {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  2 * row.yAWitnessed - yADouble row.next

def Spec (row : Row Fp) : Prop :=
  2 * row.yAWitnessed = yADouble row.next

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (poly row)

def circuit : FormalAssertion Fp Row where
  name := "GATE q_mul_1 == 1 checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, poly, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h_holds)
  completeness := by
    circuit_proof_start [main, Spec, poly, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    exact by simpa [sub_eq_add_neg] using sub_eq_zero.mpr h_spec

end Init

namespace Loop

structure Row (F : Type) where
  zCur : F
  zPrev : F
  cur : Sinsemilla.DoubleAndAddRow F
  xANext : F
  yPCur : F
  yANextDouble : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  row.zCur - row.zPrev * 2

def gradient1 {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Row K) : K :=
  2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) - yADouble row.cur +
    2 * ((bit row * 2 - 1) * row.yPCur)

def secantLine {K : Type} [Sub K] [Mul K] (row : Row K) : K :=
  row.cur.lambda2 * row.cur.lambda2 - row.xANext -
    Sinsemilla.DoubleAndAdd.xR row.cur - row.cur.xA

def gradient2 {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  2 * row.cur.lambda2 * (row.cur.xA - row.xANext) - yADouble row.cur - row.yANextDouble

def Spec (row : Row Fp) : Prop :=
  IsBool (bit row) ∧
    2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) +
        2 * ((bit row * 2 - 1) * row.yPCur) = yADouble row.cur ∧
    row.cur.lambda2 * row.cur.lambda2 =
        row.xANext + Sinsemilla.DoubleAndAdd.xR row.cur + row.cur.xA ∧
    2 * row.cur.lambda2 * (row.cur.xA - row.xANext) =
        yADouble row.cur + row.yANextDouble

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (gradient1 row)
  assertZero (secantLine row)
  assertZero (gradient2 row)

def circuit : FormalAssertion Fp Row where
  name := "GATE q_mul_3 == 1 checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, NoteCommit.boolPoly, bit, gradient1,
      secantLine, gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
    rcases h_holds with ⟨hBool, hGradient1, hSecant, hGradient2⟩
    exact ⟨isBool_of_boolPoly_eq_zero (by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBool),
      by linear_combination hGradient1,
      by linear_combination hSecant,
      by linear_combination hGradient2⟩
  completeness := by
    circuit_proof_start [main, Spec, NoteCommit.boolPoly, bit, gradient1,
      secantLine, gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
    rcases h_spec with ⟨hBool, hGradient1, hSecant, hGradient2⟩
    exact ⟨by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hBool,
      by linear_combination hGradient1,
      by linear_combination hSecant,
      by linear_combination hGradient2⟩

end Loop

namespace MainLoop

structure Row (F : Type) extends Loop.Row F where
  xPNext : F
  yPNext : F
deriving ProvableStruct

def xPCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.cur.xP - row.xPNext

def yPCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.yPCur - row.yPNext

def Spec (row : Row Fp) : Prop :=
  row.cur.xP = row.xPNext ∧ row.yPCur = row.yPNext ∧ Loop.Spec row.toRow

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (xPCheck row)
  assertZero (yPCheck row)
  Loop.circuit row.toRow

def circuit : FormalAssertion Fp Row where
  name := "GATE q_mul_2 == 1 checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, xPCheck, yPCheck, Loop.circuit, Loop.Spec]
    rcases h_holds with ⟨hxP, hyP, hLoop⟩
    exact ⟨sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hxP),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hyP),
      hLoop⟩
  completeness := by
    circuit_proof_start [main, Spec, xPCheck, yPCheck, Loop.circuit, Loop.Spec]
    rcases h_spec with ⟨hxP, hyP, hLoop⟩
    exact ⟨by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hxP,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hyP,
      hLoop⟩

end MainLoop

/-!
### `incomplete.rs::Config::double_and_add`

The synthesis-level double-and-add over `numBits = n + 1` incomplete-addition rows,
shared by the `hi` (125 bits) and `lo` (126 bits) halves of variable-base scalar
multiplication. This ports the `CircuitVersion::AnchoredBase` variant: the first row's
`x_p, y_p` cells are copies of `base`, and the `q_mul_2` constancy checks propagate the
base to every row.

The scalar bits are prover-side `Value<bool>`s, modeled as an `Unconstrained` hint
(MSB-first, indexed from the first processed bit).

The running accumulator's y-coordinate is not a per-row cell in the source; it exists
only as the derived expression `y_{A,i} = Y_{A,i}/2`. Only the initial y (copied into
the `lambda_1` column) and the final y (witnessed after the last row) are cells.

Cell order matches the source's assignment order: the three starting copies
(`z`, `x_a`, `y_a`), then per loop row the cells `z, x_p, y_p, λ1, λ2, x_a(next)`
in the order `assign_advice` is called, then the final `y_a`. Gates are asserted
after witnessing; in the source they are global polynomial identities whose
selectors are enabled before any assignment, so assertion order carries no content.
-/

namespace DoubleAndAdd

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- Prover-side scalar bits, MSB-first, indexed from the first processed bit. -/
def BitsHint : Type := ℕ → Bool

instance : Inhabited BitsHint := ⟨fun _ => false⟩

/-- The inputs of `double_and_add`: the non-identity base point, the accumulator cells
`(x_a, y_a)`, the starting running-sum cell `z`, and the prover-side scalar bits. -/
structure Input (F : Type) where
  base : Ecc.Point F
  xA : F
  yA : F
  z : F
  bits : Unconstrained BitsHint F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ base := { x := default, y := default }, xA := default, yA := default,
     z := default, bits := fun _ => default }⟩

/-- The cells freshly witnessed for the first row (its `x_p, y_p` are copies of
`base` in the anchored circuit version). -/
structure LambdaCells (F : Type) where
  lambda1 : F
  lambda2 : F
  xANext : F
deriving ProvableStruct

/-- The outputs of `double_and_add`: the final accumulator cells and all interstitial
running-sum cells (excluding the copied starting `z`). -/
structure Output (numBits : ℕ) (F : Type) where
  xA : F
  yA : F
  zs : Vector F numBits
deriving ProvableStruct

/-! ### Honest-prover witness values -/

/-- The running sum after bit `b` (MSB-first): `z_b = 2 z_{b-1} + k_b`. -/
def zRunValue (zIn : Fp) (bits : ℕ → Bool) : ℕ → Fp
  | 0 => 2 * zIn + (if bits 0 then 1 else 0)
  | b + 1 => 2 * zRunValue zIn bits b + (if bits (b + 1) then 1 else 0)

/-- Honest lambda cells of one double-and-add row, from the accumulator `(x_a, y_a)`
entering the row and the row's bit. The assigned `x_p, y_p` cells always hold the base
coordinates; the conditional negation `(2k-1) y_p` only enters `λ1`. -/
def lambdaCellsValue (baseX baseY xA yA : Fp) (bit : Bool) : LambdaCells Fp :=
  let yP := if bit then baseY else -baseY
  let lambda1 := (yA - yP) / (xA - baseX)
  let xR := lambda1 * lambda1 - xA - baseX
  let lambda2 := 2 * yA / (xA - xR) - lambda1
  { lambda1, lambda2, xANext := lambda2 * lambda2 - xA - xR }

/-- The honest accumulator `(x_a, y_a)` entering row `r`
(`incomplete.rs::double_and_add` assignment formulas, total via `0⁻¹ = 0`). -/
def accVal (baseX baseY xA yA : Fp) (bits : ℕ → Bool) : ℕ → Fp × Fp
  | 0 => (xA, yA)
  | r + 1 =>
    let p := accVal baseX baseY xA yA bits r
    let l := lambdaCellsValue baseX baseY p.1 p.2 (bits r)
    (l.xANext, l.lambda2 * (p.1 - l.xANext) - p.2)

/-- The honest lambda cells of row `r`. -/
def rowLambdaValue (baseX baseY xA yA : Fp) (bits : ℕ → Bool) (r : ℕ) : LambdaCells Fp :=
  lambdaCellsValue baseX baseY
    (accVal baseX baseY xA yA bits r).1 (accVal baseX baseY xA yA bits r).2 (bits r)

/-- The accumulated multiplier after `b` double-and-add steps starting from `[m]P`:
each step computes `(acc + (2k-1) P) + acc`, so `m_b = 2 m_{b-1} + 2 k_{b-1} - 1`. -/
def accScalar (m : ℕ) (bits : ℕ → Bool) : ℕ → ℕ
  | 0 => m
  | b + 1 => 2 * accScalar m bits b + (if bits b then 1 else 0) * 2 - 1

/-- The conditionally-negated per-bit point `(2k-1) P` added by each step. -/
noncomputable def stepPoint (P : SWPoint Pallas.curve) (bits : ℕ → Bool) :
    ℕ → SWPoint Pallas.curve :=
  fun b => if bits b then P else -P

private theorem incompleteAdd_some {X Y : SWPoint Pallas.curve}
    (hX : X ≠ 0) (hY : Y ≠ 0) (hxy : X.x ≠ Y.x) :
    Orchard.Specs.Sinsemilla.incompleteAdd X Y = some (X + Y) := by
  rw [Orchard.Specs.Sinsemilla.incompleteAdd,
    if_neg (by push_neg; exact ⟨hX, hY, hxy⟩)]

/-- A non-degenerate double-and-add step on a small positive multiple of the base:
`([m]P ⸭ (2k-1)P) ⸭ [m]P = [2m + 2k - 1]P`. -/
private theorem step_nsmul {P : SWPoint Pallas.curve} (hP : P ≠ 0) (bits : ℕ → Bool)
    {m : ℕ} (h2 : 2 ≤ m) (hBound : 2 * m + 1 < PALLAS_SCALAR_CARD) (b : ℕ) :
    Orchard.Specs.Sinsemilla.step (stepPoint P bits) (m • P) b
      = some ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P) := by
  have hA0 : m • P ≠ 0 := Ecc.pallas_nsmul_ne_zero hP (by omega) (by omega)
  have hxm1 : (m • P).x ≠ P.x := by
    have h := Ecc.pallas_nsmul_x_ne hP (s := 1) (t := m) (by omega) (by omega) (by omega)
    rwa [one_nsmul] at h
  rw [Orchard.Specs.Sinsemilla.step, stepPoint]
  by_cases hb : bits b
  · rw [if_pos hb,
      incompleteAdd_some hA0 hP hxm1,
      show m • P + P = (m + 1) • P from by rw [succ_nsmul],
      Option.bind_some,
      incompleteAdd_some (Ecc.pallas_nsmul_ne_zero hP (by omega) (by omega)) hA0
        (Ecc.pallas_nsmul_x_ne hP (s := m) (t := m + 1) (by omega) (by omega) (by omega)),
      ← add_nsmul]
    rw [if_pos hb]
    norm_num
    congr 1
    omega
  · rw [if_neg hb,
      incompleteAdd_some hA0 (neg_ne_zero.mpr hP) hxm1,
      show m • P + -P = (m - 1) • P from by
        have hm : m • P = (m - 1) • P + P := by
          rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
        rw [hm, add_neg_cancel_right],
      Option.bind_some,
      incompleteAdd_some (Ecc.pallas_nsmul_ne_zero hP (by omega) (by omega)) hA0
        (Ne.symm (Ecc.pallas_nsmul_x_ne hP (s := m - 1) (t := m) (by omega) (by omega)
          (by omega))),
      ← add_nsmul]
    rw [if_neg hb]
    norm_num
    congr 1
    omega

/-! ### Circuit -/

/-- The six cells assigned by one loop iteration of `double_and_add`, in source
assignment order. A plain expression-level bag; never evaluated as a unit. -/
structure RowCells (F : Type) where
  z : F
  xP : F
  yP : F
  lambda1 : F
  lambda2 : F
  xANext : F

def main (n : ℕ) (input : Var Input Fp) :
    Circuit Fp (Var (Output (n + 1)) Fp) := do
  -- copy the starting running sum, x_a, and y_a (the latter into the lambda_1 column)
  let z₀ <== input.z
  let xA₀ <== input.xA
  let yA₀ <== input.yA
  -- the loop rows, witnessed in source assignment order: z, x_p, y_p, λ1, λ2, next x_a
  let rows ← Circuit.mapFinRange (n + 1) fun (r : Fin (n + 1)) => do
    let z ← witnessField fun env => zRunValue (env input.z) (input.bits env) r.val
    let xP ← witnessField fun env => env input.base.x
    let yP ← witnessField fun env => env input.base.y
    let l1 ← witnessField fun env =>
      (rowLambdaValue (env input.base.x) (env input.base.y) (env input.xA)
        (env input.yA) (input.bits env) r.val).lambda1
    let l2 ← witnessField fun env =>
      (rowLambdaValue (env input.base.x) (env input.base.y) (env input.xA)
        (env input.yA) (input.bits env) r.val).lambda2
    let xANext ← witnessField fun env =>
      (accVal (env input.base.x) (env input.base.y) (env input.xA) (env input.yA)
        (input.bits env) (r.val + 1)).1
    return ({ z, xP, yP, lambda1 := l1, lambda2 := l2, xANext } : RowCells (Expression Fp))
  -- the first row's x_p, y_p cells are copies of `base` (CircuitVersion::AnchoredBase);
  -- the q_mul_2 constancy checks propagate the anchor to every row
  (rows[0]'(by omega)).xP === input.base.x
  (rows[0]'(by omega)).yP === input.base.y
  -- the witnessed final y_a
  let yAFinal ← witnessField fun env =>
    (accVal (env input.base.x) (env input.base.y) (env input.xA) (env input.yA)
      (input.bits env) (n + 1)).2
  -- the double-and-add row structs (x_a chained from the copied accumulator)
  let dRow : Fin (n + 1) → Var Sinsemilla.DoubleAndAddRow Fp := fun r =>
    { xA := if _ : r.val = 0 then xA₀ else (rows[r.val - 1]'(by omega)).xANext,
      xP := (rows[r.val]'r.isLt).xP,
      lambda1 := (rows[r.val]'r.isLt).lambda1,
      lambda2 := (rows[r.val]'r.isLt).lambda2 }
  let zPrevOf : Fin (n + 1) → Expression Fp := fun r =>
    if _ : r.val = 0 then z₀ else (rows[r.val - 1]'(by omega)).z
  -- q_mul_1: the copied y_a is the derived y of the first row
  Init.circuit { yAWitnessed := yA₀, next := dRow ⟨0, by omega⟩ }
  -- q_mul_2 on rows 0..n-1
  let gateRows : Vector (Var MainLoop.Row Fp) n := .ofFn fun i =>
    { toRow := {
        zCur := (rows[i.val]'(by have := i.isLt; omega)).z,
        zPrev := zPrevOf ⟨i.val, by omega⟩,
        cur := dRow ⟨i.val, by omega⟩,
        xANext := (rows[i.val]'(by have := i.isLt; omega)).xANext,
        yPCur := (rows[i.val]'(by have := i.isLt; omega)).yP,
        yANextDouble := Sinsemilla.DoubleAndAdd.yA (dRow ⟨i.val + 1, by omega⟩) },
      xPNext := (rows[i.val + 1]'(by have := i.isLt; omega)).xP,
      yPNext := (rows[i.val + 1]'(by have := i.isLt; omega)).yP }
  Circuit.forEach gateRows MainLoop.circuit
  -- q_mul_3 on the last row
  Loop.circuit {
    zCur := (rows[n]'(by omega)).z, zPrev := zPrevOf ⟨n, by omega⟩,
    cur := dRow ⟨n, by omega⟩,
    xANext := (rows[n]'(by omega)).xANext,
    yPCur := (rows[n]'(by omega)).yP,
    yANextDouble := 2 * yAFinal }
  return { xA := (rows[n]'(by omega)).xANext, yA := yAFinal, zs := rows.map (·.z) }

instance elaborated (n : ℕ) : ElaboratedCircuit Fp Input (Output (n + 1)) (main n) := by
  elaborate_circuit

/-- Soundness contract. The constraints pin a bit sequence through the running-sum
chain, and — for any base/accumulator interpretation satisfying the incomplete-addition
preconditions — force the output accumulator to be the double-and-add result. -/
def Spec (n : ℕ) (input : Value Input Fp)
    (output : Output (n + 1) Fp) (_ : ProverData Fp) : Prop :=
  ∃ bits : ℕ → Bool,
    (output.zs[0] = 2 * input.z + (if bits 0 then 1 else 0) ∧
      ∀ b : Fin n, output.zs[b.val + 1] =
        2 * output.zs[b.val]'(by have := b.isLt; omega) +
          (if bits (b.val + 1) then 1 else 0)) ∧
    ∀ (P : SWPoint Pallas.curve) (m : ℕ),
      P ≠ 0 →
      (input.base.x, input.base.y) = (P.x, P.y) →
      (input.xA, input.yA) = ((m • P).x, (m • P).y) →
      2 ≤ m → 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254 →
      (output.xA, output.yA) =
        ((accScalar m bits (n + 1) • P).x, (accScalar m bits (n + 1) • P).y)

def ProverAssumptions (n : ℕ) (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  ∃ (P : SWPoint Pallas.curve) (m : ℕ),
    P ≠ 0 ∧ (input.base.x, input.base.y) = (P.x, P.y) ∧
    (input.xA, input.yA) = ((m • P).x, (m • P).y) ∧
    2 ≤ m ∧ 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254

def ProverSpec (n : ℕ) (input : ProverValue Input Fp) (output : Output (n + 1) Fp)
    (_ : ProverHint Fp) : Prop :=
  (∀ b : Fin (n + 1), output.zs[b.val] = zRunValue input.z input.bits b.val) ∧
  ∀ (P : SWPoint Pallas.curve) (m : ℕ),
    P ≠ 0 →
    (input.base.x, input.base.y) = (P.x, P.y) →
    (input.xA, input.yA) = ((m • P).x, (m • P).y) →
    2 ≤ m → 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254 →
    (output.xA, output.yA) =
      ((accScalar m input.bits (n + 1) • P).x, (accScalar m input.bits (n + 1) • P).y)

private theorem accScalar_two_le {m : ℕ} (h2 : 2 ≤ m) (bits : ℕ → Bool) :
    ∀ b, 2 ≤ accScalar m bits b
  | 0 => h2
  | b + 1 => by
    have ih := accScalar_two_le h2 bits b
    simp only [accScalar]
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb] <;> norm_num <;> omega

private theorem accScalar_le {m : ℕ} (bits : ℕ → Bool) :
    ∀ b, accScalar m bits b ≤ 2 ^ b * (m + 1) - 1
  | 0 => by simp [accScalar]
  | b + 1 => by
    have ih := accScalar_le (m := m) bits b
    have hpos : 0 < 2 ^ b * (m + 1) := by positivity
    have hsplit : 2 ^ (b + 1) * (m + 1) = 2 * (2 ^ b * (m + 1)) := by ring
    simp only [accScalar]
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb] <;> norm_num <;> omega

private theorem pow254_lt_card : 2 ^ 254 < PALLAS_SCALAR_CARD := by
  norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]

/-- The witnessed `z` cell of loop row `r`. -/
private def rowZ (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6)

/-- The `x_a` cell entering row `r`: the copied accumulator for row 0, the previous
row's witnessed `x_a'` afterwards. -/
private def rowXA (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  if r = 0 then env.get (i₀ + 1)
  else env.get (i₀ + 1 + 1 + 1 + (r - 1) * 6 + 1 + 1 + 1 + 1 + 1)

/-- The `x_p` cell of row `r` (row 0's is the anchored copy of `base.x`). -/
private def rowXP (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1)

/-- The `y_p` cell of row `r` (row 0's is the anchored copy of `base.y`). -/
private def rowYP (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1 + 1)

/-- The `λ₁` cell of row `r`. -/
private def rowL1 (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1 + 1 + 1)

/-- The `λ₂` cell of row `r`. -/
private def rowL2 (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1 + 1 + 1 + 1)

/-- The double-and-add row struct of row `r`. -/
private def rowD (env : Environment Fp) (i₀ r : ℕ) : Sinsemilla.DoubleAndAddRow Fp :=
  { xA := rowXA env i₀ r, xP := rowXP env i₀ r,
    lambda1 := rowL1 env i₀ r, lambda2 := rowL2 env i₀ r }

/--
The chain induction of variable-base double-and-add over cleaned row facts:
`XA, XP, YP, L1, L2` are the per-row cell values, `YAD r` the derived `Y_A` expression
value of row `r` (with `YAD (n+1)` the witnessed doubled final `y`), and `bits` the bit
values. Splitting this from `soundness` keeps each declaration within the elaboration
budget.
-/
private theorem soundness_aux (n : ℕ) (P : SWPoint Pallas.curve) (hP : P ≠ 0)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (XA XP YP L1 L2 YAD : ℕ → Fp) (bits : ℕ → Bool)
    (hxA0 : XA 0 = (m • P).x)
    (hYAD0 : YAD 0 = 2 * (m • P).y)
    (hyad : ∀ r, r ≤ n → YAD r = (L1 r + L2 r) * (XA r - (L1 r * L1 r - XA r - XP r)))
    (hxp : ∀ r, r ≤ n → XP r = P.x)
    (hyp : ∀ r, r ≤ n → YP r = P.y)
    (hg1 : ∀ r, r ≤ n → 2 * L1 r * (XA r - XP r) +
      2 * (((if bits r then 1 else 0) * 2 - 1) * YP r) = YAD r)
    (hsec : ∀ r, r ≤ n → L2 r * L2 r
      = XA (r + 1) + (L1 r * L1 r - XA r - XP r) + XA r)
    (hg2 : ∀ r, r ≤ n → 2 * L2 r * (XA r - XA (r + 1)) = YAD r + YAD (r + 1)) :
    XA (n + 1) = (accScalar m bits (n + 1) • P).x ∧
      YAD (n + 1) = 2 * (accScalar m bits (n + 1) • P).y := by
  -- the inductive invariant: row r enters with the accumulator `[accScalar m bits r] P`
  suffices hinv : ∀ r, r ≤ n + 1 →
      XA r = (accScalar m bits r • P).x ∧ YAD r = 2 * (accScalar m bits r • P).y by
    exact hinv (n + 1) (by omega)
  intro r hr
  induction r with
  | zero => exact ⟨hxA0, hYAD0⟩
  | succ v ih =>
    obtain ⟨ihx, ihy⟩ := ih (by omega)
    have hv : v ≤ n := by omega
    -- bounds on the accumulated multiplier
    have hMle : accScalar m bits v ≤ 2 ^ v * (m + 1) - 1 := accScalar_le bits v
    have hM2 : 2 ≤ accScalar m bits v := accScalar_two_le h2 bits v
    have hpow : 2 ^ v * (m + 1) ≤ 2 ^ (n + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hMbound : 2 * accScalar m bits v + 1 < PALLAS_SCALAR_CARD := by
      have h254 := pow254_lt_card
      have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
      omega
    -- the non-degenerate spec-level step
    have hstep := step_nsmul hP bits hM2 hMbound v
    -- the entering accumulator point
    set M := accScalar m bits v with hM
    have hA0 : M • P ≠ 0 :=
      Ecc.pallas_nsmul_ne_zero hP (by omega) (by omega)
    -- the row equations in step_pinned's shape
    have hstepXP : XP v = (stepPoint P bits v).x := by
      rw [hxp v hv]
      unfold stepPoint
      rcases Bool.dichotomy (bits v) with hb | hb <;> rw [hb]
      · rfl
      · rfl
    have hstepYP : 2 * (M • P).y - 2 * L1 v * ((M • P).x - XP v)
        = 2 * (stepPoint P bits v).y := by
      have h := hg1 v hv
      rw [← ihx]
      unfold stepPoint
      rcases Bool.dichotomy (bits v) with hb | hb <;>
        rw [hb] at h ⊢ <;>
        simp only [Bool.false_eq_true, if_false, if_true] at h ⊢
      · show _ = 2 * (-P).y
        rw [show ((-P : SWPoint Pallas.curve)).y = -P.y from rfl]
        linear_combination -h - ihy - 2 * hyp v hv
      · show _ = 2 * P.y
        linear_combination -h - ihy + 2 * hyp v hv
    have hstepYA : 2 * (M • P).y
        = (L1 v + L2 v) * ((M • P).x - (L1 v * L1 v - (M • P).x - XP v)) := by
      rw [← ihx, ← ihy]
      exact hyad v hv
    have hstepSec : L2 v * L2 v
        = XA (v + 1) + (L1 v * L1 v - (M • P).x - XP v) + (M • P).x := by
      rw [← ihx]
      exact hsec v hv
    have hstepYC : 4 * L2 v * ((M • P).x - XA (v + 1))
        = 4 * (M • P).y + 2 * YAD (v + 1) := by
      have h := hg2 v hv
      rw [← ihx]
      linear_combination 2 * h + 2 * ihy
    have hpinned := Sinsemilla.HashPiece.step_pinned (stepPoint P bits)
      hstep hstepYP hstepXP hstepYA hstepSec hstepYC
    have haccv : accScalar m bits (v + 1) = 2 * M + (if bits v then 1 else 0) * 2 - 1 :=
      rfl
    constructor
    · rw [haccv]
      exact hpinned.1
    · rw [haccv]
      exact hpinned.2

/--
The honest row at a small positive multiple of the base: the gate equations hold for
`lambdaCellsValue`'s cells, and they step the accumulator to `[2m + 2k - 1] P`.
-/
private theorem honest_step {P : SWPoint Pallas.curve} (hP : P ≠ 0) (bits : ℕ → Bool)
    {m : ℕ} (h2 : 2 ≤ m) (hBound : 2 * m + 1 < PALLAS_SCALAR_CARD) (b : ℕ) :
    2 * (m • P).y - 2 * (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 *
        ((m • P).x - P.x)
      = 2 * (stepPoint P bits b).y ∧
    2 * (m • P).y
      = ((lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 +
          (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda2) *
        ((m • P).x -
          ((lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 *
            (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 -
            (m • P).x - P.x)) ∧
    (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).xANext
      = ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P).x ∧
    (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda2 *
        ((m • P).x - (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).xANext) -
        (m • P).y
      = ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P).y := by
  set l := lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b) with hl
  have hA0 : m • P ≠ 0 := Ecc.pallas_nsmul_ne_zero hP (by omega) (by omega)
  have hxne1 : (m • P).x ≠ P.x := by
    have h := Ecc.pallas_nsmul_x_ne hP (s := 1) (t := m) (by omega) (by omega) (by omega)
    rwa [one_nsmul] at h
  have hxne1' : (m • P).x - P.x ≠ 0 := sub_ne_zero.mpr hxne1
  -- λ1 is the chord slope through `[m]P` and `±P`
  have hYP : 2 * (m • P).y - 2 * l.lambda1 * ((m • P).x - P.x)
      = 2 * (stepPoint P bits b).y := by
    rw [hl]
    unfold stepPoint lambdaCellsValue
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb] <;> simp only [if_true]
    · show _ = 2 * (-P).y
      rw [show ((-P : SWPoint Pallas.curve)).y = -P.y from rfl]
      field_simp
      norm_num
    · field_simp
      ring
  -- the first incomplete addition: `x_R` is the x-coordinate of `[m ± 1] P`
  have hyPval : (if bits b then P.y else -P.y) = (stepPoint P bits b).y := by
    unfold stepPoint
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb]
    · rfl
    · rfl
  have hstep := step_nsmul hP bits h2 hBound b
  -- the spec-level step is two incomplete additions; recover the intermediate point
  rw [Orchard.Specs.Sinsemilla.step] at hstep
  have hS0 : stepPoint P bits b ≠ 0 := by
    unfold stepPoint
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb]
    · exact neg_ne_zero.mpr hP
    · exact hP
  have hxSP : (stepPoint P bits b).x = P.x := by
    unfold stepPoint
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb]
    · rfl
    · rfl
  rw [incompleteAdd_some hA0 hS0 (by rw [hxSP]; exact hxne1), Option.bind_some] at hstep
  set R := m • P + stepPoint P bits b with hR
  have hRne : R ≠ 0 ∧ R.x ≠ (m • P).x := by
    constructor
    · intro h0
      rw [Orchard.Specs.Sinsemilla.incompleteAdd, if_pos (Or.inl h0)] at hstep
      simp at hstep
    · intro hx
      rw [Orchard.Specs.Sinsemilla.incompleteAdd, if_pos (Or.inr (Or.inr hx))] at hstep
      simp at hstep
  -- the chord construction lands on `R`
  have hRadd := Ecc.AddIncomplete.outputValue_eq_add
    (input := { p := { x := (m • P).x, y := (m • P).y },
                q := { x := P.x, y := (stepPoint P bits b).y } })
    (by
      intro h
      apply hA0
      apply SWPoint.ext_pair
      have hx := congrArg Ecc.Point.x h
      have hy := congrArg Ecc.Point.y h
      simp only [Ecc.Point.zero] at hx hy
      rw [show ((0 : SWPoint Pallas.curve).x, (0 : SWPoint Pallas.curve).y)
        = ((0 : Fp), (0 : Fp)) from rfl, hx, hy])
    (by
      intro h
      apply hS0
      apply SWPoint.ext_pair
      have hx := congrArg Ecc.Point.x h
      have hy := congrArg Ecc.Point.y h
      simp only [Ecc.Point.zero] at hx hy
      rw [show ((0 : SWPoint Pallas.curve).x, (0 : SWPoint Pallas.curve).y)
        = ((0 : Fp), (0 : Fp)) from rfl, hxSP, hx, hy])
    hxne1
  rw [show (({ x := (m • P).x, y := (m • P).y } : Ecc.Point Fp)).coords
      = ((m • P).x, (m • P).y) from rfl,
    show (({ x := P.x, y := (stepPoint P bits b).y } : Ecc.Point Fp)).coords
      = ((stepPoint P bits b).x, (stepPoint P bits b).y) from by rw [hxSP]; rfl,
    Pallas.add_coords, ← hR] at hRadd
  have hlam1 : l.lambda1 = ((m • P).y - (stepPoint P bits b).y) / ((m • P).x - P.x) := by
    rw [hl, ← hyPval]
    rfl
  have hxne2 : P.x - (m • P).x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne1)
  have hRx : l.lambda1 * l.lambda1 - (m • P).x - P.x = R.x := by
    have h := congrArg Prod.fst hRadd
    simp only [Ecc.AddIncomplete.outputValue, Ecc.Point.coords] at h
    rw [← h, hlam1]
    field_simp
    ring
  have hxRne : (m • P).x - (l.lambda1 * l.lambda1 - (m • P).x - P.x) ≠ 0 := by
    rw [hRx]
    exact sub_ne_zero.mpr fun h => hRne.2 h.symm
  -- λ2's defining identity
  have hlam2 : l.lambda2
      = 2 * (m • P).y / ((m • P).x - (l.lambda1 * l.lambda1 - (m • P).x - P.x))
        - l.lambda1 := by
    rw [hl]
    rfl
  have hYA : 2 * (m • P).y
      = (l.lambda1 + l.lambda2) *
        ((m • P).x - (l.lambda1 * l.lambda1 - (m • P).x - P.x)) := by
    rw [hlam2]
    have hD : (m • P).x - (l.lambda1 ^ 2 - (m • P).x - P.x) ≠ 0 := by
      rw [pow_two]
      exact hxRne
    field_simp
    ring
  -- pin the outputs with the row engine
  have hpinned := Sinsemilla.HashPiece.step_pinned (stepPoint P bits)
    (step_nsmul hP bits h2 hBound b)
    (xp := P.x) (lambda1 := l.lambda1) (lambda2 := l.lambda2)
    (xa' := l.xANext)
    (YA' := 2 * (l.lambda2 * ((m • P).x - l.xANext) - (m • P).y))
    hYP (by rw [hxSP]) hYA
    (by rw [hl]; unfold lambdaCellsValue; ring)
    (by ring)
  refine ⟨hYP, hYA, hpinned.1, ?_⟩
  have h := hpinned.2
  exact mul_left_cancel₀ Add.pallas_two_ne_zero h

theorem soundness (n : ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main n) (fun _ _ => True)
      (Spec n) := by
  circuit_proof_start [main, Spec, Init.circuit, Init.Spec, MainLoop.circuit, MainLoop.Spec,
    Loop.circuit, Loop.Spec]
  obtain ⟨h_z0, h_xA0, h_yA0, h_xP0, h_yP0, h_init, h_loop, h_last⟩ := h_holds
  have hchain_of_bool : ∀ zP zN : Fp, IsBool (zN - zP * 2) →
      zN = 2 * zP + (if decide (zN = 2 * zP + 1) = true then 1 else 0) := by
    intro zP zN hb
    rcases hb with h | h
    · have hz : zN = 2 * zP := by linear_combination h
      have hcond : ¬(zN = 2 * zP + 1) := by
        rw [hz]
        intro hc
        exact one_ne_zero (α := Fp) (by linear_combination -hc)
      simp [hz]
    · have hz : zN = 2 * zP + 1 := by linear_combination h
      simp [hz]
  have hrow : ∀ (j : ℕ) (hj : j < n),
      rowXP env i₀ j = rowXP env i₀ (j + 1) ∧
      rowYP env i₀ j = rowYP env i₀ (j + 1) ∧
      IsBool (rowZ env i₀ j -
        (if j = 0 then input_z else rowZ env i₀ (j - 1)) * 2) ∧
      2 * rowL1 env i₀ j * (rowXA env i₀ j - rowXP env i₀ j) +
        2 * (((rowZ env i₀ j -
          (if j = 0 then input_z else rowZ env i₀ (j - 1)) * 2) * 2 - 1) *
            rowYP env i₀ j)
        = yADouble (rowD env i₀ j) ∧
      rowL2 env i₀ j * rowL2 env i₀ j
        = rowXA env i₀ (j + 1) +
          Sinsemilla.DoubleAndAdd.xR (rowD env i₀ j) +
          rowXA env i₀ j ∧
      2 * rowL2 env i₀ j * (rowXA env i₀ j - rowXA env i₀ (j + 1))
        = yADouble (rowD env i₀ j) + yADouble (rowD env i₀ (j + 1)) := by
    intro j hj
    have h := h_loop ⟨j, hj⟩
    simp only [Vector.get] at h
    rcases j with _ | j'
    · norm_num at h
      simp only [circuit_norm, Expression.eval, Loop.bit, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR] at h
      rw [show env.get i₀ = input_z from h_z0] at h
      simp only [rowZ, rowXA, rowXP, rowYP, rowL1, rowL2, rowD, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
      norm_num at h ⊢
      refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_, ?_⟩
      · linear_combination h.2.2.2.1
      · linear_combination h.2.2.2.2.1
      · linear_combination h.2.2.2.2.2
    · norm_num at h
      simp only [circuit_norm, Expression.eval, Loop.bit, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR] at h
      simp only [rowZ, rowXA, rowXP, rowYP, rowL1, rowL2, rowD, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
      norm_num at h ⊢
      refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_, ?_⟩
      · linear_combination h.2.2.2.1
      · linear_combination h.2.2.2.2.1
      · linear_combination h.2.2.2.2.2
  refine ⟨fun b => decide (env.get (i₀ + 1 + 1 + 1 + b * 6)
    = (2 * if b = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (b - 1) * 6)) + 1),
    ⟨?_, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain ⟨h_lb, h_lrest⟩ := h_last
      norm_num at h_lb
      simp only [Loop.bit, Expression.eval] at h_lb
      rw [show env.get i₀ = input_z from h_z0] at h_lb
      simpa using hchain_of_bool _ _ h_lb
    · have h := (hrow 0 hn).2.2.1
      simp only [rowZ] at h
      simpa using hchain_of_bool _ _ h
  · intro b
    obtain ⟨bv, hbvlt⟩ := b
    rcases Nat.lt_or_ge (bv + 1) n with hb | hb
    · have h := (hrow (bv + 1) hb).2.2.1
      simp only [rowZ, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at h
      simpa using hchain_of_bool _ _ h
    · have hbn : bv + 1 = n := by omega
      subst hbn
      obtain ⟨h_lb, h_lrest⟩ := h_last
      norm_num at h_lb
      have h := hchain_of_bool _ _ h_lb
      simpa using h
  · intro Pt mm hPt hbase hacc h2m hbnd
    -- the last row's gate facts
    obtain ⟨hlb, hlg1, hlsec, hlg2⟩ := h_last
    norm_num at hlb hlg1 hlsec hlg2
    simp only [circuit_norm, Expression.eval, Loop.bit, yADouble,
      apply_ite (Expression.eval env), Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR] at hlb hlg1 hlsec hlg2
    norm_num at h_init
    -- inputs in point coordinates
    obtain ⟨hbx, hby⟩ : Expression.eval env input_var.base.x = Pt.x ∧
        Expression.eval env input_var.base.y = Pt.y := by
      have h := h_input.1
      constructor
      · rw [show Expression.eval env input_var.base.x = input_base.x from by rw [← h]]
        exact congrArg Prod.fst hbase
      · rw [show Expression.eval env input_var.base.y = input_base.y from by rw [← h]]
        exact congrArg Prod.snd hbase
    obtain ⟨haccx, haccy⟩ : input_xA = (mm • Pt).x ∧ input_yA = (mm • Pt).y :=
      ⟨congrArg Prod.fst hacc, congrArg Prod.snd hacc⟩
    -- base-point constancy along the rows
    have hconst : ∀ r, r ≤ n → rowXP env i₀ r = Pt.x ∧ rowYP env i₀ r = Pt.y := by
      intro r
      induction r with
      | zero =>
        intro _
        constructor
        · rw [show rowXP env i₀ 0 = env.get (i₀ + 1 + 1 + 1 + 0 * 6 + 1) from rfl,
            h_xP0, hbx]
        · rw [show rowYP env i₀ 0 = env.get (i₀ + 1 + 1 + 1 + 0 * 6 + 1 + 1) from rfl,
            h_yP0, hby]
      | succ v ih =>
        intro hv
        obtain ⟨hx, hy⟩ := ih (by omega)
        obtain ⟨hcx, hcy, -⟩ := hrow v (by omega)
        exact ⟨by rw [← hcx]; exact hx, by rw [← hcy]; exact hy⟩
    -- the per-row bit values, decidably
    have hbiteq : ∀ r, r ≤ n →
        env.get (i₀ + 1 + 1 + 1 + r * 6) -
          (if r = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (r - 1) * 6)) * 2 =
        (if (decide (env.get (i₀ + 1 + 1 + 1 + r * 6)
          = (2 * if r = 0 then input_z
              else env.get (i₀ + 1 + 1 + 1 + (r - 1) * 6)) + 1)) = true
          then 1 else 0) := by
      intro r hr
      have hb : IsBool (env.get (i₀ + 1 + 1 + 1 + r * 6) -
          (if r = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (r - 1) * 6)) * 2) := by
        rcases Nat.lt_or_ge r n with h | h
        · have hb' := (hrow r h).2.2.1
          simp only [rowZ] at hb'
          exact hb'
        · have hrn : r = n := by omega
          subst hrn
          rcases Nat.eq_zero_or_pos r with h0 | h0
          · subst h0
            rw [if_pos rfl]
            rw [show input_z = env.get i₀ from h_z0.symm]
            simpa using hlb
          · rw [if_neg (by omega)]
            simpa [if_neg (Nat.pos_iff_ne_zero.mp h0)] using hlb
      have hch := hchain_of_bool _ _ hb
      linear_combination hch
    -- assemble the chain induction
    have haux := soundness_aux n Pt hPt mm h2m hbnd
      (rowXA env i₀) (rowXP env i₀) (rowYP env i₀) (rowL1 env i₀) (rowL2 env i₀)
      (fun r => if r = n + 1 then
          2 * env.get (i₀ + 1 + 1 + 1 + (n + 1) * 6)
        else yADouble (rowD env i₀ r))
      (fun b => decide (env.get (i₀ + 1 + 1 + 1 + b * 6)
        = (2 * if b = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (b - 1) * 6)) + 1))
      ?hxA0 ?hYAD0 ?hyad ?hxp ?hyp ?hg1 ?hsec ?hg2
    case hxA0 =>
      rw [show rowXA env i₀ 0 = env.get (i₀ + 1) from if_pos rfl, h_xA0, haccx]
    case hYAD0 =>
      simp only []
      rw [if_neg (by omega)]
      simp only [Expression.eval, yADouble, Sinsemilla.DoubleAndAdd.yA,
        Sinsemilla.DoubleAndAdd.xR] at h_init
      simp only [rowD, rowXA, rowXP, rowL1, rowL2, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
      norm_num
      rw [← haccy, ← h_yA0]
      linear_combination -h_init
    case hyad =>
      intro r hr
      simp only []
      rw [if_neg (by omega)]
      simp only [yADouble, Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR, rowD]
      try ring
    case hxp => exact fun r hr => (hconst r hr).1
    case hyp => exact fun r hr => (hconst r hr).2
    case hg1 =>
      intro r hr
      simp only []
      rw [if_neg (show ¬(r = n + 1) by omega)]
      have hbit := hbiteq r hr
      rw [← hbit]
      rcases Nat.lt_or_ge r n with h | h
      · have hg := (hrow r h).2.2.2.1
        simp only [rowZ] at hg ⊢
        exact hg
      · have hrn : r = n := by omega
        subst hrn
        simp only [rowD, rowXA, rowXP, rowYP, rowL1, rowL2, yADouble,
          Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · subst h0
          norm_num
          rw [show input_z = env.get i₀ from h_z0.symm]
          norm_num at hlg1
          linear_combination hlg1
        · simp only [if_neg (Nat.pos_iff_ne_zero.mp h0)] at hlg1 ⊢
          linear_combination hlg1
    case hsec =>
      intro r hr
      rcases Nat.lt_or_ge r n with h | h
      · exact (hrow r h).2.2.2.2.1
      · have hrn : r = n := by omega
        subst hrn
        simp only [rowXA, rowXP, rowL1, rowL2]
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · subst h0
          norm_num
          norm_num at hlsec
          linear_combination hlsec
        · simp only [if_neg (Nat.pos_iff_ne_zero.mp h0), if_neg (Nat.succ_ne_zero r),
            Nat.add_sub_cancel] at hlsec ⊢
          linear_combination hlsec
    case hg2 =>
      intro r hr
      simp only []
      rcases Nat.lt_or_ge r n with h | h
      · rw [if_neg (show ¬(r = n + 1) by omega), if_neg (show ¬(r + 1 = n + 1) by omega)]
        exact (hrow r h).2.2.2.2.2
      · have hrn : r = n := by omega
        subst hrn
        rw [if_neg (show ¬(r = r + 1) by omega), if_pos rfl]
        simp only [rowD, rowXA, rowXP, rowL1, rowL2, yADouble,
          Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · subst h0
          norm_num
          norm_num at hlg2
          linear_combination hlg2
        · simp only [if_neg (Nat.pos_iff_ne_zero.mp h0), if_neg (Nat.succ_ne_zero r),
            Nat.add_sub_cancel] at hlg2 ⊢
          linear_combination hlg2
    obtain ⟨hx, hy⟩ := haux
    simp only [rowXA, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at hx
    rw [if_pos rfl] at hy
    exact Prod.ext hx (mul_left_cancel₀ Add.pallas_two_ne_zero hy)


theorem completeness (n : ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main n) (ProverAssumptions n)
      (ProverSpec n) := by
  sorry

/-- `incomplete.rs::Config::<{n+1}>::double_and_add` (`CircuitVersion::AnchoredBase`).
Instantiated at `n = 124` for the `hi` half and `n = 125` for the `lo` half. -/
def circuit (n : ℕ) :
    GeneralFormalCircuit.WithHint Fp Input (Output (n + 1)) where
  main := main n
  Spec := Spec n
  ProverAssumptions := ProverAssumptions n
  ProverSpec := ProverSpec n
  soundness := soundness n
  completeness := completeness n

end DoubleAndAdd

end Orchard.Ecc.ScalarMul.Mul.Incomplete
