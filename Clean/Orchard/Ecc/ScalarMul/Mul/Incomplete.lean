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

Note on cell order: the z running-sum cells are witnessed as one block up front instead
of interleaved per row; Clean's linear witness tape does not model the source's
column/row grid, and the conformance map already records this layout gap.
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
  let xR := lambda1 ^ 2 - xA - baseX
  let lambda2 := 2 * yA / (xA - xR) - lambda1
  { lambda1, lambda2, xANext := lambda2 ^ 2 - xA - xR }

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

def main (n : ℕ) (input : Var Input Fp) :
    Circuit Fp (Var (Output (n + 1)) Fp) := do
  -- copy the starting running sum, y_a (into the lambda_1 column), and x_a
  let z₀ <== input.z
  let yA₀ <== input.yA
  let xA₀ <== input.xA
  -- the interstitial running-sum cells of all n + 1 bits
  let zs ← witnessVector (n + 1) fun env =>
    .ofFn fun (b : Fin (n + 1)) => zRunValue (env input.z) (input.bits env) b.val
  let zsAll := Vector.cast (Nat.add_comm 1 (n + 1))
    ((#v[z₀] : Vector (Expression Fp) 1) ++ zs)
  -- first row: x_p, y_p are anchored to `base` (CircuitVersion::AnchoredBase)
  let xP₀ <== input.base.x
  let yP₀ <== input.base.y
  -- later rows' x_p, y_p cells; the q_mul_2 constancy checks pin them to the anchor
  let xPs ← witnessVector n fun env => .ofFn fun _ => env input.base.x
  let yPs ← witnessVector n fun env => .ofFn fun _ => env input.base.y
  -- the lambda cells and next-row x_a cells of every row
  let l1s ← witnessVector (n + 1) fun env =>
    .ofFn fun (r : Fin (n + 1)) =>
      (rowLambdaValue (env input.base.x) (env input.base.y) (env input.xA)
        (env input.yA) (input.bits env) r.val).lambda1
  let l2s ← witnessVector (n + 1) fun env =>
    .ofFn fun (r : Fin (n + 1)) =>
      (rowLambdaValue (env input.base.x) (env input.base.y) (env input.xA)
        (env input.yA) (input.bits env) r.val).lambda2
  let xAs ← witnessVector (n + 1) fun env =>
    .ofFn fun (r : Fin (n + 1)) =>
      (accVal (env input.base.x) (env input.base.y) (env input.xA) (env input.yA)
        (input.bits env) (r.val + 1)).1
  -- the witnessed final y_a
  let yAFinal ← witnessField fun env =>
    (accVal (env input.base.x) (env input.base.y) (env input.xA) (env input.yA)
      (input.bits env) (n + 1)).2
  -- the double-and-add row structs (x_a chained from the copied accumulator)
  let dRow : Fin (n + 1) → Var Sinsemilla.DoubleAndAddRow Fp := fun r =>
    { xA := if _ : r.val = 0 then xA₀ else xAs[r.val - 1]'(by omega),
      xP := if _ : r.val = 0 then xP₀ else xPs[r.val - 1]'(by omega),
      lambda1 := l1s[r.val]'(r.isLt),
      lambda2 := l2s[r.val]'(r.isLt) }
  let yPof : Fin (n + 1) → Expression Fp := fun r =>
    if _ : r.val = 0 then yP₀ else yPs[r.val - 1]'(by omega)
  -- q_mul_1: the copied y_a is the derived y of the first row
  Init.circuit { yAWitnessed := yA₀, next := dRow ⟨0, by omega⟩ }
  -- q_mul_2 on rows 0..n-1
  let gateRows : Vector (Var MainLoop.Row Fp) n := .ofFn fun i =>
    { toRow := {
        zCur := zsAll[i.val + 1]'(by have := i.isLt; omega),
        zPrev := zsAll[i.val]'(by have := i.isLt; omega),
        cur := dRow ⟨i.val, by omega⟩,
        xANext := xAs[i.val]'(by have := i.isLt; omega),
        yPCur := yPof ⟨i.val, by omega⟩,
        yANextDouble := Sinsemilla.DoubleAndAdd.yA (dRow ⟨i.val + 1, by omega⟩) },
      xPNext := (dRow ⟨i.val + 1, by omega⟩).xP,
      yPNext := yPof ⟨i.val + 1, by omega⟩ }
  Circuit.forEach gateRows MainLoop.circuit
  -- q_mul_3 on the last row
  Loop.circuit {
    zCur := zsAll[n + 1]'(by omega), zPrev := zsAll[n]'(by omega),
    cur := dRow ⟨n, by omega⟩,
    xANext := xAs[n]'(by omega),
    yPCur := yPof ⟨n, by omega⟩,
    yANextDouble := 2 * yAFinal }
  return { xA := xAs[n]'(by omega), yA := yAFinal, zs }

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

/-- The running-sum cells of the circuit, named: `zsAll[0]` is the copied `z` and
`zsAll[b+1]` is the witnessed cell of bit `b`. Stated over an abstract `v` so the
`getElem`s elaborate. -/
private theorem zsAll_get (i₀ n : ℕ) (v : Vector (Expression Fp) (1 + (n + 1)))
    (hv : v = (#v[var { index := i₀ }] : Vector (Expression Fp) 1) ++
      (Vector.mapRange (n + 1) fun i => var { index := i₀ + 1 + 1 + 1 + i } :
        Vector (Expression Fp) (n + 1))) :
    v[0]'(by omega) = var { index := i₀ } ∧
    ∀ (b : ℕ) (hb : b < n + 1), v[b + 1]'(by omega) = var { index := i₀ + 1 + 1 + 1 + b } := by
  subst hv
  constructor
  · simp [Vector.getElem_append]
  · intro b hb
    simp [Vector.getElem_append, Vector.getElem_mapRange]

/-- The evaluation of an arbitrary running-sum cell, as a value-level conditional. -/
private theorem zsAll_get_at (env : Environment Fp) (i₀ n : ℕ)
    (v : Vector (Expression Fp) (1 + (n + 1)))
    (hv : v = (#v[var { index := i₀ }] : Vector (Expression Fp) 1) ++
      (Vector.mapRange (n + 1) fun i => var { index := i₀ + 1 + 1 + 1 + i } :
        Vector (Expression Fp) (n + 1)))
    (b : ℕ) (hb : b < n + 2) :
    Expression.eval env (v[b]'(by omega))
      = if b = 0 then env.get i₀ else env.get (i₀ + 1 + 1 + 1 + (b - 1)) := by
  subst hv
  rcases b with _ | b'
  · simp only [Vector.getElem_append]
    norm_num
    rfl
  · rw [if_neg (by omega)]
    simp only [Vector.getElem_append, Vector.getElem_mapRange]
    norm_num
    rfl

/-- The `x_a` cell entering row `r`: the copied accumulator for row 0, the previous
row's witnessed `x_a'` afterwards. -/
private def rowXA (env : Environment Fp) (i₀ n : ℕ) (r : ℕ) : Fp :=
  if r = 0 then env.get (i₀ + 1 + 1)
  else env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + n + n + (n + 1) + (n + 1) + (r - 1))

/-- The `x_p` cell of row `r`: the anchored copy for row 0, witnessed afterwards. -/
private def rowXP (env : Environment Fp) (i₀ n : ℕ) (r : ℕ) : Fp :=
  if r = 0 then env.get (i₀ + 1 + 1 + 1 + (n + 1))
  else env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + (r - 1))

/-- The `y_p` cell of row `r`. -/
private def rowYP (env : Environment Fp) (i₀ n : ℕ) (r : ℕ) : Fp :=
  if r = 0 then env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1)
  else env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + n + (r - 1))

/-- The `λ₁` cell of row `r`. -/
private def rowL1 (env : Environment Fp) (i₀ n : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + n + n + r)

/-- The `λ₂` cell of row `r`. -/
private def rowL2 (env : Environment Fp) (i₀ n : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + n + n + (n + 1) + r)

/-- The double-and-add row struct of row `r`. -/
private def rowD (env : Environment Fp) (i₀ n r : ℕ) : Sinsemilla.DoubleAndAddRow Fp :=
  { xA := rowXA env i₀ n r, xP := rowXP env i₀ n r,
    lambda1 := rowL1 env i₀ n r, lambda2 := rowL2 env i₀ n r }

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
  sorry

theorem soundness (n : ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main n) (fun _ _ => True)
      (Spec n) := by
  circuit_proof_start [main, Spec, Init.circuit, Init.Spec, MainLoop.circuit, MainLoop.Spec,
    Loop.circuit, Loop.Spec]
  obtain ⟨h_z0, h_yA0, h_xA0, h_xP0, h_yP0, h_init, h_loop, h_last⟩ := h_holds
  obtain ⟨hzs0, hzsS⟩ := zsAll_get i₀ n _ rfl
  have hchain_of_bool : ∀ zP zN : Fp, IsBool (zN - zP * 2) →
      zN = 2 * zP + (if decide (zN = 2 * zP + 1) = true then 1 else 0) := by
    intro zP zN hb
    rcases hb with h | h
    · have hz : zN = 2 * zP := by linear_combination h
      have hcond : ¬(zN = 2 * zP + 1) := by
        rw [hz]
        intro hc
        exact one_ne_zero (α := Fp) (by linear_combination -hc)
      simp [hcond, hz]
    · have hz : zN = 2 * zP + 1 := by linear_combination h
      simp [hz]
  have hrow : ∀ (j : ℕ) (hj : j < n),
      rowXP env i₀ n j = rowXP env i₀ n (j + 1) ∧
      rowYP env i₀ n j = rowYP env i₀ n (j + 1) ∧
      IsBool (env.get (i₀ + 1 + 1 + 1 + j) -
        (if j = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (j - 1))) * 2) ∧
      2 * rowL1 env i₀ n j * (rowXA env i₀ n j - rowXP env i₀ n j) +
        2 * (((env.get (i₀ + 1 + 1 + 1 + j) -
          (if j = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (j - 1))) * 2) * 2 - 1) *
            rowYP env i₀ n j)
        = yADouble (rowD env i₀ n j) ∧
      rowL2 env i₀ n j * rowL2 env i₀ n j
        = rowXA env i₀ n (j + 1) +
          Sinsemilla.DoubleAndAdd.xR (rowD env i₀ n j) +
          rowXA env i₀ n j ∧
      2 * rowL2 env i₀ n j * (rowXA env i₀ n j - rowXA env i₀ n (j + 1))
        = yADouble (rowD env i₀ n j) + yADouble (rowD env i₀ n (j + 1)) := by
    intro j hj
    have h := h_loop ⟨j, hj⟩
    simp only [Vector.get, Vector.getElem_ofFn, Fin.val_mk] at h
    rcases j with _ | j'
    · norm_num [Vector.getElem_append, Vector.getElem_mapRange] at h
      rw [show Expression.eval env (var { index := i₀ }) = input_z from h_z0] at h
      simp only [circuit_norm, Expression.eval, Loop.bit, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR] at h
      simp only [rowXA, rowXP, rowYP, rowL1, rowL2, rowD, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
      norm_num at h ⊢
      refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_, ?_⟩
      · linear_combination h.2.2.2.1
      · linear_combination h.2.2.2.2.1
      · linear_combination h.2.2.2.2.2
    · norm_num [Vector.getElem_append, Vector.getElem_mapRange] at h
      simp only [circuit_norm, Expression.eval, Loop.bit, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR] at h
      simp only [rowXA, rowXP, rowYP, rowL1, rowL2, rowD, yADouble,
        Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
      norm_num at h ⊢
      refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_, ?_⟩
      · linear_combination h.2.2.2.1
      · linear_combination h.2.2.2.2.1
      · linear_combination h.2.2.2.2.2
  refine ⟨fun b => decide (env.get (i₀ + 1 + 1 + 1 + b)
    = (2 * if b = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (b - 1))) + 1),
    ⟨?_, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain ⟨h_lb, h_lrest⟩ := h_last
      rw [hzsS 0 (by omega), hzs0,
        show Expression.eval env (var { index := i₀ }) = input_z from h_z0] at h_lb
      simpa using hchain_of_bool _ _ h_lb
    · have h := (hrow 0 hn).2.2.1
      simp only [if_pos rfl] at h
      simpa using hchain_of_bool _ _ h
  · intro b
    obtain ⟨bv, hbvlt⟩ := b
    simp only [Fin.val_mk]
    rcases Nat.lt_or_ge (bv + 1) n with hb | hb
    · have h := (hrow (bv + 1) hb).2.2.1
      try simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at h
      simpa using hchain_of_bool _ _ h
    · have hbn : bv + 1 = n := by omega
      subst hbn
      obtain ⟨h_lb, h_lrest⟩ := h_last
      rw [hzsS (bv + 1) (by omega), hzsS bv (by omega)] at h_lb
      have h := hchain_of_bool _ _ h_lb
      simpa using h
  · intro Pt mm hPt hbase hacc h2m hbnd
    -- the last row's gate facts
    obtain ⟨hlb, hlg1, hlsec, hlg2⟩ := h_last
    norm_num [Vector.getElem_append, Vector.getElem_mapRange, Nat.lt_one_iff]
      at hlb hlg1 hlsec hlg2
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
    have hconst : ∀ r, r ≤ n → rowXP env i₀ n r = Pt.x ∧ rowYP env i₀ n r = Pt.y := by
      intro r
      induction r with
      | zero =>
        intro _
        constructor
        · rw [show rowXP env i₀ n 0 = env.get (i₀ + 1 + 1 + 1 + (n + 1)) from if_pos rfl,
            h_xP0, hbx]
        · rw [show rowYP env i₀ n 0 = env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1) from if_pos rfl,
            h_yP0, hby]
      | succ v ih =>
        intro hv
        obtain ⟨hx, hy⟩ := ih (by omega)
        obtain ⟨hcx, hcy, -⟩ := hrow v (by omega)
        exact ⟨by rw [← hcx]; exact hx, by rw [← hcy]; exact hy⟩
    -- the per-row bit values, decidably
    have hbiteq : ∀ r, r ≤ n →
        env.get (i₀ + 1 + 1 + 1 + r) -
          (if r = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (r - 1))) * 2 =
        (if (decide (env.get (i₀ + 1 + 1 + 1 + r)
          = (2 * if r = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (r - 1))) + 1)) = true
          then 1 else 0) := by
      intro r hr
      have hb : IsBool (env.get (i₀ + 1 + 1 + 1 + r) -
          (if r = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (r - 1))) * 2) := by
        rcases Nat.lt_or_ge r n with h | h
        · exact (hrow r h).2.2.1
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
      (rowXA env i₀ n) (rowXP env i₀ n) (rowYP env i₀ n) (rowL1 env i₀ n) (rowL2 env i₀ n)
      (fun r => if r = n + 1 then
          2 * env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + n + n + (n + 1) + (n + 1) + (n + 1))
        else yADouble (rowD env i₀ n r))
      (fun b => decide (env.get (i₀ + 1 + 1 + 1 + b)
        = (2 * if b = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (b - 1))) + 1))
      ?hxA0 ?hYAD0 ?hyad ?hxp ?hyp ?hg1 ?hsec ?hg2
    case hxA0 =>
      rw [show rowXA env i₀ n 0 = env.get (i₀ + 1 + 1) from if_pos rfl, h_xA0, haccx]
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
      rw [if_neg (show ¬(r = n + 1) by omega), ← hbiteq r hr]
      rcases Nat.lt_or_ge r n with h | h
      · exact (hrow r h).2.2.2.1
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
        · simp only [if_neg (Nat.pos_iff_ne_zero.mp h0), if_neg (Nat.succ_ne_zero r),
            Nat.add_sub_cancel] at hlg1 ⊢
          linear_combination hlg1
    case hsec =>
      intro r hr
      rcases Nat.lt_or_ge r n with h | h
      · exact (hrow r h).2.2.2.2.1
      · have hrn : r = n := by omega
        subst hrn
        simp only [rowD, rowXA, rowXP, rowYP, rowL1, rowL2, yADouble,
          Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
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
        simp only [rowD, rowXA, rowXP, rowYP, rowL1, rowL2, yADouble,
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
