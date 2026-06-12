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

/-- The cells freshly witnessed for each later row. -/
structure IterCells (F : Type) where
  xP : F
  yP : F
  lambda1 : F
  lambda2 : F
  xANext : F
deriving ProvableStruct

/-- Loop state: the previous row's cells and the previous row's `x_a`. -/
structure LoopState (F : Type) where
  prev : IterCells F
  xA : F
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

/-- The derived accumulator y-coordinate of a row: `y_A = Y_A / 2` where
`Y_A = (λ1 + λ2)(x_A − x_R)`. -/
def yAValue (c : IterCells Fp) (xA : Fp) : Fp :=
  ((c.lambda1 + c.lambda2) * (xA - (c.lambda1 ^ 2 - xA - c.xP))) / 2

/-- The accumulator y-coordinate after a row: `y_A' = λ2(x_A − x_A') − y_A`. -/
def yANextValue (c : IterCells Fp) (xA : Fp) : Fp :=
  c.lambda2 * (xA - c.xANext) - yAValue c xA

/-- Honest lambda cells of one double-and-add row, from the accumulator `(x_a, y_a)`
entering the row and the row's bit. The assigned `x_p, y_p` cells always hold the base
coordinates; the conditional negation `(2k-1) y_p` only enters `λ1`. -/
def lambdaCellsValue (baseX baseY xA yA : Fp) (bit : Bool) : LambdaCells Fp :=
  let yP := if bit then baseY else -baseY
  let lambda1 := (yA - yP) / (xA - baseX)
  let xR := lambda1 ^ 2 - xA - baseX
  let lambda2 := 2 * yA / (xA - xR) - lambda1
  { lambda1, lambda2, xANext := lambda2 ^ 2 - xA - xR }

/-- Honest cells of one later double-and-add row. -/
def iterCellsValue (baseX baseY xA yA : Fp) (bit : Bool) : IterCells Fp :=
  let l := lambdaCellsValue baseX baseY xA yA bit
  { xP := baseX, yP := baseY, lambda1 := l.lambda1, lambda2 := l.lambda2,
    xANext := l.xANext }

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
  let w₀ : Var LambdaCells Fp ← witness fun env =>
    lambdaCellsValue (env input.base.x) (env input.base.y)
      (env input.xA) (env input.yA) (input.bits env 0)
  -- q_mul_1: the copied y_a is the derived y of the first row
  Init.circuit {
    yAWitnessed := yA₀,
    next := { xA := xA₀, xP := xP₀, lambda1 := w₀.lambda1, lambda2 := w₀.lambda2 } }
  let s₁ : Var LoopState Fp := {
    prev := { xP := xP₀, yP := yP₀, lambda1 := w₀.lambda1, lambda2 := w₀.lambda2,
              xANext := w₀.xANext },
    xA := xA₀ }
  -- rows 1..n: witness the row, then close the previous row with q_mul_2
  let sLast ← Circuit.foldlRange n s₁ fun s i => do
    let w : Var IterCells Fp ← witness fun env =>
      iterCellsValue (env input.base.x) (env input.base.y)
        (env s.prev.xANext) (yANextValue (eval env s.prev) (env s.xA))
        (input.bits env (i.val + 1))
    MainLoop.circuit {
      toRow := {
        zCur := zsAll[i.val + 1]'(by have := i.isLt; omega),
        zPrev := zsAll[i.val]'(by have := i.isLt; omega),
        cur := { xA := s.xA, xP := s.prev.xP,
                 lambda1 := s.prev.lambda1, lambda2 := s.prev.lambda2 },
        xANext := s.prev.xANext, yPCur := s.prev.yP,
        yANextDouble := Sinsemilla.DoubleAndAdd.yA
          { xA := s.prev.xANext, xP := w.xP, lambda1 := w.lambda1, lambda2 := w.lambda2 } },
      xPNext := w.xP, yPNext := w.yP }
    return { prev := w, xA := s.prev.xANext }
  -- witness the final y_a, then close the last row with q_mul_3
  let yAFinal ← witnessField fun env =>
    yANextValue (eval env sLast.prev) (env sLast.xA)
  Loop.circuit {
    zCur := zsAll[n + 1]'(by omega), zPrev := zsAll[n]'(by omega),
    cur := { xA := sLast.xA, xP := sLast.prev.xP,
             lambda1 := sLast.prev.lambda1, lambda2 := sLast.prev.lambda2 },
    xANext := sLast.prev.xANext, yPCur := sLast.prev.yP,
    yANextDouble := 2 * yAFinal }
  return { xA := sLast.prev.xANext, yA := yAFinal, zs }

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

/-- The `x_a` cell entering row `j` (the copied accumulator for row 0, the previous
iteration's `x_a'` cell afterwards). -/
private def rowXA (env : Environment Fp) (i₀ n : ℕ) : ℕ → Fp
  | 0 => env.get (i₀ + 1 + 1)
  | j + 1 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + 3 + j * 5 + 1 + 1 + 1 + 1)

/-- The `x_p` cell of row `j`. -/
private def rowXP (env : Environment Fp) (i₀ n : ℕ) : ℕ → Fp
  | 0 => env.get (i₀ + 1 + 1 + 1 + (n + 1))
  | j + 1 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + 3 + j * 5)

/-- The `y_p` cell of row `j`. -/
private def rowYP (env : Environment Fp) (i₀ n : ℕ) : ℕ → Fp
  | 0 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1)
  | j + 1 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + 3 + j * 5 + 1)

/-- The `λ₁` cell of row `j`. -/
private def rowL1 (env : Environment Fp) (i₀ n : ℕ) : ℕ → Fp
  | 0 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1)
  | j + 1 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + 3 + j * 5 + 1 + 1)

/-- The `λ₂` cell of row `j`. -/
private def rowL2 (env : Environment Fp) (i₀ n : ℕ) : ℕ → Fp
  | 0 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + 1)
  | j + 1 => env.get (i₀ + 1 + 1 + 1 + (n + 1) + 1 + 1 + 3 + j * 5 + 1 + 1 + 1)

/-- The double-and-add row struct of row `j`. -/
private def rowD (env : Environment Fp) (i₀ n j : ℕ) : Sinsemilla.DoubleAndAddRow Fp :=
  { xA := rowXA env i₀ n j, xP := rowXP env i₀ n j,
    lambda1 := rowL1 env i₀ n j, lambda2 := rowL2 env i₀ n j }

theorem soundness (n : ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main n) (fun _ _ => True)
      (Spec n) := by
  circuit_proof_start [main, Spec, Init.circuit, Init.Spec, MainLoop.circuit, MainLoop.Spec,
    Loop.circuit, Loop.Spec]
  obtain ⟨h_z0, h_yA0, h_xA0, h_xP0, h_yP0, h_init, h_loop, h_last⟩ := h_holds
  -- name the running-sum cells
  obtain ⟨hzs0, hzsS⟩ := zsAll_get i₀ n _ rfl
  -- the bit of row `b`, read off the running-sum cells
  refine ⟨fun b => decide (env.get (i₀ + 1 + 1 + 1 + b)
    = 2 * (if b = 0 then input_z else env.get (i₀ + 1 + 1 + 1 + (b - 1))) + 1),
    ⟨?_, ?_⟩, ?_⟩
  all_goals
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
      simp only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Circuit.FoldlM.foldlAcc,
        Vector.getElem_finRange, Fin.val_mk, circuit_norm] at h
      rcases j with _ | j'
      · simp only [Fin.foldl_zero] at h
        rw [hzsS 0 (by omega), hzs0,
          show Expression.eval env (var { index := i₀ }) = input_z from h_z0] at h
        try simp only [if_pos rfl]
        sorry
      · try simp only [Fin.foldl_const, Fin.val_last] at h
        rw [hzsS (j' + 1) (by omega), hzsS j' (by omega)] at h
        try simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        sorry
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain ⟨h_lb, h_lrest⟩ := h_last
      rw [hzsS 0 (by omega), hzs0,
        show Expression.eval env (var { index := i₀ }) = input_z from h_z0] at h_lb
      simpa using hchain_of_bool _ _ h_lb
    · have h := (hrow 0 hn).2.2.1
      try simp only [if_pos rfl] at h
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
  · sorry

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
