import Mathlib.Data.ZMod.Basic
import Clean.Circuit
import Clean.Gadgets.Binius64.SVI
import Clean.Utils.Tactics.CircuitProofStart
import Clean.Utils.Bits

namespace Gadgets.Binius64

open Circuit

def p : ℕ := 2
instance : Fact (Nat.Prime p) := by decide

variable {k m : ShiftKind} {a b : Fin 64}

/-- Inputs to the Binius 64-bit multiplication gadget. -/
structure IMulInputs (k m : ShiftKind) (a b : Fin 64) (F : Type) where
  lhs : SVI k a F
  rhs : SVI m b F

/-- Outputs of the multiplication gadget: low and high parts. -/
structure IMulOutputs (F : Type) where
  low : SVI .sll 0 F
  high : SVI .sll 0 F

instance : ProvableStruct (IMulInputs k m a b) where
  components := [SVI k a, SVI m b]
  toComponents := fun { lhs, rhs } => .cons lhs (.cons rhs .nil)
  fromComponents := fun
    | .cons lhs (.cons rhs .nil) => { lhs, rhs }

instance : ProvableStruct (IMulOutputs) where
  components := [SVI .sll 0, SVI .sll 0]
  toComponents := fun { low, high } => .cons low (.cons high .nil)
  fromComponents := fun
    | .cons low (.cons high .nil) => { low, high }

namespace IMul

variable {α : Type}
variable [Add α] [Sub α] [Mul α]
variable [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 4]
variable [Zero α]

private def fullAdder (a b cin : α) : α × α :=
  let sum := a + b + cin
  let carry := a * b + cin * (a + b)
  (sum, carry)

private def addBitvec : ∀ {n : ℕ}, Vector α n → Vector α n → α →
    Vector α n × α
  | 0, _, _, carry => (#v[], carry)
  | n + 1, xs, ys, carry =>
      let (sumBit, carry') := fullAdder xs.head ys.head carry
      let (rest, nextCarry) :=
        addBitvec (n:=n) xs.tail ys.tail carry'
      (Vector.cons sumBit rest, nextCarry)

private def partialRow
    (lhs rhs : Vector α 64) (shift : Fin 64) :
    Vector α 128 :=
  Vector.ofFn fun idx =>
    if hlt : idx.val < shift.val then
      (0 : α)
    else
      let j := idx.val - shift.val
      if hj : j < 64 then
        let jFin : Fin 64 := ⟨j, hj⟩
        lhs[jFin] * rhs[shift]
      else
        (0 : α)

private def mul64
    (lhs rhs : Vector α 64) : Vector α 128 :=
  let rows :=
    (Vector.finRange 64).map (fun i => partialRow lhs rhs i)
  let init : Vector α 128 := Vector.replicate 128 (0 : α)
  (rows.toList.foldl
    (fun (acc : Vector α 128) row =>
      (addBitvec acc row (0 : α)).1)
    init)

private def split128
    (bits : Vector α 128) : Vector α 64 × Vector α 64 :=
  -- let lo := bits.extract 0 64
  -- let hi := bits.extract 64 128
  -- (hi, lo)
  let lo := Vector.ofFn fun i : Fin 64 =>
    bits[(i.castLT (by
      have h : i.val < 128 :=
        Nat.lt_of_lt_of_le i.isLt (by decide : 64 ≤ 128)
      exact h) : Fin 128)]
  let hi := Vector.ofFn fun i : Fin 64 =>
    bits[(⟨i.val + 64, by
      have h : i.val < 64 := i.isLt
      have : i.val + 64 < 128 := by linarith
      simpa using this⟩ : Fin 128)]
  (hi, lo)

private def unsignedMulExpr
    (lhs rhs : Vector (Expression (F p)) 64) :
    Vector (Expression (F p)) 64 × Vector (Expression (F p)) 64 :=
  split128 (mul64 lhs rhs)

private def unsignedMulVals
    (lhs rhs : Vector (F p) 64) :
    Vector (F p) 64 × Vector (F p) 64 :=
  split128 (mul64 lhs rhs)

private lemma fullAdder_eval
    (env : Environment (F p)) (a b c : Expression (F p)) :
    env ((fullAdder a b c).1) = (fullAdder (env a) (env b) (env c)).1 ∧
      env ((fullAdder a b c).2) = (fullAdder (env a) (env b) (env c)).2 := by
  constructor <;> simp [fullAdder, Expression.eval, eval_add]

private lemma fullAdder_correct
    (a b c : F p) :
    let res := fullAdder a b c
    ZMod.val res.1 + 2 * ZMod.val res.2 =
      ZMod.val a + ZMod.val b + ZMod.val c := by
  -- Over F₂ we can brute force the eight possible inputs.
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private lemma addBitvec_eval
    {n : ℕ} (env : Environment (F p))
    (xs ys : Vector (Expression (F p)) n) (carry : Expression (F p)) :
    let resExpr := addBitvec (α := Expression (F p)) xs ys carry
    let xsVals := Vector.map env xs
    let ysVals := Vector.map env ys
    let resVals := addBitvec (α := F p) xsVals ysVals (env carry)
    Vector.map env resExpr.1 = resVals.1 ∧ env resExpr.2 = resVals.2 := by
  sorry

private lemma addBitvec_correct
    {n : ℕ} (xs ys : Vector (F p) n) (carry : F p) :
    let res := addBitvec (α := F p) xs ys carry
    Utils.Bits.fromBits (Vector.map ZMod.val res.1) +
        2^n * ZMod.val res.2 =
      Utils.Bits.fromBits (Vector.map ZMod.val xs) +
        Utils.Bits.fromBits (Vector.map ZMod.val ys) +
        ZMod.val carry := by
  simp only [Utils.Bits.fromBits, Vector.getElem_map]
  induction n with
  | zero => simp [addBitvec]
  | succ n ih =>
    simp only [addBitvec, Fin.foldl_succ_last,
      Fin.coe_castSucc, Fin.val_last]
    -- ring_nf
    let x := Fin.foldl n (fun x i ↦ x + xs[i.val].val * 2 ^ i.val) 0
    let x' := Fin.foldl n (fun x i ↦ x + xs.pop[i.val].val * 2 ^ i.val) 0
    let y := Fin.foldl n (fun x i ↦ x + ys[i.val].val * 2 ^ i.val) 0
    let y' := Fin.foldl n (fun x i ↦ x + ys.pop[i.val].val * 2 ^ i.val) 0

    have hx : x = x' := by simp [x, x']
    have hy : y = y' := by simp [y, y']

    show _ = (x + xs[n].val * 2 ^ n) + (y + ys[n].val * 2 ^ n) + ZMod.val carry
    rw [hx, hy]

    have h_comm : (x' + xs[n].val * 2 ^ n) + (y' + ys[n].val * 2 ^ n) + ZMod.val carry
      = (x' + y' + ZMod.val carry) +
        xs[n].val * 2 ^ n + ys[n].val * 2 ^ n := by
      sorry
    rw [h_comm]
    let h_ih := ih xs.pop ys.pop
    change _ = x' + y' + ZMod.val carry at h_ih
    rw [←h_ih]
    clear ih h_ih h_comm
    simp only [Vector.cons, Vector.getElem_mk,
      List.getElem_toArray]
    sorry



private lemma partialRow_eval
    (env : Environment (F p))
    (lhs rhs : Vector (Expression (F p)) 64) (shift : Fin 64) :
    Vector.map env (partialRow lhs rhs shift) =
      partialRow (Vector.map env lhs) (Vector.map env rhs) shift := by
  classical
  apply Vector.ext
  intro i hi
  let idx : Fin 128 := ⟨i, hi⟩
  by_cases hlt : i < shift.val
  · simp [partialRow, hlt, Expression.eval_zero]
  · by_cases hj : i - shift.val < 64
    · simp [partialRow, hlt, hj, eval_mul']
    · simp [partialRow, hlt, hj, Expression.eval_zero]

private lemma partialRow_correct
    (lhs rhs : Vector (F p) 64) (shift : Fin 64) (idx : Fin 128) :
    (partialRow lhs rhs shift)[idx] =
      if idx.val < shift.val then (0 : F p)
      else
        let j := idx.val - shift.val
        if hj : j < 64 then lhs[(⟨j, hj⟩ : Fin 64)] * rhs[shift] else (0 : F p) := by
  sorry

private lemma mul64_eval
    (env : Environment (F p)) (lhs rhs : Vector (Expression (F p)) 64) :
    Vector.map env (mul64 lhs rhs) =
      mul64 (Vector.map env lhs) (Vector.map env rhs) := by
  classical
  let f := fun (acc : Vector (Expression (F p)) 128) (row : Vector (Expression (F p)) 128) =>
    (addBitvec acc row (0 : Expression (F p))).1
  let g := fun (acc : Vector (F p) 128) (row : Vector (F p) 128) =>
    (addBitvec acc row (0 : F p)).1
  let rows := (Vector.finRange 64).map (fun i => partialRow lhs rhs i)
  let rows' := (Vector.finRange 64).map (fun i => partialRow (Vector.map env lhs) (Vector.map env rhs) i)
  have hvec : Vector.map (Vector.map env) rows = rows' := by
    ext i
    simp [rows, rows', partialRow_eval, Vector.getElem_map]
  have hrows : rows.toList.map (Vector.map env) = rows'.toList := by
    simpa [Vector.toList_map] using congrArg Vector.toList hvec

  have hf :
      ∀ (acc : Vector (Expression (F p)) 128) (rs : List (Vector (Expression (F p)) 128))
        (rs' : List (Vector (F p) 128)),
        rs.map (Vector.map env) = rs' →
        Vector.map env (rs.foldl f acc) = rs'.foldl g (Vector.map env acc) := by
    intro acc rs
    induction rs generalizing acc with
    | nil =>
        intro rs' hmap
        cases rs' <;> simp at hmap
        simp [f, g]
    | cons r rs ih =>
        intro rs' hmap
        cases rs' with
        | nil => cases hmap
        | cons r' rs' =>
            have hhead : Vector.map env r = r' := by
              have := congrArg List.head? hmap
              simpa using this
            have htail : rs.map (Vector.map env) = rs' := by
              have := congrArg List.tail hmap
              simpa using this
            have hstep := addBitvec_eval (env:=env) (xs:=acc) (ys:=r) (carry:=0)
            have hcarry := hstep.right
            have hvec := hstep.left
            specialize ih ((addBitvec acc r 0).1) rs' htail
            have hvec :
                Vector.map env (f acc r) = g (Vector.map env acc) r' := by
              have hadd := addBitvec_eval (env:=env) (xs:=acc) (ys:=r) (carry:=0)
              simpa [f, g, hhead] using hadd.left
            have hrec :
                Vector.map env (rs.foldl f (f acc r)) =
                  rs'.foldl g (Vector.map env (f acc r)) := ih
            -- combine
            simpa [List.foldl, f, g, hhead, hvec] using hrec

  -- apply the fold lemma to our rows
  have hfold := hf (acc := Vector.replicate 128 (0 : Expression (F p)))
    (rs := rows.toList) (rs' := rows'.toList) hrows
  -- simplify back to mul64
  simpa [mul64, f, g, rows, rows']
    using hfold

private lemma split128_eval
    (env : Environment (F p)) (bits : Vector (Expression (F p)) 128) :
    let res := split128 bits
    let vals := split128 (Vector.map env bits)
    Vector.map env res.1 = vals.1 ∧ Vector.map env res.2 = vals.2 := by
  classical
  dsimp [split128]
  constructor
  · ext i
    simp [Vector.getElem_map, Vector.getElem_ofFn]
  · ext i
    simp [Vector.getElem_map, Vector.getElem_ofFn]

private lemma unsignedMulExpr_eval
    (env : Environment (F p))
    (lhs rhs : Vector (Expression (F p)) 64) :
    let (highExpr, lowExpr) := unsignedMulExpr lhs rhs
    let lhsVals := Vector.map env lhs
    let rhsVals := Vector.map env rhs
    let (highVals, lowVals) := unsignedMulVals lhsVals rhsVals
    Vector.map env highExpr = highVals ∧ Vector.map env lowExpr = lowVals := by
  classical
  dsimp [unsignedMulExpr, unsignedMulVals]
  have hMul := mul64_eval (env := env) lhs rhs
  have hSplit := split128_eval (env := env) (bits := mul64 lhs rhs)
  simpa [hMul] using hSplit

def main (k m : ShiftKind) (a b : Fin 64)
    (input : Var (IMulInputs k m a b) (F p)) :
    Circuit (F p) (Var IMulOutputs (F p)) := do
  let ⟨lhs, rhs⟩ := input
  let lhsShifted ← applyShiftExpr lhs
  let rhsShifted ← applyShiftExpr rhs
  let (highWire, lowWire) := unsignedMulExpr lhsShifted rhsShifted
  return { high := { wire := highWire }, low := { wire := lowWire } }

def Assumptions (_ : IMulInputs k m a b (F p)) : Prop := True

private def bitsToNat64 (v : Vector (F p) 64) : ℕ :=
  Utils.Bits.fromBits (Vector.map ZMod.val v)

private def natToBits128 (n : ℕ) : Vector (F p) 128 :=
  Vector.map (fun x : ℕ  => (x : F p)) (Utils.Bits.toBits 128 n)

private def splitBits128
    (bits : Vector (F p) 128) : Vector (F p) 64 × Vector (F p) 64 :=
  split128 bits

private lemma mul64_correct
    (lhs rhs : Vector (F p) 64) :
    splitBits128 (natToBits128 (bitsToNat64 lhs * bitsToNat64 rhs)) =
      unsignedMulVals lhs rhs := by
  -- placeholder, to be proven
  sorry

def Spec (input : IMulInputs k m a b (F p))
    (output : IMulOutputs (F p)) : Prop :=
  let lhsShift := applyShift input.lhs
  let rhsShift := applyShift input.rhs
  let lhsNat := bitsToNat64 lhsShift
  let rhsNat := bitsToNat64 rhsShift
  let prodBits := natToBits128 (lhsNat * rhsNat)
  let (highVals, lowVals) := splitBits128 prodBits
  output.high.wire = highVals ∧ output.low.wire = lowVals

instance elaborated (k m : ShiftKind) (a b : Fin 64) :
    ElaboratedCircuit (F p) (IMulInputs k m a b) IMulOutputs where
  main := main k m a b
  localLength _ := 0

theorem soundness (k m : ShiftKind) (a b : Fin 64) :
    Soundness (F p) (elaborated (k:=k) (m:=m) (a:=a) (b:=b))
      (Assumptions (k:=k) (m:=m) (a:=a) (b:=b))
      (Spec (k:=k) (m:=m) (a:=a) (b:=b)) := by
  circuit_proof_start
  classical
  have h_eval :=
    unsignedMulExpr_eval (env := env)
      (lhs := (applyShiftExpr input_var.lhs i₀).1)
      (rhs :=
        (applyShiftExpr input_var.rhs
          (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)
  obtain ⟨h_high, h_low⟩ := h_eval
  have hl :
      Vector.map (Expression.eval env) (applyShiftExpr input_var.lhs i₀).1 =
        applyShift
          ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
            SVI k a (F p)) := by
    simp [applyShiftExpr, applyShift, map_eval_applyShiftVec, circuit_norm]
  have hr :
      Vector.map (Expression.eval env)
          (applyShiftExpr input_var.rhs
            (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1 =
        applyShift
          ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
            SVI m b (F p)) := by
    simp [applyShiftExpr, applyShift, map_eval_applyShiftVec, circuit_norm]

  have h_congr_high :
      (unsignedMulVals
          (Vector.map (Expression.eval env) (applyShiftExpr input_var.lhs i₀).1)
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).1 =
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p)))
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
              SVI m b (F p)))).1 := by
    have h₁ :=
      congrArg (fun lhs =>
        (unsignedMulVals lhs
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).1) hl
    have h₂ :=
      congrArg (fun rhs =>
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p))) rhs).1) hr
    simpa [applyShift] using h₁.trans h₂
  have h_congr_low :
      (unsignedMulVals
          (Vector.map (Expression.eval env) (applyShiftExpr input_var.lhs i₀).1)
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).2 =
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p)))
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
              SVI m b (F p)))).2 := by
    have h₁ :=
      congrArg (fun lhs =>
        (unsignedMulVals lhs
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).2) hl
    have h₂ :=
      congrArg (fun rhs =>
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p))) rhs).2) hr
    simpa [applyShift] using h₁.trans h₂

  have h_high' := h_high.trans h_congr_high
  have h_low' := h_low.trans h_congr_low
  have h_nat := mul64_correct
    (lhs := applyShift
      ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
        SVI k a (F p)))
    (rhs := applyShift
      ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
        SVI m b (F p)))
  have h_nat_high :
      (splitBits128
        (natToBits128
          (bitsToNat64
            (applyShift
              ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
                SVI k a (F p)))
          * bitsToNat64
            (applyShift
              ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
                SVI m b (F p)))))).1 =
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p)))
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
              SVI m b (F p)))).1 := by
    simpa using congrArg Prod.fst h_nat
  have h_nat_low :
      (splitBits128
        (natToBits128
          (bitsToNat64
            (applyShift
              ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
                SVI k a (F p)))
          * bitsToNat64
            (applyShift
              ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
                SVI m b (F p)))))).2 =
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p)))
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
              SVI m b (F p)))).2 := by
    simpa using congrArg Prod.snd h_nat

  cases h_input
  refine ?_
  exact And.intro
    (h_high'.trans h_nat_high.symm)
    (h_low'.trans h_nat_low.symm)

theorem completeness (k m : ShiftKind) (a b : Fin 64) :
    Completeness (F p) (elaborated (k:=k) (m:=m) (a:=a) (b:=b))
      (Assumptions) := by
  circuit_proof_start [applyShiftExpr]

def circuit (k m : ShiftKind) (a b : Fin 64) :
    FormalCircuit (F p) (IMulInputs k m a b) IMulOutputs where
  elaborated := elaborated (k:=k) (m:=m) (a:=a) (b:=b)
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness (k:=k) (m:=m) (a:=a) (b:=b)
  completeness := completeness (k:=k) (m:=m) (a:=a) (b:=b)

end IMul

end Gadgets.Binius64
