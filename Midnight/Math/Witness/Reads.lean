import Clean.Halo2.WitnessIR

/-! A decidable read discipline for the scalar witness IR used by source Halo2
circuits. Unsupported constructors are rejected, including native callbacks,
main-Clean tape/data reads and local variables. External hints are explicit.
The semantic theorem proves that accepted programs depend only on allowed cells
and the supplied hint; it does not assume the program's output equation. -/
namespace Midnight.Math.Witness.Reads

variable {F V Env : Type}

mutual
 def field (allowed : V → Bool) : Witgen.FExprOver F V → Bool
  | .expr cell => allowed cell
  | .const _ => true
  | .add a b | .mul a b => field allowed a && field allowed b
  | .inv a => field allowed a
  | .ofU64 a => nat allowed a
  | .hintGet _ _ row _ => nat allowed row
  | _ => false
 def nat (allowed : V → Bool) : Witgen.U64ExprOver F V → Bool
  | .const _ => true
  | .val a => field allowed a
  | .add a b | .mul a b | .div a b | .mod a b | .land a b | .lor a b | .lxor a b
  | .shiftL a b | .shiftR a b => nat allowed a && nat allowed b
  | _ => false
end

section Semantics
variable [FiniteField F] [Witgen.WitgenEnv F Env V]

mutual
 theorem field_congr (allowed : V → Bool) (expression : Witgen.FExprOver F V)
    (accepted : field allowed expression = true)
    (left right : Witgen.CtxOver F Env)
    (cells : ∀ cell, allowed cell = true →
      Witgen.WitgenEnv.readVar (F := F) left.env cell = Witgen.WitgenEnv.readVar (F := F) right.env cell)
    (hints : Witgen.WitgenEnv.hint (F := F) (V := V) left.env = Witgen.WitgenEnv.hint (F := F) (V := V) right.env) :
    expression.eval left = expression.eval right := by
  cases expression with
  | expr cell => exact cells cell accepted
  | const _ => rfl
  | add a b =>
    have both := Bool.and_eq_true_iff.mp accepted
    exact congrArg₂ (· + ·) (field_congr allowed a both.1 left right cells hints)
      (field_congr allowed b both.2 left right cells hints)
  | mul a b =>
    have both := Bool.and_eq_true_iff.mp accepted
    exact congrArg₂ (· * ·) (field_congr allowed a both.1 left right cells hints)
      (field_congr allowed b both.2 left right cells hints)
  | inv a => exact congrArg Inv.inv (field_congr allowed a accepted left right cells hints)
  | ofU64 a =>
    exact congrArg (fun x : UInt64 => FiniteField.fromNat (F := F) x.toNat)
      (nat_congr allowed a accepted left right cells hints)
  | hintGet key n row col =>
    have same := nat_congr allowed row accepted left right cells hints
    simp only [Witgen.FExprOver.eval, same, hints]
  | _ => contradiction
 theorem nat_congr (allowed : V → Bool) (expression : Witgen.U64ExprOver F V)
    (accepted : nat allowed expression = true)
    (left right : Witgen.CtxOver F Env)
    (cells : ∀ cell, allowed cell = true →
      Witgen.WitgenEnv.readVar (F := F) left.env cell = Witgen.WitgenEnv.readVar (F := F) right.env cell)
    (hints : Witgen.WitgenEnv.hint (F := F) (V := V) left.env = Witgen.WitgenEnv.hint (F := F) (V := V) right.env) :
    expression.eval left = expression.eval right := by
  cases expression with
  | const _ => rfl
  | val a =>
    exact congrArg (fun x => UInt64.ofNat (FiniteField.val x)) (field_congr allowed a accepted left right cells hints)
  | add a b | mul a b | div a b | mod a b | land a b | lor a b | lxor a b | shiftL a b | shiftR a b =>
    have both := Bool.and_eq_true_iff.mp accepted
    have ha := nat_congr allowed a both.1 left right cells hints
    have hb := nat_congr allowed b both.2 left right cells hints
    simp only [Witgen.U64ExprOver.eval, ha, hb]
  | _ => contradiction
end

/-- The source scalar programs have an empty local-step list and one expression.
Rejecting all other shapes makes the accepted external dependency set explicit. -/
def program {n : Nat} (allowed : V → Bool) : Witgen.WitgenIROver F Env V n → Bool
  | .ir [] (.lit expressions) => expressions.toArray.all (field allowed)
  | _ => false

theorem program_congr {n : Nat} (allowed : V → Bool) (compute : Witgen.WitgenIROver F Env V n)
    (accepted : program allowed compute = true) (left right : Env)
    (cells : ∀ cell, allowed cell = true →
      Witgen.WitgenEnv.readVar (F := F) left cell = Witgen.WitgenEnv.readVar (F := F) right cell)
    (hints : Witgen.WitgenEnv.hint (F := F) (V := V) left = Witgen.WitgenEnv.hint (F := F) (V := V) right) :
    compute.eval left = compute.eval right := by
  cases compute with
  | native _ => contradiction
  | ir steps out =>
    cases steps with
    | cons _ _ => contradiction
    | nil =>
      cases out with
      | lit expressions =>
        apply Vector.ext
        intro i hi
        have accept : field allowed expressions[i] = true :=
          Array.all_eq_true.mp accepted i (by simpa only [Vector.size_toArray] using hi)
        simpa only [Witgen.WitgenIROver.eval, Witgen.VExprOver.eval, Witgen.evalSteps,
          Vector.getElem_map] using
          field_congr allowed expressions[i] accept {env := left} {env := right} cells hints
      | mapRange _ _ | envRange _ | bitsOf _ | append _ _ => contradiction

end Semantics
end Midnight.Math.Witness.Reads
