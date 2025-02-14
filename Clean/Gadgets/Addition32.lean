import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Clean.Utils.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Gadgets.Addition8
import Clean.Gadgets.Addition8Full

/-
  32-bit addition gadget
-/
namespace Addition32
open Expression
variable {p : ℕ} [p_is_prime: Fact p.Prime] [p_large_enough: Fact (p > 512)]

def Limbs4 (N : ℕ+) (M p: ℕ) :=
  Expression N M (F p)
  × Expression N M (F p)
  × Expression N M (F p)
  × Expression N M (F p)

def Limbs4.get (N : ℕ+) (M p: ℕ) (x : Limbs4 N M p) : ℕ -> Expression N M (F p)
  | 0 => x.fst
  | 1 => x.snd.fst
  | 2 => x.snd.snd.fst
  | 3 => x.snd.snd.snd
  | _ => 0

def Limbs4.value (N : ℕ+) (M p: ℕ) (x : Limbs4 N M p) (trace: TraceOfLength N M (F p)) : ℕ :=
  (trace.eval (x.get 0)).val +
  256 * (trace.eval (x.get 1)).val +
  256^2 * (trace.eval (x.get 2)).val +
  256^3 * (trace.eval (x.get 3)).val

def circuit (N : ℕ+) (M : ℕ) (x y out carries : Limbs4 N M p) : ConstraintGadget p N M :=
  ⟨
    [],
    [],
    [
      /-
        he circuit is composed of one half-adder and three full-adders
        The carries are shared between the full-adders
      -/
      Addition8.circuit N M (x.get 0) (y.get 0) (out.get 0) (carries.get 0),
      Addition8Full.circuit N M (x.get 1) (y.get 1) (out.get 1) (carries.get 0) (carries.get 1),
      Addition8Full.circuit N M (x.get 2) (y.get 2) (out.get 2) (carries.get 1) (carries.get 2),
      Addition8Full.circuit N M (x.get 3) (y.get 3) (out.get 3) (carries.get 2) (carries.get 3)
    ]
  ⟩

def spec (N : ℕ+) (M : ℕ) (x y out _carries : Limbs4 N M p) : TraceOfLength N M (F p) -> Prop :=
  (fun trace =>
      have x := x.value trace
      have y := y.value trace
      have out := out.value trace

      -- the output is correct
      (out = (x + y) % 2^32)

      -- TODO: add all the other props that are necessary for completeness
      )

def soundness (N : ℕ+) (M : ℕ) (x0 x1 x2 x3 y0 y1 y2 y3 out0 out1 out2 out3 c0 c1 c2 c3 : ℕ)
    (h : out0 = (x0 + y0) % 256
    ∧ c0 = (x0 + y0) / 256
    ∧ out1 = (c0 + x1 + y1) % 256
    ∧ c1 = (c0 + x1 + y1) / 256
    ∧ out2 = (c1 + x2 + y2) % 256
    ∧ c2 = (c1 + x2 + y2) / 256
    ∧ out3 = (c2 + x3 + y3) % 256
    ∧ c3 = (c2 + x3 + y3) / 256)

    : out0 + 256 * out1 + 256^2 * out2 + 256^3 * out3 =
      (
        (x0 + 256 * x1 + 256^2 * x2 + 256^3 * x3)
        + (y0 + 256 * y1 + 256^2 * y2 + 256^3 * y3)
      ) % 2^32
  := by
  -- TODO: Clean things up a bit
  -- Prove equality from right-hand side to left-hand side as it's more convenient
  symm

  -- Unpack the hypothesis 'h' into individual equalities
  rcases h with ⟨h_out0, h_c0, h_out1, h_c1, h_out2, h_c2, h_out3, h_c3⟩

  -- Prove Euclidean division equalities
  have eq0 : x0 + y0 = 256 * c0 + out0 := by
    rw [h_out0, h_c0]
    symm
    exact Nat.div_add_mod (x0 + y0) 256

  have eq1 : c0 + x1 + y1 = 256 * c1 + out1 := by
    rw [h_out1, h_c1]
    symm
    exact Nat.div_add_mod (c0 + x1 + y1) 256

  have eq2 : c1 + x2 + y2 = 256 * c2 + out2 := by
    rw [h_out2, h_c2]
    symm
    exact Nat.div_add_mod (c1 + x2 + y2) 256

  have eq3 : c2 + x3 + y3 = 256 * c3 + out3 := by
    rw [h_out3, h_c3]
    symm
    exact Nat.div_add_mod (c2 + x3 + y3) 256

  -- Rewrite eq1, eq2, eq3 so that the LHS of all Euclidean division equalities
  -- is of the form x_i + y_i
  have eq1_min_c0 : x1 + y1 = 256 * c1 + out1 - c0 := by
    refine Nat.eq_sub_of_add_eq' ?eq1
    rw [← add_assoc]
    exact eq1

  have eq2_min_c1 : x2 + y2 = 256 * c2 + out2 - c1 := by
    refine Nat.eq_sub_of_add_eq' ?eq2
    rw [← add_assoc]
    exact eq2

  have eq3_min_c2 : x3 + y3 = 256 * c3 + out3 - c2 := by
    refine Nat.eq_sub_of_add_eq' ?eq3
    rw [← add_assoc]
    exact eq3

  -- Prove that 256 * ci + outi - c(i-1) >= 0 for all i
  have c1_out1_c0_ge_0 : 256 * c1 + out1 - c0 >= 0 := by
    rw [← eq1, add_assoc, add_comm, Nat.add_sub_cancel]
    linarith

  have c2_out2_c1_ge_0 : 256 * c2 + out2 - c1 >= 0 := by
    rw [← eq2, add_assoc, add_comm, Nat.add_sub_cancel]
    linarith

  have c3_out3_c2_ge_0 : 256 * c3 + out3 - c2 >= 0 := by
    rw [← eq3, add_assoc, add_comm, Nat.add_sub_cancel]
    linarith

  -- Prove that 256 * ci + outi >= c(i-1) for all i
  have c1_out1_ge_c0 : 256 * c1 + out1 >= c0 := by
    linarith

  have c2_out2_ge_c1 : 256 * c2 + out2 >= c1 := by
    linarith

  have c3_out3_ge_c2 : 256 * c3 + out3 >= c2 := by
    linarith

  -- Prove that out_i < 256 for all i (required for linarith to work later)
  have h_out0' : out0 < 256 := by
    rw [h_out0]
    apply Nat.mod_lt
    norm_num

  have h_out1' : out1 < 256 := by
    rw [h_out1]
    apply Nat.mod_lt
    norm_num

  have h_out2' : out2 < 256 := by
    rw [h_out2]
    apply Nat.mod_lt
    norm_num

  have h_out3' : out3 < 256 := by
    rw [h_out3]
    apply Nat.mod_lt
    norm_num

  -- Express LHS of goal in terms of x_i + y_i
  -- Group x_0 + y_0
  rw [← add_assoc, ← add_assoc, ← add_assoc]
  nth_rewrite 5 [add_assoc]
  nth_rewrite 4 [add_comm]
  rw [← add_assoc, ← add_assoc, ← add_assoc]
  nth_rewrite 7 [add_comm]
  -- Group x_1 + y_1
  nth_rewrite 6 [add_comm]
  nth_rewrite 3 [add_comm]
  rw [← add_assoc, ← add_assoc, ← add_assoc]
  nth_rewrite 6 [add_comm]
  rw [← mul_add]
  -- Group x_2 + y_2
  nth_rewrite 2 [add_comm]
  nth_rewrite 4 [add_comm]
  rw [← add_assoc, ← add_assoc, ← add_assoc]
  nth_rewrite 5 [add_comm]
  rw [← mul_add]
  -- Group x_3 + y_3
  rw [add_assoc, ← mul_add]

  -- Replace x_i + y_i using eq0 and eq_i_min_c(i-1)
  simp only [eq0, eq1_min_c0, eq2_min_c1, eq3_min_c2]

  -- Helper lemmas to prove eq4
  have eq41 : 256^4 = 256^3 * 256 := rfl
  have eq42 : 256^3 = 256^2 * 256 := rfl
  have eq43 : 256^2 = 256 * 256 := rfl

  have cast1 : (Nat.cast (256 * c2 + out2 - c1) : ℤ) = 256 * Nat.cast c2 + Nat.cast out2 - Nat.cast c1:= by
    apply Nat.cast_sub
    linarith

  have cast2 : (Nat.cast (256 * c1 + out1 - c0) : ℤ) = 256 * Nat.cast c1 + Nat.cast out1 - Nat.cast c0:= by
    apply Nat.cast_sub
    linarith

  have cast3 : (Nat.cast (256 * c3 + out3 - c2) : ℤ) = 256 * Nat.cast c3 + Nat.cast out3 - Nat.cast c2:= by
    apply Nat.cast_sub
    linarith

  -- Simplify, multiply out parenthesis, and cancel terms
  have eq4 :
  256 ^ 2 * (256 * c2 + out2 - c1)
  + 256 * (256 * c1 + out1 - c0)
  + (256 * c0 + out0)
  + 256 ^ 3 * (256 * c3 + out3 - c2)
  = 256 ^ 4 * c3
  + 256 ^ 3 * out3
  + 256 ^ 2 * out2
  + 256 * out1
  + out0 := by
    zify
    rw [cast1, cast2, cast3]
    ring

  -- Apply eq4 and rearrange terms
  rw [eq4]
  rw [add_comm]
  nth_rewrite 2 [add_comm]
  nth_rewrite 3 [add_comm]
  nth_rewrite 4 [add_comm]
  rw [← add_assoc, ← add_assoc, ← add_assoc]

  -- Show that 2^32 = 256^4
  have eq5 : 2^32 = 256^4 := by norm_num

  -- Replace 256^4 with 2^32
  rw [eq5]

  -- Cancel c3 term
  rw [Nat.add_mod]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mul_mod]
  rw [Nat.mod_self]
  rw [zero_mul, Nat.zero_mod, add_zero]

  -- Convert goal to: "Show out0 + 256 * out1 + 256 ^ 2 * out2 + 256 ^ 3 * out3 < 256^4 for all out_i"
  refine Nat.mod_eq_of_lt ?intro.intro.intro.intro.intro.intro.intro.h

  -- Solve one of the subgoals using linarith
  linarith

  -- Solve remaining subgoal
  rw [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, add_zero]
  apply Nat.mod_lt
  norm_num

theorem equiv (N : ℕ+) (M : ℕ) (x y out carries : Limbs4 N M p) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y out carries)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y out carries)) (fun constraint => X.eval constraint = 0))
      ↔
      spec N M x y out carries X
    )
  ) := by
  intro X


  -- TODO: ideally this whole block would be a tactic, this just
  -- substitutes all the constraints of the sub gadgets into the corresponding spec
  rw [fullConstraintSetGroupedEquivalence, circuit]
  simp [ByteLookup.lookup, fullConstraintSetGrouped, forallList, fullConstraintSetGrouped.foldl]

  intros hx0 hy0 hout0 hx1 hy1 hout1 hx2 hy2 hout2 hx3 hy3 hout3

  let equivAdd0 := Addition8.equiv N M (x.get 0) (y.get 0) (out.get 0) (carries.get 0) X
  simp [forallList, ByteLookup.lookup, Addition8.spec] at equivAdd0
  specialize equivAdd0 hx0 hy0 hout0
  rw [equivAdd0]

  let equivAdd1 := Addition8Full.equiv N M (x.get 1) (y.get 1) (out.get 1) (carries.get 0) (carries.get 1) X
  simp [forallList, ByteLookup.lookup, Addition8Full.spec] at equivAdd1
  specialize equivAdd1 hx1 hy1 hout1
  rw [equivAdd1]

  let equivAdd2 := Addition8Full.equiv N M (x.get 2) (y.get 2) (out.get 2) (carries.get 1) (carries.get 2) X
  simp [forallList, ByteLookup.lookup, Addition8Full.spec] at equivAdd2
  specialize equivAdd2 hx2 hy2 hout2
  rw [equivAdd2]

  let equivAdd3 := Addition8Full.equiv N M (x.get 3) (y.get 3) (out.get 3) (carries.get 2) (carries.get 3) X
  simp [forallList, ByteLookup.lookup, Addition8Full.spec] at equivAdd3
  specialize equivAdd3 hx3 hy3 hout3
  rw [equivAdd3]

  -- expand the spec
  rw [spec]
  simp [Limbs4.value]

  -- simplify a bit the statement
  set x0 := ZMod.val (X.eval (x.get 0))
  set x1 := ZMod.val (X.eval (x.get 1))
  set x2 := ZMod.val (X.eval (x.get 2))
  set x3 := ZMod.val (X.eval (x.get 3))
  set y0 := ZMod.val (X.eval (y.get 0))
  set y1 := ZMod.val (X.eval (y.get 1))
  set y2 := ZMod.val (X.eval (y.get 2))
  set y3 := ZMod.val (X.eval (y.get 3))
  set out0 := ZMod.val (X.eval (out.get 0))
  set out1 := ZMod.val (X.eval (out.get 1))
  set out2 := ZMod.val (X.eval (out.get 2))
  set out3 := ZMod.val (X.eval (out.get 3))
  set c0 := ZMod.val (X.eval (carries.get 0))
  set c1 := ZMod.val (X.eval (carries.get 1))
  set c2 := ZMod.val (X.eval (carries.get 2))
  set c3 := ZMod.val (X.eval (carries.get 3))

  -- at this point the entire statement is lifted and is about limbs
  -- and carries over ℕ, so we have to prove the actual relation
  constructor
  -- soundness
  · intro h
    have s := soundness N M x0 x1 x2 x3 y0 y1 y2 y3 out0 out1 out2 out3 c0 c1 c2 c3 (by sorry)
    simp at s
    exact s

  -- completeness
  · sorry


instance (N M : ℕ+) (x y out carries : Limbs4 N M p) : Constraint N M p :=
{
  circuit := circuit N M x y out carries,
  spec := spec N M x y out carries,
  equiv := equiv N M x y out carries
}

end Addition32
