import Midnight.Math.Witness.Reads

/-! Values-free dependency plans for exactly the witness IR fragment accepted
by `Reads`. Plans retain repeated cell reads in expression order and include
reads used to compute an external hint's row. Unsupported syntax returns `none`;
it is never interpreted as an empty dependency list. -/
namespace Midnight.Math.Witness.Dependencies
variable {F V Env : Type}

/-- Whether every cell in a supported dependency plan is permitted. -/
def accepts (allowed : V → Bool) : Option (List V) → Bool
  | none => false
  | some cells => cells.all allowed

/-- Combining plans preserves failure of either child expression. -/
def join : Option (List V) → Option (List V) → Option (List V)
  | some left, some right => some (left ++ right)
  | _, _ => none

theorem accepts_join (allowed : V → Bool) (left right : Option (List V)) :
    accepts allowed (join left right) = (accepts allowed left && accepts allowed right) := by
  cases left <;> cases right <;> simp [join, accepts, List.all_append]

mutual
 def field : Witgen.FExprOver F V → Option (List V)
  | .expr cell => some [cell]
  | .const _ => some []
  | .add a b | .mul a b => join (field a) (field b)
  | .inv a => field a
  | .ofU64 a => nat a
  | .hintGet _ _ row _ => nat row
  | _ => none
 def nat : Witgen.U64ExprOver F V → Option (List V)
  | .const _ => some []
  | .val a => field a
  | .add a b | .mul a b | .div a b | .mod a b | .land a b | .lor a b | .lxor a b
  | .shiftL a b | .shiftR a b => join (nat a) (nat b)
  | _ => none
end

mutual
 theorem field_eq (allowed : V → Bool) (expression : Witgen.FExprOver F V) :
    Reads.field allowed expression = accepts allowed (field expression) := by
  cases expression with
  | expr _ => simp [Reads.field, field, accepts]
  | const _ => rfl
  | add a b | mul a b =>
    simp only [Reads.field, field, accepts_join, field_eq allowed a, field_eq allowed b]
  | inv a => exact field_eq allowed a
  | ofU64 a => exact nat_eq allowed a
  | hintGet _ _ row _ => exact nat_eq allowed row
  | _ => rfl
 theorem nat_eq (allowed : V → Bool) (expression : Witgen.U64ExprOver F V) :
    Reads.nat allowed expression = accepts allowed (nat expression) := by
  cases expression with
  | const _ => rfl
  | val a => exact field_eq allowed a
  | add a b | mul a b | div a b | mod a b | land a b | lor a b | lxor a b
  | shiftL a b | shiftR a b =>
    simp only [Reads.nat, nat, accepts_join, nat_eq allowed a, nat_eq allowed b]
  | _ => rfl
end

/-- Concatenate output-expression plans without evaluating field values. -/
def fields : List (Witgen.FExprOver F V) → Option (List V)
  | [] => some []
  | expression :: rest => join (field expression) (fields rest)

theorem fields_eq (allowed : V → Bool) (expressions : List (Witgen.FExprOver F V)) :
    expressions.all (Reads.field allowed) = accepts allowed (fields expressions) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
    simp only [List.all_cons, fields, accepts_join, field_eq, ih]

/-- The same supported program shapes as `Reads.program`, including empty
output vectors. Local steps, callbacks and nonliteral vectors are rejected. -/
def program {n : Nat} : Witgen.WitgenIROver F Env V n → Option (List V)
  | .ir [] (.lit expressions) => fields expressions.toArray.toList
  | _ => none

theorem program_eq {n : Nat} (allowed : V → Bool) (compute : Witgen.WitgenIROver F Env V n) :
    Reads.program allowed compute = accepts allowed (program compute) := by
  cases compute with
  | native _ => rfl
  | ir steps out =>
    cases steps with
    | cons _ _ => rfl
    | nil =>
      cases out with
      | lit expressions =>
        simpa only [Reads.program, program, Array.all_toList] using
          fields_eq allowed expressions.toArray.toList
      | mapRange _ _ | envRange _ | bitsOf _ | append _ _ => rfl

end Midnight.Math.Witness.Dependencies
