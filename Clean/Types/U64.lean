import Clean.GadgetsNew.ByteLookup

section
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2*2^64)]

instance : NeZero p := ⟨‹Fact p.Prime›.elim.ne_zero⟩
instance : Fact (p > 512) := by apply Fact.mk; linarith [p_large_enough.elim]

/--
  A 64-bit unsigned integer is represented using four limbs of 8 bits each.
-/
structure U64 (T: Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T
  x4 : T
  x5 : T
  x6 : T
  x7 : T

namespace U64

/--
  Witness a 64-bit unsigned integer.
-/
def witness (compute : Unit → U64 (F p)) := do
  let val := compute ()
  let x0 ← witness_var (fun _ => val.x0)
  let x1 ← witness_var (fun _ => val.x1)
  let x2 ← witness_var (fun _ => val.x2)
  let x3 ← witness_var (fun _ => val.x3)
  let x4 ← witness_var (fun _ => val.x4)
  let x5 ← witness_var (fun _ => val.x5)
  let x6 ← witness_var (fun _ => val.x6)
  let x7 ← witness_var (fun _ => val.x7)

  byte_lookup x0
  byte_lookup x1
  byte_lookup x2
  byte_lookup x3
  byte_lookup x4
  byte_lookup x5
  byte_lookup x6
  byte_lookup x7

  return U64.mk x0 x1 x2 x3 x4 x5 x6 x7
end U64
