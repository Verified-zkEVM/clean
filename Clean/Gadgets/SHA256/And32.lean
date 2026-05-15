import Clean.Gadgets.SHA256.BitwiseOps

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# 32-bit Bitwise AND for SHA-256

Per bit: z = a · b  (correct when a, b ∈ {0, 1}).
Witnesses 32 output bits.
-/

/-- Bitwise AND of two 32-bit words.
    Per bit: z = a · b  (correct when a, b ∈ {0, 1}). -/
def and32 (a b : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      env a[i] * env b[i]
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - a[i] * b[i])
  return z

namespace And32

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  and32 input.a input.b

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) where
  main := main
  localLength _ := 32
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = valueBits input.a &&& valueBits input.b ∧ Normalized z

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end And32
end Gadgets.SHA256
end
