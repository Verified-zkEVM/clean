import Clean.Gadgets.SHA256.BitwiseOps
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# Majority function Maj(a, b, c) for SHA-256

Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c).
Decomposition: let t = a·b; then maj = t + c·(a + b − 2·t).
Two R1CS constraints per bit:
  (1)  a·b = t
  (2)  c·(a + b − 2·t) = z − t
Witnesses 64 variables: 32 for t, 32 for z.
-/

/-- Majority function: Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c).
    Decomposition: let t = a·b; then maj = t + c·(a + b − 2·t).
    Two R1CS constraints per bit:
      (1)  a·b = t
      (2)  c·(a + b − 2·t) = z − t -/
def maj32 (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  -- Witness the intermediate product t[i] = a[i] * b[i]
  let t ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) => env a[i] * env b[i]
  -- Witness the majority output
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      let ti := env t[i]
      env t[i] + env c[i] * (env a[i] + env b[i] - 2 * ti)
  -- Constraint (1): t[i] = a[i] * b[i]
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (t[i] - a[i] * b[i])
  -- Constraint (2): z[i] = t[i] + c[i] * (a[i] + b[i] - 2 * t[i])
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - t[i] - c[i] * (a[i] + b[i] - 2 * t[i]))
  return z

namespace Maj32

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
  c : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  maj32 input.a input.b input.c

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) where
  main := main
  localLength _ := 64
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.Maj (valueBits input.a) (valueBits input.b) (valueBits input.c) ∧
  Normalized z

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end Maj32
end Gadgets.SHA256
end
