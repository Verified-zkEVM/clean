import Clean.Gadgets.SHA256.Xor32
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# Σ₁ (upper sigma 1) for SHA-256

Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x)

Two xor32 calls = 64 witnesses total.
-/

/-- Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x) -/
def upperSigma1 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let r1 ← xor32 (rotr32 6  x) (rotr32 11 x)
  xor32 r1 (rotr32 25 x)

namespace UpperSigma1

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  upperSigma1 x

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) where
  main := main
  localLength _ := 64
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.upperSigma1 (valueBits x) ∧ Normalized z

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end UpperSigma1
end Gadgets.SHA256
end
