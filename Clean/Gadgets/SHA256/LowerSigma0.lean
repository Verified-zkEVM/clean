import Clean.Gadgets.SHA256.Xor32
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# σ₀ (lower sigma 0) for SHA-256

σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)

Two xor32 calls = 64 witnesses total.
-/

/-- σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x) -/
def lowerSigma0 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let r1 ← xor32 (rotr32 7  x) (rotr32 18 x)
  xor32 r1 (shr32 3 x)

namespace LowerSigma0

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  lowerSigma0 x

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) where
  main := main
  localLength _ := 64
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.lowerSigma0 (valueBits x) ∧ Normalized z

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end LowerSigma0
end Gadgets.SHA256
end
