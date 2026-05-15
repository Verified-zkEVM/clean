import Clean.Gadgets.SHA256.BitwiseOps

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# 32-bit Modular Addition for SHA-256

Adds two 32-bit words (as `fields 32` bit vectors, LSB first) modulo 2^32.

R1CS structure (per call):
- 32 witnesses for output bits z[0..31]
- 1  witness  for carry-out bit cout
- 32 boolean constraints: z[i] · (z[i] − 1) = 0
- 1  boolean constraint:  cout · (cout − 1) = 0
- 1  linear  constraint:  Σ a[i]·2^i + Σ b[i]·2^i = Σ z[i]·2^i + 2^32 · cout

Soundness requires the prime p to exceed 2^33 so that the linear constraint
can distinguish the intended ℕ-level relation from field wraparound.
-/

private def evalBitsNat (env : ProverEnvironment (F p)) (a : Var (fields 32) (F p)) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => (env a[i]).val * 2^i.val

/-- Add two 32-bit words mod 2^32.
    Both inputs are assumed to have boolean values in each bit position. -/
def add32 (a b : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  -- Witness the lower 32 bits of the sum
  let z ← witnessVector 32 fun env =>
    let s := (evalBitsNat env a + evalBitsNat env b) % 2^32
    Vector.ofFn fun (i : Fin 32) => ((s / 2^i.val % 2 : ℕ) : F p)
  -- Witness the carry-out bit
  let cout ← witnessField fun env =>
    ((( evalBitsNat env a + evalBitsNat env b) / 2^32 % 2 : ℕ) : F p)
  -- Boolean constraints on output bits
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  -- Boolean constraint on carry-out
  assertZero (cout * (cout - 1))
  -- Sum constraint: fromBits(a) + fromBits(b) = fromBits(z) + 2^32 * cout
  assertZero (fromBitsExpr a + fromBitsExpr b - fromBitsExpr z - (2^32 : F p) * cout)
  return z

namespace Add32

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  add32 input.a input.b

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) where
  main := main
  localLength _ := 33
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = (valueBits input.a + valueBits input.b) % 2^32 ∧ Normalized z

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end Add32
end Gadgets.SHA256
end
