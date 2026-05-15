import Clean.Gadgets.SHA256.BitwiseOps
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# Choice function Ch(e, f, g) for SHA-256

Ch(e, f, g) = (e AND f) XOR (NOT e AND g) = g + e·(f − g).
Per bit: ch = g + e·(f − g), which equals f when e = 1 and g when e = 0.
One R1CS constraint per bit: e·(f − g) = ch − g.
Witnesses 32 output bits.
-/

/-- Choice function: Ch(e, f, g) = (e AND f) XOR (NOT e AND g) = g + e·(f − g).
    Per bit: ch = g + e·(f − g), which equals f when e = 1 and g when e = 0.
    One R1CS constraint per bit: e·(f − g) = ch − g. -/
def ch32 (e f g : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      env g[i] + env e[i] * (env f[i] - env g[i])
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - g[i] - e[i] * (f[i] - g[i]))
  return z

namespace Ch32

structure Inputs (F : Type) where
  e : fields 32 F
  f : fields 32 F
  g : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  ch32 input.e input.f input.g

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) where
  main := main
  localLength _ := 32
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.e ∧ Normalized input.f ∧ Normalized input.g

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.Ch (valueBits input.e) (valueBits input.f) (valueBits input.g) ∧
  Normalized z

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end Ch32
end Gadgets.SHA256
end
