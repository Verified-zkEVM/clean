/-
BabyJubJub Point Addition Circuit

Implements the unified Edwards point addition formula from circomlib's BabyAdd.
Original source: https://github.com/iden3/circomlib/blob/master/circuits/babyjub.circom

Formula:
  x₃ = (x₁·y₂ + y₁·x₂) / (1 + d·x₁·x₂·y₁·y₂)
  y₃ = (y₁·y₂ - a·x₁·x₂) / (1 - d·x₁·x₂·y₁·y₂)

Division is handled via witness + multiplication check (same pattern as Comparators.IsZero).
-/
import Clean.Circuit
import Clean.Specs.BabyJubJub
import Clean.Utils.Tactics.CircuitProofStart

namespace Circomlib.BabyJubJub

open Specs.BabyJubJub (Point a_nat d_nat)

variable {p : ℕ} [Fact p.Prime]

instance : ProvableType Point where
  size := 2
  toElements pt := #v[pt.x, pt.y]
  fromElements v :=
    let ⟨.mk [x, y], _⟩ := v
    ⟨x, y⟩
  fromElements_toElements x := by
    cases x; rfl

-- TODO: add proper eval lemmas for custom ProvableType Point.
-- `ProvableType.eval` needs a circuit_norm lemma that reduces `eval env p` to
-- `Point.mk (Expression.eval env p.x) (Expression.eval env p.y)` so that
-- `circuit_proof_start` can decompose struct inputs in soundness/completeness proofs.
@[circuit_norm]
theorem eval_point {F : Type} [FiniteField F] (env : Environment F) (p : Point (Expression F)) :
    eval env p = Point.mk (Expression.eval env p.x) (Expression.eval env p.y) := by
  sorry

structure Inputs (F : Type) where
  p1 : Point F
  p2 : Point F
deriving ProvableStruct

namespace PointAdd

def main (input : Inputs (Expression (F p))) : Circuit (F p) (Point (Expression (F p))) := do
  let { p1, p2 } := input
  let a : Expression (F p) := (a_nat : F p)
  let d : Expression (F p) := (d_nat : F p)
  let x1x2 <== p1.x * p2.x
  let y1y2 <== p1.y * p2.y
  let x1y2 <== p1.x * p2.y
  let y1x2 <== p1.y * p2.x
  let tau <== d * x1x2 * y1y2
  let denom1 <== 1 + tau
  let denom2 <== 1 - tau
  let num1 <== x1y2 + y1x2
  let num2 <== y1y2 - a * x1x2
  let inv1 ← witness (.ite (denom1 =? 0) 0 denom1⁻¹)
  let inv2 ← witness (.ite (denom2 =? 0) 0 denom2⁻¹)
  let x3 <== inv1 * num1
  let y3 <== inv2 * num2
  x3 * denom1 === num1
  y3 * denom2 === num2
  return { x := x3, y := y3 }

def Assumptions (input : Inputs (F p)) : Prop :=
  let a := (a_nat : F p); let d := (d_nat : F p)
  Point.onCurve a d input.p1 ∧ Point.onCurve a d input.p2

def Spec (input : Inputs (F p)) (output : Point (F p)) : Prop :=
  let a := (a_nat : F p); let d := (d_nat : F p)
  output = Point.add a d input.p1 input.p2

instance elaborated : ElaboratedCircuit (F p) Inputs Point main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  sorry

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start
  sorry

def circuit : FormalCircuit (F p) Inputs Point where
  main
  Assumptions
  Spec
  soundness
  completeness

end PointAdd
end Circomlib.BabyJubJub
