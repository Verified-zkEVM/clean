import Clean.Gadgets.SHA256.BitwiseOps

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^35)]

namespace Gadgets.SHA256

/-!
# Multi-operand 32-bit modular addition for SHA-256

Adds `n ≤ 8` 32-bit words (as `fields 32` bit vectors, LSB first) modulo `2^32` in a single
range reduction, exploiting that linear combinations are free in R1CS.  Instead of chaining
binary `add32` (each re-witnessing 32 output bits), we sum the operands as one free linear
combination and bit-decompose the result once, with a 3-bit carry.

R1CS structure (per call):
- 32 witnesses for output bits `z[0..31]`, 3 witnesses for carry bits `c[0..2]`
- 32 + 3 boolean constraints
- 1  linear constraint: `Σ_j valueBits(op_j) = valueBits(z) + 2^32 · (c0 + 2·c1 + 4·c2)`

Soundness needs `p > 2^35` so the linear constraint lifts from `F p` to `ℕ`
(`Σ < 8·2^32 = 2^35`).  The 254-bit BN254 scalar field satisfies this with huge margin.

NOTE: this file currently provides the gadget *definition* and its intended `Assumptions`/`Spec`.
The `FormalCircuit` soundness/completeness proofs are still to be added; nothing depends on this
gadget yet, so the rest of the SHA-256 development is unaffected.
-/

variable {n : ℕ}

/-- Natural-number value of all operands summed. -/
def opsValueSum (ops : Vector (fields 32 (F p)) n) : ℕ :=
  ∑ j : Fin n, valueBits ops[j]

/-- Linear-combination expression of the operand sum (free in R1CS). -/
def sumExpr (ops : Vector (Var (fields 32) (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc (j : Fin n) => acc + fromBitsExpr ops[j]) (0 : Expression (F p))

/-- Carry expression from three boolean bit variables. -/
def carryExpr (c : Var (fields 3) (F p)) : Expression (F p) :=
  c[0] + (2 : F p) * c[1] + (4 : F p) * c[2]

private def evalBitsNat (env : ProverEnvironment (F p)) (a : Var (fields 32) (F p)) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => (env a[i]).val * 2^i.val

private def sumBitsNat (env : ProverEnvironment (F p)) (ops : Vector (Var (fields 32) (F p)) n) : ℕ :=
  ∑ j : Fin n, evalBitsNat env ops[j]

/-- Add `n` 32-bit words mod `2^32` (single reduction with a 3-bit carry). -/
def addMod32 (ops : Vector (Var (fields 32) (F p)) n) :
    Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    let s := (sumBitsNat env ops) % 2^32
    Vector.ofFn fun (i : Fin 32) => ((s / 2^i.val % 2 : ℕ) : F p)
  let c ← witnessVector 3 fun env =>
    let s := sumBitsNat env ops
    Vector.ofFn fun (i : Fin 3) => ((s / 2^32 / 2^i.val % 2 : ℕ) : F p)
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  Circuit.forEach (Vector.finRange 3) fun i =>
    assertZero (c[i] * (c[i] - 1))
  assertZero (sumExpr ops - fromBitsExpr z - (2^32 : F p) * carryExpr c)
  return z

namespace AddMod32

/-- All operands are normalized (boolean bit vectors). -/
def Assumptions (ops : ProvableVector (fields 32) n (F p)) : Prop :=
  ∀ j : Fin n, Normalized ops[j]

/-- The output is the modular sum of the operands, and is normalized. -/
def Spec (ops : ProvableVector (fields 32) n (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = (opsValueSum ops) % 2^32 ∧ Normalized z

end AddMod32
end Gadgets.SHA256
end
