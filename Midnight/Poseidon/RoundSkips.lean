import Midnight.Poseidon.Constants
import Midnight.Keygen.Configure
import Midnight.Configuration

/-!
Port of `circuits/src/hash/poseidon/round_skips.rs` at the pinned Midnight commit.
The optimized identities are computed from the canonical MDS matrix. No precomputed identities
from a VK are used.
-/
namespace Midnight.Poseidon
open Midnight.Keygen

structure RoundVarId where
  /-- Canonical field representatives keep precomputation reduction efficient. -/
  vars : Array Nat
  constants : Array Nat
deriving Inhabited

def RoundVarId.zero : RoundVarId :=
  ⟨Array.replicate (width + circuitSkips) 0,
   Array.replicate (width * (1 + circuitSkips)) 0⟩

def RoundVarId.variable (index : Nat) : RoundVarId :=
  { RoundVarId.zero with vars := RoundVarId.zero.vars.set! index 1 }

def RoundVarId.constant (row column : Nat) : RoundVarId :=
  { RoundVarId.zero with constants := RoundVarId.zero.constants.set! (row * width + column) 1 }

def RoundVarId.addMul (left right : RoundVarId) (coefficient : Nat) : RoundVarId :=
  ⟨(left.vars.zip right.vars).map (fun (a,b) => (a + b * coefficient) % BLS12_381.scalarFieldSize),
   (left.constants.zip right.constants).map (fun (a,b) => (a + b * coefficient) % BLS12_381.scalarFieldSize)⟩

/-- `RoundId::generate(5)`, including its otherwise skipped trivial identity
at position WIDTH-1. Each iteration replaces the two linear-state identities
and appends the identity for the next nonlinear state variable. -/
def generateRoundIds : Array RoundVarId := Id.run do
  let mut ids := (Array.range (width + 1 + circuitSkips)).map fun i =>
    if i < width then RoundVarId.variable i else RoundVarId.zero
  for row in [:1 + circuitSkips] do
    let current := (Array.range width).map fun i =>
      if i == width - 1 then RoundVarId.variable (width - 1 + row) else ids[i]!
    for i in [:width - 1] do
      let mut next := RoundVarId.constant row i
      for j in [:width] do next := next.addMul current[j]! ((mdsNat[i]!)[j]!)
      ids := ids.set! i next
    let mut last := RoundVarId.constant row (width - 1)
    for j in [:width] do last := last.addMul current[j]! ((mdsNat[width - 1]!)[j]!)
    ids := ids.set! (width + row) last
  return ids

/-- The eight output/auxiliary identities, in the exact source constraint order. -/
def partialRoundIds : Array RoundVarId :=
  generateRoundIds.extract 0 (width - 1) ++
    generateRoundIds.extract width generateRoundIds.size

def sbox (x : E) : E := x * ((x * x) * (x * x))

/-- Rust simplifies multiplication by a literal one. -/
def constProduct (c : F) (x : E) : E :=
  if c == 0 then .const 0 else if c == 1 then x else .const c * x

def sumTerms : List E → E
  | [] => .const 0
  | x :: xs => xs.foldl (· + ·) x

/-- Port `RoundVarId::to_expression`: skip zero coefficients, linear variables
first, then S-box variables. Constant-one/zero simplification matches Rust's AST. -/
def RoundVarId.toExpression (id : RoundVarId) (inputs : Array E) : E :=
  let terms := (id.vars.zip inputs).toList.zipIdx
  sumTerms (terms.filterMap fun ((coefficient, x), index) =>
    if coefficient == 0 then none
    else some (constProduct (coefficient : F) (if index < width - 1 then x else sbox x)))

def partialExpressions (inputs : Array E) : Array E :=
  partialRoundIds.map (·.toExpression inputs)

end Midnight.Poseidon
