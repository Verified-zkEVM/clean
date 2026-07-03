/-
BabyJubJub Elliptic Curve Specification

This file defines the BabyJubJub twisted Edwards curve mathematically, matching
the circomlib implementation in circuits/babyjub.circom and the iden3 specification.

Curve equation: a*x^2 + y^2 = 1 + d*x^2*y^2
-/
import Clean.Specs.Poseidon

namespace Specs.BabyJubJub

open Specs.Poseidon (BN254_PRIME)

/-! Curve parameters (from circomlib babyjub.circom, as Nat constants) -/

def a_nat : ℕ := 168700
def d_nat : ℕ := 168696

def subgroupOrder : ℕ :=
  2736030358979909402780800718157159386076813972158567259200215660948447373041

def cofactor : ℕ := 8

/-! Point type -/

@[ext]
structure Point (F : Type) where
  x : F
  y : F
deriving Repr, DecidableEq, Inhabited

namespace Point

variable {F : Type} [Field F]

instance : Zero (Point F) where
  zero := { x := 0, y := 1 }

instance : Neg (Point F) where
  neg p := { x := -p.x, y := p.y }

/-! Curve equation: onCurve a d p := a*p.x^2 + p.y^2 = 1 + d*p.x^2*p.y^2 -/

def onCurve (a d : F) (p : Point F) : Prop :=
  a * p.x^2 + p.y^2 = 1 + d * p.x^2 * p.y^2

/-!
Point arithmetic using the unified Edwards addition formula.
These are complete on BabyJubJub because d is a non-square,
so the denominators never vanish for any valid curve points.

  x₃ = (x₁·y₂ + y₁·x₂) / (1 + d·x₁·x₂·y₁·y₂)
  y₃ = (y₁·y₂ - a·x₁·x₂) / (1 - d·x₁·x₂·y₁·y₂)
-/

def add (a d : F) (p q : Point F) : Point F :=
  let x1x2 := p.x * q.x
  let y1y2 := p.y * q.y
  let tau := d * x1x2 * y1y2
  { x := (p.x * q.y + p.y * q.x) / (1 + tau)
    y := (y1y2 - a * x1x2) / (1 - tau)
  }

def double (a d : F) (p : Point F) : Point F := add a d p p

/-- Scalar multiplication: double-and-add (simple, not constant-time). -/
def scalarMul (a d : F) (k : ℕ) (p : Point F) : Point F :=
  match k with
  | 0 => 0
  | 1 => p
  | k' + 2 =>
    let half := scalarMul a d (k' / 2 + 1) p
    let doubled := double a d half
    if k' % 2 = 0 then doubled else add a d doubled p

end Point

/-! Generator points (over BN254 scalar field) -/

-- Full curve generator G (order 8*l)
def G : Point (ZMod BN254_PRIME) :=
  { x := 995203441582195749578291179787384436505546430278305826713579947235728471134
    y := 5472060717959818805561601436314318772137091100104008585924551046643952123905
  }

-- Base point B = 8*G, generator of the prime-order subgroup (order l).
-- This is Base8 in circomlib's EdDSA.
def Base8 : Point (ZMod BN254_PRIME) :=
  { x := 5299619240641551281634865583518297030282874472190772894086521144482721001553
    y := 16950150798460657717958625567821834550301663161624707787222815936182638968203
  }

end Specs.BabyJubJub
