/-
Adapted from CompElliptic's `Curves/Pasta/Fast/Projective.lean` and `MsmProj.lean`
(zksecurity/compelliptic-lean4-35 at f26a235f), whose notice reads:

Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude

This adaptation is used under the MIT license option, as is the rest of this repository (LICENSE).
-/
import Midnight.Keygen.G1

/-! Gregor Mitscha-Baude's projective Pippenger (CompElliptic `Curves/Pasta/Fast/Projective.lean`
and `MsmProj.lean`), adapted from Vesta to BLS12-381 G1 without porting his proof that it equals
the affine Pippenger: nothing here is proved, `rust_key` only checks the bytes it produces. A proof
would go through his generic `Msm.pippengerFast_eq_msm`. The formulas are Renes–Costello–Batina's
complete addition at `a = 0`, `b3 = 12`, so an MSM converts to affine once (two divisions by `Z`)
instead of on every addition; `E(𝔽_p)` has odd order, so no 2-torsion, which their completeness
needs. Names follow his code. -/
namespace Midnight.Keygen.G1.Projective
open CompElliptic.Curves.Pasta.Fast

structure PG1 where
  X : Fp
  Y : Fp
  Z : Fp
  deriving DecidableEq

/-- `add-2015-rcb` at `a = 0`, `b3 = 12`. -/
def padd (P Q : PG1) : PG1 where
  X := P.X*P.Y*Q.Y^2 - 12*P.X*P.Y*Q.Z^2 - 24*P.X*P.Z*Q.Y*Q.Z
       + P.Y^2*Q.X*Q.Y - 12*P.Z^2*Q.X*Q.Y - 24*P.Y*P.Z*Q.X*Q.Z
  Y := P.Y^2*Q.Y^2 + 36*P.X^2*Q.X*Q.Z + 36*P.X*P.Z*Q.X^2 - 144*P.Z^2*Q.Z^2
  Z := P.Y^2*Q.Y*Q.Z + P.Y*P.Z*Q.Y^2 + 3*P.X^2*Q.X*Q.Y + 3*P.X*P.Y*Q.X^2
       + 12*P.Y*P.Z*Q.Z^2 + 12*P.Z^2*Q.Y*Q.Z

def pid : PG1 := ⟨0, 1, 0⟩

def ofAffine (p : Point) : PG1 := if p.x = 0 ∧ p.y = 0 then pid else ⟨p.x, p.y, 1⟩

/-- `(X/Z, Y/Z)`, checked to be on the curve; points at infinity (and anything off the curve)
read as the identity, as in Gregor's `toAffine`. -/
def toAffine (P : PG1) : Point :=
  if P.Z = 0 then 0 else (ofFp? (P.X / P.Z) (P.Y / P.Z)).getD 0

def pnsmulFast (n : Nat) (P : PG1) : PG1 := CompElliptic.binNsmul padd pid n P

def paccStep (a : PG1) (p : PG1 × PG1) : PG1 × PG1 := (padd p.1 a, padd p.2 (padd p.1 a))

/-- `Msm.dpOf` on `PG1`, which has no `AddCommMonoid`. -/
def pdpOf (base i : Nat) (pterms : List (Nat × PG1)) : List (Nat × PG1) :=
  pterms.map fun t => (Msm.digit base i t.1, t.2)

def pscatterStep (a : Array PG1) (p : Nat × PG1) : Array PG1 :=
  if p.1 = 0 then a else a.modify (p.1 - 1) (fun v => padd v p.2)

def pbucketScatter (base : Nat) (dp : List (Nat × PG1)) : Array PG1 :=
  dp.foldl pscatterStep (Array.replicate (base - 1) pid)

def pwindowValueFast (base i : Nat) (pterms : List (Nat × PG1)) : PG1 :=
  (List.foldr paccStep (pid, pid) (pbucketScatter base (pdpOf base i pterms)).toList).2

def phornerList (base : Nat) (vals : List PG1) : PG1 :=
  List.foldr (fun v acc => padd (pnsmulFast base acc) v) pid vals

def pippengerProjScatter (c : Nat) (terms : List (Nat × Point)) : Point :=
  toAffine (phornerList (2 ^ c)
    ((List.range (Msm.numWindows c terms)).map fun i =>
      pwindowValueFast (2 ^ c) i (terms.map fun t => (t.1, ofAffine t.2))))

end Midnight.Keygen.G1.Projective

namespace Midnight.Keygen.G1

/-- The MSM key derivation commits with. -/
def msm (terms : List (Nat × Point)) : Point :=
  Projective.pippengerProjScatter (window terms.length) terms

end Midnight.Keygen.G1
