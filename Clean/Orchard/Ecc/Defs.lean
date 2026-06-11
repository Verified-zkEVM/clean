import Clean.Circuit
import Clean.Orchard.Specs.Elliptic.Curves.Pasta
import Clean.Orchard.Specs.Elliptic.CurveForms.ShortWeierstrass
import Clean.Utils.Tactics
import Mathlib.Tactic

/-!
# Orchard ECC definitions

Shared Pallas field, point, fixed-base, and scalar-multiplication relations used by the
Orchard ECC circuits.
-/

namespace Orchard
namespace Ecc

variable {F : Type} [Field F]

abbrev PallasBaseField := CompElliptic.Fields.Pasta.PallasBaseField
abbrev PallasScalarField := CompElliptic.Fields.Pasta.PallasScalarField

def pallasB : F := 5

structure Point (F : Type) where
  x : F
  y : F

instance : ProvableType Point where
  size := 2
  toElements point := #v[point.x, point.y]
  fromElements elems := {
    x := elems[0]
    y := elems[1]
  }

@[circuit_norm]
theorem eval_point (env : Environment F) (point : Point (Expression F)) :
    eval env point = ({ x := env point.x, y := env point.y } : Point F) := by
  with_unfolding_all rfl

def curveEquation (point : Point F) : F :=
  point.y * point.y - point.x * point.x * point.x - pallasB

def onCurve (point : Point F) : Prop :=
  curveEquation point = 0

def isIdentityEncoding (point : Point F) : Prop :=
  point.x = 0 ∧ point.y = 0

def isPointOrIdentity (point : Point F) : Prop :=
  isIdentityEncoding point ∨ onCurve point

def pointCoords (point : Point F) : F × F :=
  (point.x, point.y)

def negPoint [Neg F] (point : Point F) : Point F where
  x := point.x
  y := -point.y

def pallasScalarMulCoords (scalar : ℕ) (base : Point PallasBaseField) :
    PallasBaseField × PallasBaseField :=
  CompElliptic.CurveForms.ShortWeierstrass.smul
    CompElliptic.Curves.Pasta.Pallas.a scalar (pointCoords base)

inductive OrchardFixedBaseId where
  | commitIvkR
  | noteCommitR
  | valueCommitV
  | valueCommitR
  | nullifierK
  | spendAuthG
deriving DecidableEq

/- Coordinates copied from Orchard 0.14.0 fixed-base generators in
`orchard/src/constants/fixed_bases/{commit_ivk_r,note_commit_r,value_commit_v,value_commit_r,nullifier_k,spend_auth_g}.rs`.
-/
def fixedBasePoint : OrchardFixedBaseId → Point PallasBaseField
  | .commitIvkR =>
      { x := 17022113834174368664964072539940476916905682548990455171271428285673934201112,
        y := 18912017636736613471143674001158885358143653198146604093009134371854861983145 }
  | .noteCommitR =>
      { x := 17502433695644481444785977856966854265310331039772160001849803703443502427667,
        y := 27531606546556235994383748883097777001194017792923801570415255878186539366371 }
  | .valueCommitV =>
      { x := 21457208314186520936880902219424053485005045883401337627148481900742711001959,
        y := 20379375922573002911833717643813254676246486412159279022689151936901102105230 }
  | .valueCommitR =>
      { x := 3597772235883004661259329170144280297379687592370687591147658848249887611537,
        y := 16317546749781193797530044795837656238506071957562073482938086095508632426954 }
  | .nullifierK =>
      { x := 17144890976040313974462754624161095328261290075490099718273142830262355741301,
        y := 9661337292872073193100428608853316471968232023361741282759000480983323509196 }
  | .spendAuthG =>
      { x := 25027635063850382358429654596649554085117301901282348152423547104939793041763,
        y := 12128007492603938773365931378340937928001494939630793217712875072231079427017 }

def IsPallasScalarMul
    (scalar : ℕ) (base product : Point PallasBaseField) : Prop :=
  isPointOrIdentity base ∧ pointCoords product = pallasScalarMulCoords scalar base

def pallasBaseFieldScalarNat (scalar : PallasBaseField) : ℕ :=
  scalar.val

def IsPallasBaseFieldScalarMul
    (scalar : PallasBaseField) (base product : Point PallasBaseField) : Prop :=
  IsPallasScalarMul (pallasBaseFieldScalarNat scalar) base product

def IsOrchardFixedBaseMul
    (baseId : OrchardFixedBaseId) (scalar : ℕ) (product : Point PallasBaseField) : Prop :=
  IsPallasScalarMul scalar (fixedBasePoint baseId) product

def IsOrchardFixedBaseBaseFieldMul
    (baseId : OrchardFixedBaseId) (scalar : PallasBaseField)
    (product : Point PallasBaseField) : Prop :=
  IsPallasBaseFieldScalarMul scalar (fixedBasePoint baseId) product

def negCoords {F : Type} [Neg F] (coords : F × F) : F × F :=
  (coords.1, -coords.2)

def IsSignedPallasScalarMul
    (scalar : ℕ) (sign : PallasBaseField)
    (base product : Point PallasBaseField) : Prop :=
  sign = 1 ∧ IsPallasScalarMul scalar base product ∨
    sign = 0 - 1 ∧
      isPointOrIdentity base ∧
      pointCoords product = negCoords (pallasScalarMulCoords scalar base)

def SignedPallasScalarMulCoords
    (scalar : ℕ) (sign : PallasBaseField)
    (base : Point PallasBaseField) (coords : PallasBaseField × PallasBaseField) : Prop :=
  sign = 1 ∧ coords = pallasScalarMulCoords scalar base ∨
    sign = 0 - 1 ∧ coords = negCoords (pallasScalarMulCoords scalar base)

def IsOrchardFixedBaseSignedMul
    (baseId : OrchardFixedBaseId) (scalar : ℕ) (sign : PallasBaseField)
    (product : Point PallasBaseField) : Prop :=
  IsSignedPallasScalarMul scalar sign (fixedBasePoint baseId) product

def NoCurvePointWithXZero : Prop :=
  ∀ y : F, ¬ onCurve ({ x := 0, y } : Point F)

end Ecc
end Orchard
