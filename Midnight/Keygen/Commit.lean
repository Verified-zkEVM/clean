import Midnight.Keygen.G1Projective
import Midnight.Keygen.Domain
import CompPoly.Univariate.NTT.Inverse

/-! KZG commitment to an evaluation vector: CompPoly's inverse NTT to coefficients, then the MSM
against the monomial SRS. Midnight commits without a blinding term. The MSM adapts Gregor's
projective Pippenger without its correctness proof (`G1Projective.lean`). -/
namespace Midnight.Keygen
open CompPoly.CPolynomial.NTT

def commit (srs : Array G1.Point) (D : Domain F) (evaluations : Array F) :
    Except String G1.Point := do
  unless srs.size == D.n && evaluations.size == D.n do
    throw "setup or evaluation length differs from the domain"
  let coefficients : Array F := Inverse.inverseImpl D evaluations
  return G1.msm ((coefficients.toList.zip srs.toList).map fun (c, p) => (c.val, p))

end Midnight.Keygen
