import Midnight.Keygen.Domain
import Clean.Halo2.Keygen.Layout
import CompPoly.Univariate.NTTFast.Coset

namespace Midnight.Keygen

/-- Each sigma entry `(column,row)` denotes delta^column * omega^row.
The mapping is derived by replaying the independently generated ordered copies. -/
def permutationPolynomials (k numColumns : Nat)
    (mapping : Array (Array (Nat × Nat))) : Except String (Array (Array F)) := do
  let n := 2 ^ k
  unless mapping.size == numColumns do throw "permutation column count mismatch"
  let roots := CompPoly.CPolynomial.NTTFast.powers (omega k) n
  let deltas := CompPoly.CPolynomial.NTTFast.powers delta numColumns
  let mut result := #[]
  for column in mapping do
    unless column.size == n do throw "permutation row count mismatch"
    let mut polynomial := Array.mkEmpty n
    for (col, row) in column do
      if col < numColumns then
        if row < n then
          polynomial := polynomial.push (deltas[col]! * roots[row]!)
        else throw "permutation row out of bounds"
      else throw "permutation column out of bounds"
    result := result.push polynomial
  return result

def derivePermutationPolynomials (k numColumns : Nat)
    (copies : List (Nat × Nat × Nat × Nat)) : Except String (Array (Array F)) := do
  let n := 2 ^ k
  for (lc, lr, rc, rr) in copies do
    unless lc < numColumns && rc < numColumns && lr < n && rr < n do
      throw "copy out of bounds"
  permutationPolynomials k numColumns (Halo2.Layout.runAssembly n numColumns copies)

end Midnight.Keygen
