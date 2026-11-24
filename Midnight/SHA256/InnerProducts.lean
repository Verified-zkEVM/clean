import Midnight.Keygen.BatchedLookup

/-! The inner products midnight-zk's SHA-256 chip builds its gate polynomials from. -/
namespace Midnight.SHA256
open Midnight.Keygen

/-- Rust folds inner products from zero but its expression addition eliminates
literal zero; multiplication eliminates literal one. All powers here are positive. -/
def sumExpr : List E → E
  | [] => .const 0
  | first :: rest => rest.foldl (· + ·) first

def pow2ip (exponents : List Nat) (terms : List E) : E :=
  sumExpr ((exponents.zip terms).map fun (e, t) =>
    if e == 0 then t else .mul (.const ((2 : F) ^ e)) t)

def pow4ip (exponents : List Nat) (terms : List E) : E :=
  pow2ip (exponents.map (2 * ·)) terms

end Midnight.SHA256
