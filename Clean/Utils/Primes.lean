import Mathlib.Data.ZMod.Basic

def p1009 := 1009
def pBabybear := 15 * 2^27 + 1
def pMersenne := 2^31 - 1

-- A small certifiable prime above 2^36, used as a *field-independent* stand-in for
-- large fields (e.g. the BN254 scalar field) when measuring/evaluating circuit cost.
-- Constraint and witness counts do not depend on the value of the prime, only on its
-- existence; this keeps `native_decide` primality fast (sqrt ≈ 2^18) while still
-- satisfying the `p > 2^33` / `p > 2^35` bounds the SHA-256 gadgets require.
def pLarge := 2^36 + 31

instance prime1009 : Fact (p1009.Prime) := by native_decide
instance primeBabybear : Fact (pBabybear.Prime) := by native_decide
instance primeMersenne : Fact (pMersenne.Prime) := by native_decide
instance primeLarge : Fact (pLarge.Prime) := by native_decide

instance : Fact (pBabybear > 512) := by native_decide
instance : Fact (pBabybear > 2^16 + 2^8) := by native_decide
instance : Fact (pMersenne > 512) := by native_decide

instance : Fact (pBabybear > 2^16 + 2^8) := by native_decide
instance : Fact (pMersenne > 2^16 + 2^8) := by native_decide

instance : Fact (pLarge > 512) := by native_decide
instance : Fact (pLarge > 2^16 + 2^8) := by native_decide
instance : Fact (pLarge > 2^33) := by native_decide
instance : Fact (pLarge > 2^35) := by native_decide
