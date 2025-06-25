import Mathlib.Data.ZMod.Basic

def p1009 := 1009
def pBabybear := 15 * 2^27 + 1
def pMersenne := 2^31 - 1

instance prime1009 : Fact (p1009.Prime) := by native_decide
instance primeBabybear : Fact (pBabybear.Prime) := by native_decide
instance primeMersenne : Fact (pMersenne.Prime) := by native_decide

instance : Fact (pBabybear > 512) := by native_decide
instance : Fact (pBabybear > 2^16 + 2^8) := by native_decide
instance : Fact (pMersenne > 512) := by native_decide

instance : Fact (pBabybear > 2^16 + 2^8) := by native_decide
instance : Fact (pMersenne > 2^16 + 2^8) := by native_decide
