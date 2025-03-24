import Mathlib.Data.ZMod.Basic

def p_1009 := 1009
def p_babybear := 15 * 2^27 + 1
def p_mersenne := 2^31 - 1

instance prime_1009 : Fact (p_1009.Prime) := by native_decide
instance prime_babybear : Fact (p_babybear.Prime) := by native_decide
instance prime_mersenne : Fact (p_mersenne.Prime) := by native_decide

instance : Fact (p_babybear > 512) := .mk (by native_decide)
instance : Fact (p_mersenne > 512) := .mk (by native_decide)
