import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

/-!
Shared definitions for Orchard scalar multiplication gates.
-/

namespace Orchard.Ecc.ScalarMul

def ternary {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K]
    (choice ifTrue ifFalse : K) : K :=
  choice * ifTrue + (1 - choice) * ifFalse

def tQ {K : Type} [OfNat K 45560315531506369815346746415080538113] : K :=
  OfNat.ofNat 45560315531506369815346746415080538113

end Orchard.Ecc.ScalarMul
