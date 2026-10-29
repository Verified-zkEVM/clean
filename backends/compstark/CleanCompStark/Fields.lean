module

public import Clean.Utils.Field
public import CompStark.KoalaBear.Field
public import CompStark.BabyBear.Field

/-!
# Clean's prime fields as CompStark's base fields

Clean's gadgets are written over `F p = ZMod p`, CompStark proves over CompPoly's Montgomery field
`FastField p`. The two are isomorphic (`Montgomery.Native32.ringEquiv`); the backend maps
constraint constants along the isomorphism and reads traces back through its inverse.
-/

@[expose] public section

namespace CleanCompStark
open Montgomery.Native32

/-- Clean's `F p` as the Montgomery field of a 32-bit prime. -/
abbrev montEquiv (p : ℕ) [Mont32Field p] : F p ≃+* FastField p := (ringEquiv p).symm

/-- Clean's KoalaBear field as CompStark's. -/
abbrev koalaBear : F KoalaBear.fieldSize ≃+* KoalaBear.Fast.Field := montEquiv KoalaBear.fieldSize

/-- Clean's BabyBear field as CompStark's. -/
abbrev babyBear : F BabyBear.fieldSize ≃+* BabyBear.Fast.Field := montEquiv BabyBear.fieldSize

end CleanCompStark
