/-!
# Circuit-owned finite shape

The finite dimensions shared by a top-level circuit, its verifying key, and every
proof made against that key.
-/

namespace Halo2

/-- The finite dimensions fixed by a top-level circuit and shared by its verifying
key and every proof made against that key. -/
@[ext] structure CircuitShape where
  k : Nat
  numAdviceColumns : Nat
  numLookups : Nat
  numPermutationSets : Nat
  numPermutationColumns : Nat
  numQuotientPieces : Nat
  numInstanceColumns : Nat
  numInstanceQueries : Nat
  numAdviceQueries : Nat
  numFixedQueries : Nat
deriving DecidableEq, Repr

end Halo2
