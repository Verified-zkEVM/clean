/-
The keccak-air kernel over KoalaBear compiled to native code, the trace generator of the CompStark
showcase.
-/
module

public import Clean.Air.FastWitness.Codegen
public import Clean.Examples.KeccakAir.FastTrace
public import CompPoly.Fields.KoalaBear.Fast
meta import Clean.Examples.KeccakAir.Ensemble
meta import CompPoly.Fields.KoalaBear.Fast

@[expose] public section

namespace KeccakAir
open Air.Flat

fast_witness_kernel koalaBearKernel for KoalaBear.fieldSize :=
  FastWitness.compileSegments (component (p := KoalaBear.fieldSize) 24) #[("keccak", 100)]

/-- `fastTrace` over KoalaBear, with the compiled kernel. -/
def koalaBearTrace (inputs : Array State) (logChunks : ℕ) : Except String (Array ByteArray) :=
  koalaBearKernel.trace #[hintWords (p := KoalaBear.fieldSize) inputs] (traceHeight inputs.size)
    logChunks

end KeccakAir
