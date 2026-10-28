/-
The keccak-air kernel over KoalaBear's Montgomery field compiled to native code, the trace generator
of the CompStark showcase.
-/
module

public import Clean.Air.WitnessGeneration.Codegen
public import Clean.Examples.KeccakAir.Trace
public import Clean.Utils.FastField
public import CompPoly.Fields.KoalaBear.Fast
meta import Clean.Examples.KeccakAir.Ensemble
meta import Clean.Utils.FastField
meta import CompPoly.Fields.KoalaBear.Fast

@[expose] public section

namespace KeccakAir
open Air.Flat Montgomery.Native32

witness_kernel koalaBearKernel over FastField KoalaBear.fieldSize :=
  WitnessGeneration.compileSegments (component (p := KoalaBear.fieldSize) 24)
    (FastField.ofZMod KoalaBear.fieldSize)
    (WitnessGeneration.hintKeys (ensemble (p := KoalaBear.fieldSize) 24).hintTables)

end KeccakAir
