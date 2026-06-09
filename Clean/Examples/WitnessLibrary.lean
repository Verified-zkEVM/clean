import Clean.Circuit.Witness
import Clean.Circomlib.AliasCheck
import Clean.Circomlib.BinSub
import Clean.Circomlib.BinSum
import Clean.Circomlib.Bitify
import Clean.Circomlib.Bitify2
import Clean.Circomlib.CompConstant
import Clean.Circomlib.Comparators
import Clean.Circomlib.Gates
import Clean.Circomlib.Mux1
import Clean.Circomlib.Mux2
import Clean.Circomlib.Mux3
import Clean.Utils.Primes

namespace Examples.WitnessLibrary

-- First 30 Circomlib formal circuits/assertions from sorted file order.
-- Current out-of-the-box result: 13 compile successfully, 17 are TODO-commented below.

-- TODO: pBabybear does not satisfy the circuit's `Fact (p > 2^253)` requirement.
-- compile_witness (Circomlib.AliasCheck.circuit (p:=pBabybear)) => aliasCheckWitness

-- TODO: generated witness declaration still has free variables.
-- compile_witness (Circomlib.BinSub.circuit (p:=pBabybear) 2 (by native_decide)) => binSub2Witness
-- TODO: witness compiler does not yet support this witness shape.
-- compile_witness (Circomlib.BinSum.circuit (p:=pBabybear) 2 2 (by native_decide)) => binSum2x2Witness

compile_witness (Circomlib.Num2Bits.arbitraryBitLengthCircuit (p:=pBabybear) 4) => num2BitsArbitrary4Witness
compile_witness (Circomlib.Num2Bits.circuit (p:=pBabybear) 4 (by native_decide)) => num2Bits4Witness
-- TODO: generated witness declaration still has free variables.
-- compile_witness (Circomlib.Bits2Num.circuit (p:=pBabybear) 4) => bits2Num4Witness
-- TODO: pBabybear does not satisfy the circuit's `Fact (p > 2^253)` requirement.
-- compile_witness (Circomlib.Num2Bits_strict.circuit (p:=pBabybear)) => num2BitsStrictWitness
-- TODO: pBabybear does not satisfy the circuit's `Fact (p > 2^253)` requirement.
-- compile_witness (Circomlib.Bits2Num_strict.circuit (p:=pBabybear)) => bits2NumStrictWitness
-- TODO: failed to synthesize an instance during witness compilation.
-- compile_witness (Circomlib.Num2BitsNeg.circuit (p:=pBabybear) 4 (by native_decide)) => num2BitsNeg4Witness

-- TODO: pBabybear does not satisfy the circuit's `Fact (p > 2^253)` requirement.
-- compile_witness (Circomlib.CompConstant.circuit (p:=pBabybear) 3 (by native_decide)) => compConstant3Witness

compile_witness (Circomlib.IsZero.circuit (p:=pBabybear)) => isZeroWitness
compile_witness (Circomlib.IsEqual.circuit (p:=pBabybear)) => isEqualWitness
-- TODO: witness compiler cannot generate setters for non-static witness length.
-- compile_witness (Circomlib.ForceEqualIfEnabled.circuit (p:=pBabybear)) => forceEqualIfEnabledWitness
-- TODO: failed to prove an array index bound through the Num2Bits subcircuit.
-- compile_witness (Circomlib.LessThan.circuit (p:=pBabybear) 4 (by native_decide)) => lessThan4Witness
compile_witness (Circomlib.LessEqThan.circuit (p:=pBabybear) 4 (by native_decide)) => lessEqThan4Witness
compile_witness (Circomlib.GreaterThan.circuit (p:=pBabybear) 4 (by native_decide)) => greaterThan4Witness
compile_witness (Circomlib.GreaterEqThan.circuit (p:=pBabybear) 4 (by native_decide)) => greaterEqThan4Witness

compile_witness (Circomlib.XOR.circuit (p:=pBabybear)) => xorWitness
compile_witness (Circomlib.AND.circuit (p:=pBabybear)) => andWitness
compile_witness (Circomlib.OR.circuit (p:=pBabybear)) => orWitness
compile_witness (Circomlib.NOT.circuit (p:=pBabybear)) => notWitness
compile_witness (Circomlib.NAND.circuit (p:=pBabybear)) => nandWitness
compile_witness (Circomlib.NOR.circuit (p:=pBabybear)) => norWitness
-- TODO: failed to prove an array index bound.
-- compile_witness (Circomlib.MultiAND.circuit (p:=pBabybear) 4) => multiAnd4Witness

-- TODO: deterministic timeout in witness compilation.
-- compile_witness (Circomlib.MultiMux1.circuit (p:=pBabybear) 4) => multiMux1_4Witness
-- TODO: witness compiler cannot generate setters for non-static witness length.
-- compile_witness (Circomlib.Mux1.circuit (p:=pBabybear)) => mux1Witness
-- TODO: deterministic timeout in witness compilation.
-- compile_witness (Circomlib.MultiMux2.circuit (p:=pBabybear) 4) => multiMux2_4Witness
-- TODO: witness compiler cannot generate setters for non-static witness length.
-- compile_witness (Circomlib.Mux2.circuit (p:=pBabybear)) => mux2Witness
-- TODO: deterministic timeout in witness compilation.
-- compile_witness (Circomlib.MultiMux3.circuit (p:=pBabybear) 4) => multiMux3_4Witness
-- TODO: witness compiler cannot generate setters for non-static witness length.
-- compile_witness (Circomlib.Mux3.circuit (p:=pBabybear)) => mux3Witness

end Examples.WitnessLibrary
