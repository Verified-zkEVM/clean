import Clean.Utils.CostR1CS
import Clean.Utils.Primes
import Clean.Gadgets.SHA256.SHA256Compress
import Clean.Gadgets.SHA256.Xor32

/-!
# SHA-256 R1CS cost report

Evaluates the R1CS cost (witness cells, `assert` constraint rows, lookup rows) of the
SHA-256 gadgets using the `CostR1CS` meter. Counts are independent of the field; we
instantiate at `pLarge` (a small certifiable prime > 2^36) as a stand-in for the BN254
scalar field so `native_decide` primality stays cheap while satisfying `p > 2^33`.

Run with `lake env lean Clean/Examples/SHA256Cost.lean` or inspect the `#eval`s in the editor.
-/

open Clean.CostR1CS
open Gadgets.SHA256

namespace SHA256Cost

abbrev P := pLarge

/-- Cost of a formal circuit on a symbolic (variable) input. -/
def costOf {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit (F P) Input Output) : Cost :=
  circuitCost (c.main (varFromOffset Input 0)) 0

#eval ("Add32       ", costOf Add32.circuit)
#eval ("Xor32       ", costOf Xor32.circuit)
#eval ("Ch32        ", costOf Ch32.circuit)
#eval ("Maj32       ", costOf Maj32.circuit)
#eval ("UpperSigma0 ", costOf UpperSigma0.circuit)
#eval ("UpperSigma1 ", costOf UpperSigma1.circuit)
#eval ("LowerSigma0 ", costOf LowerSigma0.circuit)
#eval ("LowerSigma1 ", costOf LowerSigma1.circuit)
#eval ("SHA256Round ", costOf SHA256Round.circuit)
#eval ("Schedule    ", costOf MessageSchedule.circuit)
#eval ("SHA256Rounds", costOf SHA256Rounds.circuit)

-- `CompressBlock.circuit` = message schedule + 64 rounds + 8 Davies-Meyer adds, so its
-- cost is the sum of those components. We compute it from the parts because a direct
-- `#eval` of the ~40k-operation block is quadratic in the interpreter (too slow).
def add32Cost : Cost := costOf Add32.circuit

#eval ("CompressBlock", costOf MessageSchedule.circuit + costOf SHA256Rounds.circuit
  + add32Cost + add32Cost + add32Cost + add32Cost
  + add32Cost + add32Cost + add32Cost + add32Cost)

/-
Current pure-R1CS bit-level implementation, lookups = 0 throughout:

  Add32          witnesses  33   constraints  34
  Xor32 / Ch32   witnesses  32   constraints  32
  Σ₀/Σ₁/σ₀/σ₁    witnesses  32   constraints  32
  Maj32          witnesses  32   constraints  64
  SHA256Round    witnesses 198   constraints 232
  Schedule       witnesses  4752 constraints  4800
  64 rounds      witnesses 12672 constraints 14848
  CompressBlock  witnesses 17688 constraints 19920

The four Σ/σ functions are 3-input XORs.  Rather than the carry-save fold (which needs two
boolean asserts per bit to pin the carry), each output bit `o` is witnessed directly and pinned
with a *single* R1CS constraint `(o + 2a + 2b + 7c)(a + b − 4c + 1) = 6a + 6b − 24c`, found by an
exhaustive search over small-integer encodings (`Clean/Gadgets/SHA256/CarrySave.lean`,
`xor3_unique`/`xor3_complete`).  The constraint is linear in `o` with a multiplier that never
vanishes on the boolean cube, so its unique root is exactly `a XOR b XOR c`.  The 3-input majority
has no such single-constraint encoding (its residual quadratic form is full rank), so `Maj` keeps
the 64-constraint carry-save form.  Witness counts are unchanged.
-/

end SHA256Cost
