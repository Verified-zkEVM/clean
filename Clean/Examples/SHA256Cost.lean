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
Current (carry-save Σ/σ/Maj), pure-R1CS bit-level implementation, lookups = 0 throughout:

  Add32          witnesses  33   constraints  34
  Xor32 / Ch32   witnesses  32   constraints  32
  Maj32 / Σ / σ  witnesses  32   constraints  64
  SHA256Round    witnesses 198   constraints 296
  Schedule       witnesses  4752 constraints  7872
  64 rounds      witnesses 12672 constraints 18944
  CompressBlock  witnesses 17688 constraints 27088

Progression of the witness count for a full block:
  - 40280  original bit-level (commit a03752e7)
  - 26904  multi-operand AddMod32
  - 17688  carry-save Σ/σ/Maj (one carry witness per output bit instead of two)

The carry-save fold uses the full-adder identity a+b+c = (a XOR b XOR c) + 2·maj(a,b,c):
each 3-input XOR (the Σ/σ functions) and the majority are computed with a single witnessed
carry bit per output bit, halving their witness count. Constraints are unchanged (still two
boolean asserts per bit). See `Clean/Gadgets/SHA256/CarrySave.lean`.
-/

end SHA256Cost
