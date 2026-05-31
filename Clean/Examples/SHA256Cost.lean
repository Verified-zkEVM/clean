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

/-! ## R1CS-row validator sanity checks

Every `#eval costOf …` above already aborts if any gadget `assert` is not a single
R1CS row; the following make the validator's behaviour explicit. -/

/-- A demo variable expression. -/
private def v (n : ℕ) : Expression (F P) := .var ⟨n⟩

-- Valid single rows: the SHA-256 XOR/Maj constraint shape `A * B - C`, a bare
-- product, a boolean constraint `b·(b−1)`, and a purely affine constraint.
#eval ("xor-shape  A*B - C", isR1CSRow ((v 0 + 2*v 1 + 7*v 2) * (v 1 - 4*v 2 + 1) - 6*v 1))
#eval ("product    a*b     ", isR1CSRow (v 0 * v 1))
#eval ("boolean    b*(b-1) ", isR1CSRow (v 0 * (v 0 - 1)))
#eval ("affine     2a+b-3  ", isR1CSRow (2*v 0 + v 1 - 3))

-- Rejected: two independent products (rank-2), and degree ≥ 3. These would each
-- need an auxiliary witness + extra row, so they are not one constraint.
#eval ("REJECT a*b + c*d    ", isR1CSRow (v 0 * v 1 + v 2 * v 3))  -- expect false
#eval ("REJECT a*b*c (deg 3)", isR1CSRow (v 0 * v 1 * v 2))        -- expect false

-- Exact-count lock, including `lookups := 0` (pure R1CS). Mirrors `costOf` but
-- asserts the full triple; aborts on any drift.
def checkOf {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit (F P) Input Output) (expected : Cost) : Cost :=
  checkCost (c.main (varFromOffset Input 0)) expected 0

#eval ("Maj32 checked", checkOf Maj32.circuit { witnesses := 32, constraints := 32, lookups := 0 })

/-
Current pure-R1CS bit-level implementation, lookups = 0 throughout:

  Add32          witnesses  33   constraints  34
  Xor32 / Ch32   witnesses  32   constraints  32
  Σ₀/Σ₁/σ₀/σ₁    witnesses  32   constraints  32
  Maj32          witnesses  32   constraints  32
  SHA256Round    witnesses 198   constraints 200
  Schedule       witnesses  4704 constraints  4752
  64 rounds      witnesses 12672 constraints 12800
  CompressBlock  witnesses 17640 constraints 17824

`AddMod32` uses the minimal carry width `cw` per call: the operand sum is `< n·2^32`, so its
quotient by `2^32` is `≤ n - 1` and `cw` bits suffice when `n ≤ 2^cw`.  The round adds
(`n = 6, 7`) need `cw = 3`, but the schedule add (`n = 4`) needs only `cw = 2`, saving one
carry witness/constraint on each of the 48 schedule steps (`-48` witnesses, `-48` constraints
versus a uniform 3-bit carry).

Both the four Σ/σ functions (3-input XORs) and `Maj` (3-input majority) use a *single* R1CS
constraint per output bit.  Rather than the carry-save fold (two boolean asserts per bit), each
output bit `o` is witnessed directly and pinned with one quadratic constraint that is linear in
`o` with a multiplier that never vanishes on the boolean cube — so its unique root is exactly the
target bit-function (`Clean/Gadgets/SHA256/CarrySave.lean`):

  XOR:  `(o + 2a + 2b + 7c)(a + b − 4c + 1) = 6a + 6b − 24c`   (`xor3_unique`/`xor3_complete`)
  Maj:  `(o + a + b − 9c + 3)(a + b + 6c − 4) = −12`            (`maj3_unique`/`maj3_complete`)

Coefficients were found by SMT search; the soundness/completeness `linear_combination` cofactors
come from a Gröbner-basis ideal lift.  No symmetric single-constraint encoding of `Maj` exists
(SMT-verified), so the majority constraint is necessarily asymmetric in `(a, b, c)`.  Witness
counts are unchanged from the carry-save form.
-/

end SHA256Cost
