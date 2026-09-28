module

public import Clean.Circuit.SimplifyFormal
public import Clean.Circuit.Basic
public import Clean.Circuit.Provable
public import Clean.Gadgets.Equality
public import Clean.Backends.Circom.Compile
public import Clean.Backends.Circom.R1CS
public import Clean.Utils.Field
public import Clean.Utils.FiniteField
public import Clean.Utils.Primes
public import Clean.Specs.Poseidon
public import Clean.Circomlib.Poseidon

public meta import Clean.Circuit.SimplifyFormal
public meta import Clean.Circuit.Basic
public meta import Clean.Circuit.Provable
public meta import Clean.Gadgets.Equality
public meta import Clean.Backends.Circom.Compile
public meta import Clean.Backends.Circom.R1CS
public meta import Clean.Utils.Field
public meta import Clean.Utils.FiniteField
public meta import Clean.Utils.Primes
public meta import Clean.Specs.Poseidon
public meta import Clean.Circomlib.Poseidon

@[expose] public section

/-!
# Certified simplification tests

Sanity checks on the executable behaviour of `simplifyFlat` and `FormalCircuit.simplify`.
-/

open Circuit.Simplify

namespace TestSimplify

abbrev Fp := F p1009

def hasSubstr (s needle : String) : Bool := (s.splitOn needle).length > 1

def jsonNat (json key : String) : Option ℕ :=
  match json.splitOn s!"\"{key}\": " with
  | _ :: rest :: _ => (rest.takeWhile Char.isDigit).toNat?
  | _ => none

def hasCommand (cmd : String) : IO Bool := do
  let r ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {cmd}"] }
  pure (r.exitCode = 0)

/-- The normalized linear form of an assert, if linear. -/
def linearOf : FlatOperation Fp → Option (Fp × List (ℕ × Fp))
  | .assert e => (toLinear? e).map fun (k, lc) => (k, normalize lc)
  | _ => none

/-- A syntactic witness of unsatisfiability: a nonzero constant assert `k = 0`, or two
linear asserts with the same terms and different constants. -/
def hasContradiction (ops : List (FlatOperation Fp)) : Bool :=
  let lins := ops.filterMap linearOf
  lins.any (fun (k, lc) => lc == [] && k != 0) ||
  lins.any (fun (k, lc) => lins.any fun (k', lc') => lc == lc' && k != k')

/-! ### iden3/circom#425 at the `Operations` level

Variables: `0` = `a`, `1` = `b` (inputs, forbidden), `2` = `o` (output, forbidden), `3` = `x`.
circom's `--O1` drops `x = 3` and `--O2` makes the system satisfiable; the certified pass
keeps the contradiction: with `maxVars = 1` as the constant assert `-2 = 0`, with larger
`maxVars` (where `x = a + b` is consumed first) as the pair `a + b = 3`, `a + b = 5`. -/

def v (i : ℕ) : Expression Fp := .var ⟨i⟩

def pins : List (FlatOperation Fp) :=
  [ .assert (v 3 - (v 0 + v 1)),   -- x = a + b
    .assert (v 3 - 3),             -- x = 3
    .assert (v 3 - 5),             -- x = 5
    .assert (v 2 - (v 3 + v 0)) ]  -- o = x + a

def fb425 : ℕ → Bool := fun i => i ≤ 2

#eval! (do
  for maxVars in [1, 4] do
    let (ops, subst) := simplifyFlat fb425 maxVars pins
    IO.println s!"#425 maxVars={maxVars}: {(FlatOperation.constraints ops).length} asserts, {subst.length} substitutions"
    unless hasContradiction ops do
      throw <| IO.userError s!"FAIL: #425 (maxVars={maxVars}): contradiction was lost"
  IO.println "OK: #425 contradiction preserved by the certified pass" : IO Unit)

/-! ### Poseidon1: regression on the counts

Asserts at the `Operations` level, and R1CS constraints after the (unchanged) lowering. -/

def poseidonInput : Var field Specs.Poseidon.F := varFromOffset field 0

def countsOf (c : FormalCircuit Specs.Poseidon.F field field) : IO (ℕ × ℕ × Option ℕ) := do
  let ops := (c.main poseidonInput).operations 1
  let flat := Operations.toFlat ops
  let r ← match Backends.Circom.compileR1CS Specs.Poseidon.BN254_PRIME 1 ["in"] [402] ops 4 with
    | .ok s => pure s | .error e => throw <| IO.userError s!"FAIL: Poseidon1 compileR1CS: {e}"
  pure ((FlatOperation.constraints flat).length, FlatOperation.localLength flat, jsonNat r "nConstraints")

#eval! (do
  let c := Circomlib.Poseidon.Poseidon1.circuit
  let expected : List (String × FormalCircuit Specs.Poseidon.F field field × ℕ × ℕ × Option ℕ) :=
    [ ("original", c, 402, 402, some 618),
      ("simplify 1", c.simplify 1, 339, 402, some 552),
      ("simplify 64", c.simplify 64, 213, 402, some 426) ]
  for (label, circ, asserts, witnesses, r1cs) in expected do
    let got ← countsOf circ
    IO.println s!"Poseidon1 {label}: asserts={got.1} witnesses={got.2.1} R1CS constraints={got.2.2}"
    unless got == (asserts, witnesses, r1cs) do
      throw <| IO.userError s!"FAIL: Poseidon1 {label}: expected {(asserts, witnesses, r1cs)}"
  IO.println "OK: Poseidon1 simplification counts" : IO Unit)

end TestSimplify
