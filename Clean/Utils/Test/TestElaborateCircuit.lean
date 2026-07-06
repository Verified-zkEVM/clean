import Clean.Circuit
import Clean.Gadgets.Equality
import Clean.Utils.Primes

/-!
# Regression tests for `elaborate_circuit`'s output quality

`elaborate_circuit` must produce **fully reduced** `localLength` and `output` data:
subcircuit metadata (`ElaboratedCircuit.localLength <sub>.main`,
`FormalCircuitBase.elaborated`, ...) has to be computed away at instance-creation
time, so that parent circuits and proofs never see stuck projections.

This property is invisible to `rfl`/`simp`-style tests (everything is defeq);
these tests inspect the *syntactic* result of elaboration instead:

* `assert_reduced t` normalizes `t` (applied to fresh variables) and fails if any
  circuit-metadata projection still occurs in the result.
* `assert_nat_literal t n` additionally checks a closed `localLength` is the
  expected `Nat` literal.

Regression context (Lean 4.30 bump): simp no longer rewrites inside
instance-implicit arguments, so the meta-level normalization inside
`elaborate_circuit` must run with `+instances`; without it, subcircuit data
stays stuck and blows up all downstream elaboration (e.g. the loop body of
Keccak's Permutation).
-/

open Lean Meta Elab Command

/-- Fail if any of the `forbidden` constants occurs in the normalized form of `e`. -/
private def checkNoConsts (forbidden : List Name) (e : Expr) : MetaM Unit := do
  let e ← instantiateMVars e
  let e ← withTransparency .instances <| whnf e
  let bad := forbidden.filter fun n => (e.find? fun sub => sub.isConstOf n).isSome
  unless bad.isEmpty do
    throwError "elaborated data is not reduced: found {bad} in{indentExpr e}"

/-- The circuit-metadata projections that must never survive elaboration. -/
private def forbiddenMeta : List Name :=
  [``ElaboratedCircuit.localLength, ``ElaboratedCircuit.output,
   ``FormalCircuitBase.elaborated, ``FormalCircuit.base,
   ``Circuit.localLength, ``Circuit.output]

/-- Assert that `t`, fully applied to fresh variables, normalizes without any
circuit-metadata projections left. -/
elab "assert_reduced " t:term : command => runTermElabM fun _ => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  forallTelescopeReducing (← inferType e) fun args _ => do
    checkNoConsts forbiddenMeta (mkAppN e args)

/-- Assert that `t` (of type `ℕ`, possibly under binders) reduces to the literal `n`. -/
elab "assert_nat_literal " t:term:max ppSpace n:num : command => runTermElabM fun _ => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  forallTelescopeReducing (← inferType e) fun args _ => do
    let v ← withTransparency .instances <| whnf (mkAppN e args)
    let some lit := v.rawNatLit? <|> v.nat?
      | throwError "localLength is not a literal:{indentExpr v}"
    unless lit == n.getNat do
      throwError "localLength is {lit}, expected {n.getNat}"

namespace TestElaborateCircuit
variable {p : ℕ} [Fact p.Prime]

/-! ### 1. Plain subcircuit composition (the `Equality.circuit` probe) -/

def mainPair (input : Var fieldPair (F p)) : Circuit (F p) (Expression (F p)) := do
  let z ← witnessField (.expr (input.1 + input.2))
  z === input.1
  return z

instance elaboratedPair : ElaboratedCircuit (F p) fieldPair field mainPair := by
  elaborate_circuit

-- one witness; the Equality subcircuit adds no witnesses
assert_nat_literal (elaboratedPair (p := pBabybear)).localLength 1
assert_reduced (elaboratedPair (p := pBabybear)).localLength
assert_reduced (elaboratedPair (p := pBabybear)).output

/-! ### 2. Loop (`Circuit.foldl`) whose body contains a subcircuit -/

def loopBody (acc x : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let y ← witnessField (.expr (acc + x))
  y === acc + x
  return y

def mainLoop (input : Var (fields 3) (F p)) : Circuit (F p) (Expression (F p)) :=
  .foldl input 0 loopBody

instance elaboratedLoop : ElaboratedCircuit (F p) (fields 3) field mainLoop := by
  elaborate_circuit

-- 3 iterations × one witness each
assert_nat_literal (elaboratedLoop (p := pBabybear)).localLength 3
assert_reduced (elaboratedLoop (p := pBabybear)).localLength
assert_reduced (elaboratedLoop (p := pBabybear)).output

end TestElaborateCircuit
