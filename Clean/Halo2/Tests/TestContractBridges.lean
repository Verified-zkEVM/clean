import Clean.Halo2
import Clean.Halo2.Tactics.ContractBridges
import Clean.Ironwood.Ecc.Add

/-!
Regression pins for `derive_contract_bridges` (C2a #2). Assert that the command generates the
five contract-projection `rfl`-bridges with the expected names and that each equals the field's
assigned value (so a consumer's `simp only [<child>_spec_eq, …]` fires exactly as with the
hand-written stack). The end-to-end acceptance is in `Clean/Ironwood/Ecc/Mul.lean` (the `Add.add`
child bridges consumed by `mul`'s soundness/completeness).
-/

namespace Halo2.ContractBridges.Test

-- generate the bridges for the `Add.add` child (unparameterized bundle)
derive_contract_bridges addTest := Ironwood.Ecc.Add.add

-- 1. the five expected bridge names exist with the right statements.
example : Ironwood.Ecc.Add.add.Spec
    = fun input output _ => output.Valid ∧ output = input.p + input.q := addTest_spec_eq
example : Ironwood.Ecc.Add.add.Assumptions
    = fun input => input.p.Valid ∧ input.q.Valid := addTest_assumptions_eq
example : Ironwood.Ecc.Add.add.EnvAssumptions = fun _ _ => True := addTest_envAssumptions_eq
example : Ironwood.Ecc.Add.add.ProverAssumptions = fun _ _ _ => True :=
  addTest_proverAssumptions_eq
example : Ironwood.Ecc.Add.add.ProverSpec = fun _ _ _ _ => True := addTest_proverSpec_eq

-- 2. the generated bridge fires under `simp only`, rewriting the folded projection (the consumer
-- pattern), exactly like a hand-written `rfl`-bridge.
example (input : Value Ironwood.Ecc.Add.Inputs Ironwood.Fp)
    (output : Value Halo2.Ironwood.Point Ironwood.Fp) (w : Unit)
    (h : Ironwood.Ecc.Add.add.Spec input output w) :
    output.Valid ∧ output = input.p + input.q := by
  simp only [addTest_spec_eq] at h
  exact h

end Halo2.ContractBridges.Test
