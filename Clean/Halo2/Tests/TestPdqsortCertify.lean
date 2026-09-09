import Clean.Halo2.Keygen.PdqsortCertify

namespace Halo2.Tests.TestPdqsortCertify

open FloorPlanner

-- The elaborator is unsafe metaprogramming, not a safe constant with a substituted body.
-- In particular, importing it must not add overrides rejected by Ironwood's trust census.
run_cmd do
  let env ← Lean.getEnv
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `Clean.Halo2.Keygen.PdqsortCertify then
      unless (Lean.Compiler.implementedByAttr.ext.getModuleEntries env i).isEmpty &&
          (Lean.externAttr.ext.getModuleEntries env i).isEmpty do
        throwError "pdqsort_certify must not introduce compiled-body overrides"

pdqsort_certify empty (#[] : Array Nat) using (· < ·)
pdqsort_certify singleton (#[7] : Array Nat) using (· < ·)
pdqsort_certify small (#[4, 1, 4, 2, 0] : Array Nat) using (· < ·)

example : Pdqsort.quicksort (#[] : Array Nat) (· < ·) = #[] := empty
example : Pdqsort.quicksort (#[7] : Array Nat) (· < ·) = #[7] := singleton
example : Pdqsort.quicksort (#[4, 1, 4, 2, 0] : Array Nat) (· < ·) = #[0, 1, 2, 4, 4] :=
  small

-- Exercise the partitioning path, reverse order, and many ties above the insertion-sort cutoff.
pdqsort_certify descending (List.range 80).toArray using (· > ·)
pdqsort_certify tied ((List.range 80).map (fun i => (i, i % 4))).toArray
  using (fun a b => a.2 < b.2)

example : Pdqsort.quicksort (List.range 80).toArray (· > ·) =
    (List.range 80).reverse.toArray := by
  rw [descending]
  decide +kernel

example : (Pdqsort.quicksort ((List.range 80).map (fun i => (i, i % 4))).toArray
    (fun a b => a.2 < b.2)).toList.map Prod.snd =
      (List.range 4).flatMap (List.replicate 20) := by
  rw [tied]
  decide +kernel

/-- info: 'Halo2.Tests.TestPdqsortCertify.tied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tied

end Halo2.Tests.TestPdqsortCertify
