import Challenge.MidnightSHA256Pareto.Baseline

/-! Test input for the VK export tool: the baseline plus a gate on a new simple selector,
enabled in a new last region. Export-only: it has no `checked`, so a kernel-checking build of it
says nothing about a contract proof. -/
namespace Solution.MidnightSHA256Pareto
open Challenge.MidnightSHA256Pareto Halo2 Midnight

def base := Baseline.candidate

def extra : Keygen.GateSpec :=
  let a : Keygen.E := .var (.advice ⟨0⟩ 0)
  { name := "extra", selector := ⟨base.source.numSelectors, true⟩,
    queries := #[.advice ⟨0⟩ 0], constraints := #[("boolean", .add (.mul a a) (.mul (.const (-1)) a))] }

def candidate : Rust.Candidate where
  source := { base.source with
    numSelectors := base.source.numSelectors + 1
    gates := base.source.gates.push extra }
  k := base.k
  circuit := fun i =>
    let (_, ops, next) := base.circuit i
    ((), ops ++ [.region "extra" ((List.range 4).map (.enableGate (extra.toClean (by decide +kernel))))],
      next + 1)

end Solution.MidnightSHA256Pareto
