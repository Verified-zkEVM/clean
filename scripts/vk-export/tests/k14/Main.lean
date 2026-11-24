import Challenge.MidnightSHA256Pareto.Baseline

/-! Export-only fixture for the VK export tool: the baseline circuit on a 2^14 domain, as an
`Rust.Candidate`, which a submission's `Configured.Candidate` compiles to. It has no
`checked`, so a kernel-checking build of it says nothing about a contract proof. -/
namespace Solution.MidnightSHA256Pareto
open Challenge.MidnightSHA256Pareto

def candidate : Rust.Candidate := { Baseline.candidate with k := 14 }

end Solution.MidnightSHA256Pareto
