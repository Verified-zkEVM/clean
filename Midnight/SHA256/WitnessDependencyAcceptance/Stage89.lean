import Midnight.SHA256.WitnessDependencyAcceptance.Stage89State

/-! Round 21's ordering check lives in its own module to bound retained proof memory. -/
namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

theorem round21Ordered : DependencyPlan.ordered place round20After round21Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
