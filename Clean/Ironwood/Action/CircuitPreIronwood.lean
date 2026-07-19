import Clean.Ironwood.Action.Circuit

/-!
# The pre-ironwood Orchard Action circuit (fixed post-NU 6.2)

The historical/current-network circuit: `Circuit::synthesize_base` alone — the staged
composition of the witness, integrity-check, and note-commitment stages, WITHOUT the
ironwood `"post-NU 6.3 cross-address checks"` region. The ironwood circuit (this
repo's main target) is `Action.Circuit.synthesize`; both share `configure` (the
constraint system is version-independent — `Config::configure` on the ironwood
branch), all three stages, and therefore all VK CS fixtures.
-/

namespace Halo2.Ironwood.Action.CircuitPreIronwood

open Halo2.Ironwood (Fp)
open Orchard.Specs.Sinsemilla (Generators)
open Halo2.Ironwood.Action.Circuit

/-- Rust `Circuit::synthesize` at `FixedPostNu6_2` (= `synthesize_base`,
`circuit.rs:461-828`), in exact region-creation order. -/
def synthesize (G : Generators) (B : Bases) (W : Witnesses) (cfg : Config) :
    Circuit Fp NoteCells := do
  let wc ← synthWitness G W cfg
  let cc ← synthChecks G B W cfg wc
  synthNotes G B W cfg wc cc

end Halo2.Ironwood.Action.CircuitPreIronwood
