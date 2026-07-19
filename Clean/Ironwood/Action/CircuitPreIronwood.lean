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
open Halo2.Ironwood.Specs.Sinsemilla (Generators)
open Halo2.Ironwood.Action.Circuit

/-- Rust `Circuit::synthesize` at `FixedPostNu6_2` (= `synthesize_base`,
`circuit.rs:461-828`), in exact region-creation order, returning the witnessed
old/new-note address points (the Rust `AddressPoints`). -/
def synthesize (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp (Var AddressPoints Fp) :=
  synthesizeBase G B W cfg

end Halo2.Ironwood.Action.CircuitPreIronwood
