import Clean.Ironwood.Action.Circuit

/-!
# The pre-NU6.3 Orchard Action circuit (fixed post-NU6.2)

The historical/current-network circuit: `Circuit::synthesize_base` alone — the staged
composition of the witness, integrity-check, and note-commitment stages, WITHOUT the
`"post-NU 6.3 cross-address checks"` region. The post-NU6.3 circuit (this repo's main
target) is `Action.Circuit.synthesize`; both share `configure` (the constraint system
is version-independent — `Config::configure` on orchard's `ironwood` branch), all three
stages, and therefore all VK CS fixtures.
-/

namespace Zcash.Circuits.Action.CircuitPreNU63

open Halo2
open Specs.Sinsemilla (Generators)
open Action.Circuit

/-- Rust `Circuit::synthesize` at `FixedPostNu6_2` (= `synthesize_base`,
`circuit.rs:461-828`), in exact region-creation order, returning the witnessed
old/new-note address points (the Rust `AddressPoints`). -/
def synthesize (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp (Var AddressPoints Fp) :=
  synthesizeBase G B W cfg

end Zcash.Circuits.Action.CircuitPreNU63
