import Clean.Halo2.Fixtures.Project
import Clean.Halo2.Fixtures.ActionPre
import Clean.Halo2.Fixtures.ActionPost
import Clean.Halo2.Fixtures.ActionSelMap
import Clean.Halo2.Tests.TestVkLayoutSinsemilla
import Clean.Ironwood.Action.Circuit

/-!
# VK-match test (CS): the full Orchard Action circuit

Projects the `ConstraintSystem` produced by the complete `Action.Circuit.configure`
(every chip of `circuit.rs::Circuit::configure`, in registration order) and checks it
equal to the fixtures dumped from the REAL orchard `Circuit` (`layout_dump.rs::
dump_layout_action` in the orchard checkout) — both pre-compression and
post-`compress_selectors` (the dumped 56-selector map applied mechanically).

`#guard` equality is fine (D1).
-/

namespace Halo2.Fixtures.Test.MatchAction

open Halo2.Ironwood (Fp)
open Halo2.Fixtures.Test.LayoutSinsemilla (layoutG)

def actionCS : ConstraintSystem Fp :=
  (Halo2.Ironwood.Action.Circuit.configure layoutG {}).2

/-- Registration-order query seed from the dumped pre layouts. -/
def seed : List Query :=
  actionPre.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ actionPre.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)
    ++ actionPre.instanceQueryLayout.map (fun (c, r) => Query.instance ⟨c⟩ r)

/-- The post-compression seed from the dumped post layouts. -/
def seedPost : List Query :=
  actionPost.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ actionPost.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)
    ++ actionPost.instanceQueryLayout.map (fun (c, r) => Query.instance ⟨c⟩ r)

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS seed actionCS == actionPre

-- Post-compression: the Rust-dumped selector map, applied mechanically, yields exactly
-- the dumped post-compression CS.
#guard projectCSPostMap seedPost actionSelMap actionCS == actionPost

end Halo2.Fixtures.Test.MatchAction
