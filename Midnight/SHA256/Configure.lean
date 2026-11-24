import Midnight.Frontend.SHA256
import Midnight.Keygen.Encoding
import Clean.Halo2.Operations

/-! The SHA-256 example's configuration: its Clean configure program, `Frontend.SHA256.configure`,
compiled by the Midnight backend. `Backend.Checks.sha256_cs` compares it with a frozen fixture. -/
namespace Midnight.SHA256
open Midnight.Keygen

def configured : CS := Backend.compile Frontend.SHA256.configure

/-- The architecture whose `ZkStdLib::configure` this is; it does not depend on `k`. -/
def architecture : Architecture := { sha2_256 := true }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configured_gates_valid : configured.gates.toList.all GateSpec.valid = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configured_lookups_valid : configured.lookups.toList.all BatchedLookup.valid = true := by
  decide +kernel

/-- Source gates as proof-carrying Clean objects. -/
def cleanGates : List (Halo2.Gate F) :=
  configured.gates.toList.attach.map fun ⟨g, hg⟩ =>
    g.toClean ((List.all_eq_true.mp configured_gates_valid) g hg)

/-- The three active-row memberships: one range tuple, two SHA spread tuples. -/
def cleanLookups : List (Halo2.LookupArgument F) :=
  configured.lookups.toList.attach.flatMap fun ⟨l, hl⟩ =>
    l.toClean ((List.all_eq_true.mp configured_lookups_valid) l hl)

/-- Translate one source selector enable to its real Clean constraints. A batched
lookup activates each tuple; the source batched protocol structure is kept in CS. -/
def activation (s row : Nat) : List (Halo2.RegionOperation F) :=
  (cleanGates.filter (·.selector.index == s)).map (fun g => .enableGate g row) ++
    (cleanLookups.filter (·.masterSelector.index == s)).map
      (fun l => .enableLookup l [⟨s, false⟩] row)

end Midnight.SHA256
