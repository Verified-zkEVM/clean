import Midnight.SHA256.Synthesis

namespace Midnight.SHA256.Synthesis
open Halo2

/-- The two Rust table-loading calls become five Clean column loads. They do not
consume region indices or affect SimpleFloorPlanner placement. -/
def tableOperations : Operations F :=
  [.loadTable ⟨⟨11⟩⟩ (byteRangeRows.map fun x => (x.1 : F)),
   .loadTable ⟨⟨12⟩⟩ (byteRangeRows.map fun x => (x.2 : F)),
   .loadTable ⟨⟨13⟩⟩ (spreadRows.map fun x => (x.1 : F)),
   .loadTable ⟨⟨14⟩⟩ (spreadRows.map fun x => (x.2.1 : F)),
   .loadTable ⟨⟨15⟩⟩ (spreadRows.map fun x => (x.2.2 : F))]

theorem shaTables_operations (i : RegionIndex) : shaTables.operations i = tableOperations := rfl

def operations (activate : Nat → Nat → List (RegionOperation F)) : Operations F :=
  toOperations activate ++ tableOperations

end Midnight.SHA256.Synthesis
