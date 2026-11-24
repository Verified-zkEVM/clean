import MidnightExport.Replay
import Midnight.SHA256.Semantics.Formal

/-! Shared pieces of the lowering replay fixtures. -/
namespace LoweringFixtures
open Halo2 Midnight Midnight.Keygen

/-- The Clean gate of a spec. An invalid spec keeps only its name and selector, so its
stream still reaches Lean's configuration check. -/
def cleanGate (g : GateSpec) : Gate F :=
  if h : g.valid = true then g.toClean h
  else GateSpec.toClean ⟨g.name, g.selector, #[], #[], false, false⟩ rfl

/-- The `i`th Clean lookup of a batch, for `enableLookup`; only the enabled selectors reach
the layout. -/
def cleanLookup (l : BatchedLookup) (i : Nat := 0) : LookupArgument F :=
  let empty : LookupArgument F :=
    { masterSelector := ⟨l.selectorIndex⟩
      inputs := []
      tables := []
      inputsNoSimpleSelectors := trivial
      tablesFree := by simp
      arity := rfl }
  if h : l.valid = true then (l.toClean h).getD i empty else empty

/-- The handle enabling selector `q` of a lookup that is not `owned` (Rust's `q.enable`); a
constraint-free gate on `q` that no configuration registers if there is none. -/
def lookupHandle (l : BatchedLookup) (q : Nat) : Gate F :=
  (l.handles.find? (·.selector.index == q)).getD
    (GateSpec.toClean ⟨l.name, ⟨q, false⟩, #[], #[], false, false⟩ rfl)

/-- Keygen never reads advice values. -/
def witness : WitgenIR F 1 := .native fun _ => #v[0]

def cell (region row : Nat) (kind : ColumnKind) (index : Nat) : Cell := ⟨region, row, ⟨kind, index⟩⟩

/-- The SHA-256 preimage circuit `rust_key` is about. -/
def sha : Export.Replay.Fixture :=
  { source := SHA256.configured, ops := SHA256.Semantics.Preimage.assertion.operations 0, k := 13 }

end LoweringFixtures
