import Clean.Halo2
import Midnight.SHA256.Semantics.Tables
import Midnight.SHA256.Configure

/-! The native byte-assignment gadget, with the range table contract discharged
by the actual table loader. Private inputs are genuine Clean prover programs;
soundness makes no assumption about their honest evaluation. -/

-- Lookup proof fields normalize concrete `List.Forall` propositions to conjunctions.
attribute [local implicit_reducible] List.Forall

namespace Midnight.SHA256.Semantics.Range
open Halo2

def nativeLookup : LookupArgument F where
  masterSelector := ⟨3⟩
  inputs := [queryFixed ⟨10⟩, queryAdvice ⟨1⟩ 0]
  tables := [queryFixed ⟨11⟩, queryFixed ⟨12⟩]
  inputsNoSimpleSelectors := by selector_free
  tablesFree := by selector_free
  arity := rfl

@[keygen_norm] theorem nativeLookup_noAux : nativeLookup.auxiliarySelectorIndices = [] := rfl

theorem activation_three (row : Nat) : SHA256.activation 3 row =
    [.enableLookup nativeLookup [⟨3, false⟩] row] := by
  have hg : SHA256.cleanGates.filter (fun g => g.selector.index == 3) = [] := by
    decide +kernel
  have hl : SHA256.cleanLookups.filter (fun l => l.masterSelector.index == 3) =
      [nativeLookup] := by decide +kernel
  simp [SHA256.activation, hg, hl]

/-- Only table contents are assumed about the ambient environment. -/
def ByteTable (env : Environment F) : Prop :=
  (∀ row : Nat, row < env.usableRows →
    ByteRangeLookup (env.fixed ⟨11⟩ row) (env.fixed ⟨12⟩ row)) ∧
  (∀ value : F, value.val < 256 → ∃ row : Nat, row < env.usableRows ∧
    env.fixed ⟨11⟩ row = 8 ∧ env.fixed ⟨12⟩ row = value)

theorem byteTable_of_load {place : RegionIndex → Nat} {env : Environment F} (i : RegionIndex)
    (h : Constraints place env ((loadRange ⟨⟨11⟩⟩ ⟨⟨12⟩⟩ [8]).operations i) i)
    (hsize : byteRangeRows.length ≤ env.usableRows) : ByteTable env := by
  constructor
  · exact loadByteRange_sound _ _ i h
  · intro value hv
    exact loadByteRange_complete _ _ i h hsize ((byteRangeLookup_eight value).mpr hv)

end Midnight.SHA256.Semantics.Range
