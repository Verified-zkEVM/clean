module

public import Clean.Air.OrderedChannel

@[expose] public section

/-!
# Static lookups

A static lookup is a verifier-known table, read by other components through a channel. It is always
set up the same way: the table is a component whose fixed columns are the table's rows, followed by
one multiplicity column, and it pushes each row as often as it is pulled. `Lookup` bundles the
channel, that component, and its witness generation from the table's rows and what it means to be in
the table.
-/

namespace Air.Flat
variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- A verifier-known table of `height` rows of type `Row`, read through a channel. -/
structure Lookup (F : Type) [FiniteField F] (Row : TypeMap) [ProvableType Row] where
  name : String
  height : UInt64
  /-- The row at index `i`. Fixed rows can't read prover data or hints. -/
  row (i : Witgen.U64Expr F) : Witgen.M F (Row (Witgen.FExpr F))
  /-- The index of the row that equals `value`, at or above `height` if there is none. -/
  rowOf (value : Var Row F) : Witgen.U64Expr F
  /-- What it means to be in the table. Pulling a row from the lookup's channel guarantees it. -/
  Contains : Row F → Prop
  /-- `Contains` holds exactly for the rows of the table. -/
  contains_iff : ∀ value, Contains value ↔ ∃ i < height, value = (row .idx).evalRow i

namespace Lookup
variable (lookup : Lookup F Row)

/-- The channel through which other components read the table. -/
def channel : Channel F Row where
  name := lookup.name
  Guarantees value _ := lookup.Contains value

@[circuit_norm] lemma channel_name : lookup.channel.name = lookup.name := rfl
@[circuit_norm] lemma channel_guarantees (value : Row F) (data : ProverData F) :
    lookup.channel.Guarantees value data ↔ lookup.Contains value := .rfl

/-- One table row: pushes its fixed row with the given multiplicity. -/
def provider : GeneralFormalCircuit F (ProvablePair Row field) unit where
  name := lookup.name
  main | (value, multiplicity) => lookup.channel.emit multiplicity value
  channelsWithRequirements := [lookup.channel.toRaw]
  Assumptions | (value, _), _ => lookup.Contains value
  ProverAssumptions | (value, _), _, _ => lookup.Contains value
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start
    rcases input with ⟨value, multiplicity⟩
    simp_all
  completeness := by circuit_proof_start

/-- The table as a component: its fixed rows, followed by a multiplicity column. Witness
generation preallocates one row per table row, whose multiplicity counts the pulls. -/
def component : Component F where
  circuit := lookup.provider
  generation := .preallocated {
    channel := lookup.channel
    trigger := .pull
    height := lookup.height
    input i := do
      let row ← lookup.row i
      return (fromElements ((toElements row).map .fixed), .multiplicity)
    rowOf := lookup.rowOf
  }
  circuit_assumptions_of_assumptions := by
    rintro i ⟨value, multiplicity⟩ data ⟨hi, hfixed⟩ - -
    refine (lookup.contains_iff value).mpr ⟨i, hi, ?_⟩
    simp only [WitnessGeneration.PreallocatedMode.FixedAt, Witgen.M.bind_def, Witgen.M.pure_def,
      toElements, Vector.toList_append, Vector.toList_map, ProvableType.toElements_fromElements,
      List.forall₂_iff_get] at hfixed
    have h : toElements value = toElements ((lookup.row .idx).evalRow i) := by
      ext j hj
      simpa [List.getElem_append_left, hj, Witgen.M.evalRow, Witgen.eval,
        WitnessGeneration.Cell.FixedMatches, ProvableType.toElements_fromElements, circuit_norm]
        using hfixed.2 j (by simp; omega) (by simp; omega)
    simpa [ProvableType.fromElements_toElements] using congrArg (fromElements (M := Row)) h

@[circuit_norm] lemma component_name : lookup.component.circuit.name = lookup.name := rfl
@[circuit_norm] lemma component_channelsWithGuarantees :
    lookup.component.circuit.channelsWithGuarantees = [] := rfl
@[circuit_norm] lemma component_channelsWithRequirements :
    lookup.component.circuit.channelsWithRequirements = [lookup.channel.toRaw] := rfl
@[circuit_norm] lemma component_assumptions (input : lookup.component.Input F)
    (data : ProverData F) : lookup.component.Assumptions input data = True := rfl

end Lookup

namespace SoundEnsemble
variable {PublicIO : TypeMap} [ProvableType PublicIO] {balance : Balance F}

/-- Add a static lookup: its table component and its channel, which is finished right away. -/
def addLookup (soundEns : SoundEnsemble F PublicIO balance) (lookup : Lookup F Row)
    (fresh : lookup.name ∉ soundEns.tables.map (·.circuit.name) := by simp [circuit_norm])
    (fresh_channel : lookup.name ∉ soundEns.channels.map (·.name) := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO balance :=
  soundEns.addChannel lookup.channel.toRaw fresh_channel
    |>.addTable lookup.component (List.nil_subset _)
      (fun channel h_channel => by
        obtain rfl := List.mem_singleton.mp (show channel ∈ [lookup.channel.toRaw] from h_channel)
        refine ⟨List.mem_cons_self .., fun h_finished => fresh_channel ?_⟩
        exact List.mem_map.mpr ⟨_, soundEns.finished_subset h_finished, rfl⟩)
      fresh
    |>.markFinished lookup.channel.toRaw (List.mem_cons_self ..)

variable {soundEns : SoundEnsemble F PublicIO balance} {lookup : Lookup F Row}
  {fresh fresh_channel}

@[circuit_norm] lemma addLookup_tables :
    (soundEns.addLookup lookup fresh fresh_channel).tables =
      lookup.component :: soundEns.tables := rfl
@[circuit_norm] lemma addLookup_channels :
    (soundEns.addLookup lookup fresh fresh_channel).channels =
      lookup.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addLookup_finished :
    (soundEns.addLookup lookup fresh fresh_channel).finished =
      lookup.channel.toRaw :: soundEns.finished := rfl
@[circuit_norm] lemma addLookup_verifier :
    (soundEns.addLookup lookup fresh fresh_channel).verifier = soundEns.verifier := rfl

end SoundEnsemble
end Air.Flat
