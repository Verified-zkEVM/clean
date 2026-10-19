module

public import Clean.Air.OrderedChannel
public import Clean.Air.WitnessGeneration

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
  valid : (row .idx).ValidForRow .fixed := by simp [circuit_norm]
  /-- What it means to be in the table. Pulling a row from the lookup's channel guarantees it. -/
  Contains : Row F → Prop
  /-- `Contains` holds exactly for the rows of the table. -/
  contains_iff : ∀ value, Contains value ↔ ∃ i < height, value = (row .idx).evalRow i

namespace Lookup
variable (lookup : Lookup F Row)

/-- The table's rows, as fixed columns. -/
def fixedColumns : FixedColumns F where
  height := lookup.height
  row := lookup.row
  valid := lookup.valid

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

omit [FiniteField F] in
/-- The first elements of a pair are those of its first component. -/
lemma take_toElements_pair {β : TypeMap} [ProvableType β] (a : Row F) (b : β F) (n : ℕ)
    (h : n = size Row) :
    (toElements (M := ProvablePair Row β) (a, b)).toList.take n = (toElements a).toList := by
  subst h
  simp only [toElements, Vector.toList_append]
  exact List.take_left' Vector.length_toList

/-- The table as a component: its fixed rows, followed by a multiplicity column. -/
def component : Component F where
  circuit := lookup.provider
  fixedColumns := some lookup.fixedColumns
  fixed_width_le_input := by simp [fixedColumns, Witgen.RowProgram.width, size]
  circuit_assumptions_of_assumptions := by
    rintro i ⟨value, multiplicity⟩ data hfixed - -
    obtain ⟨hi, hrow⟩ := hfixed _ rfl
    replace hrow :=
      (take_toElements_pair value multiplicity lookup.fixedColumns.width rfl).symm.trans hrow
    change lookup.Contains value
    refine (lookup.contains_iff value).mpr ⟨i, hi, ?_⟩
    have h : toElements value = toElements ((lookup.row .idx).evalRow i) :=
      Vector.toList_inj.mp (hrow.trans rfl)
    simpa [ProvableType.fromElements_toElements] using congrArg (fromElements (M := Row)) h

@[circuit_norm] lemma component_name : lookup.component.circuit.name = lookup.name := rfl
@[circuit_norm] lemma component_channelsWithGuarantees :
    lookup.component.circuit.channelsWithGuarantees = [] := rfl
@[circuit_norm] lemma component_channelsWithRequirements :
    lookup.component.circuit.channelsWithRequirements = [lookup.channel.toRaw] := rfl
@[circuit_norm] lemma component_assumptions (input : lookup.component.Input F)
    (data : ProverData F) : lookup.component.Assumptions input data = True := rfl

/-- Witness generation for the table: one preallocated row per table row, whose multiplicity counts
the pulls. -/
def generation : WitnessGeneration.Generation lookup.component :=
  .preallocated {
    Row := unit
    row _ := pure ()
    counters := [fun (_, multiplicity) => multiplicity]
  }

end Lookup

namespace SoundEnsemble
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Add a static lookup: its table component and its channel, which is finished right away. -/
def addLookup (soundEns : SoundEnsemble F PublicIO) (lookup : Lookup F Row)
    (fresh : lookup.name ∉ soundEns.tables.map (·.circuit.name) := by simp [circuit_norm])
    (not_finished : lookup.channel.toRaw ∉ soundEns.finished := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO :=
  soundEns.addTable lookup.component (List.nil_subset _)
    (fun channel h_channel h_mem =>
      not_finished
        (List.mem_singleton.mp (show channel ∈ [lookup.channel.toRaw] from h_mem) ▸ h_channel))
    fresh
    |>.addFinishedChannel lookup.channel.toRaw

variable {soundEns : SoundEnsemble F PublicIO} {lookup : Lookup F Row} {fresh not_finished}

@[circuit_norm] lemma addLookup_tables :
    (soundEns.addLookup lookup fresh not_finished).tables =
      lookup.component :: soundEns.tables := rfl
@[circuit_norm] lemma addLookup_channels :
    (soundEns.addLookup lookup fresh not_finished).channels =
      lookup.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addLookup_finished :
    (soundEns.addLookup lookup fresh not_finished).finished =
      lookup.channel.toRaw :: soundEns.finished := rfl
@[circuit_norm] lemma addLookup_verifier :
    (soundEns.addLookup lookup fresh not_finished).verifier = soundEns.verifier := rfl

end SoundEnsemble
end Air.Flat
