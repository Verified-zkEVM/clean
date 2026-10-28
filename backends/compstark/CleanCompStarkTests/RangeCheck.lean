module

public import CleanCompStark
public import Clean.Examples.FibonacciVm.Ensemble
public import CompStark.Plonky3.Batch
public import CompStark.BabyBear.Poseidon2
public import CompStark.BabyBear.Challenge

-- `#guard` runs compiled code from these modules.
public meta import CleanCompStark
public meta import Clean.Examples.FibonacciVm.Ensemble
public meta import CompStark.Plonky3.Batch
public meta import CompStark.BabyBear.Poseidon2
public meta import CompStark.BabyBear.Challenge

@[expose] public section

/-!
# A range check as a batch STARK

An ensemble of two components on the channel `bytes`: the lookup table of the bytes, its values a
fixed column and its multiplicities committed, and a table that pulls one value per row. As a
CompStark batch over BabyBear, a balanced trace pair proves and verifies, and a query out of range
unbalances the bus.
-/

namespace CleanCompStarkTests.RangeCheck
open CleanCompStark CompStark CompStark.Stark Air.Flat

abbrev p : ℕ := _root_.BabyBear.fieldSize
abbrev K : Type := _root_.BabyBear.Fast.Field
local notation "EF" => _root_.BabyBear.Fast.Ext4

instance : Fact (p > 512) := ⟨by norm_num [p, _root_.BabyBear.fieldSize]⟩

/-- A row that pulls its value from the bytes. -/
def query : GeneralFormalCircuit (F p) field unit where
  name := "query"
  main x := bytes.channel.pull x
  Spec x _ _ := x.val < 256
  ProverAssumptions x _ _ := x.val < 256
  soundness := by circuit_proof_start [bytes]; simp_all
  completeness := by circuit_proof_start [bytes]; simp_all

/-- The queries, `height` rows, which answer no demand. -/
def queries (height : UInt64) : Component (F p) where
  circuit := query
  generation := .standalone { height, input i := pure (.witness (.ofU64 i)) }

def ensemble (height : UInt64) : Ensemble (F p) unit where
  tables := [queries height, bytes.component]
  unique_names := by simp [circuit_norm, bytes, queries, query]
  channels := [bytes.channel.toRaw]
  unique_channel_names := by simp
  tables_channels := by simp [circuit_norm, bytes, queries, query]
  verifier_channels := by simp [circuit_norm, Verifier.Program.empty]

/-! ### Proving and verifying -/

/-- The queries `3 i` of 16 rows. -/
def queryRows (values : List ℕ) : List (Array (F p)) := values.map fun x => #[(x : F p)]

/-- The bytes table with the multiplicities of the values. -/
def byteRows (values : List ℕ) : List (Array (F p)) :=
  (List.range 256).map fun v => #[(v : F p), (values.count v : F p)]

def values : List ℕ := (List.range 16).map (3 * ·)

def instances : List (Batch.Instance K) :=
  [⟨toAir babyBear (queries 16) 4, 4⟩, ⟨toAir babyBear (bytes (p := p)).component 8, 8⟩]

def traces (values : List ℕ) : List (Array K) :=
  [toTrace babyBear (queries 16) (queryRows values),
    toTrace babyBear (bytes (p := p)).component (byteRows values)]

/-- FRI with blowup `4`, folding by arity `2` to a constant, and `8` queries. -/
def params : Fri.Params := ⟨2, 0, 1, 8, 0, 0, 0, 0, 0, 0⟩

def proveAndVerify (values : List ℕ) : Except String Unit :=
  Batch.verifyBatch params instances (Batch.setupBatch params instances)
    (Batch.proveBatch EF params instances (traces values) [[], []]) [[], []]

#guard toRows babyBear (bytes (p := p)).component 8 ((traces values)[1]!) == byteRows values
#guard toRows babyBear (queries 16) 4 ((traces values)[0]!) == queryRows values
#guard proveAndVerify values matches .ok ()
-- a query out of range: its value is no byte, so the bus does not balance
#guard proveAndVerify (300 :: values.tail) matches .error _

/-! ### Soundness -/

/-- The range check proves its tables' specs: every query is a byte. -/
theorem tableSoundness (height : UInt64) : (ensemble height).TableSoundness := by
  apply Ensemble.tableSoundness_of_soundChannels
  refine ⟨[bytes.channel.toRaw], by simp [ensemble], ?_, ?_, ?_⟩
  · simp [circuit_norm, ensemble, queries, query, bytes]
  · simp [circuit_norm, ensemble, queries, query, bytes]
  · simp only [List.mem_singleton, forall_eq]
    infer_instance

/-- Every query of the first table is a byte. -/
def QueriesInRange (tables : List (List (Array (F p)))) : Prop :=
  ∀ row ∈ tables.getD 0 [], (row[0]?.getD 0).val < 256

theorem witnessSound (height : UInt64) : WitnessSound (ensemble height) QueriesInRange := by
  intro witness constraints balanced
  have assumptions : witness.Assumptions := by
    intro table htable row _
    have hmem := EnsembleWitness.component_mem_tables_of_mem htable
    obtain ⟨component, rows, data, _, _, _, _, _⟩ := table
    simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> trivial
  have hspec := (tableSoundness height witness assumptions constraints balanced).2
  have hlen : 0 < witness.tables.length := by rw [← witness.same_length]; simp [ensemble]
  have hcomponent := (witness.same_circuits 0 (by simp [ensemble])).symm
  have key : ∀ table : Table (F p), table.component = queries height → table.Spec →
      ∀ row ∈ table.table, (row[0]?.getD 0).val < 256 := by
    rintro ⟨_, rows, data, _, _, _, _, _⟩ rfl hspec row hrow
    have := hspec row hrow
    simp only [Component.Spec, queries, query, circuit_norm, Table.environment,
      valueFromOffset] at this
    exact this
  intro row hrow
  rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map] at hrow
  exact key _ (by simpa [ensemble] using hcomponent) (hspec _ (List.getElem_mem hlen)) row hrow

end CleanCompStarkTests.RangeCheck
