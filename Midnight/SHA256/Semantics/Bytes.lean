import Midnight.SHA256.Semantics.Arithmetic
import Midnight.SHA256.Semantics.Range
import Midnight.SHA256.Semantics.Field
import Midnight.SHA256.WitnessCircuit
import Midnight.SHA256.Spec

/-!
Semantic refinement of the actual native `wordToBytes` path. The auxiliary uses
four arithmetic rows with one term per row, range-checks their bytes in descending
row order, and copies its initial result to the source word in a second region.
-/
-- Concrete lookup proof fields use the conjunction form of `List.Forall`.
attribute [local implicit_reducible] List.Forall

namespace Midnight.SHA256.Semantics.Bytes
open Halo2

attribute [local cbv_opaque] Arithmetic.nativeGate Range.nativeLookup
attribute [local cbv_opaque] Witgen.WitgenIROver.ofFExpr
-- Keep the field dictionary symbolic: eagerly reducing its Nat.casesOn-based
-- ZMod implementation would recurse through the 255-bit modulus itself.
attribute [local cbv_opaque] BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing

def reverse (bytes : Arithmetic.Inputs F) : Arithmetic.Inputs F :=
  ⟨bytes.d, bytes.c, bytes.b, bytes.a⟩

/-- All four output cells are bytes, and their big-endian packing is the input
word. This is the relation enforced by the four native arithmetic equations. -/
def Relation (word : F) (bytes : Arithmetic.Inputs F) : Prop :=
  Arithmetic.ByteInputs bytes ∧
    word = Arithmetic.linearValue Arithmetic.byteCoefficients 0 (reverse bytes)

theorem relation_decode (word : F) (bytes : Arithmetic.Inputs F)
    (hword : word.val < 2 ^ 32) (h : Relation word bytes) :
    bytes.a.val = Spec.wordByte word.val 0 ∧
    bytes.b.val = Spec.wordByte word.val 1 ∧
    bytes.c.val = Spec.wordByte word.val 2 ∧
    bytes.d.val = Spec.wordByte word.val 3 := by
  have hr : Arithmetic.ByteInputs (reverse bytes) :=
    ⟨h.1.2.2.2, h.1.2.2.1, h.1.2.1, h.1.1⟩
  have hn : word.val = Arithmetic.packedNat (reverse bytes) := by
    apply nat_eq_of_field_eq
      (hword.trans (by norm_num [BLS12_381.scalarFieldSize]))
      ((Arithmetic.packedNat_lt _ hr).trans (by norm_num [BLS12_381.scalarFieldSize]))
    simpa only [ZMod.natCast_zmod_val, Arithmetic.linearValue_bytes_eq_nat] using h.2
  obtain ⟨ha, hb, hc, hd⟩ := h.1
  simp only [Arithmetic.packedNat, reverse] at hn
  norm_num [Spec.wordByte]
  omega

/-- The native coefficient write stencil for a one-term auxiliary row. -/
def stamp (coefficient next : F) (row : Nat) : RegionCircuit F Unit := do
  Arithmetic.nativeGate.enable row
  let _ ← assignFixed ⟨4⟩ row (-1)
  let _ ← assignFixed ⟨5⟩ row coefficient
  let _ ← assignFixed ⟨6⟩ row 0
  let _ ← assignFixed ⟨7⟩ row 0
  let _ ← assignFixed ⟨8⟩ row 0
  let _ ← assignFixed ⟨0⟩ row next
  let _ ← assignFixed ⟨1⟩ row 0
  let _ ← assignFixed ⟨2⟩ row 0
  let _ ← assignFixed ⟨3⟩ row 0
  return ()

def byteExpr (word : AssignedCell F) (index : Nat) : FExpr F :=
  .ofU64 (WitnessIR.limb (WitnessIR.readNat word) (8 * index, 8))

/-- Exact source recurrence, retaining the initial zero in each chunk fold. -/
def remainingExpr (word : AssignedCell F) : Nat → FExpr F
  | 0 => .expr word
  | i + 1 => remainingExpr word i - (.const 0 + .const ((256 ^ i : Nat) : F) * byteExpr word i)

def row (word : AssignedCell F) (index : Nat) (next : F) :
    RegionCircuit F (AssignedCell F × AssignedCell F) := do
  let result ← assignAdvice ⟨0⟩ index (.ofFExpr (remainingExpr word index))
  let byte ← assignAdvice ⟨1⟩ index (.ofFExpr (byteExpr word index))
  stamp ((256 ^ index : Nat) : F) next index
  return (result, byte)

def rangeRow (index : Nat) : RegionCircuit F Unit := do
  Range.nativeLookup.enable [] index
  let _ ← assignFixed ⟨10⟩ index 8
  return ()

def core (word : AssignedCell F) :
    RegionCircuit F (AssignedCell F × Array (AssignedCell F)) := do
  let a ← row word 0 1
  let b ← row word 1 1
  let c ← row word 2 1
  let d ← row word 3 0
  rangeRow 3
  rangeRow 2
  rangeRow 1
  rangeRow 0
  return (a.1, #[a.2, b.2, c.2, d.2])

@[circuit_norm, keygen_norm, keygen_output_norm]
theorem core_output (word : AssignedCell F) (self : RegionIndex) :
    (core word).output self =
      (.of self 0 (⟨0⟩ : Column .advice),
        #[.of self 0 (⟨1⟩ : Column .advice), .of self 1 (⟨1⟩ : Column .advice),
          .of self 2 (⟨1⟩ : Column .advice), .of self 3 (⟨1⟩ : Column .advice)]) := rfl

private def fixedValue (column : Column .fixed) (row : Nat) : F :=
  if column.index = 4 then -1 else
  if column.index = 5 then ((256 ^ row : Nat) : F) else
  if column.index = 0 then (if row < 3 then 1 else 0) else
  if column.index = 10 then 8 else 0

private theorem core_fixed_value (word : AssignedCell F) (self : RegionIndex)
    (column : Column .fixed) (row : Nat) (value : F)
    (h : .assignFixed column row value ∈ (core word).operations self) :
    value = fixedValue column row := by
  simp only [core, Bytes.row, stamp, rangeRow, circuit_norm, List.mem_cons,
    List.not_mem_nil, or_false, RegionOperation.assignFixed.injEq, reduceCtorEq,
    false_or] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl, rfl⟩
  all_goals norm_num [fixedValue]

theorem core_fixedAssignmentsAgree (word : AssignedCell F) (self : RegionIndex) :
    ((core word).operations self).FixedAssignmentsAgree := by
  intro column row left right hl hr
  exact (core_fixed_value word self column row left hl).trans
    (core_fixed_value word self column row right hr).symm

theorem sourceCore_eq (word : AssignedCell F) :
    WitnessCircuit.wordToBytesRegion word = core word := by
  funext self
  unfold WitnessCircuit.wordToBytesRegion WitnessCircuit.linearAux
    WitnessCircuit.custom WitnessCircuit.enable
  simp only [Arithmetic.activation_zero, Range.activation_three]
  cbv

/-- Direct wrapper of the source program; the cache is unused by this gadget. -/
def synthesize (_config : Unit) (word : AssignedCell F) :
    Circuit F (Arithmetic.Inputs (AssignedCell F)) := do
  let (bytes, _) ← (WitnessCircuit.wordToBytes word).run []
  return ⟨bytes[0]!, bytes[1]!, bytes[2]!, bytes[3]!⟩

/-- A finite expansion used to prove the source program's contract. -/
def expanded (_config : Unit) (word : AssignedCell F) :
    Circuit F (Arithmetic.Inputs (AssignedCell F)) := do
  let (result, bytes) ← assignRegion "decompose core" (core word)
  assignRegion "copy" (constrainEqual word result)
  return ⟨bytes[3]!, bytes[2]!, bytes[1]!, bytes[0]!⟩

@[circuit_norm, keygen_norm]
theorem synthesize_eq_expanded (config : Unit) (word : AssignedCell F) :
    synthesize config word = expanded config word := by
  unfold synthesize WitnessCircuit.wordToBytes
  rw [sourceCore_eq]
  funext self
  cbv

def configure : Unit → Configure F Unit := pure

instance elaborated : ElaboratedCircuit F Unit Unit field Arithmetic.Inputs
    configure synthesize where
  keygenRequirements :=
    { gates _ _ := [Arithmetic.nativeGate]
      lookups _ _ := [Range.nativeLookup]
      fixedColumns _ _ := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨10⟩]
      permutationColumns _ _ := [(⟨0⟩ : Column .advice)]
      inputCells _ _ word := [word.cell] }
  registered := by keygen_registration [configure, expanded, core, row, stamp, rangeRow]
  copyCellsAssigned := by
    intro config counts _ input self
    change ((synthesize config input).operations self).CopyCellsAssigned self [input.cell]
    simp only [synthesize_eq_expanded, expanded, circuit_norm, Operations.CopyCellsAssigned,
      Operations.copyCellsAssignedFrom_region_iff, Operations.copyCellsAssignedFrom_nil_iff,
      and_true]
    constructor
    · apply RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
      simp [core, row, stamp, rangeRow, circuit_norm, RegionOperation.copiedCells]
    · simp only [RegionOperations.copyCellsAssignedFrom_constrainEqual_iff,
        RegionOperations.copyCellsAssignedFrom_nil_iff, and_true]
      constructor
      · rw [RegionOperations.mem_assignedCellsAfter_iff]
        simp
      · rw [RegionOperations.mem_assignedCellsAfter_iff]
        simp [core, row, stamp, rangeRow, circuit_norm,
          RegionOperations.assignedCells, RegionOperation.assignedCells]
  fixedWritesLawful := by
    intro config counts _ input self
    change ((synthesize config input).operations self).FixedWritesLawful []
    rw [synthesize_eq_expanded]
    apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
    · simp only [expanded, circuit_norm, List.forall_cons,
        Operation.FixedAssignmentsAgree]
      constructor
      · exact core_fixedAssignmentsAgree input self
      · simp [RegionOperations.FixedAssignmentsAgree, circuit_norm]
    · simp only [expanded, circuit_norm, synthesis_summary_norm]
  lookupActivationsWellFormed := by
    intro config input self
    simp [expanded, core, row, stamp, rangeRow, Range.nativeLookup, circuit_norm]
  output _ _ self :=
    ⟨.of self 3 (⟨1⟩ : Column .advice), .of self 2 (⟨1⟩ : Column .advice),
      .of self 1 (⟨1⟩ : Column .advice), .of self 0 (⟨1⟩ : Column .advice)⟩
  output_eq := by
    intro config input self
    rw [synthesize_eq_expanded]
    rfl
  regionCount _ := 2
  regionCount_eq := by
    intro config input self
    simp only [synthesize_eq_expanded, expanded, circuit_norm, Operations.regionCount]
  synthesisSummary config input self :=
    FloorPlanner.synthesisSummary ((expanded config input).operations self)
  synthesisSummary_eq := by intro config input self; rw [synthesize_eq_expanded]

theorem soundness : ∀ config : Unit,
    FormalCircuit.Soundness (F := F) (Input := field) (Output := Arithmetic.Inputs) (Witness := fun _ => Unit) configure synthesize config
      (fun _ _ _ => ()) (fun env => Range.ByteTable env.env)
      (fun (word : F) => word.val < 2 ^ 32) (fun word bytes _ => Relation word bytes) := by
  circuit_proof_start [expanded, core, row, stamp, rangeRow, Arithmetic.nativeGate,
    Range.nativeLookup, Relation, Arithmetic.linearValue, Arithmetic.byteCoefficients,
    reverse, Arithmetic.ByteInputs]
  change Constraints place env ((synthesize cfg input_var).operations i₀) i₀ at hc
  rw [synthesize_eq_expanded] at hc
  simp only [expanded, core, row, stamp, rangeRow, Arithmetic.nativeGate,
    Range.nativeLookup, circuit_norm] at hc
  rcases hc with ⟨⟨g0, f04, f05, f06, f07, f08, f00, f01, f02, f03,
    g1, f14, f15, f16, f17, f18, f10, f11, f12, f13,
    g2, f24, f25, f26, f27, f28, f20, f21, f22, f23,
    g3, f34, f35, f36, f37, f38, f30, f31, f32, f33,
    l3, t3, l2, t2, l1, t1, l0, t0⟩, hcopy⟩
  rcases h_output with ⟨ha, hb, hc, hd⟩
  have byte (value : F)
      (hlookup : ∃ r : Nat, r < env.usableRows ∧
        [8, value] = [env.fixed ⟨11⟩ r, env.fixed ⟨12⟩ r]) : value.val < 256 := by
    obtain ⟨r, hr, heq⟩ := hlookup
    have ht := _hE.1 r hr
    have he := List.cons.inj heq
    have hv := List.cons.inj he.2
    rw [← he.1, ← hv.1] at ht
    exact (byteRangeLookup_eight value).mp ht
  constructor
  · refine ⟨byte output_a ?_, byte output_b ?_, byte output_c ?_, byte output_d ?_⟩
    · simpa only [t3, ha] using l3
    · simpa only [t2, hb] using l2
    · simpa only [t1, hc] using l1
    · simpa only [t0, hd] using l0
  · simp only [f04, f05, f06, f07, f08, f00, f01, f02, f03,
      f14, f15, f16, f17, f18, f10, f11, f12, f13,
      f24, f25, f26, f27, f28, f20, f21, f22, f23,
      f34, f35, f36, f37, f38, f30, f31, f32, f33,
      ha, hb, hc, hd] at g0 g1 g2 g3
    rw [h_input] at hcopy
    norm_num at g0 g1 g2 g3
    linear_combination -g0 -g1 -g2 -g3 + hcopy

theorem honest_packing_nat (word : Nat) (hword : word < 2 ^ 32) :
    word = word % 256 + 256 * (word / 256 % 256) +
      65536 * (word / 65536 % 256) + 16777216 * (word / 16777216 % 256) := by
  omega
theorem honest_packing (word : F) (hword : word.val < 2 ^ 32) :
    word = (word.val % 256 : Nat) + 256 * ((word.val / 256 % 256 : Nat) : F) +
      65536 * ((word.val / 65536 % 256 : Nat) : F) +
      16777216 * ((word.val / 16777216 % 256 : Nat) : F) := by
  have h := congrArg (fun n : Nat => (n : F)) (honest_packing_nat word.val hword)
  norm_num [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] at h ⊢
  exact h
theorem limb_field_val (word shift : Nat) :
    (((word / shift % 256 : Nat) : F)).val = word / shift % 256 := by
  apply ZMod.val_natCast_of_lt
  exact (Nat.mod_lt _ (by decide)).trans (by norm_num [BLS12_381.scalarFieldSize])

theorem completeness : ∀ config : Unit,
    FormalCircuit.Completeness (F := F) (Input := field) (Output := Arithmetic.Inputs)
      (Witness := fun _ => Unit) configure synthesize config
      (fun _ _ _ => ()) (fun env => Range.ByteTable env.env)
      (fun (word : F) => word.val < 2 ^ 32) (fun _ _ _ => True)
      (fun word bytes _ _ => Relation word bytes) := by
  circuit_proof_start [expanded, core, row, stamp, rangeRow, Arithmetic.nativeGate,
    Range.nativeLookup, Relation, Arithmetic.linearValue, Arithmetic.byteCoefficients,
    reverse, Arithmetic.ByteInputs]
  change ExtendsWitnesses place env ((synthesize cfg input_var).operations i₀) i₀ at hwit
  change Constraints place env.toEnvironment ((synthesize cfg input_var).operations i₀) i₀ ∧ _
  rw [synthesize_eq_expanded] at hwit ⊢
  simp only [expanded, core, row, stamp, rangeRow, Arithmetic.nativeGate,
    Range.nativeLookup, byteExpr, remainingExpr, WitnessIR.limb, WitnessIR.readNat,
    circuit_norm] at hwit ⊢
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hwit h_output ⊢
  rcases hwit with ⟨a0, b0, f04, f05, f06, f07, f08, f00, f01, f02, f03,
    a1, b1, f14, f15, f16, f17, f18, f10, f11, f12, f13,
    a2, b2, f24, f25, f26, f27, f28, f20, f21, f22, f23,
    a3, b3, f34, f35, f36, f37, f38, f30, f31, f32, f33, t3, t2, t1, t0⟩
  rcases h_output with ⟨ha, hb, hc, hd⟩
  simp only [a0, b0, a1, b1, a2, b2, a3, b3,
    f04, f05, f06, f07, f08, f00, f01, f02, f03,
    f14, f15, f16, f17, f18, f10, f11, f12, f13,
    f24, f25, f26, f27, f28, f20, f21, f22, f23,
    f34, f35, f36, f37, f38, f30, f31, f32, f33, t3, t2, t1, t0,
    h_input, Nat.shiftRight_eq_div_pow] at ha hb hc hd ⊢
  simp only [← ha, ← hb, ← hc, ← hd]
  norm_num
  have lookup (shift : Nat) : ∃ r : Nat, r < env.usableRows ∧
      (8 : F) = env.fixed ⟨11⟩ r ∧
      (((ZMod.val (n := BLS12_381.scalarFieldSize) input) / shift % 256 : Nat) : F) = env.fixed ⟨12⟩ r := by
    obtain ⟨r, hr, ht, hv⟩ := _hE.2 (((ZMod.val (n := BLS12_381.scalarFieldSize) input) / shift % 256 : Nat) : F)
      (by rw [limb_field_val]; exact Nat.mod_lt _ (by decide))
    exact ⟨r, hr, ht.symm, hv.symm⟩
  constructor
  · refine ⟨?_, lookup 16777216, lookup 65536, lookup 256, ?_⟩
    · linear_combination -(honest_packing input hA)
    · simpa using lookup 1
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, honest_packing input hA⟩
    all_goals exact (Nat.mod_le _ _).trans_lt (Nat.mod_lt _ (by decide))

end Midnight.SHA256.Semantics.Bytes
