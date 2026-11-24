import Midnight.SHA256.Semantics.Bytes
import Midnight.SHA256.Semantics.Feedforward

/-! Source digest serialization through the existing verified native
wordToBytes circuit. The array loop preserves all source regions and copies. -/
namespace Midnight.SHA256.Semantics.Digest
open Halo2 WitnessCircuit WitnessBuild Linear

abbrev Cell := WitnessCircuit.Cell
abbrev Cache := WitnessCircuit.Cache

attribute [local irreducible] WitnessCircuit.wordToBytes

def values (env : Placed Environment F) (cells : Array Cell) : Array Nat :=
  cells.map (PrepareCircuit.cellValue env.place env.env)

def wordBytes (word : Nat) : Array Nat :=
  #[Spec.wordByte word 0, Spec.wordByte word 1, Spec.wordByte word 2, Spec.wordByte word 3]

theorem wordToBytes_output (word : Cell) (cache : Cache) (self : RegionIndex) :
    ((WitnessCircuit.wordToBytes word).run cache).output self =
      (#[.of self 3 (⟨1⟩ : Column .advice), .of self 2 (⟨1⟩ : Column .advice),
         .of self 1 (⟨1⟩ : Column .advice), .of self 0 (⟨1⟩ : Column .advice)], cache) := by
  unfold WitnessCircuit.wordToBytes
  rw [Bytes.sourceCore_eq]
  change (((Bytes.core word).output self).2.reverse, cache) = _
  rw [Bytes.core_output]
  apply Prod.ext
  · apply Array.ext'
    simp
  · rfl

theorem wordToBytes_operations (word : Cell) (cache : Cache) (self : RegionIndex) :
    ((WitnessCircuit.wordToBytes word).run cache).operations self =
      (Bytes.synthesize () word).operations self := by
  rw [Bytes.synthesize_eq_expanded]
  unfold WitnessCircuit.wordToBytes
  rw [Bytes.sourceCore_eq]
  change ([Operation.region "decompose core" ((Bytes.core word).operations self),
    .region "copy" [.constrainEqual word.cell ((Bytes.core word).output self).1.cell]] : Operations F) = _
  simp only [Bytes.expanded, circuit_norm, List.append_nil]

theorem wordToBytes_lawful (word : Cell) : Lawful (WitnessCircuit.wordToBytes word) := by
  intro cache self
  unfold WitnessCircuit.wordToBytes
  rfl

/-- The existing FormalCircuit applies directly to the original source Build,
with an arbitrary incoming cache; this helper does not change that cache. -/
theorem wordToBytes_sound (word : Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (table : Range.ByteTable env.env)
    (bound : (word.eval env.place env.env).val < 2^32)
    (hc : Constraints env.place env.env
      (((WitnessCircuit.wordToBytes word).run cache).operations self) self) :
    let output := ((WitnessCircuit.wordToBytes word).run cache).output self
    values env output.1 = wordBytes (word.eval env.place env.env).val ∧ output.2 = cache := by
  rw [wordToBytes_operations] at hc
  have h := Bytes.soundness () self env word table (by simpa only [circuit_norm] using bound) hc
  simp only [circuit_norm] at h
  have decoded := Bytes.relation_decode _ _ bound h
  have ho : Bytes.elaborated.output () word self =
      (⟨.of self 3 (⟨1⟩ : Column .advice), .of self 2 (⟨1⟩ : Column .advice),
        .of self 1 (⟨1⟩ : Column .advice), .of self 0 (⟨1⟩ : Column .advice)⟩ :
        Arithmetic.Inputs (AssignedCell F)) := rfl
  rw [ho] at decoded
  simp only [circuit_norm] at decoded
  rw [wordToBytes_output]
  constructor
  · simp only [values, wordBytes]
    simpa [PrepareCircuit.cellValue, circuit_norm] using decoded
  · rfl

theorem wordToBytes_complete (word : Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) (table : Range.ByteTable env.env.toEnvironment)
    (bound : (word.eval env.place env.env.toEnvironment).val < 2^32)
    (hw : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.wordToBytes word).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.wordToBytes word).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.wordToBytes word).run cache).output self
     values env.toEnvironment output.1 = wordBytes (word.eval env.place env.env.toEnvironment).val ∧
       output.2 = cache) := by
  have hw' := hw
  rw [wordToBytes_operations] at hw'
  have h := Bytes.completeness () self env word hw' table (by simpa only [circuit_norm] using bound) trivial
  have hc : Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.wordToBytes word).run cache).operations self) self := by
    rw [wordToBytes_operations]
    exact h.1
  exact ⟨hc, wordToBytes_sound word cache self env.toEnvironment table bound hc⟩

def appendBytes (word : Cell) (initial : Array Cell) : Build (Array Cell) := do
  let bytes ← WitnessCircuit.wordToBytes word
  return initial ++ bytes

theorem appendBytes_lawful (word : Cell) (initial : Array Cell) : Lawful (appendBytes word initial) :=
  lawful_bind (wordToBytes_lawful _) (fun _ => lawful_pure _)

theorem appendBytes_sound (word : Cell) (initial : Array Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (table : Range.ByteTable env.env)
    (bound : (word.eval env.place env.env).val < 2^32)
    (hc : Constraints env.place env.env ((appendBytes word initial cache).operations self) self) :
    let output := (appendBytes word initial cache).output self
    values env output.1 = values env initial ++ wordBytes (word.eval env.place env.env).val ∧
      output.2 = cache := by
  unfold appendBytes at hc ⊢
  rw [bind_constraints _ _ (wordToBytes_lawful _) _ _ _ _] at hc
  obtain ⟨hv, hk⟩ := wordToBytes_sound word cache self env table bound hc.1
  change values env (initial ++ (((WitnessCircuit.wordToBytes word).run cache).output self).1) = _ ∧ _
  exact ⟨by simpa only [values, Array.map_append] using congrArg (values env initial ++ ·) hv, hk⟩

theorem appendBytes_complete (word : Cell) (initial : Array Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) (table : Range.ByteTable env.env.toEnvironment)
    (bound : (word.eval env.place env.env.toEnvironment).val < 2^32)
    (hw : ExtendsWitnesses env.place env.env ((appendBytes word initial cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((appendBytes word initial cache).operations self) self ∧
    (let output := (appendBytes word initial cache).output self
     values env.toEnvironment output.1 = values env.toEnvironment initial ++
       wordBytes (word.eval env.place env.env.toEnvironment).val ∧ output.2 = cache) := by
  have hc : Constraints env.place env.env.toEnvironment ((appendBytes word initial cache).operations self) self := by
    unfold appendBytes at hw ⊢
    rw [bind_extendsWitnesses _ _ (wordToBytes_lawful _) _ _ _ _] at hw
    rw [bind_constraints _ _ (wordToBytes_lawful _) _ _ _ _]
    exact ⟨(wordToBytes_complete word cache self env table bound hw.1).1, trivial⟩
  exact ⟨hc, appendBytes_sound word initial cache self env.toEnvironment table bound hc⟩

/-- The unchanged inline final loop from WitnessCircuit.body. -/
def serialize (digest : Array Cell) : Build (Array Cell) := do
  let mut outputs := #[]
  for word in digest do outputs := outputs ++ (← WitnessCircuit.wordToBytes word)
  return outputs

def loop (items : List Cell) (initial : Array Cell) : Build (Array Cell) :=
  forIn items initial fun word cells => do return .yield (← appendBytes word cells)

theorem source_loop (digest : Array Cell) : serialize digest = loop digest.toList #[] := by
  unfold serialize loop appendBytes
  simp only [WitnessBuild.bind_assoc, WitnessBuild.pure_bind, WitnessBuild.bind_pure,
    Array.forIn_toList]

theorem loop_lawful (items : List Cell) (initial : Array Cell) : Lawful (loop items initial) :=
  lawful_forIn_list items initial _ (fun word _ cells =>
    lawful_bind (appendBytes_lawful word cells) (fun _ => lawful_pure _))

attribute [local irreducible] serialize loop

theorem serialize_lawful (digest : Array Cell) : Lawful (serialize digest) := by
  rw [source_loop]
  exact loop_lawful _ _

def BoundedWords (env : Placed Environment F) (items : List Cell) : Prop :=
  ∀ word ∈ items, (word.eval env.place env.env).val < 2^32

theorem loop_sound (items : List Cell) (initial : Array Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (table : Range.ByteTable env.env) (bound : BoundedWords env items)
    (hc : Constraints env.place env.env ((loop items initial cache).operations self) self) :
    let output := (loop items initial cache).output self
    values env output.1 = values env initial ++
      items.toArray.flatMap (fun word => wordBytes (word.eval env.place env.env).val) ∧ output.2 = cache := by
  unfold loop at hc ⊢
  apply forIn_list_prefix items initial appendBytes []
    (fun processed cells nextCache _ => values env cells = values env initial ++
      processed.toArray.flatMap (fun word => wordBytes (word.eval env.place env.env).val) ∧ nextCache = cache)
    env.place env.env (fun word _ cells => appendBytes_lawful word cells) ?_ cache self ?_ hc
  · intro processed word remaining decomposition cells nextCache nextIndex previous satisfied
    have member : word ∈ items := by rw [decomposition]; simp
    obtain ⟨hv, hk⟩ := appendBytes_sound word cells nextCache nextIndex env table
      (bound word member) satisfied
    refine ⟨?_, hk.trans previous.2⟩
    rw [hv, previous.1]
    apply Array.ext'
    simp
  · simp [values]

theorem loop_complete (items : List Cell) (initial : Array Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) (table : Range.ByteTable env.env.toEnvironment)
    (bound : BoundedWords env.toEnvironment items)
    (hw : ExtendsWitnesses env.place env.env ((loop items initial cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((loop items initial cache).operations self) self ∧
    (let output := (loop items initial cache).output self
     values env.toEnvironment output.1 = values env.toEnvironment initial ++
       items.toArray.flatMap (fun word => wordBytes (word.eval env.place env.env.toEnvironment).val) ∧
         output.2 = cache) := by
  unfold loop at hw ⊢
  apply forIn_list_prefix_complete items initial appendBytes []
    (fun processed cells nextCache _ => values env.toEnvironment cells = values env.toEnvironment initial ++
      processed.toArray.flatMap (fun word => wordBytes (word.eval env.place env.env.toEnvironment).val) ∧
        nextCache = cache)
    env.place env.env (fun word _ cells => appendBytes_lawful word cells) ?_ cache self ?_ hw
  · intro processed word remaining decomposition cells nextCache nextIndex previous witnesses
    have member : word ∈ items := by rw [decomposition]; simp
    obtain ⟨hc, hv, hk⟩ := appendBytes_complete word cells nextCache nextIndex env table
      (bound word member) witnesses
    refine ⟨hc, ?_, hk.trans previous.2⟩
    rw [hv, previous.1]
    apply Array.ext'
    simp
  · simp [values]

/-- The flattened eight-word big-endian order is the reference digest encoding. -/
theorem wordBytes_reference (words : Vector Nat 8) :
    words.toArray.flatMap wordBytes = (Spec.encodeDigest words).toArray := by
  have hw : words.toArray = #[words[0],words[1],words[2],words[3],words[4],words[5],words[6],words[7]] := by
    apply Array.ext
    · simp
    · intro i hi hj
      have bound : i < 8 := by simpa using hi
      interval_cases i <;> rfl
  rw [hw]
  apply Array.ext
  · simp [wordBytes]
  · intro i hi hj
    have bound : i < 32 := by simpa using hj
    interval_cases i <;> simp [wordBytes, Spec.encodeDigest, Vector.getElem_mapFinRange]
    all_goals rfl

theorem serialize_sound (digest : Array Cell) (words : Vector Nat 8)
    (env : Placed Environment F) (table : Range.ByteTable env.env)
    (rep : values env digest = words.toArray) (bound : ∀ i : Fin 8, words[i] < 2^32)
    (cache : Cache) (self : RegionIndex)
    (hc : Constraints env.place env.env ((serialize digest cache).operations self) self) :
    let output := (serialize digest cache).output self
    values env output.1 = (Spec.encodeDigest words).toArray ∧ output.2 = cache := by
  have hb : BoundedWords env digest.toList := by
    intro word hw
    have hm : (word.eval env.place env.env).val ∈ values env digest :=
      Array.mem_map.mpr ⟨word, Array.mem_toList_iff.mp hw, rfl⟩
    rw [rep] at hm
    obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hm
    rw [← heq]
    exact bound ⟨i, by simpa using hi⟩
  rw [source_loop] at hc ⊢
  obtain ⟨hv, hk⟩ := loop_sound digest.toList #[] cache self env table hb hc
  refine ⟨hv.trans ?_, hk⟩
  simp only [values, Array.map_empty, Array.empty_append, Array.toArray_toList]
  have he : digest.flatMap (fun word => wordBytes (word.eval env.place env.env).val) =
      (values env digest).flatMap wordBytes := by
        simp only [values, Array.flatMap_map]
        rfl
  rw [he, rep, wordBytes_reference]

theorem serialize_complete (digest : Array Cell) (words : Vector Nat 8)
    (env : Placed ProverEnvironment F) (table : Range.ByteTable env.env.toEnvironment)
    (rep : values env.toEnvironment digest = words.toArray) (bound : ∀ i : Fin 8, words[i] < 2^32)
    (cache : Cache) (self : RegionIndex)
    (hw : ExtendsWitnesses env.place env.env ((serialize digest cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((serialize digest cache).operations self) self ∧
    (let output := (serialize digest cache).output self
     values env.toEnvironment output.1 = (Spec.encodeDigest words).toArray ∧ output.2 = cache) := by
  have hb : BoundedWords env.toEnvironment digest.toList := by
    intro word hw
    change (word.eval env.place env.env.toEnvironment).val < 2^32
    have hm : (word.eval env.place env.env.toEnvironment).val ∈ values env.toEnvironment digest :=
      Array.mem_map.mpr ⟨word, Array.mem_toList_iff.mp hw, rfl⟩
    rw [rep] at hm
    obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hm
    rw [← heq]
    exact bound ⟨i, by simpa using hi⟩
  have hc : Constraints env.place env.env.toEnvironment ((serialize digest cache).operations self) self := by
    rw [source_loop] at hw ⊢
    exact (loop_complete digest.toList #[] cache self env table hb hw).1
  exact ⟨hc, serialize_sound digest words env.toEnvironment table rep bound cache self hc⟩

end Midnight.SHA256.Semantics.Digest
