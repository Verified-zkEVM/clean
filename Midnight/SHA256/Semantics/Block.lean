import Midnight.SHA256.Semantics.Linear
import Midnight.SHA256.Spec
import Midnight.SHA256.WitnessBuild

/-! The actual source blockFromBytes loop: native arithmetic and cache semantics
are composed into big-endian parsing of a 64-byte SHA block. -/
namespace Midnight.SHA256.Semantics.Block
open Halo2
open Linear

abbrev Cell := WitnessCircuit.Cell

def read (env : Placed Environment F) (cell : Cell) : F :=
  AssignedCell.eval env.place env.env cell

def ByteInputs (env : Placed Environment F) (bytes : Array Cell) : Prop :=
  ∀ cell ∈ bytes, (read env cell).val < 256

/-- Source coefficients and reversed cell addresses, before cache filtering. -/
def wordTerms (bytes : Array Cell) (word : Nat) : Array (F × Cell) :=
  (Array.range 4).map fun i => (((256 ^ i : Nat) : F), bytes[word*4+3-i]!)

theorem wordTerms_size (bytes : Array Cell) (word : Nat) : (wordTerms bytes word).size = 4 := by
  simp [wordTerms]

private theorem wordTerms_eq (bytes : Array Cell) (word : Nat) :
    wordTerms bytes word = #[(1, bytes[word*4+3]!), (256, bytes[word*4+2]!),
      (65536, bytes[word*4+1]!), (16777216, bytes[word*4]!)] := by
  have hr : Array.range 4 = #[0,1,2,3] := by decide +kernel
  norm_num [wordTerms, hr, Nat.add_sub_assoc]

def wordInputs (env : Placed Environment F) (bytes : Array Cell) (word : Nat) :
    Arithmetic.Inputs F :=
  ⟨read env bytes[word*4+3]!, read env bytes[word*4+2]!,
    read env bytes[word*4+1]!, read env bytes[word*4]!⟩

theorem dot_wordTerms (env : Placed Environment F) (bytes : Array Cell) (word : Nat) :
    dot env (wordTerms bytes word) =
      Arithmetic.linearValue Arithmetic.byteCoefficients 0 (wordInputs env bytes word) := by
  rw [wordTerms_eq]
  simp [dot, wordInputs, read, Arithmetic.linearValue, Arithmetic.byteCoefficients, add_assoc]

private theorem byte_at (env : Placed Environment F) (bytes : Array Cell)
    (hbytes : ByteInputs env bytes) (index : Nat) (hi : index < bytes.size) :
    (read env bytes[index]!).val < 256 := by
  apply hbytes
  rw [getElem!_pos bytes index hi]
  exact Array.getElem_mem hi

theorem wordInputs_bytes (env : Placed Environment F) (bytes : Array Cell)
    (hsize : bytes.size = 64) (hbytes : ByteInputs env bytes) (word : Nat) (hw : word < 16) :
    Arithmetic.ByteInputs (wordInputs env bytes word) := by
  refine ⟨byte_at env bytes hbytes _ ?_, byte_at env bytes hbytes _ ?_,
    byte_at env bytes hbytes _ ?_, byte_at env bytes hbytes _ ?_⟩ <;> omega

def packedWord (env : Placed Environment F) (bytes : Array Cell) (word : Nat) : Nat :=
  Specs.SHA256.bytesToWord32BE
    (read env bytes[word*4]!).val (read env bytes[word*4+1]!).val
    (read env bytes[word*4+2]!).val (read env bytes[word*4+3]!).val

theorem packedWord_eq (env : Placed Environment F) (bytes : Array Cell) (word : Nat) :
    packedWord env bytes word = Arithmetic.packedNat (wordInputs env bytes word) := by
  simp only [packedWord, Specs.SHA256.bytesToWord32BE, Arithmetic.packedNat, wordInputs]
  omega

theorem word_dot_val (env : Placed Environment F) (bytes : Array Cell)
    (hsize : bytes.size = 64) (hbytes : ByteInputs env bytes) (word : Nat) (hw : word < 16) :
    (dot env (wordTerms bytes word)).val = packedWord env bytes word := by
  rw [dot_wordTerms, Arithmetic.packedValue_val _ (wordInputs_bytes env bytes hsize hbytes word hw)]
  exact (packedWord_eq env bytes word).symm

theorem packedWord_lt (env : Placed Environment F) (bytes : Array Cell)
    (hsize : bytes.size = 64) (hbytes : ByteInputs env bytes) (word : Nat) (hw : word < 16) :
    packedWord env bytes word < 2 ^ 32 := by
  rw [packedWord_eq]
  exact Arithmetic.packedNat_lt _ (wordInputs_bytes env bytes hsize hbytes word hw)

/-- The linear continuation consumes exactly its reported region count. -/
theorem finish_nextRegionIndex (zero : Cell) (terms : Array (F × Cell)) (self : RegionIndex) :
    (Linear.finish zero terms).nextRegionIndex self =
      self + ((Linear.finish zero terms).operations self).regionCount := by
  cases he : terms.isEmpty <;> cases hs : (terms.size == 1 && terms[0]!.1 == 1) <;>
    simp_all only [Linear.finish, Bool.false_eq_true, ↓reduceIte, circuit_norm,
      Operations.regionCount, Nat.add_zero]

theorem linearCombination_nextRegionIndex (input : Array (F × Cell))
    (cache : Cache) (self : RegionIndex) :
    ((WitnessCircuit.linearCombination input).run cache).nextRegionIndex self =
      self + (((WitnessCircuit.linearCombination input).run cache).operations self).regionCount := by
  rw [linearCombination_run_finish]
  simp only [circuit_norm, Operations.regionCount_append]
  rw [finish_nextRegionIndex, constant_nextRegionIndex]
  simp [Nat.add_assoc]

/-- Fixed-size view of the actual input cells. The full parsing contract below
requires size 64, so these defaults are never read there. -/
def byteVector (env : Placed Environment F) (bytes : Array Cell) : Vector Nat 64 :=
  Vector.mapFinRange 64 fun i => (read env bytes[i.val]!).val

theorem packedWord_reference (env : Placed Environment F) (bytes : Array Cell) (word : Fin 16) :
    packedWord env bytes word.val = (Specs.SHA256.bytesToBlock (byteVector env bytes))[word] := by
  simp [packedWord, Specs.SHA256.bytesToBlock, byteVector, Nat.mul_comm,
    Vector.getElem_mapFinRange]

def expected (env : Placed Environment F) (bytes : Array Cell) : Array F :=
  (Array.range 16).map fun word => dot env (wordTerms bytes word)

theorem expected_reference (env : Placed Environment F) (bytes : Array Cell)
    (hsize : bytes.size = 64) (hbytes : ByteInputs env bytes) :
    (expected env bytes).map ZMod.val = (Specs.SHA256.bytesToBlock (byteVector env bytes)).toArray := by
  apply Array.ext
  · simp [expected]
  · intro i hi hj
    have hw : i < 16 := by simpa [expected] using hi
    simp only [expected, Array.getElem_map, Array.getElem_range]
    rw [word_dot_val env bytes hsize hbytes i hw]
    exact packedWord_reference env bytes ⟨i, hw⟩

def readArray (env : Placed Environment F) (cells : Array Cell) : Array F := cells.map (read env)

def appendWord (bytes : Array Cell) (word : Nat) (words : Array Cell) :
    WitnessCircuit.Build (Array Cell) := do
  let cell ← WitnessCircuit.linearCombination (wordTerms bytes word)
  return words.push cell

theorem linearCombination_lawful (input : Array (F × Cell)) :
    WitnessBuild.Lawful (WitnessCircuit.linearCombination input) :=
  linearCombination_nextRegionIndex input

theorem appendWord_lawful (bytes : Array Cell) (word : Nat) (words : Array Cell) :
    WitnessBuild.Lawful (appendWord bytes word words) :=
  WitnessBuild.lawful_bind (linearCombination_lawful _) (fun _ => WitnessBuild.lawful_pure _)

theorem appendWord_sound (bytes : Array Cell) (word : Nat) (words : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env ((appendWord bytes word words cache).operations self) self) :
    let output := (appendWord bytes word words cache).output self
    readArray env output.1 = (readArray env words).push (dot env (wordTerms bytes word)) ∧
      CacheMeaning env output.2 := by
  unfold appendWord at hc ⊢
  rw [WitnessBuild.bind_constraints _ _ (linearCombination_lawful _) _ _ _ _] at hc
  have hs := linearCombination_sound (wordTerms bytes word) (by rw [wordTerms_size])
    cache self env hcache hc.1
  change readArray env (words.push (((WitnessCircuit.linearCombination (wordTerms bytes word)) cache).output self).1) =
    (readArray env words).push (dot env (wordTerms bytes word)) ∧
    CacheMeaning env (((WitnessCircuit.linearCombination (wordTerms bytes word)) cache).output self).2
  exact ⟨by simpa only [readArray, Array.map_push, read, StateT.run] using
    congrArg (fun value => (readArray env words).push value) hs.1, hs.2⟩

theorem appendWord_complete (bytes : Array Cell) (word : Nat) (words : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hw : ExtendsWitnesses env.place env.env
      ((appendWord bytes word words cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      ((appendWord bytes word words cache).operations self) self := by
  unfold appendWord at hw ⊢
  rw [WitnessBuild.bind_extendsWitnesses _ _ (linearCombination_lawful _) _ _ _ _] at hw
  rw [WitnessBuild.bind_constraints _ _ (linearCombination_lawful _) _ _ _ _]
  exact ⟨linearCombination_constraints_of_witnesses (wordTerms bytes word)
    (by rw [wordTerms_size]) cache self env hw.1, trivial⟩

/-- Source loop body, with an explicit accumulator for its semantic invariant. -/
def loop (bytes : Array Cell) (items : List Nat) (initial : Array Cell) :
    WitnessCircuit.Build (Array Cell) :=
  forIn items initial fun word words => do return .yield (← appendWord bytes word words)

theorem source_loop (bytes : Array Cell) :
    WitnessCircuit.blockFromBytes bytes = loop bytes (List.range 16) #[] := by
  unfold WitnessCircuit.blockFromBytes loop appendWord wordTerms
  simp only [WitnessBuild.bind_assoc, WitnessBuild.pure_bind, WitnessBuild.bind_pure,
    Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem loop_lawful (bytes : Array Cell) (items : List Nat) (initial : Array Cell) :
    WitnessBuild.Lawful (loop bytes items initial) :=
  WitnessBuild.lawful_forIn_list items initial _ (fun item _ state =>
    WitnessBuild.lawful_bind (appendWord_lawful bytes item state)
      (fun _ => WitnessBuild.lawful_pure _))

theorem blockFromBytes_lawful (bytes : Array Cell) :
    WitnessBuild.Lawful (WitnessCircuit.blockFromBytes bytes) := by
  rw [source_loop]
  exact loop_lawful bytes _ _

theorem loop_sound (bytes : Array Cell) (items : List Nat) (initial : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env ((loop bytes items initial cache).operations self) self) :
    let output := (loop bytes items initial cache).output self
    readArray env output.1 = readArray env initial ++
      (items.toArray.map fun word => dot env (wordTerms bytes word)) ∧ CacheMeaning env output.2 := by
  apply WitnessBuild.forIn_list_prefix items initial (appendWord bytes) []
    (fun processed words nextCache _ =>
      readArray env words = readArray env initial ++
        (processed.toArray.map fun word => dot env (wordTerms bytes word)) ∧
      CacheMeaning env nextCache) env.place env.env
    (fun item _ words => appendWord_lawful bytes item words) ?_ cache self ?_ hc
  · intro processed item remaining _ words nextCache nextIndex hprev hstep
    have h := appendWord_sound bytes item words nextCache nextIndex env hprev.2 hstep
    refine ⟨?_, h.2⟩
    rw [h.1, hprev.1]
    apply Array.ext'
    simp
  · simpa using hcache

attribute [local irreducible] WitnessCircuit.blockFromBytes loop

theorem blockFromBytes_sound (bytes : Array Cell) (cache : Cache)
    (self : RegionIndex) (env : Placed Environment F) (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env
      (((WitnessCircuit.blockFromBytes bytes).run cache).operations self) self) :
    let output := ((WitnessCircuit.blockFromBytes bytes).run cache).output self
    readArray env output.1 = expected env bytes ∧ CacheMeaning env output.2 := by
  rw [source_loop] at hc ⊢
  have h := loop_sound bytes (List.range 16) #[] cache self env hcache hc
  have he : readArray env #[] ++
      ((List.range 16).toArray.map fun word => dot env (wordTerms bytes word)) = expected env bytes := by
    have hr : (List.range 16).toArray = Array.range 16 := by decide +kernel
    simp only [readArray, Array.map_empty, Array.empty_append, hr, expected]
  exact ⟨h.1.trans he, h.2⟩

theorem loop_complete (bytes : Array Cell) (items : List Nat) (initial : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hcache : CacheMeaning env.toEnvironment cache)
    (hw : ExtendsWitnesses env.place env.env ((loop bytes items initial cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((loop bytes items initial cache).operations self) self ∧
    (let output := (loop bytes items initial cache).output self
     readArray env.toEnvironment output.1 = readArray env.toEnvironment initial ++
       (items.toArray.map fun word => dot env.toEnvironment (wordTerms bytes word)) ∧
       CacheMeaning env.toEnvironment output.2) := by
  unfold loop at hw ⊢
  apply WitnessBuild.forIn_list_prefix_complete items initial (appendWord bytes) []
    (fun processed words nextCache _ =>
      readArray env.toEnvironment words = readArray env.toEnvironment initial ++
        (processed.toArray.map fun word => dot env.toEnvironment (wordTerms bytes word)) ∧
      CacheMeaning env.toEnvironment nextCache) env.place env.env
    (fun item _ words => appendWord_lawful bytes item words) ?_ cache self ?_ hw
  · intro processed item remaining _ words nextCache nextIndex hprev hstep
    have hc := appendWord_complete bytes item words nextCache nextIndex env hstep
    have h := appendWord_sound bytes item words nextCache nextIndex env.toEnvironment hprev.2 hc
    refine ⟨hc, ?_, h.2⟩
    rw [h.1, hprev.1]
    apply Array.ext'
    simp
  · simpa using hcache

theorem blockFromBytes_complete (bytes : Array Cell) (cache : Cache)
    (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hcache : CacheMeaning env.toEnvironment cache)
    (hw : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.blockFromBytes bytes).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.blockFromBytes bytes).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.blockFromBytes bytes).run cache).output self
     readArray env.toEnvironment output.1 = expected env.toEnvironment bytes ∧
       CacheMeaning env.toEnvironment output.2) := by
  have hc : Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.blockFromBytes bytes).run cache).operations self) self := by
    rw [source_loop] at hw ⊢
    exact (loop_complete bytes (List.range 16) #[] cache self env hcache hw).1
  exact ⟨hc, blockFromBytes_sound bytes cache self env.toEnvironment hcache hc⟩

/-- Actual source output cells encode the reference's 16 big-endian words,
with an unchanged meaningful cache. Bounds exclude every default input read. -/
theorem blockFromBytes_reference (bytes : Array Cell) (hsize : bytes.size = 64)
    (env : Placed Environment F) (hbytes : ByteInputs env bytes)
    (cache : Cache) (self : RegionIndex) (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env
      (((WitnessCircuit.blockFromBytes bytes).run cache).operations self) self) :
    let output := ((WitnessCircuit.blockFromBytes bytes).run cache).output self
    output.1.size = 16 ∧
      (output.1.map fun cell => (read env cell).val) =
        (Specs.SHA256.bytesToBlock (byteVector env bytes)).toArray ∧ CacheMeaning env output.2 := by
  obtain ⟨h, hcache⟩ := blockFromBytes_sound bytes cache self env hcache hc
  refine ⟨?_, ?_, hcache⟩
  · have hs := congrArg Array.size h
    simpa only [readArray, expected, Array.size_map, Array.size_range] using hs
  · have hv := congrArg (fun values : Array F => values.map ZMod.val) h
    have hr := expected_reference env bytes hsize hbytes
    simpa only [readArray, Array.map_map, Function.comp_def] using hv.trans hr

end Midnight.SHA256.Semantics.Block
