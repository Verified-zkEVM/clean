import Midnight.SHA256.Semantics.Block

/-! Source padding for the 24-byte example. Constants are obtained through the
actual canonical-value cache, and the result has the reference SHA padding. -/
namespace Midnight.SHA256.Semantics.Padding
open Halo2
open Linear Block

abbrev Cell := WitnessCircuit.Cell

def paddedFields (bytes : Array F) : Array F :=
  bytes.push 128 ++ Array.replicate 31 0 ++ #[0,0,0,0,0,0,0,192]

def appendConstant (n : Nat) (cells : Array Cell) : WitnessCircuit.Build (Array Cell) := do
  let cell ← WitnessCircuit.constant n
  return cells.push cell

theorem constant_lawful (n : Nat) : WitnessBuild.Lawful (WitnessCircuit.constant n) :=
  constant_nextRegionIndex n

theorem appendConstant_lawful (n : Nat) (cells : Array Cell) :
    WitnessBuild.Lawful (appendConstant n cells) :=
  WitnessBuild.lawful_bind (constant_lawful _) (fun _ => WitnessBuild.lawful_pure _)

theorem appendConstant_sound (n : Nat) (cells : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env ((appendConstant n cells cache).operations self) self) :
    let output := (appendConstant n cells cache).output self
    readArray env output.1 = (readArray env cells).push (n : F) ∧ CacheMeaning env output.2 := by
  unfold appendConstant at hc ⊢
  rw [WitnessBuild.bind_constraints _ _ (constant_lawful _) _ _ _ _] at hc
  have hs := constant_sound n cache self env hcache hc.1
  change readArray env (cells.push (((WitnessCircuit.constant n) cache).output self).1) =
    (readArray env cells).push (n : F) ∧ CacheMeaning env (((WitnessCircuit.constant n) cache).output self).2
  exact ⟨by simpa only [readArray, Array.map_push, Block.read, StateT.run] using
    congrArg (fun value => (readArray env cells).push value) hs.1, hs.2⟩

theorem appendConstant_complete (n : Nat) (cells : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hw : ExtendsWitnesses env.place env.env
      ((appendConstant n cells cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      ((appendConstant n cells cache).operations self) self := by
  unfold appendConstant at hw ⊢
  rw [WitnessBuild.bind_extendsWitnesses _ _ (constant_lawful _) _ _ _ _] at hw
  rw [WitnessBuild.bind_constraints _ _ (constant_lawful _) _ _ _ _]
  exact ⟨constant_constraints_of_witnesses n cache self env hw.1, trivial⟩

theorem paddedFields_size (bytes : Array F) (hsize : bytes.size = 24) :
    (paddedFields bytes).size = 64 := by
  simp [paddedFields, hsize]

theorem paddedFields_reference (message : Vector F 24) :
    ((paddedFields message.toArray).map ZMod.val).toList =
      Spec.paddedBytes (message.map scalarNat) := by
  have h128 : (128 : F).val = 128 := by decide +kernel
  have h192 : (192 : F).val = 192 := by decide +kernel
  simp [paddedFields, Spec.paddedBytes, Vector.toList_map, h128, h192]
  rfl

/-- Exact stateful constant loop used for the encoded 192-bit message length. -/
def constantLoop (items : List Nat) (initial : Array Cell) : WitnessCircuit.Build (Array Cell) :=
  forIn items initial fun n cells => do return .yield (← appendConstant n cells)

theorem constantLoop_lawful (items : List Nat) (initial : Array Cell) :
    WitnessBuild.Lawful (constantLoop items initial) :=
  WitnessBuild.lawful_forIn_list items initial _ (fun n _ cells =>
    WitnessBuild.lawful_bind (appendConstant_lawful n cells)
      (fun _ => WitnessBuild.lawful_pure _))

theorem constantLoop_sound (items : List Nat) (initial : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env ((constantLoop items initial cache).operations self) self) :
    let output := (constantLoop items initial cache).output self
    readArray env output.1 = readArray env initial ++ items.toArray.map (fun n : Nat => (n : F)) ∧
      CacheMeaning env output.2 := by
  apply WitnessBuild.forIn_list_prefix items initial appendConstant []
    (fun processed cells nextCache _ =>
      readArray env cells = readArray env initial ++ processed.toArray.map (fun n : Nat => (n : F)) ∧
      CacheMeaning env nextCache) env.place env.env
    (fun n _ cells => appendConstant_lawful n cells) ?_ cache self ?_ hc
  · intro processed n remaining _ cells nextCache nextIndex hprev hstep
    have h := appendConstant_sound n cells nextCache nextIndex env hprev.2 hstep
    refine ⟨?_, h.2⟩
    rw [h.1, hprev.1]
    apply Array.ext'
    simp
  · simpa using hcache

theorem constantLoop_complete (items : List Nat) (initial : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hcache : CacheMeaning env.toEnvironment cache)
    (hw : ExtendsWitnesses env.place env.env ((constantLoop items initial cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((constantLoop items initial cache).operations self) self ∧
    (let output := (constantLoop items initial cache).output self
     readArray env.toEnvironment output.1 = readArray env.toEnvironment initial ++
       items.toArray.map (fun n : Nat => (n : F)) ∧ CacheMeaning env.toEnvironment output.2) := by
  unfold constantLoop at hw ⊢
  apply WitnessBuild.forIn_list_prefix_complete items initial appendConstant []
    (fun processed cells nextCache _ =>
      readArray env.toEnvironment cells = readArray env.toEnvironment initial ++
        processed.toArray.map (fun n : Nat => (n : F)) ∧ CacheMeaning env.toEnvironment nextCache)
    env.place env.env (fun n _ cells => appendConstant_lawful n cells) ?_ cache self ?_ hw
  · intro processed n remaining _ cells nextCache nextIndex hprev hstep
    have hc := appendConstant_complete n cells nextCache nextIndex env hstep
    have h := appendConstant_sound n cells nextCache nextIndex env.toEnvironment hprev.2 hc
    refine ⟨hc, ?_, h.2⟩
    rw [h.1, hprev.1]
    apply Array.ext'
    simp
  · simpa using hcache

/-- A decomposition of the unchanged source program, including cache hits. -/
def sourcePad (bytes : Array Cell) : WitnessCircuit.Build (Array Cell) := do
  let one ← WitnessCircuit.constant 128
  let zero ← WitnessCircuit.constant 0
  constantLoop [0,0,0,0,0,0,0,192] (bytes.push one ++ Array.replicate 31 zero)

theorem source_pad (bytes : Array Cell) : WitnessCircuit.pad bytes = sourcePad bytes := by
  unfold WitnessCircuit.pad sourcePad constantLoop appendConstant
  simp only [WitnessBuild.bind_assoc, WitnessBuild.pure_bind, WitnessBuild.bind_pure]
  rfl

attribute [local irreducible] WitnessCircuit.pad constantLoop WitnessCircuit.constant

theorem pad_lawful (bytes : Array Cell) : WitnessBuild.Lawful (WitnessCircuit.pad bytes) := by
  rw [source_pad]
  exact WitnessBuild.lawful_bind (constant_lawful 128) (fun _ =>
    WitnessBuild.lawful_bind (constant_lawful 0) (fun _ => constantLoop_lawful _ _))

theorem pad_sound (bytes : Array Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env (((WitnessCircuit.pad bytes).run cache).operations self) self) :
    let output := ((WitnessCircuit.pad bytes).run cache).output self
    readArray env output.1 = paddedFields (readArray env bytes) ∧ CacheMeaning env output.2 := by
  rw [source_pad] at hc ⊢
  unfold sourcePad StateT.run at hc ⊢
  rw [WitnessBuild.bind_constraints _ _ (constant_lawful _) _ _ _ _] at hc
  have h1 := constant_sound 128 cache self env hcache hc.1
  have hc2 := hc.2
  rw [WitnessBuild.bind_constraints _ _ (constant_lawful _) _ _ _ _] at hc2
  have h2 := constant_sound 0 _ _ env h1.2 hc2.1
  have h3 := constantLoop_sound [0,0,0,0,0,0,0,192] _ _ _ env h2.2 hc2.2
  simp only [WitnessBuild.bind_output]
  refine ⟨h3.1.trans ?_, h3.2⟩
  simp only [readArray, Array.map_append, Array.map_push, Array.map_replicate, Block.read,
    paddedFields]
  dsimp only [StateT.run] at h1 h2
  rw [h1.1, h2.1]
  norm_num

theorem pad_complete (bytes : Array Cell) (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) (hcache : CacheMeaning env.toEnvironment cache)
    (hw : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.pad bytes).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.pad bytes).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.pad bytes).run cache).output self
     readArray env.toEnvironment output.1 = paddedFields (readArray env.toEnvironment bytes) ∧
       CacheMeaning env.toEnvironment output.2) := by
  have hc : Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.pad bytes).run cache).operations self) self := by
    rw [source_pad] at hw ⊢
    unfold sourcePad StateT.run at hw ⊢
    rw [WitnessBuild.bind_extendsWitnesses _ _ (constant_lawful _) _ _ _ _] at hw
    rw [WitnessBuild.bind_constraints _ _ (constant_lawful _) _ _ _ _]
    have h1 := constant_complete 128 cache self env hcache hw.1
    refine ⟨h1.1, ?_⟩
    have hw2 := hw.2
    rw [WitnessBuild.bind_extendsWitnesses _ _ (constant_lawful _) _ _ _ _] at hw2
    rw [WitnessBuild.bind_constraints _ _ (constant_lawful _) _ _ _ _]
    have h2 := constant_complete 0 _ _ env h1.2.2 hw2.1
    exact ⟨h2.1, (constantLoop_complete _ _ _ _ env h2.2.2 hw2.2).1⟩
  exact ⟨hc, pad_sound bytes cache self env.toEnvironment hcache hc⟩

theorem paddedFields_bytes (bytes : Array F) (hbytes : ∀ value ∈ bytes, value.val < 256) :
    ∀ value ∈ paddedFields bytes, value.val < 256 := by
  intro value hv
  have h0 : (0 : F).val < 256 := by decide +kernel
  have h128 : (128 : F).val < 256 := by decide +kernel
  have h192 : (192 : F).val < 256 := by decide +kernel
  simp [paddedFields] at hv
  aesop

/-- The verifier-extracted message; private witness hints do not appear here. -/
def message (env : Placed Environment F) (bytes : Array Cell) (hsize : bytes.size = 24) :
    Vector F 24 := ⟨readArray env bytes, by simpa only [readArray, Array.size_map] using hsize⟩

/-- Actual source padding produces 64 byte-valued cells and exactly the reference
padding of the input cells' assigned values, preserving the constant-cache invariant. -/
theorem pad_reference (bytes : Array Cell) (hsize : bytes.size = 24)
    (env : Placed Environment F) (hbytes : ByteInputs env bytes)
    (cache : Cache) (self : RegionIndex) (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env (((WitnessCircuit.pad bytes).run cache).operations self) self) :
    let output := ((WitnessCircuit.pad bytes).run cache).output self
    output.1.size = 64 ∧ ByteInputs env output.1 ∧
      (output.1.map fun cell => (Block.read env cell).val).toList =
        Spec.paddedBytes ((message env bytes hsize).map scalarNat) ∧ CacheMeaning env output.2 := by
  obtain ⟨h, hcache⟩ := pad_sound bytes cache self env hcache hc
  have hs : (readArray env bytes).size = 24 := by simpa only [readArray, Array.size_map] using hsize
  have hb : ∀ value ∈ readArray env bytes, value.val < 256 := by
    intro value hv
    obtain ⟨cell, hc, rfl⟩ := Array.mem_map.mp hv
    exact hbytes cell hc
  refine ⟨?_, ?_, ?_, hcache⟩
  · have hsize' := congrArg Array.size h
    simpa only [readArray, Array.size_map] using hsize'.trans (paddedFields_size _ hs)
  · intro cell hc
    have hm : Block.read env cell ∈ readArray env
        (((WitnessCircuit.pad bytes).run cache).output self).1 :=
      Array.mem_map.mpr ⟨cell, hc, rfl⟩
    rw [h] at hm
    exact paddedFields_bytes _ hb _ hm
  · have hv := congrArg (fun values : Array F => (values.map ZMod.val).toList) h
    have hr := paddedFields_reference (message env bytes hsize)
    simpa only [readArray, Array.map_map, Function.comp_def, message] using hv.trans hr

end Midnight.SHA256.Semantics.Padding
