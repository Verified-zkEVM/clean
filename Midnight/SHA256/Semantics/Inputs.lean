import Midnight.SHA256.Semantics.Padding
import Midnight.SHA256.Semantics.Range

/-! Semantics of the actual 24-byte private-input assignment loop. Soundness
extracts the assigned cells; only honest completeness refers to private programs. -/
namespace Midnight.SHA256.Semantics.Inputs
open Halo2
open Linear Block

abbrev Cell := WitnessCircuit.Cell

def byteRegion (program : WitgenIR F 1) : RegionCircuit F Cell := do
  Range.nativeLookup.enable [] 0
  let _ ← assignFixed ⟨10⟩ 0 8
  assignAdvice ⟨1⟩ 0 program

def assign (program : WitgenIR F 1) : WitnessCircuit.Build Cell :=
  WitnessCircuit.region "assign_many_small" (byteRegion program)

theorem assign_lawful (program : WitgenIR F 1) : WitnessBuild.Lawful (assign program) :=
  WitnessBuild.lawful_region _ _

theorem assign_output (program : WitgenIR F 1) (cache : Cache) (self : RegionIndex) :
    ((assign program).run cache).output self = (.of self 0 (⟨1⟩ : Column .advice), cache) := rfl

theorem assign_operations (program : WitgenIR F 1) (cache : Cache) (self : RegionIndex) :
    ((assign program).run cache).operations self =
      [.region "assign_many_small" [.enableLookup Range.nativeLookup [⟨3, false⟩] 0,
        .assignFixed ⟨10⟩ 0 8, .assignAdvice ⟨1⟩ 0 program]] := rfl

theorem assign_sound (program : WitgenIR F 1) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (ht : Range.ByteTable env.env)
    (hc : Constraints env.place env.env (((assign program).run cache).operations self) self) :
    (Block.read env (((assign program).run cache).output self).1).val < 256 := by
  rcases env with ⟨place, env⟩
  simp only [assign_operations, assign_output, Range.nativeLookup, circuit_norm, Block.read,
    Nat.add_zero, Int.add_zero] at hc ⊢
  obtain ⟨⟨row, hrow, heq⟩, hfixed⟩ := hc
  have hp : env.fixed ⟨10⟩ (place self) = env.fixed ⟨11⟩ row ∧
      env.advice ⟨1⟩ (place self) = env.fixed ⟨12⟩ row := by
    simpa only [List.cons.injEq, and_true, Nat.add_zero, Int.add_zero] using heq
  have hlookup := ht.1 row hrow
  rw [← hp.1, ← hp.2] at hlookup
  have hf : env.fixed ⟨10⟩ (place self) = 8 := by simpa using hfixed
  rw [hf] at hlookup
  simpa only [Block.read, circuit_norm, Nat.add_zero, Int.add_zero] using
    (byteRangeLookup_eight _).mp hlookup

theorem assign_complete (program : WitgenIR F 1) (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) (ht : Range.ByteTable env.env.toEnvironment)
    (hb : (program.eval env)[0].val < 256)
    (hw : ExtendsWitnesses env.place env.env (((assign program).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment (((assign program).run cache).operations self) self ∧
    Block.read env.toEnvironment (((assign program).run cache).output self).1 = (program.eval env)[0] := by
  rcases env with ⟨place, env⟩
  simp only [assign_operations, assign_output, Range.nativeLookup, circuit_norm, Block.read,
    Nat.add_zero, Int.add_zero] at hw ⊢
  obtain ⟨row, hrow, htag, hvalue⟩ := ht.2 (program.eval ⟨place, env⟩)[0] hb
  aesop

def appendAssigned (program : WitgenIR F 1) (cells : Array Cell) :
    WitnessCircuit.Build (Array Cell) := do
  let cell ← assign program
  return cells.push cell

theorem appendAssigned_lawful (program : WitgenIR F 1) (cells : Array Cell) :
    WitnessBuild.Lawful (appendAssigned program cells) :=
  WitnessBuild.lawful_bind (assign_lawful program) (fun _ => WitnessBuild.lawful_pure _)

theorem appendAssigned_output (program : WitgenIR F 1) (cells : Array Cell)
    (cache : Cache) (self : RegionIndex) :
    ((appendAssigned program cells).run cache).output self =
      (cells.push (.of self 0 (⟨1⟩ : Column .advice)), cache) := rfl

theorem appendAssigned_sound (program : WitgenIR F 1) (cells : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (ht : Range.ByteTable env.env) (hbytes : ByteInputs env cells)
    (hc : Constraints env.place env.env
      (((appendAssigned program cells).run cache).operations self) self) :
    let output := ((appendAssigned program cells).run cache).output self
    ByteInputs env output.1 ∧ output.1.size = cells.size + 1 ∧ output.2 = cache := by
  unfold appendAssigned StateT.run at hc
  rw [WitnessBuild.bind_constraints _ _ (assign_lawful _) _ _ _ _] at hc
  have hbyte := assign_sound program cache self env ht hc.1
  rw [assign_output] at hbyte
  rw [appendAssigned_output]
  refine ⟨?_, Array.size_push _, rfl⟩
  intro cell hcell
  rcases Array.mem_push.mp hcell with hc | rfl
  · exact hbytes cell hc
  · exact hbyte

theorem appendAssigned_complete (program : WitgenIR F 1) (cells : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (ht : Range.ByteTable env.env.toEnvironment) (hb : (program.eval env)[0].val < 256)
    (hw : ExtendsWitnesses env.place env.env
      (((appendAssigned program cells).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((appendAssigned program cells).run cache).operations self) self ∧
    (let output := ((appendAssigned program cells).run cache).output self
     readArray env.toEnvironment output.1 = (readArray env.toEnvironment cells).push (program.eval env)[0] ∧
       output.2 = cache) := by
  have hc : Constraints env.place env.env.toEnvironment
      (((appendAssigned program cells).run cache).operations self) self := by
    unfold appendAssigned StateT.run at hw ⊢
    rw [WitnessBuild.bind_extendsWitnesses _ _ (assign_lawful _) _ _ _ _] at hw
    rw [WitnessBuild.bind_constraints _ _ (assign_lawful _) _ _ _ _]
    exact ⟨(assign_complete program cache self env ht hb hw.1).1, trivial⟩
  refine ⟨hc, ?_⟩
  unfold appendAssigned StateT.run at hw
  rw [WitnessBuild.bind_extendsWitnesses _ _ (assign_lawful _) _ _ _ _] at hw
  have h := (assign_complete program cache self env ht hb hw.1).2
  rw [assign_output] at h
  rw [appendAssigned_output]
  exact ⟨by simp only [readArray, Array.map_push, h], rfl⟩

def loop (items : List (WitgenIR F 1)) (initial : Array Cell) : WitnessCircuit.Build (Array Cell) :=
  forIn items initial fun program cells => do return .yield (← appendAssigned program cells)

theorem source_loop (input : Vector (WitgenIR F 1) 24) :
    WitnessCircuit.assignBytes input = loop input.toList #[] := by
  have he : WitnessCircuit.enable 3 0 = Range.nativeLookup.enable [] 0 := by
    funext self
    simp only [WitnessCircuit.enable, Range.activation_three, circuit_norm]
    rfl
  unfold WitnessCircuit.assignBytes loop appendAssigned assign byteRegion
  simp only [WitnessBuild.bind_assoc, WitnessBuild.pure_bind, WitnessBuild.bind_pure, he]
  change _ = forIn input.toArray.toList _ _
  rw [Array.forIn_toList]

theorem loop_lawful (items : List (WitgenIR F 1)) (initial : Array Cell) :
    WitnessBuild.Lawful (loop items initial) :=
  WitnessBuild.lawful_forIn_list items initial _ (fun program _ cells =>
    WitnessBuild.lawful_bind (appendAssigned_lawful program cells)
      (fun _ => WitnessBuild.lawful_pure _))

theorem loop_sound (items : List (WitgenIR F 1)) (initial : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (ht : Range.ByteTable env.env) (hbytes : ByteInputs env initial)
    (hc : Constraints env.place env.env ((loop items initial cache).operations self) self) :
    let output := (loop items initial cache).output self
    ByteInputs env output.1 ∧ output.1.size = initial.size + items.length ∧ output.2 = cache := by
  apply WitnessBuild.forIn_list_prefix items initial appendAssigned []
    (fun processed cells nextCache _ => ByteInputs env cells ∧
      cells.size = initial.size + processed.length ∧ nextCache = cache) env.place env.env
    (fun program _ cells => appendAssigned_lawful program cells) ?_ cache self ?_ hc
  · intro processed program remaining _ cells nextCache nextIndex hprev hstep
    obtain ⟨hb, hs, hk⟩ := appendAssigned_sound program cells nextCache nextIndex env ht hprev.1 hstep
    refine ⟨hb, ?_, hk.trans hprev.2.2⟩
    simp only [StateT.run, List.nil_append, List.length_append, List.length_singleton] at hs hprev ⊢
    omega
  · simpa using hbytes

attribute [local irreducible] WitnessCircuit.assignBytes loop

theorem assignBytes_lawful (input : Vector (WitgenIR F 1) 24) :
    WitnessBuild.Lawful (WitnessCircuit.assignBytes input) := by
  rw [source_loop]
  exact loop_lawful _ _

/-- Verifier-side input extraction: byte bounds follow from real lookup constraints,
without any condition on the private input programs. -/
theorem assignBytes_sound (input : Vector (WitgenIR F 1) 24)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (ht : Range.ByteTable env.env)
    (hc : Constraints env.place env.env
      (((WitnessCircuit.assignBytes input).run cache).operations self) self) :
    let output := ((WitnessCircuit.assignBytes input).run cache).output self
    ByteInputs env output.1 ∧ output.1.size = 24 ∧ output.2 = cache := by
  rw [source_loop] at hc ⊢
  have h := loop_sound input.toList #[] cache self env ht (by simp [ByteInputs]) hc
  simpa [StateT.run] using h

/-- Honest programs are evaluated in the actual placed prover environment. -/
def HonestBytes (env : Placed ProverEnvironment F) (items : List (WitgenIR F 1)) : Prop :=
  ∀ program ∈ items, (program.eval env)[0].val < 256

theorem loop_complete (items : List (WitgenIR F 1)) (initial : Array Cell)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (ht : Range.ByteTable env.env.toEnvironment) (hb : HonestBytes env items)
    (hw : ExtendsWitnesses env.place env.env ((loop items initial cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((loop items initial cache).operations self) self ∧
    (let output := (loop items initial cache).output self
     readArray env.toEnvironment output.1 = readArray env.toEnvironment initial ++
       items.toArray.map (fun program => (program.eval env)[0]) ∧ output.2 = cache) := by
  unfold loop at hw ⊢
  apply WitnessBuild.forIn_list_prefix_complete items initial appendAssigned []
    (fun processed cells nextCache _ =>
      readArray env.toEnvironment cells = readArray env.toEnvironment initial ++
        processed.toArray.map (fun program => (program.eval env)[0]) ∧ nextCache = cache)
    env.place env.env (fun program _ cells => appendAssigned_lawful program cells) ?_ cache self ?_ hw
  · intro processed program remaining decomposition cells nextCache nextIndex hprev hstep
    have hmem : program ∈ items := by rw [decomposition]; simp
    obtain ⟨hc, hvalue, hk⟩ := appendAssigned_complete program cells nextCache nextIndex env ht
      (hb program hmem) hstep
    refine ⟨hc, ?_, hk.trans hprev.2⟩
    dsimp only [StateT.run] at hvalue
    rw [hvalue, hprev.1]
    apply Array.ext'
    simp
  · simp [readArray]

/-- Honest completeness derives every lookup constraint and the exact ordered
program outputs; it does not assume those values as verifier-side input facts. -/
theorem assignBytes_complete (input : Vector (WitgenIR F 1) 24)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (ht : Range.ByteTable env.env.toEnvironment) (hb : HonestBytes env input.toList)
    (hw : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.assignBytes input).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.assignBytes input).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.assignBytes input).run cache).output self
     readArray env.toEnvironment output.1 = input.toArray.map (fun program => (program.eval env)[0]) ∧
       output.2 = cache) := by
  rw [source_loop] at hw ⊢
  have h := loop_complete input.toList #[] cache self env ht hb hw
  simpa only [readArray, Array.map_empty, Array.empty_append, Vector.toArray_toList, StateT.run] using h

end Midnight.SHA256.Semantics.Inputs
