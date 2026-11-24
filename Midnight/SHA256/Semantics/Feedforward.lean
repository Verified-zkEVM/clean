import Midnight.SHA256.Semantics.RoundGadgets
import Midnight.SHA256.Semantics.Block

/-! Source feed-forward: each of the eight real state pairs is added through
native A/E preparation, including its range constraints and constant cache. -/
namespace Midnight.SHA256.Semantics.Feedforward
open Halo2 WitnessCircuit WitnessBuild Initialize PrepareCircuit RoundGadgets Linear

attribute [local irreducible] WitnessCircuit.prepareA WitnessCircuit.prepareE

def values (env : Placed Environment F) (cells : Array (AssignedCell F)) : Array Nat :=
  cells.map (cellValue env.place env.env)

def expected (initial final : Vector Nat 8) : Vector Nat 8 :=
  Vector.mapFinRange 8 fun i => add32 initial[i] final[i]

theorem expected_bound (initial final : Vector Nat 8) (i : Fin 8) :
    (expected initial final)[i] < 2^32 := by
  simp only [expected, Vector.getElemFin_mapFinRange, add32]
  exact Nat.mod_lt _ (by decide)

theorem state_plain_at {env : Placed Environment F} {state : Compression} {words : Vector Nat 8}
    (rep : StateRep env state words) (i : Fin 8) :
    cellValue env.place env.env (plainState state)[i.val]! = words[i] := by
  have h := congrArg (fun xs : Array Nat => xs[i.val]!) rep.plainValues
  have hs : (plainState state).size = 8 := rfl
  simpa [getElem!_pos, hs, i.isLt] using h

def terms (initial final : Compression) (i : Nat) : Array (AssignedCell F) :=
  #[(plainState initial)[i]!, (plainState final)[i]!]

def preparePlain (i : Nat) (summands : Array (AssignedCell F)) : Build (AssignedCell F) := do
  let word ← if i < 4 then WitnessCircuit.prepareA summands else WitnessCircuit.prepareE summands
  return word.combined.plain

theorem preparePlain_lawful (i : Nat) (summands : Array (AssignedCell F)) :
    Lawful (preparePlain i summands) := by
  unfold preparePlain
  split
  · exact lawful_bind (prepareA_lawful _) (fun _ => lawful_pure _)
  · exact lawful_bind (prepareE_lawful _) (fun _ => lawful_pure _)

theorem preparePlain_sound (i : Nat) (summands : Array (AssignedCell F))
    (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env cell < 2^32) :
    Sound env (preparePlain i summands) (fun cell => PlainRep env cell
      ((summands.toList.map (cellValue env.place env.env)).sum % 2^32)) := by
  unfold preparePlain
  split
  · apply sound_bind (prepareA_lawful _) (prepareA_action env table summands size inputs)
    intro word rep
    exact sound_pure env _ _ (pairRep_of_ARep rep).1
  · apply sound_bind (prepareE_lawful _) (prepareE_action env table summands size inputs)
    intro word rep
    exact sound_pure env _ _ (pairRep_of_ERep rep).1

theorem preparePlain_complete (i : Nat) (summands : Array (AssignedCell F))
    (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env.toEnvironment cell < 2^32) :
    Complete env (preparePlain i summands) (fun cell => PlainRep env.toEnvironment cell
      ((summands.toList.map (cellValue env.place env.env.toEnvironment)).sum % 2^32)) := by
  unfold preparePlain
  split
  · apply complete_bind (prepareA_lawful _) (prepareA_action_complete env table summands size inputs)
    intro word rep
    exact complete_pure env _ _ (pairRep_of_ARep rep).1
  · apply complete_bind (prepareE_lawful _) (prepareE_action_complete env table summands size inputs)
    intro word rep
    exact complete_pure env _ _ (pairRep_of_ERep rep).1

theorem terms_bounded (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed Environment F) (hx : StateRep env initial x) (hy : StateRep env final y)
    (i : Nat) (hi : i < 8) :
    ∀ cell ∈ terms initial final i, cellValue env.place env.env cell < 2^32 := by
  intro cell hc
  simp [terms] at hc
  rcases hc with rfl | rfl
  · rw [state_plain_at hx ⟨i, hi⟩]; exact hx.bounded ⟨i, hi⟩
  · rw [state_plain_at hy ⟨i, hi⟩]; exact hy.bounded ⟨i, hi⟩

theorem terms_sum (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed Environment F) (hx : StateRep env initial x) (hy : StateRep env final y)
    (i : Nat) (hi : i < 8) :
    ((terms initial final i).toList.map (cellValue env.place env.env)).sum % 2^32 =
      (expected x y)[i] := by
  change (cellValue env.place env.env (plainState initial)[i]! +
    cellValue env.place env.env (plainState final)[i]!) % 2^32 = _
  rw [state_plain_at hx ⟨i, hi⟩, state_plain_at hy ⟨i, hi⟩]
  simp [expected, add32, Vector.getElem_mapFinRange]

def appendWord (initial final : Compression) (i : Nat) (cells : Array (AssignedCell F)) :
    Build (Array (AssignedCell F)) := do
  let cell ← preparePlain i (terms initial final i)
  return cells.push cell

theorem appendWord_lawful (initial final : Compression) (i : Nat) (cells : Array (AssignedCell F)) :
    Lawful (appendWord initial final i cells) :=
  lawful_bind (preparePlain_lawful _ _) (fun _ => lawful_pure _)

theorem appendWord_sound (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (hx : StateRep env initial x) (hy : StateRep env final y)
    (i : Nat) (hi : i < 8) (cells : Array (AssignedCell F)) :
    Sound env (appendWord initial final i cells) (fun output =>
      values env output = (values env cells).push ((expected x y)[i])) := by
  unfold appendWord
  apply sound_bind (preparePlain_lawful _ _)
    (preparePlain_sound i (terms initial final i) env table (by simp [terms])
      (terms_bounded initial final x y env hx hy i hi))
  intro cell rep
  apply sound_pure
  have hv := rep.2.trans (terms_sum initial final x y env hx hy i hi)
  simp only [values, Array.map_push, hv]

theorem appendWord_complete (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (hx : StateRep env.toEnvironment initial x) (hy : StateRep env.toEnvironment final y)
    (i : Nat) (hi : i < 8) (cells : Array (AssignedCell F)) :
    Complete env (appendWord initial final i cells) (fun output =>
      values env.toEnvironment output = (values env.toEnvironment cells).push ((expected x y)[i])) := by
  unfold appendWord
  apply complete_bind (preparePlain_lawful _ _)
    (preparePlain_complete i (terms initial final i) env table (by simp [terms])
      (terms_bounded initial final x y env.toEnvironment hx hy i hi))
  intro cell rep
  apply complete_pure
  have hv := rep.2.trans (terms_sum initial final x y env.toEnvironment hx hy i hi)
  simp only [values, Array.map_push, hv]

def loop (initial final : Compression) (items : List Nat) (cells : Array (AssignedCell F)) :
    Build (Array (AssignedCell F)) :=
  forIn items cells fun i result => do return .yield (← appendWord initial final i result)

theorem source_loop (initial final : Compression) :
    WitnessCircuit.addStates initial final = loop initial final (List.range 8) #[] := by
  unfold WitnessCircuit.addStates loop appendWord preparePlain terms
  simp only [WitnessBuild.bind_assoc, WitnessBuild.pure_bind, WitnessBuild.bind_pure,
    Std.Legacy.Range.forIn_eq_forIn_range']
  congr 1
  funext i result
  split_ifs <;> simp only [WitnessBuild.bind_assoc, WitnessBuild.pure_bind]

attribute [local irreducible] WitnessCircuit.addStates

theorem loop_lawful (initial final : Compression) (items : List Nat) (cells : Array (AssignedCell F)) :
    Lawful (loop initial final items cells) :=
  lawful_forIn_list items cells _ (fun i _ result =>
    lawful_bind (appendWord_lawful initial final i result) (fun _ => lawful_pure _))

theorem addStates_lawful (initial final : Compression) : Lawful (WitnessCircuit.addStates initial final) := by
  rw [source_loop]
  exact loop_lawful _ _ _ _

attribute [local irreducible] loop

theorem loop_sound (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (hx : StateRep env initial x) (hy : StateRep env final y)
    (items : List Nat) (bounded : ∀ i ∈ items, i < 8) (cells : Array (AssignedCell F)) :
    Sound env (loop initial final items cells) (fun output =>
      values env output = values env cells ++ items.toArray.map (fun i => (expected x y).toArray[i]!)) := by
  intro cache self hcache hc
  unfold loop at hc ⊢
  apply forIn_list_prefix items cells (appendWord initial final) []
    (fun processed output nextCache _ =>
      values env output = values env cells ++ processed.toArray.map (fun i => (expected x y).toArray[i]!) ∧
      CacheMeaning env nextCache) env.place env.env
    (fun i _ result => appendWord_lawful initial final i result) ?_ cache self ?_ hc
  · intro processed i remaining decomposition result nextCache nextIndex previous satisfied
    have member : i ∈ items := by rw [decomposition]; simp
    have bound := bounded i member
    obtain ⟨hv, hk⟩ := appendWord_sound initial final x y env table hx hy i bound result
      nextCache nextIndex previous.2 satisfied
    refine ⟨?_, hk⟩
    rw [hv, previous.1]
    apply Array.ext'
    simp [getElem!_pos, bound]
  · simpa using hcache

theorem loop_complete (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (hx : StateRep env.toEnvironment initial x) (hy : StateRep env.toEnvironment final y)
    (items : List Nat) (bounded : ∀ i ∈ items, i < 8) (cells : Array (AssignedCell F)) :
    Complete env (loop initial final items cells) (fun output =>
      values env.toEnvironment output = values env.toEnvironment cells ++
        items.toArray.map (fun i => (expected x y).toArray[i]!)) := by
  intro cache self hcache hw
  unfold loop at hw ⊢
  apply forIn_list_prefix_complete items cells (appendWord initial final) []
    (fun processed output nextCache _ =>
      values env.toEnvironment output = values env.toEnvironment cells ++
        processed.toArray.map (fun i => (expected x y).toArray[i]!) ∧
      CacheMeaning env.toEnvironment nextCache) env.place env.env
    (fun i _ result => appendWord_lawful initial final i result) ?_ cache self ?_ hw
  · intro processed i remaining decomposition result nextCache nextIndex previous witnesses
    have member : i ∈ items := by rw [decomposition]; simp
    have bound := bounded i member
    obtain ⟨hc, hv, hk⟩ := appendWord_complete initial final x y env table hx hy i bound result
      nextCache nextIndex previous.2 witnesses
    refine ⟨hc, ?_, hk⟩
    rw [hv, previous.1]
    apply Array.ext'
    simp [getElem!_pos, bound]
  · simpa using hcache

private theorem range_expected (words : Vector Nat 8) :
    (List.range 8).toArray.map (fun i => words.toArray[i]!) = words.toArray := by
  have hr : (List.range 8).toArray = Array.range 8 := by decide +kernel
  rw [hr]
  apply Array.ext
  · simp
  · intro i hi hj
    simp only [Array.getElem_map, Array.getElem_range]
    exact getElem!_pos words.toArray i hj

/-- The actual source feed-forward output, with no input/output equations assumed
beyond the represented incoming compression states. -/
theorem addStates_sound (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (hx : StateRep env initial x) (hy : StateRep env final y) :
    Sound env (WitnessCircuit.addStates initial final)
      (fun output => values env output = (expected x y).toArray) := by
  rw [source_loop]
  have h := loop_sound initial final x y env table hx hy (List.range 8)
    (fun i hi => List.mem_range.mp hi) #[]
  simpa only [values, Array.map_empty, Array.empty_append, range_expected] using h

theorem addStates_complete (initial final : Compression) (x y : Vector Nat 8)
    (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (hx : StateRep env.toEnvironment initial x) (hy : StateRep env.toEnvironment final y) :
    Complete env (WitnessCircuit.addStates initial final)
      (fun output => values env.toEnvironment output = (expected x y).toArray) := by
  rw [source_loop]
  have h := loop_complete initial final x y env table hx hy (List.range 8)
    (fun i hi => List.mem_range.mp hi) #[]
  simpa only [values, Array.map_empty, Array.empty_append, range_expected] using h

end Midnight.SHA256.Semantics.Feedforward
