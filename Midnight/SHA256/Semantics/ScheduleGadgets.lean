import Midnight.SHA256.Semantics.Initialize
import Midnight.SHA256.Semantics.PrepareWitness
import Midnight.SHA256.Semantics.BitwiseWitness
import Midnight.SHA256.Semantics.RoundGadgets

/-! Source-gadget contracts and word-array invariants used to compose the
actual message schedule. -/
set_option linter.constructorNameAsVariable false

namespace Midnight.SHA256.Semantics.ScheduleGadgets
open Halo2 WitnessCircuit WitnessBuild Initialize PrepareCircuit Linear

abbrev Cache := WitnessCircuit.Cache

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
attribute [local irreducible] WitnessCircuit.prepareMessage WitnessCircuit.sigma0 WitnessCircuit.sigma1

theorem prepareMessage_lawful (summands : Array (AssignedCell F)) :
    Lawful (WitnessCircuit.prepareMessage summands) := by
  intro cache self
  change ((WitnessCircuit.prepareMessage summands).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.prepareMessage summands).run cache).operations self).regionCount
  rw [prepareMessage_run]
  simp only [circuit_norm, Operations.regionCount_append, Operations.regionCount, Nat.add_zero]
  rw [Linear.constant_nextRegionIndex]
  rfl

theorem sigma0_lawful (word : Word) : Lawful (WitnessCircuit.sigma0 word) := by
  intro cache self
  change ((WitnessCircuit.sigma0 word).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.sigma0 word).run cache).operations self).regionCount
  rw [BitwiseGadgets.sigma0_source]
  simp only [circuit_norm, Operations.regionCount, Nat.add_zero]

theorem sigma1_lawful (word : Word) : Lawful (WitnessCircuit.sigma1 word) := by
  intro cache self
  change ((WitnessCircuit.sigma1 word).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.sigma1 word).run cache).operations self).regionCount
  rw [BitwiseGadgets.sigma1_source]
  simp only [circuit_norm, Operations.regionCount, Nat.add_zero]

theorem lowerSigma0_lt {n : Nat} (bound : n < 2 ^ 32) : Specs.SHA256.lowerSigma0 n < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Rotations.rotRight32_lt bound 7)
    (Rotations.rotRight32_lt bound 18)) ((Nat.div_le_self n _).trans_lt bound)

theorem lowerSigma1_lt {n : Nat} (bound : n < 2 ^ 32) : Specs.SHA256.lowerSigma1 n < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Rotations.rotRight32_lt bound 17)
    (Rotations.rotRight32_lt bound 19)) ((Nat.div_le_self n _).trans_lt bound)

theorem message_plain {env : Placed Environment F} {word : Word} {n : Nat}
    (rep : MessageRep env.place env.env word n) : PlainRep env word.combined.plain n := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,e,f,g,h,_,_,value,_⟩ := rep
  exact ⟨bound,value⟩

theorem sigma0_plain (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (word : Word) (n : Nat) (rep : MessageRep env.place env.env word n) :
    Sound env (WitnessCircuit.sigma0 word)
      (fun cell => PlainRep env cell (Specs.SHA256.lowerSigma0 n)) := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,e,f,g,h,bounded,rfl,_,inputs⟩ := rep
  intro cache self valid satisfied
  have result := BitwiseGadgets.sigma0_sound table word cache a b c d e f g h bounded inputs satisfied
  refine ⟨⟨lowerSigma0_lt bound,result⟩,?_⟩
  change CacheMeaning env (((WitnessCircuit.sigma0 word).run cache).output self).2
  rw [BitwiseGadgets.sigma0_source]
  exact valid

theorem sigma1_plain (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (word : Word) (n : Nat) (rep : MessageRep env.place env.env word n) :
    Sound env (WitnessCircuit.sigma1 word)
      (fun cell => PlainRep env cell (Specs.SHA256.lowerSigma1 n)) := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,e,f,g,h,bounded,rfl,_,inputs⟩ := rep
  intro cache self valid satisfied
  have result := BitwiseGadgets.sigma1_sound table word cache a b c d e f g h bounded inputs satisfied
  refine ⟨⟨lowerSigma1_lt bound,result⟩,?_⟩
  change CacheMeaning env (((WitnessCircuit.sigma1 word).run cache).output self).2
  rw [BitwiseGadgets.sigma1_source]
  exact valid

theorem sigma0_complete (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (word : Word) (n : Nat) (rep : MessageRep env.place env.env.toEnvironment word n)
    (cache : Cache) (self : RegionIndex) (valid : CacheMeaning env.toEnvironment cache)
    (witnesses : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.sigma0 word).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.sigma0 word).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.sigma0 word).run cache).output self
     PlainRep env.toEnvironment output.1 (Specs.SHA256.lowerSigma0 n) ∧
       CacheMeaning env.toEnvironment output.2) := by
  have representation := rep
  obtain ⟨a,b,c,d,e,f,g,h,bounded,rfl,_,inputs⟩ := rep
  have result := BitwiseWitness.sigma0_complete table word cache a b c d e f g h bounded inputs witnesses
  exact ⟨result.1, sigma0_plain env.toEnvironment table word _ representation cache self valid result.1⟩

theorem sigma1_complete (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (word : Word) (n : Nat) (rep : MessageRep env.place env.env.toEnvironment word n)
    (cache : Cache) (self : RegionIndex) (valid : CacheMeaning env.toEnvironment cache)
    (witnesses : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.sigma1 word).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.sigma1 word).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.sigma1 word).run cache).output self
     PlainRep env.toEnvironment output.1 (Specs.SHA256.lowerSigma1 n) ∧
       CacheMeaning env.toEnvironment output.2) := by
  have representation := rep
  obtain ⟨a,b,c,d,e,f,g,h,bounded,rfl,_,inputs⟩ := rep
  have result := BitwiseWitness.sigma1_complete table word cache a b c d e f g h bounded inputs witnesses
  exact ⟨result.1, sigma1_plain env.toEnvironment table word _ representation cache self valid result.1⟩

/-- Every stored source word represents the matching mathematical schedule
entry. Array lengths are part of the contract, so default reads are excluded. -/
def WordsRep (env : Placed Environment F) (words : Array Word) (values : Array Nat) : Prop :=
  words.size = values.size ∧ ∀ i, i < words.size →
    MessageRep env.place env.env words[i]! values[i]!

theorem WordsRep.push {env : Placed Environment F} {words : Array Word} {values : Array Nat}
    {word : Word} {n : Nat} (before : WordsRep env words values)
    (next : MessageRep env.place env.env word n) :
    WordsRep env (words.push word) (values.push n) := by
  refine ⟨by simpa only [Array.size_push] using congrArg (· + 1) before.1, ?_⟩
  intro i hi
  by_cases old : i < words.size
  · have other : i < values.size := by rw [← before.1]; exact old
    have hi' : i < (values.push n).size := by simp only [Array.size_push]; omega
    simpa only [getElem!_pos words i old, getElem!_pos values i other,
      getElem!_pos (words.push word) i hi, getElem!_pos (values.push n) i hi',
      Array.getElem_push_lt old, Array.getElem_push_lt other] using before.2 i old
  · have last : i = words.size := by simp only [Array.size_push] at hi; omega
    subst i
    rw [getElem!_pos (words.push word) words.size hi, Array.getElem_push_eq, before.1,
      getElem!_pos (values.push n) values.size (by simp), Array.getElem_push_eq]
    exact next

theorem WordsRep.plainValues {env : Placed Environment F} {words : Array Word} {values : Array Nat}
    (rep : WordsRep env words values) :
    (words.map fun word => cellValue env.place env.env word.combined.plain) = values := by
  apply Array.ext
  · simpa using rep.1
  intro i hi hj
  have iw : i < words.size := by simpa using hi
  have value := (message_plain (env := env) (rep.2 i iw)).2
  simpa only [Array.getElem_map, getElem!_pos words i iw, getElem!_pos values i hj] using value

theorem prepareMessage_action (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (summands : Array (AssignedCell F)) (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env cell < 2 ^ 32) :
    Sound env (WitnessCircuit.prepareMessage summands) (fun word =>
      MessageRep env.place env.env word
        ((summands.toList.map (cellValue env.place env.env)).sum % 2 ^ 32)) := by
  intro cache self valid satisfied
  exact prepareMessage_sound summands cache self env table valid size inputs satisfied

def appendInput (block : Array (AssignedCell F)) (i : Nat) (words : Array Word) : Build (Array Word) := do
  let word ← prepareMessage #[block[i]!]
  return words.push word

theorem appendInput_lawful (block : Array (AssignedCell F)) (i : Nat) (words : Array Word) :
    Lawful (appendInput block i words) :=
  lawful_bind (prepareMessage_lawful _) (fun _ => lawful_pure _)

theorem appendInput_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (block : Array (AssignedCell F)) (i : Nat) (words : Array Word) (values : Array Nat)
    (rep : WordsRep env words values) (n : Nat) (input : PlainRep env block[i]! n) :
    Sound env (appendInput block i words) (fun output => WordsRep env output (values.push n)) := by
  unfold appendInput
  apply sound_bind (prepareMessage_lawful _)
    (prepareMessage_action env table #[block[i]!] (by change 1 ≤ 7; decide +kernel) ?_)
  · intro word represented
    apply sound_pure
    apply rep.push
    simpa only [List.toList_toArray, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, input.2, Nat.mod_eq_of_lt input.1] using represented
  · intro cell member
    rw [Array.mem_singleton.mp member, input.2]
    exact input.1

theorem appendInput_complete (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (block : Array (AssignedCell F)) (i : Nat) (words : Array Word)
    (n : Nat) (input : PlainRep env.toEnvironment block[i]! n)
    (cache : Cache) (self : RegionIndex) (valid : CacheMeaning env.toEnvironment cache)
    (witnesses : ExtendsWitnesses env.place env.env
      ((appendInput block i words cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((appendInput block i words cache).operations self) self := by
  unfold appendInput at witnesses ⊢
  rw [bind_extendsWitnesses _ _ (prepareMessage_lawful _) _ _ _ _] at witnesses
  apply (bind_constraints _ _ (prepareMessage_lawful _) _ _ _ _).mpr
  refine ⟨?_, trivial⟩
  apply (PrepareWitness.prepareMessage_complete #[block[i]!] cache self env table valid
    (by change 1 ≤ 7; decide +kernel) ?_ witnesses.1).1
  intro cell member
  rw [Array.mem_singleton.mp member]
  change cellValue env.toEnvironment.place env.toEnvironment.env block[i]! < 2 ^ 32
  rw [input.2]
  exact input.1

def appendExpanded (i : Nat) (words : Array Word) : Build (Array Word) := do
  let s0 ← sigma0 words[i-15]!
  let s1 ← sigma1 words[i-2]!
  let word ← prepareMessage #[words[i-16]!.combined.plain, words[i-7]!.combined.plain, s0, s1]
  return words.push word

theorem appendExpanded_lawful (i : Nat) (words : Array Word) : Lawful (appendExpanded i words) := by
  unfold appendExpanded
  apply lawful_bind (sigma0_lawful _)
  intro s0
  apply lawful_bind (sigma1_lawful _)
  intro s1
  apply lawful_bind (prepareMessage_lawful _)
  intro word
  exact lawful_pure _

theorem prepareFour_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (a b c d : AssignedCell F) (x y z t : Nat)
    (ha : PlainRep env a x) (hb : PlainRep env b y)
    (hc : PlainRep env c z) (hd : PlainRep env d t) :
    Sound env (prepareMessage #[a,b,c,d])
      (fun word => MessageRep env.place env.env word ((x+y+z+t) % 2^32)) := by
  have inputs : ∀ cell ∈ #[a,b,c,d], cellValue env.place env.env cell < 2^32 := by
    intro cell member
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · rw [ha.2]; exact ha.1
    · rw [hb.2]; exact hb.1
    · rw [hc.2]; exact hc.1
    · rw [hd.2]; exact hd.1
  have result := prepareMessage_action env table #[a,b,c,d] (by change 4 ≤ 7; decide +kernel) inputs
  simpa only [List.toList_toArray, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, ha.2, hb.2, hc.2, hd.2, Nat.add_assoc] using result

theorem appendExpanded_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (i : Nat) (words : Array Word) (values : Array Nat)
    (rep : WordsRep env words values) (start : 16 ≤ i) (size : words.size = i) :
    Sound env (appendExpanded i words) (fun output => WordsRep env output
      (values.push ((values[i-16]! + values[i-7]! + Specs.SHA256.lowerSigma0 values[i-15]! +
        Specs.SHA256.lowerSigma1 values[i-2]!) % 2 ^ 32))) := by
  have rep16 := rep.2 (i-16) (by omega)
  have rep7 := rep.2 (i-7) (by omega)
  have rep15 := rep.2 (i-15) (by omega)
  have rep2 := rep.2 (i-2) (by omega)
  have p16 := message_plain (env := env) rep16
  have p7 := message_plain (env := env) rep7
  unfold appendExpanded
  apply sound_bind (sigma0_lawful _) (sigma0_plain env table _ _ rep15)
  intro s0 p0
  apply sound_bind (sigma1_lawful _) (sigma1_plain env table _ _ rep2)
  intro s1 p1
  apply sound_bind (prepareMessage_lawful _)
    (prepareFour_sound env table _ _ _ _ _ _ _ _ p16 p7 p0 p1)
  intro word represented
  exact sound_pure env (words.push word) _ (rep.push represented)

theorem appendInput_honest (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (block : Array (AssignedCell F)) (i : Nat) (words : Array Word) (values : Array Nat)
    (rep : WordsRep env.toEnvironment words values) (n : Nat)
    (input : PlainRep env.toEnvironment block[i]! n) :
    RoundGadgets.Complete env (appendInput block i words)
      (fun output => WordsRep env.toEnvironment output (values.push n)) := by
  intro cache self valid witnesses
  have constraints := appendInput_complete env table block i words n input cache self valid witnesses
  exact ⟨constraints, appendInput_sound env.toEnvironment table block i words values rep n input
    cache self valid constraints⟩

theorem prepareFour_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (a b c d : AssignedCell F) (x y z t : Nat)
    (ha : PlainRep env.toEnvironment a x) (hb : PlainRep env.toEnvironment b y)
    (hc : PlainRep env.toEnvironment c z) (hd : PlainRep env.toEnvironment d t) :
    RoundGadgets.Complete env (prepareMessage #[a,b,c,d])
      (fun word => MessageRep env.place env.env.toEnvironment word ((x+y+z+t) % 2^32)) := by
  have inputs : ∀ cell ∈ #[a,b,c,d],
      cellValue env.toEnvironment.place env.toEnvironment.env cell < 2^32 := by
    intro cell member
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · rw [ha.2]; exact ha.1
    · rw [hb.2]; exact hb.1
    · rw [hc.2]; exact hc.1
    · rw [hd.2]; exact hd.1
  have result : RoundGadgets.Complete env (prepareMessage #[a,b,c,d])
      (fun word => MessageRep env.place env.env.toEnvironment word
        (([a,b,c,d].map (cellValue env.toEnvironment.place env.toEnvironment.env)).sum % 2^32)) := by
    intro cache self valid witnesses
    exact PrepareWitness.prepareMessage_complete #[a,b,c,d] cache self env table valid
      (by change 4 ≤ 7; decide +kernel) inputs witnesses
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    ha.2, hb.2, hc.2, hd.2, Nat.add_assoc] using result

theorem sigma0_honest (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (word : Word) (n : Nat) (rep : MessageRep env.place env.env.toEnvironment word n) :
    RoundGadgets.Complete env (WitnessCircuit.sigma0 word)
      (fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.lowerSigma0 n)) := by
  intro cache self valid witnesses
  exact sigma0_complete env table word n rep cache self valid witnesses

theorem sigma1_honest (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (word : Word) (n : Nat) (rep : MessageRep env.place env.env.toEnvironment word n) :
    RoundGadgets.Complete env (WitnessCircuit.sigma1 word)
      (fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.lowerSigma1 n)) := by
  intro cache self valid witnesses
  exact sigma1_complete env table word n rep cache self valid witnesses

theorem appendExpanded_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (i : Nat) (words : Array Word) (values : Array Nat)
    (rep : WordsRep env.toEnvironment words values) (start : 16 ≤ i) (size : words.size = i) :
    RoundGadgets.Complete env (appendExpanded i words)
      (fun output => WordsRep env.toEnvironment output
        (values.push ((values[i-16]! + values[i-7]! + Specs.SHA256.lowerSigma0 values[i-15]! +
          Specs.SHA256.lowerSigma1 values[i-2]!) % 2 ^ 32))) := by
  have rep16 := rep.2 (i-16) (by omega)
  have rep7 := rep.2 (i-7) (by omega)
  have rep15 := rep.2 (i-15) (by omega)
  have rep2 := rep.2 (i-2) (by omega)
  have p16 := message_plain (env := env.toEnvironment) rep16
  have p7 := message_plain (env := env.toEnvironment) rep7
  unfold appendExpanded
  apply RoundGadgets.complete_bind
    (middle := fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.lowerSigma0 values[i-15]!))
    (sigma0_lawful _)
    (sigma0_honest env table _ _ rep15)
  intro s0 p0
  apply RoundGadgets.complete_bind
    (middle := fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.lowerSigma1 values[i-2]!))
    (sigma1_lawful _)
    (sigma1_honest env table _ _ rep2)
  intro s1 p1
  apply RoundGadgets.complete_bind (prepareMessage_lawful _)
    (prepareFour_complete env table _ _ _ _ _ _ _ _ p16 p7 p0 p1)
  intro word represented
  exact RoundGadgets.complete_pure env (words.push word) _ (rep.push represented)

end Midnight.SHA256.Semantics.ScheduleGadgets
