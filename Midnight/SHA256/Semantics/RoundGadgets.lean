import Midnight.SHA256.Semantics.Initialize
import Midnight.SHA256.Semantics.ChoiceWitness
import Midnight.SHA256.Semantics.PrepareWitness

/-! Composition of the actual source compression round, preserving its cache,
region counter, represented words, and Clean's SHA-256 round specification. -/
namespace Midnight.SHA256.Semantics.RoundGadgets
open Halo2 WitnessCircuit WitnessBuild Initialize PrepareCircuit Linear

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
attribute [local irreducible] WitnessCircuit.constant WitnessCircuit.bigSigma0
  WitnessCircuit.bigSigma1 WitnessCircuit.majority WitnessCircuit.choice
  WitnessCircuit.prepareA WitnessCircuit.prepareE

def Complete {α : Type} (env : Placed ProverEnvironment F) (action : Build α)
    (post : α → Prop) : Prop :=
  ∀ cache self, CacheMeaning env.toEnvironment cache →
    ExtendsWitnesses env.place env.env ((action cache).operations self) self →
    Constraints env.place env.env.toEnvironment ((action cache).operations self) self ∧
    post ((action cache).output self).1 ∧ CacheMeaning env.toEnvironment ((action cache).output self).2

theorem complete_pure {α : Type} (env : Placed ProverEnvironment F) (value : α)
    (post : α → Prop) (valid : post value) : Complete env (pure value) post := by
  intro cache self hc _
  exact ⟨trivial,valid,hc⟩

theorem complete_bind {α β : Type} {env : Placed ProverEnvironment F}
    {first : Build α} {next : α → Build β} {middle : α → Prop} {post : β → Prop}
    (law : Lawful first) (before : Complete env first middle)
    (after : ∀ value, middle value → Complete env (next value) post) :
    Complete env (first >>= next) post := by
  intro cache self valid witnesses
  obtain ⟨head,tail⟩ := (bind_extendsWitnesses first next law env.place env.env cache self).mp witnesses
  obtain ⟨headConstraints,mid,nextCache⟩ := before cache self valid head
  obtain ⟨tailConstraints,result,finalCache⟩ := after _ mid _ _ nextCache tail
  exact ⟨(bind_constraints first next law env.place env.env.toEnvironment cache self).mpr
    ⟨headConstraints,tailConstraints⟩, result,finalCache⟩

theorem majority_lawful (a b c : AssignedCell F) : Lawful (WitnessCircuit.majority a b c) := by
  intro cache self
  change ((WitnessCircuit.majority a b c).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.majority a b c).run cache).operations self).regionCount
  rw [BitwiseGadgets.majority_source]
  simp only [circuit_norm, Operations.regionCount, Nat.add_zero]

theorem bigSigma0_lawful (word : Word) : Lawful (WitnessCircuit.bigSigma0 word) := by
  intro cache self
  change ((WitnessCircuit.bigSigma0 word).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.bigSigma0 word).run cache).operations self).regionCount
  rw [BitwiseGadgets.bigSigma0_source]
  simp only [circuit_norm, Operations.regionCount, Nat.add_zero]

theorem bigSigma1_lawful (word : Word) : Lawful (WitnessCircuit.bigSigma1 word) := by
  intro cache self
  change ((WitnessCircuit.bigSigma1 word).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.bigSigma1 word).run cache).operations self).regionCount
  rw [BitwiseGadgets.bigSigma1_source]
  simp only [circuit_norm, Operations.regionCount, Nat.add_zero]

theorem choice_lawful (e f g : AssignedCell F) : Lawful (WitnessCircuit.choice e f g) := by
  intro cache self
  change ((WitnessCircuit.choice e f g).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.choice e f g).run cache).operations self).regionCount
  rw [ChoiceGadget.choice_run]
  simp only [circuit_norm, Operations.regionCount_append, Operations.regionCount, Nat.add_zero]
  rw [Linear.constant_nextRegionIndex]
  rfl

theorem prepareA_lawful (summands : Array (AssignedCell F)) : Lawful (WitnessCircuit.prepareA summands) := by
  intro cache self
  change ((WitnessCircuit.prepareA summands).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.prepareA summands).run cache).operations self).regionCount
  rw [prepareA_run]
  simp only [circuit_norm, Operations.regionCount_append, Operations.regionCount, Nat.add_zero]
  rw [Linear.constant_nextRegionIndex]
  rfl

theorem prepareE_lawful (summands : Array (AssignedCell F)) : Lawful (WitnessCircuit.prepareE summands) := by
  intro cache self
  change ((WitnessCircuit.prepareE summands).run cache).nextRegionIndex self =
    self + (((WitnessCircuit.prepareE summands).run cache).operations self).regionCount
  rw [prepareE_run]
  simp only [circuit_norm, Operations.regionCount_append, Operations.regionCount, Nat.add_zero]
  rw [Linear.constant_nextRegionIndex]
  rfl

theorem upperSigma0_lt {n : Nat} (bound : n < 2^32) : Specs.SHA256.upperSigma0 n < 2^32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Rotations.rotRight32_lt bound 2)
    (Rotations.rotRight32_lt bound 13)) (Rotations.rotRight32_lt bound 22)

theorem upperSigma1_lt {n : Nat} (bound : n < 2^32) : Specs.SHA256.upperSigma1 n < 2^32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Rotations.rotRight32_lt bound 6)
    (Rotations.rotRight32_lt bound 11)) (Rotations.rotRight32_lt bound 25)

theorem majority_lt {a b c : Nat} (ha : a < 2^32) (hb : b < 2^32) : Specs.SHA256.Maj a b c < 2^32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.and_le_left.trans_lt ha)
    (Nat.and_le_left.trans_lt ha)) (Nat.and_le_left.trans_lt hb)

theorem choice_lt {e f g : Nat} (he : e < 2^32) (hg : g < 2^32) : Specs.SHA256.Ch e f g < 2^32 :=
  Nat.xor_lt_two_pow (Nat.and_le_left.trans_lt he) (Nat.and_le_right.trans_lt hg)

theorem bigSigma0_plain (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (word : Word) (n : Nat) (rep : ARep env.place env.env word n) :
    Sound env (WitnessCircuit.bigSigma0 word) (fun cell => PlainRep env cell (Specs.SHA256.upperSigma0 n)) := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,bounded,rfl,_,_,inputs⟩ := rep
  intro cache self valid satisfied
  have result := BitwiseGadgets.bigSigma0_sound table word cache a b c d bounded inputs satisfied
  refine ⟨⟨upperSigma0_lt bound,result⟩,?_⟩
  change CacheMeaning env (((WitnessCircuit.bigSigma0 word).run cache).output self).2
  rw [BitwiseGadgets.bigSigma0_source]
  exact valid

theorem bigSigma1_plain (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (word : Word) (n : Nat) (rep : ERep env.place env.env word n) :
    Sound env (WitnessCircuit.bigSigma1 word) (fun cell => PlainRep env cell (Specs.SHA256.upperSigma1 n)) := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,e,bounded,rfl,_,_,inputs⟩ := rep
  intro cache self valid satisfied
  have result := BitwiseGadgets.bigSigma1_sound table word cache a b c d e bounded inputs satisfied
  refine ⟨⟨upperSigma1_lt bound,result⟩,?_⟩
  change CacheMeaning env (((WitnessCircuit.bigSigma1 word).run cache).output self).2
  rw [BitwiseGadgets.bigSigma1_source]
  exact valid

theorem majority_plain (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (a b c : PlainSpread) (x y z : Nat) (ax : PairRep env a x) (by_ : PairRep env b y) (cz : PairRep env c z) :
    Sound env (WitnessCircuit.majority a.spread b.spread c.spread)
      (fun cell => PlainRep env cell (Specs.SHA256.Maj x y z)) := by
  intro cache self valid satisfied
  have result := BitwiseGadgets.majority_sound table a.spread b.spread c.spread cache x y z
    ax.1.1 by_.1.1 cz.1.1 ax.2 by_.2 cz.2 satisfied
  refine ⟨⟨majority_lt ax.1.1 by_.1.1,result⟩,?_⟩
  change CacheMeaning env (((WitnessCircuit.majority a.spread b.spread c.spread).run cache).output self).2
  rw [BitwiseGadgets.majority_source]
  exact valid

theorem choice_plain (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (e f g : PlainSpread) (x y z : Nat) (ex : PairRep env e x) (fy : PairRep env f y) (gz : PairRep env g z) :
    Sound env (WitnessCircuit.choice e.spread f.spread g.spread)
      (fun cell => PlainRep env cell (Specs.SHA256.Ch x y z)) := by
  intro cache self valid satisfied
  obtain ⟨result,next⟩ := ChoiceGadget.choice_sound e.spread f.spread g.spread cache self env table valid
    x y z ex.1.1 fy.1.1 gz.1.1 ex.2 fy.2 gz.2 satisfied
  exact ⟨⟨choice_lt ex.1.1 gz.1.1,result⟩,next⟩

theorem prepareA_action (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (summands : Array (AssignedCell F)) (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env cell < 2^32) :
    Sound env (WitnessCircuit.prepareA summands) (fun word => ARep env.place env.env word
      ((summands.toList.map (cellValue env.place env.env)).sum % 2^32)) := by
  intro cache self valid satisfied
  exact PrepareCircuit.prepareA_sound summands cache self env table valid size inputs satisfied

theorem prepareE_action (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (summands : Array (AssignedCell F)) (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env cell < 2^32) :
    Sound env (WitnessCircuit.prepareE summands) (fun word => ERep env.place env.env word
      ((summands.toList.map (cellValue env.place env.env)).sum % 2^32)) := by
  intro cache self valid satisfied
  exact PrepareCircuit.prepareE_sound summands cache self env table valid size inputs satisfied

theorem constant_plain_complete (env : Placed ProverEnvironment F) (n : Nat)
    (bound : n < 2^32) :
    Complete env (WitnessCircuit.constant n) (fun cell => PlainRep env.toEnvironment cell n) := by
  intro cache self valid witnesses
  obtain ⟨satisfied,value,next⟩ := Linear.constant_complete n cache self env valid witnesses
  exact ⟨satisfied,plainRep_of_eval bound value,next⟩

theorem bigSigma0_plain_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (word : Word) (n : Nat) (rep : ARep env.place env.env.toEnvironment word n) :
    Complete env (WitnessCircuit.bigSigma0 word)
      (fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.upperSigma0 n)) := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,bounded,rfl,_,_,inputs⟩ := rep
  intro cache self valid witnesses
  obtain ⟨satisfied,result⟩ := BitwiseWitness.bigSigma0_complete table word cache a b c d bounded inputs witnesses
  refine ⟨satisfied,⟨upperSigma0_lt bound,result⟩,?_⟩
  change CacheMeaning env.toEnvironment (((WitnessCircuit.bigSigma0 word).run cache).output self).2
  rw [BitwiseGadgets.bigSigma0_source]
  exact valid

theorem bigSigma1_plain_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (word : Word) (n : Nat) (rep : ERep env.place env.env.toEnvironment word n) :
    Complete env (WitnessCircuit.bigSigma1 word)
      (fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.upperSigma1 n)) := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,e,bounded,rfl,_,_,inputs⟩ := rep
  intro cache self valid witnesses
  obtain ⟨satisfied,result⟩ := BitwiseWitness.bigSigma1_complete table word cache a b c d e bounded inputs witnesses
  refine ⟨satisfied,⟨upperSigma1_lt bound,result⟩,?_⟩
  change CacheMeaning env.toEnvironment (((WitnessCircuit.bigSigma1 word).run cache).output self).2
  rw [BitwiseGadgets.bigSigma1_source]
  exact valid

theorem majority_plain_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment) (a b c : PlainSpread) (x y z : Nat)
    (ax : PairRep env.toEnvironment a x) (by_ : PairRep env.toEnvironment b y)
    (cz : PairRep env.toEnvironment c z) :
    Complete env (WitnessCircuit.majority a.spread b.spread c.spread)
      (fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.Maj x y z)) := by
  intro cache self valid witnesses
  obtain ⟨satisfied,result⟩ := BitwiseWitness.majority_complete table a.spread b.spread c.spread cache x y z
    ax.1.1 by_.1.1 cz.1.1 ax.2 by_.2 cz.2 witnesses
  refine ⟨satisfied,⟨majority_lt ax.1.1 by_.1.1,result⟩,?_⟩
  change CacheMeaning env.toEnvironment (((WitnessCircuit.majority a.spread b.spread c.spread).run cache).output self).2
  rw [BitwiseGadgets.majority_source]
  exact valid

theorem choice_plain_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment) (e f g : PlainSpread) (x y z : Nat)
    (ex : PairRep env.toEnvironment e x) (fy : PairRep env.toEnvironment f y)
    (gz : PairRep env.toEnvironment g z) :
    Complete env (WitnessCircuit.choice e.spread f.spread g.spread)
      (fun cell => PlainRep env.toEnvironment cell (Specs.SHA256.Ch x y z)) := by
  intro cache self valid witnesses
  obtain ⟨satisfied,result,next⟩ := ChoiceWitness.choice_complete e.spread f.spread g.spread cache self env table valid
    x y z ex.1.1 fy.1.1 gz.1.1 ex.2 fy.2 gz.2 witnesses
  exact ⟨satisfied,⟨choice_lt ex.1.1 gz.1.1,result⟩,next⟩

theorem prepareA_action_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (summands : Array (AssignedCell F)) (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env.toEnvironment cell < 2^32) :
    Complete env (WitnessCircuit.prepareA summands) (fun word => ARep env.place env.env.toEnvironment word
      ((summands.toList.map (cellValue env.place env.env.toEnvironment)).sum % 2^32)) := by
  intro cache self valid witnesses
  exact PrepareWitness.prepareA_complete summands cache self env table valid size inputs witnesses

theorem prepareE_action_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (summands : Array (AssignedCell F)) (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env.toEnvironment cell < 2^32) :
    Complete env (WitnessCircuit.prepareE summands) (fun word => ERep env.place env.env.toEnvironment word
      ((summands.toList.map (cellValue env.place env.env.toEnvironment)).sum % 2^32)) := by
  intro cache self valid witnesses
  exact PrepareWitness.prepareE_complete summands cache self env table valid size inputs witnesses

end Midnight.SHA256.Semantics.RoundGadgets
