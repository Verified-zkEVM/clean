import Midnight.SHA256.Semantics.PrepareCircuit
import Midnight.SHA256.WitnessBuild
import Midnight.SHA256.Spec

/-! Initial and round constants of the actual source circuit. The cache is
threaded through every source call; no advice equality or idealized cells are
substituted for the returned source cells. -/
namespace Midnight.SHA256.Semantics.Initialize
open Halo2 WitnessCircuit WitnessBuild PrepareCircuit Linear

abbrev Cache := WitnessCircuit.Cache

attribute [local irreducible] WitnessCircuit.constant WitnessCircuit.constantPair
  WitnessCircuit.initialState
attribute [local cbv_opaque] WitnessCircuit.constant WitnessCircuit.constantPair
  Midnight.SHA256.spread HAppend.hAppend HDiv.hDiv HMod.hMod
  BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing

def PlainRep (env : Placed Environment F) (cell : AssignedCell F) (n : Nat) : Prop :=
  n < 2 ^ 32 ∧ cellValue env.place env.env cell = n

def PairRep (env : Placed Environment F) (pair : PlainSpread) (n : Nat) : Prop :=
  PlainRep env pair.plain n ∧ pair.spread.eval env.place env.env = (spread n : F)

/-- Invariant arranged in the same order as the source compression state. -/
def StateRep (env : Placed Environment F) (state : Compression) (words : Vector Nat 8) : Prop :=
  ARep env.place env.env state.a words[0] ∧
  PairRep env state.b words[1] ∧ PairRep env state.c words[2] ∧
  PlainRep env state.d words[3] ∧ ERep env.place env.env state.e words[4] ∧
  PairRep env state.f words[5] ∧ PairRep env state.g words[6] ∧
  PlainRep env state.h words[7]

theorem pairRep_of_ARep {env : Placed Environment F} {word : Word} {n : Nat}
    (rep : ARep env.place env.env word n) : PairRep env word.combined n := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,_,_,plain,expanded,_⟩ := rep
  exact ⟨⟨bound, plain⟩, expanded⟩

theorem pairRep_of_ERep {env : Placed Environment F} {word : Word} {n : Nat}
    (rep : ERep env.place env.env word n) : PairRep env word.combined n := by
  have bound := rep.bounded
  obtain ⟨a,b,c,d,e,_,_,plain,expanded,_⟩ := rep
  exact ⟨⟨bound, plain⟩, expanded⟩

theorem StateRep.bounded {env : Placed Environment F} {state : Compression}
    {words : Vector Nat 8} (rep : StateRep env state words) (index : Fin 8) :
    words[index] < 2 ^ 32 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hg,hh⟩ := rep
  fin_cases index
  · exact ha.bounded
  · exact hb.1.1
  · exact hc.1.1
  · exact hd.1
  · exact he.bounded
  · exact hf.1.1
  · exact hg.1.1
  · exact hh.1

theorem StateRep.plainValues {env : Placed Environment F} {state : Compression}
    {words : Vector Nat 8} (rep : StateRep env state words) :
    (plainState state).map (cellValue env.place env.env) = words.toArray := by
  obtain ⟨ha,hb,hc,hd,he,hf,hg,hh⟩ := rep
  have va := (pairRep_of_ARep ha).1.2
  have ve := (pairRep_of_ERep he).1.2
  apply Array.ext
  · simp [plainState]
  intro i hi hj
  have bound : i < 8 := by simpa [plainState] using hi
  interval_cases i <;> simp [plainState, va, ve, hb.1.2, hc.1.2, hd.2, hf.1.2, hg.1.2, hh.2]

theorem roundConstants_eq_K :
    Synthesis.roundConstants = (Specs.SHA256.K.map UInt32.toNat).toArray := by
  decide +kernel

theorem roundConstant_lt (index : Fin 64) : Synthesis.roundConstants[index.val]! < 2 ^ 32 := by
  rw [roundConstants_eq_K]
  simpa using (Specs.SHA256.K[index]).toNat_lt

def aExpanded (n : Nat) : Build Word := do
  let pair ← constantPair n
  let a ← constant (spread (n / 2 ^ 22 % 2 ^ 10))
  let b ← constant (spread (n / 2 ^ 13 % 2 ^ 9))
  let c ← constant (spread (n / 2 ^ 2 % 2 ^ 11))
  let d ← constant (spread (n / 2 ^ 0 % 2 ^ 2))
  return ⟨pair, #[a,b,c,d]⟩

def eExpanded (n : Nat) : Build Word := do
  let pair ← constantPair n
  let a ← constant (spread (n / 2 ^ 25 % 2 ^ 7))
  let b ← constant (spread (n / 2 ^ 13 % 2 ^ 12))
  let c ← constant (spread (n / 2 ^ 11 % 2 ^ 2))
  let d ← constant (spread (n / 2 ^ 6 % 2 ^ 5))
  let e ← constant (spread (n / 2 ^ 0 % 2 ^ 6))
  return ⟨pair, #[a,b,c,d,e]⟩

theorem constantWordA_eq (n : Nat) : constantWord n #[10,9,11,2] = aExpanded n := by
  funext cache self
  unfold constantWord aExpanded
  cbv
  simp only [List.append_nil]

theorem constantWordE_eq (n : Nat) : constantWord n #[7,12,2,5,6] = eExpanded n := by
  funext cache self
  unfold constantWord eExpanded
  cbv
  simp only [List.append_nil]

/-- Source constants have a lawful index and imply their constraints from
honest assignments without any assumptions on private advice inputs. -/
private structure ConstantProgram {α : Type} (action : Build α) : Prop where
  lawful : Lawful action
  complete : ∀ (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F),
    ExtendsWitnesses env.place env.env ((action cache).operations self) self →
    Constraints env.place env.env.toEnvironment ((action cache).operations self) self

private theorem constantProgram_pure {α : Type} (value : α) :
    ConstantProgram (pure value) :=
  ⟨lawful_pure value, by intro _ _ _ _; trivial⟩

private theorem constantProgram_bind {α β : Type} {first : Build α} {next : α → Build β}
    (hfirst : ConstantProgram first) (hnext : ∀ value, ConstantProgram (next value)) :
    ConstantProgram (first >>= next) := by
  refine ⟨lawful_bind hfirst.lawful (fun value => (hnext value).lawful), ?_⟩
  intro cache self env witnesses
  obtain ⟨firstWitness, nextWitness⟩ :=
    (bind_extendsWitnesses first next hfirst.lawful env.place env.env cache self).mp witnesses
  apply (bind_constraints first next hfirst.lawful env.place env.env.toEnvironment cache self).mpr
  exact ⟨hfirst.complete cache self env firstWitness,
    (hnext _).complete _ _ env nextWitness⟩

private theorem constant_program (n : Nat) : ConstantProgram (constant n) :=
  ⟨constant_nextRegionIndex n, constant_constraints_of_witnesses n⟩

private theorem constantPair_program (n : Nat) : ConstantProgram (constantPair n) := by
  unfold constantPair
  apply constantProgram_bind (constant_program n)
  intro plain
  apply constantProgram_bind (constant_program (spread n))
  intro expanded
  exact constantProgram_pure (⟨plain, expanded⟩ : PlainSpread)

private theorem constantWordA_program (n : Nat) : ConstantProgram (constantWord n #[10,9,11,2]) := by
  rw [constantWordA_eq]
  unfold aExpanded
  apply constantProgram_bind (constantPair_program n)
  intro pair
  apply constantProgram_bind (constant_program _)
  intro a
  apply constantProgram_bind (constant_program _)
  intro b
  apply constantProgram_bind (constant_program _)
  intro c
  apply constantProgram_bind (constant_program _)
  intro d
  exact constantProgram_pure (⟨pair, #[a,b,c,d]⟩ : Word)

private theorem constantWordE_program (n : Nat) : ConstantProgram (constantWord n #[7,12,2,5,6]) := by
  rw [constantWordE_eq]
  unfold eExpanded
  apply constantProgram_bind (constantPair_program n)
  intro pair
  apply constantProgram_bind (constant_program _)
  intro a
  apply constantProgram_bind (constant_program _)
  intro b
  apply constantProgram_bind (constant_program _)
  intro c
  apply constantProgram_bind (constant_program _)
  intro d
  apply constantProgram_bind (constant_program _)
  intro e
  exact constantProgram_pure (⟨pair, #[a,b,c,d,e]⟩ : Word)

/-- A cache-preserving semantic contract for the actual builder output. -/
def Sound {α : Type} (env : Placed Environment F) (action : Build α) (post : α → Prop) : Prop :=
  ∀ cache self, CacheMeaning env cache →
    Constraints env.place env.env ((action cache).operations self) self →
    post ((action cache).output self).1 ∧ CacheMeaning env ((action cache).output self).2

theorem sound_pure {α : Type} (env : Placed Environment F) (value : α)
    (post : α → Prop) (holds : post value) : Sound env (pure value) post := by
  intro cache self cacheValid _
  exact ⟨holds, cacheValid⟩

theorem sound_bind {α β : Type} {env : Placed Environment F}
    {first : Build α} {next : α → Build β} {firstPost : α → Prop} {post : β → Prop}
    (firstLawful : Lawful first) (firstSound : Sound env first firstPost)
    (nextSound : ∀ value, firstPost value → Sound env (next value) post) :
    Sound env (first >>= next) post := by
  intro cache self cacheValid satisfied
  obtain ⟨firstConstraints, nextConstraints⟩ :=
    (bind_constraints first next firstLawful env.place env.env cache self).mp satisfied
  obtain ⟨firstValue, nextCache⟩ := firstSound cache self cacheValid firstConstraints
  simpa only [bind_output] using nextSound _ firstValue _ _ nextCache nextConstraints

private theorem sound_constant (env : Placed Environment F) (n : Nat) :
    Sound env (constant n) (fun cell => cell.eval env.place env.env = (n : F)) := by
  intro cache self valid satisfied
  exact constant_sound n cache self env valid satisfied

theorem plainRep_of_eval {env : Placed Environment F} {cell : AssignedCell F} {n : Nat}
    (bound : n < 2 ^ 32) (value : cell.eval env.place env.env = (n : F)) :
    PlainRep env cell n := by
  refine ⟨bound, ?_⟩
  simp only [cellValue, value, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  exact bound.trans (by norm_num [BLS12_381.scalarFieldSize])

theorem constantPair_sound (env : Placed Environment F) (n : Nat) (bound : n < 2 ^ 32) :
    Sound env (constantPair n) (fun pair => PairRep env pair n) := by
  unfold constantPair
  apply sound_bind (constant_program n).lawful (sound_constant env n)
  intro plain plainValue
  apply sound_bind (constant_program (spread n)).lawful (sound_constant env (spread n))
  intro expanded spreadValue
  apply sound_pure
  exact ⟨plainRep_of_eval bound plainValue, spreadValue⟩

theorem constantWordA_sound (env : Placed Environment F) (n : Nat) (bound : n < 2 ^ 32) :
    Sound env (constantWord n #[10,9,11,2])
      (fun word => ARep env.place env.env word n) := by
  rw [constantWordA_eq]
  unfold aExpanded
  apply sound_bind (constantPair_program n).lawful (constantPair_sound env n bound)
  intro pair pairValue
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro a ha
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro b hb
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro c hc
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro d hd
  apply sound_pure
  refine ⟨Witness.limb n (22,10), Witness.limb n (13,9), Witness.limb n (2,11),
    Witness.limb n (0,2), Prepare.a_bounded n, (Prepare.pack_a n bound).symm,
    pairValue.1.2, pairValue.2, ?_⟩
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [BitwiseGadgets.limbValues, Witness.limb, Nat.shiftRight_eq_div_pow,
      ha, hb, hc, hd]

theorem constantWordE_sound (env : Placed Environment F) (n : Nat) (bound : n < 2 ^ 32) :
    Sound env (constantWord n #[7,12,2,5,6])
      (fun word => ERep env.place env.env word n) := by
  rw [constantWordE_eq]
  unfold eExpanded
  apply sound_bind (constantPair_program n).lawful (constantPair_sound env n bound)
  intro pair pairValue
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro a ha
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro b hb
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro c hc
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro d hd
  apply sound_bind (constant_program _).lawful (sound_constant env _)
  intro e he
  apply sound_pure
  refine ⟨Witness.limb n (25,7), Witness.limb n (13,12), Witness.limb n (11,2),
    Witness.limb n (6,5), Witness.limb n (0,6), Prepare.e_bounded n,
    (Prepare.pack_e n bound).symm, pairValue.1.2, pairValue.2, ?_⟩
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [BitwiseGadgets.limbValues, Witness.limb, Nat.shiftRight_eq_div_pow,
      ha, hb, hc, hd, he]

theorem constant_plain_sound (env : Placed Environment F) (n : Nat) (bound : n < 2 ^ 32) :
    Sound env (constant n) (fun cell => PlainRep env cell n) := by
  intro cache self valid satisfied
  obtain ⟨value, nextCache⟩ := constant_sound n cache self env valid satisfied
  exact ⟨plainRep_of_eval bound value, nextCache⟩

private theorem initialState_program : ConstantProgram initialState := by
  unfold initialState
  apply constantProgram_bind (constantWordA_program _)
  intro a
  apply constantProgram_bind (constantPair_program _)
  intro b
  apply constantProgram_bind (constantPair_program _)
  intro c
  apply constantProgram_bind (constant_program _)
  intro d
  apply constantProgram_bind (constantWordE_program _)
  intro e
  apply constantProgram_bind (constantPair_program _)
  intro f
  apply constantProgram_bind (constantPair_program _)
  intro g
  apply constantProgram_bind (constant_program _)
  intro h
  exact constantProgram_pure (⟨a,b,c,d,e,f,g,h⟩ : Compression)

theorem initialState_lawful : Lawful initialState := initialState_program.lawful

theorem initialState_complete (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) :
    ExtendsWitnesses env.place env.env ((initialState cache).operations self) self →
    Constraints env.place env.env.toEnvironment ((initialState cache).operations self) self :=
  initialState_program.complete cache self env

/-- Native cache allocation initializes all eight SHA registers to Clean's
reference H0, with the exact spread and limb representations needed by rounds. -/
theorem initialState_sound (env : Placed Environment F) :
    Sound env initialState (fun state => StateRep env state Specs.SHA256.H0) := by
  unfold initialState
  apply sound_bind (constantWordA_program _).lawful
    (constantWordA_sound env _ (by decide +kernel))
  intro a ha
  apply sound_bind (constantPair_program _).lawful
    (constantPair_sound env _ (by decide +kernel))
  intro b hb
  apply sound_bind (constantPair_program _).lawful
    (constantPair_sound env _ (by decide +kernel))
  intro c hc
  apply sound_bind (constant_program _).lawful
    (constant_plain_sound env _ (by decide +kernel))
  intro d hd
  apply sound_bind (constantWordE_program _).lawful
    (constantWordE_sound env _ (by decide +kernel))
  intro e he
  apply sound_bind (constantPair_program _).lawful
    (constantPair_sound env _ (by decide +kernel))
  intro f hf
  apply sound_bind (constantPair_program _).lawful
    (constantPair_sound env _ (by decide +kernel))
  intro g hg
  apply sound_bind (constant_program _).lawful
    (constant_plain_sound env _ (by decide +kernel))
  intro h hh
  apply sound_pure
  exact ⟨ha, hb, hc, hd, he, hf, hg, hh⟩

end Midnight.SHA256.Semantics.Initialize
