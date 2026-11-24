import Midnight.SHA256.Semantics.RoundGadgets

/-! Soundness and honest completeness of the actual native compression round. -/
namespace Midnight.SHA256.Semantics.Round
open Halo2 WitnessCircuit WitnessBuild Initialize PrepareCircuit Linear RoundGadgets
attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
attribute [local irreducible] PrepareCircuit.ARep PrepareCircuit.ERep PrepareCircuit.cellValue
attribute [local irreducible] Nat.mod Nat.add Nat.xor Nat.land Nat.mul
attribute [local irreducible] Specs.SHA256.sha256Round
  Specs.SHA256.upperSigma0 Specs.SHA256.upperSigma1 Specs.SHA256.Maj Specs.SHA256.Ch
attribute [local irreducible] WitnessCircuit.constant WitnessCircuit.bigSigma0
  WitnessCircuit.bigSigma1 WitnessCircuit.majority WitnessCircuit.choice
  WitnessCircuit.prepareA WitnessCircuit.prepareE

theorem compressionRound_lawful (state : Compression) (k : Nat) (word : AssignedCell F) :
    Lawful (compressionRound state k word) := by
  unfold compressionRound
  apply lawful_bind (Linear.constant_nextRegionIndex k)
  intro kcell
  apply lawful_bind (bigSigma0_lawful state.a)
  intro s0
  apply lawful_bind (majority_lawful _ _ _)
  intro maj
  apply lawful_bind (bigSigma1_lawful state.e)
  intro s1
  apply lawful_bind (choice_lawful _ _ _)
  intro ch
  apply lawful_bind (prepareA_lawful _)
  intro a
  apply lawful_bind (prepareE_lawful _)
  intro e
  exact lawful_pure _

private theorem vector8_a (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[0] = a := rfl
private theorem vector8_b (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[1] = b := rfl
private theorem vector8_c (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[2] = c := rfl
private theorem vector8_d (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[3] = d := rfl
private theorem vector8_e (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[4] = e := rfl
private theorem vector8_f (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[5] = f := rfl
private theorem vector8_g (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[6] = g := rfl
private theorem vector8_h (a b c d e f g h : Nat) : (#v[a,b,c,d,e,f,g,h])[7] = h := rfl

private theorem flat_mod7 (h s1 ch k w s0 maj m : Nat) :
    (((((h+s1)%m+ch)%m+k)%m+w)%m+(s0+maj)%m)%m = (h+s1+ch+k+w+s0+maj)%m := by
  simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

private theorem flat_mod6 (d h s1 ch k w m : Nat) :
    (d+((((h+s1)%m+ch)%m+k)%m+w)%m)%m = (d+h+s1+ch+k+w)%m := by
  simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

/-- Native flat sum and Clean's nested add32 round have the same A update. -/
theorem round_a (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[0]'(by decide)) =
      ((words[7]'(by decide)) + Specs.SHA256.upperSigma1 (words[4]'(by decide)) + Specs.SHA256.Ch (words[4]'(by decide)) (words[5]'(by decide)) (words[6]'(by decide)) +
        k + w + Specs.SHA256.upperSigma0 (words[0]'(by decide)) + Specs.SHA256.Maj (words[0]'(by decide)) (words[1]'(by decide)) (words[2]'(by decide))) % 2^32 := by
  unfold Specs.SHA256.sha256Round
  exact (vector8_a _ _ _ _ _ _ _ _).trans
    (flat_mod7 (words[7]'(by decide)) (Specs.SHA256.upperSigma1 (words[4]'(by decide)))
      (Specs.SHA256.Ch (words[4]'(by decide)) (words[5]'(by decide)) (words[6]'(by decide))) k w (Specs.SHA256.upperSigma0 (words[0]'(by decide)))
      (Specs.SHA256.Maj (words[0]'(by decide)) (words[1]'(by decide)) (words[2]'(by decide))) (2^32))

/-- Native flat sum and Clean's nested add32 round have the same E update. -/
theorem round_e (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[4]'(by decide)) =
      ((words[3]'(by decide)) + (words[7]'(by decide)) + Specs.SHA256.upperSigma1 (words[4]'(by decide)) + Specs.SHA256.Ch (words[4]'(by decide)) (words[5]'(by decide)) (words[6]'(by decide)) + k + w) % 2^32 := by
  unfold Specs.SHA256.sha256Round
  exact (vector8_e _ _ _ _ _ _ _ _).trans
    (flat_mod6 (words[3]'(by decide)) (words[7]'(by decide)) (Specs.SHA256.upperSigma1 (words[4]'(by decide)))
      (Specs.SHA256.Ch (words[4]'(by decide)) (words[5]'(by decide)) (words[6]'(by decide))) k w (2^32))

private theorem round_b (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[1]'(by decide)) = (words[0]'(by decide)) := by
  unfold Specs.SHA256.sha256Round
  exact vector8_b _ _ _ _ _ _ _ _

private theorem round_c (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[2]'(by decide)) = (words[1]'(by decide)) := by
  unfold Specs.SHA256.sha256Round
  exact vector8_c _ _ _ _ _ _ _ _

private theorem round_d (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[3]'(by decide)) = (words[2]'(by decide)) := by
  unfold Specs.SHA256.sha256Round
  exact vector8_d _ _ _ _ _ _ _ _

private theorem round_f (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[5]'(by decide)) = (words[4]'(by decide)) := by
  unfold Specs.SHA256.sha256Round
  exact vector8_f _ _ _ _ _ _ _ _

private theorem round_g (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[6]'(by decide)) = (words[5]'(by decide)) := by
  unfold Specs.SHA256.sha256Round
  exact vector8_g _ _ _ _ _ _ _ _

private theorem round_h (words : Vector Nat 8) (k w : Nat) :
    ((Specs.SHA256.sha256Round words k w)[7]'(by decide)) = (words[6]'(by decide)) := by
  unfold Specs.SHA256.sha256Round
  exact vector8_h _ _ _ _ _ _ _ _

private theorem prepare7A_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (a b c d e f g : AssignedCell F) (n0 n1 n2 n3 n4 n5 n6 : Nat)
    (ha : PlainRep env a n0)
    (hb : PlainRep env b n1)
    (hc : PlainRep env c n2)
    (hd : PlainRep env d n3)
    (he : PlainRep env e n4)
    (hf : PlainRep env f n5)
    (hg : PlainRep env g n6)
    : Sound env (WitnessCircuit.prepareA #[a,b,c,d,e,f,g])
      (fun word => ARep env.place env.env word ((n0+n1+n2+n3+n4+n5+n6) % 2^32)) := by
  have inputs : ∀ cell ∈ #[a,b,c,d,e,f,g], cellValue env.place env.env cell < 2^32 := by
    intro cell member
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ha.2]; exact ha.1
    · rw [hb.2]; exact hb.1
    · rw [hc.2]; exact hc.1
    · rw [hd.2]; exact hd.1
    · rw [he.2]; exact he.1
    · rw [hf.2]; exact hf.1
    · rw [hg.2]; exact hg.1
  have result := prepareA_action env table #[a,b,c,d,e,f,g] (by change 7 ≤ 7; decide +kernel) inputs
  simpa only [List.toList_toArray, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, ha.2, hb.2, hc.2, hd.2, he.2, hf.2, hg.2, Nat.add_assoc] using result

private theorem prepare7A_complete (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (a b c d e f g : AssignedCell F) (n0 n1 n2 n3 n4 n5 n6 : Nat)
    (ha : PlainRep env.toEnvironment a n0)
    (hb : PlainRep env.toEnvironment b n1)
    (hc : PlainRep env.toEnvironment c n2)
    (hd : PlainRep env.toEnvironment d n3)
    (he : PlainRep env.toEnvironment e n4)
    (hf : PlainRep env.toEnvironment f n5)
    (hg : PlainRep env.toEnvironment g n6)
    : Complete env (WitnessCircuit.prepareA #[a,b,c,d,e,f,g])
      (fun word => ARep env.place env.env.toEnvironment word ((n0+n1+n2+n3+n4+n5+n6) % 2^32)) := by
  have inputs : ∀ cell ∈ #[a,b,c,d,e,f,g], cellValue env.toEnvironment.place env.toEnvironment.env cell < 2^32 := by
    intro cell member
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ha.2]; exact ha.1
    · rw [hb.2]; exact hb.1
    · rw [hc.2]; exact hc.1
    · rw [hd.2]; exact hd.1
    · rw [he.2]; exact he.1
    · rw [hf.2]; exact hf.1
    · rw [hg.2]; exact hg.1
  intro cache self valid witnesses
  obtain ⟨satisfied,_,_⟩ := prepareA_action_complete env table #[a,b,c,d,e,f,g]
    (by change 7 ≤ 7; decide +kernel) inputs cache self valid witnesses
  exact ⟨satisfied, prepare7A_sound env.toEnvironment table a b c d e f g n0 n1 n2 n3 n4 n5 n6 ha hb hc hd he hf hg
    cache self valid satisfied⟩

private theorem prepare6E_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (a b c d e f : AssignedCell F) (n0 n1 n2 n3 n4 n5 : Nat)
    (ha : PlainRep env a n0)
    (hb : PlainRep env b n1)
    (hc : PlainRep env c n2)
    (hd : PlainRep env d n3)
    (he : PlainRep env e n4)
    (hf : PlainRep env f n5)
    : Sound env (WitnessCircuit.prepareE #[a,b,c,d,e,f])
      (fun word => ERep env.place env.env word ((n0+n1+n2+n3+n4+n5) % 2^32)) := by
  have inputs : ∀ cell ∈ #[a,b,c,d,e,f], cellValue env.place env.env cell < 2^32 := by
    intro cell member
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ha.2]; exact ha.1
    · rw [hb.2]; exact hb.1
    · rw [hc.2]; exact hc.1
    · rw [hd.2]; exact hd.1
    · rw [he.2]; exact he.1
    · rw [hf.2]; exact hf.1
  have result := prepareE_action env table #[a,b,c,d,e,f] (by change 6 ≤ 7; decide +kernel) inputs
  simpa only [List.toList_toArray, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, ha.2, hb.2, hc.2, hd.2, he.2, hf.2, Nat.add_assoc] using result

private theorem prepare6E_complete (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (a b c d e f : AssignedCell F) (n0 n1 n2 n3 n4 n5 : Nat)
    (ha : PlainRep env.toEnvironment a n0)
    (hb : PlainRep env.toEnvironment b n1)
    (hc : PlainRep env.toEnvironment c n2)
    (hd : PlainRep env.toEnvironment d n3)
    (he : PlainRep env.toEnvironment e n4)
    (hf : PlainRep env.toEnvironment f n5)
    : Complete env (WitnessCircuit.prepareE #[a,b,c,d,e,f])
      (fun word => ERep env.place env.env.toEnvironment word ((n0+n1+n2+n3+n4+n5) % 2^32)) := by
  have inputs : ∀ cell ∈ #[a,b,c,d,e,f], cellValue env.toEnvironment.place env.toEnvironment.env cell < 2^32 := by
    intro cell member
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ha.2]; exact ha.1
    · rw [hb.2]; exact hb.1
    · rw [hc.2]; exact hc.1
    · rw [hd.2]; exact hd.1
    · rw [he.2]; exact he.1
    · rw [hf.2]; exact hf.1
  intro cache self valid witnesses
  obtain ⟨satisfied,_,_⟩ := prepareE_action_complete env table #[a,b,c,d,e,f]
    (by change 6 ≤ 7; decide +kernel) inputs cache self valid witnesses
  exact ⟨satisfied, prepare6E_sound env.toEnvironment table a b c d e f n0 n1 n2 n3 n4 n5 ha hb hc hd he hf
    cache self valid satisfied⟩

private theorem nextState_rep (env : Placed Environment F)
    (state : Compression) (words : Vector Nat 8) (rep : StateRep env state words)
    (k w : Nat) (nextA nextE : Word)
    (ar : ARep env.place env.env nextA
      (((words[7]'(by decide)) + Specs.SHA256.upperSigma1 (words[4]'(by decide)) +
        Specs.SHA256.Ch (words[4]'(by decide)) (words[5]'(by decide)) (words[6]'(by decide)) + k + w +
        Specs.SHA256.upperSigma0 (words[0]'(by decide)) +
        Specs.SHA256.Maj (words[0]'(by decide)) (words[1]'(by decide)) (words[2]'(by decide))) % 2^32))
    (er : ERep env.place env.env nextE
      (((words[3]'(by decide)) + (words[7]'(by decide)) + Specs.SHA256.upperSigma1 (words[4]'(by decide)) +
        Specs.SHA256.Ch (words[4]'(by decide)) (words[5]'(by decide)) (words[6]'(by decide)) + k + w) % 2^32)) :
    StateRep env ⟨nextA,state.a.combined,state.b,state.c.plain,nextE,state.e.combined,state.f,state.g.plain⟩
      (Specs.SHA256.sha256Round words k w) := by
  obtain ⟨ra,rb,rc,_,re,rf,rg,_⟩ := rep
  have pa := pairRep_of_ARep ra
  have pe := pairRep_of_ERep re
  simp only [StateRep, round_a, round_b, round_c, round_d, round_e, round_f, round_g, round_h]
  exact ⟨ar,pa,rb,rc.1,er,pe,rf,rg.1⟩

/-- Soundness of the unchanged source compressionRound, including all calls,
actual copied cells, cache updates, and the SHA-256 round state permutation. -/
theorem compressionRound_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (state : Compression) (words : Vector Nat 8) (rep : StateRep env state words)
    (k : Nat) (hk : k < 2^32) (word : AssignedCell F) (w : Nat) (hw : PlainRep env word w) :
    Sound env (compressionRound state k word)
      (fun output => StateRep env output (Specs.SHA256.sha256Round words k w)) := by
  have original := rep
  obtain ⟨ra,rb,rc,rd,re,rf,rg,rh⟩ := rep
  have pa := pairRep_of_ARep ra
  have pe := pairRep_of_ERep re
  unfold compressionRound
  apply sound_bind (Linear.constant_nextRegionIndex k) (Initialize.constant_plain_sound env k hk)
  intro kcell kr
  apply sound_bind (bigSigma0_lawful state.a) (bigSigma0_plain env table _ _ ra)
  intro s0 sr0
  apply sound_bind (majority_lawful _ _ _) (majority_plain env table _ _ _ _ _ _ pa rb rc)
  intro maj mr
  apply sound_bind (bigSigma1_lawful state.e) (bigSigma1_plain env table _ _ re)
  intro s1 sr1
  apply sound_bind (choice_lawful _ _ _) (choice_plain env table _ _ _ _ _ _ pe rf rg)
  intro ch cr
  apply sound_bind (prepareA_lawful _)
    (prepare7A_sound env table _ _ _ _ _ _ _ _ _ _ _ _ _ _ rh sr1 cr kr hw sr0 mr)
  intro nextA ar
  apply sound_bind (prepareE_lawful _)
    (prepare6E_sound env table _ _ _ _ _ _ _ _ _ _ _ _ rd rh sr1 cr kr hw)
  intro nextE er
  apply sound_pure
  exact nextState_rep env state words original k w nextA nextE ar er

/-- Honest execution of every source subprogram satisfies the actual round's
constraints and returns the specified next state, preserving the source cache. -/
theorem compressionRound_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (state : Compression) (words : Vector Nat 8) (rep : StateRep env.toEnvironment state words)
    (k : Nat) (hk : k < 2^32) (word : AssignedCell F) (w : Nat)
    (hw : PlainRep env.toEnvironment word w) :
    ∀ cache self, CacheMeaning env.toEnvironment cache →
      ExtendsWitnesses env.place env.env (((compressionRound state k word) cache).operations self) self →
      Constraints env.place env.env.toEnvironment (((compressionRound state k word) cache).operations self) self ∧
      StateRep env.toEnvironment (((compressionRound state k word) cache).output self).1
        (Specs.SHA256.sha256Round words k w) ∧
      CacheMeaning env.toEnvironment (((compressionRound state k word) cache).output self).2 := by
  change Complete env (compressionRound state k word)
    (fun output => StateRep env.toEnvironment output (Specs.SHA256.sha256Round words k w))

  have original := rep
  obtain ⟨ra,rb,rc,rd,re,rf,rg,rh⟩ := rep
  have pa := pairRep_of_ARep ra
  have pe := pairRep_of_ERep re
  unfold compressionRound
  apply complete_bind (Linear.constant_nextRegionIndex k) (constant_plain_complete env k hk)
  intro kcell kr
  apply complete_bind (bigSigma0_lawful state.a) (bigSigma0_plain_complete env table _ _ ra)
  intro s0 sr0
  apply complete_bind (majority_lawful _ _ _) (majority_plain_complete env table _ _ _ _ _ _ pa rb rc)
  intro maj mr
  apply complete_bind (bigSigma1_lawful state.e) (bigSigma1_plain_complete env table _ _ re)
  intro s1 sr1
  apply complete_bind (choice_lawful _ _ _) (choice_plain_complete env table _ _ _ _ _ _ pe rf rg)
  intro ch cr
  apply complete_bind (prepareA_lawful _)
    (prepare7A_complete env table _ _ _ _ _ _ _ _ _ _ _ _ _ _ rh sr1 cr kr hw sr0 mr)
  intro nextA ar
  apply complete_bind (prepareE_lawful _)
    (prepare6E_complete env table _ _ _ _ _ _ _ _ _ _ _ _ rd rh sr1 cr kr hw)
  intro nextE er
  apply complete_pure
  exact nextState_rep env.toEnvironment state words original k w nextA nextE ar er

end Midnight.SHA256.Semantics.Round
