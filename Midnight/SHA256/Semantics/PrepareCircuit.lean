import Midnight.SHA256.Semantics.PrepareRows
import Midnight.SHA256.Semantics.ParityGadget
import Midnight.SHA256.Semantics.BitwiseGadgets
import Midnight.SHA256.Semantics.Linear
import Midnight.SHA256.WitnessPrepare

/-! Contracts for the actual word preparation source regions. Copy constraints
connect the seven gate queries to the original input cells; output range and
spread invariants are derived from the native gates and loaded table. -/
namespace Midnight.SHA256.Semantics.PrepareCircuit
open Halo2 Gates PrepareGates PrepareRows WitnessCircuit WitnessPrepare ParityGadget

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
set_option linter.constructorNameAsVariable false

def cellValue (place : RegionIndex → Nat) (env : Environment F) (cell : AssignedCell F) : Nat :=
  (cell.eval place env).val

theorem toList_seven {α : Type} [Inhabited α] (terms : Array α)
    (size : terms.size = 7) :
    terms.toList = [terms[0]!, terms[1]!, terms[2]!, terms[3]!, terms[4]!, terms[5]!, terms[6]!] := by
  apply List.ext_getElem
  · simpa using size
  intro i hi hj
  have small : i < 7 := by simpa [size] using hi
  interval_cases i <;> simp_all

/-- Exact copy and activation consequences of the actual addition helper. The
seven-term precondition matches its native source copy loop. -/
theorem addMod_facts {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7)
    (satisfied : RegionOperations.Constraints place self env
      ((addMod summands zero).operations self)) :
    RegionOperations.Constraints place self env (activation 15 1) ∧
    RegionOperations.Constraints place self env (activation 4 2) ∧
    env.fixed ⟨1⟩ (place self + 2 : Nat) = (3 : F) ∧
    summandValues env (place self + 1 : Nat) =
      ((summands ++ Array.replicate (7 - summands.size) zero).toList.map (cellValue place env)) := by
  rw [addMod_eq] at satisfied
  simp only [addModExpanded, scopy, circuit_norm, and_true, true_and,
    plainAndSpread_constraints] at satisfied
  obtain ⟨gate, h0, h1, h2, h3, h4, h5, h6, active, tag⟩ := satisfied
  refine ⟨gate, active, tag, ?_⟩
  rw [toList_seven _ (paddedTerms_size summands zero size)]
  simp only [summandValues, List.map_cons, List.map_nil, cellValue]
  norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] at h0 h1 h2 h3 h4 h5 h6 ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, and_self]

/-- The A word invariant uses the first four limbs. The source also emits a
dummy fifth limb, whereas initial constant A words have only four limbs. -/
def ARep (place : RegionIndex → Nat) (env : Environment F) (word : Word) (n : Nat) : Prop :=
  ∃ a b c d : Nat,
    Decomposition.Bounded (Decomposition.aLimbs a b c d) ∧
    n = Decomposition.pack (Decomposition.aLimbs a b c d) ∧
    cellValue place env word.combined.plain = n ∧
    word.combined.spread.eval place env = (spread n : F) ∧
    BitwiseGadgets.limbValues place env word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F)]

def ERep (place : RegionIndex → Nat) (env : Environment F) (word : Word) (n : Nat) : Prop :=
  ∃ a b c d e : Nat,
    Decomposition.Bounded (Decomposition.eLimbs a b c d e) ∧
    n = Decomposition.pack (Decomposition.eLimbs a b c d e) ∧
    cellValue place env word.combined.plain = n ∧
    word.combined.spread.eval place env = (spread n : F) ∧
    BitwiseGadgets.limbValues place env word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F)]

/-- Message words intentionally carry no combined spread value: their native
source uses the plain cell as a placeholder in that record field. -/
def MessageRep (place : RegionIndex → Nat) (env : Environment F) (word : Word) (n : Nat) : Prop :=
  ∃ a b c d e f g h : Nat,
    Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h) ∧
    n = Decomposition.pack (Decomposition.messageLimbs a b c d e f g h) ∧
    cellValue place env word.combined.plain = n ∧
    BitwiseGadgets.limbValues place env word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F),
         (spread e:F), (spread f:F), (spread g:F), (spread h:F)]

theorem paddedValues_bounded {place : RegionIndex → Nat} {env : Environment F}
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (zeroValue : cellValue place env zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env cell < 2 ^ 32) :
    ∀ n ∈ ((summands ++ Array.replicate (7 - summands.size) zero).toList.map
      (cellValue place env)), n < 2 ^ 32 := by
  intro n hn
  simp only [Array.toList_append, Array.toList_replicate, List.map_append,
    List.mem_append, List.mem_map, List.mem_replicate] at hn
  rcases hn with ⟨cell, hcell, rfl⟩ | ⟨cell, ⟨_, rfl⟩, rfl⟩
  · exact inputs cell (by simpa using hcell)
  · rw [zeroValue]
    norm_num

theorem aRegion_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7) (zeroValue : cellValue place env zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env cell < 2 ^ 32)
    (satisfied : RegionOperations.Constraints place self env
      ((aRegion summands zero).operations self)) :
    ARep place env ((aRegion summands zero).output self)
      ((summands.toList.map (cellValue place env)).sum % 2 ^ 32) := by
  simp only [aRegion, circuit_norm, true_and] at satisfied
  obtain ⟨gate, addition, limb0, limb1, limb2, limb3, limb4⟩ := satisfied
  obtain ⟨addGate, active2, carryTag, copies⟩ :=
    addMod_facts (place := place) (self := self) (env := env) summands zero size addition
  have h0 := (plainAndSpread_constraints place self env 10 0 0 _).mp limb0
  have h1 := (plainAndSpread_constraints place self env 9 0 1 _).mp limb1
  have h2 := (plainAndSpread_constraints place self env 11 1 0 _).mp limb2
  have h3 := (plainAndSpread_constraints place self env 2 1 1 _).mp limb3
  have h4 := (plainAndSpread_constraints place self env 0 2 0 _).mp limb4
  have bounded : ∀ n ∈ summandValues env (place self + 1 : Nat), n < 2 ^ 32 := by
    rw [copies]
    exact paddedValues_bounded summands zero zeroValue inputs
  have result := a_result (place := place) (self := self) (env := env)
    table h0.1 h2.1 active2 gate addGate ⟨h0.2, h1.2⟩ ⟨h2.2, h3.2⟩ ⟨h4.2, carryTag⟩ bounded
  have total : (summandValues env (place self + 1 : Nat)).sum =
      (summands.toList.map (cellValue place env)).sum := by
    rw [copies, paddedTerms_sum summands zero _ zeroValue]
  rw [total] at result
  have lookup0 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 10 0 ⟨0, by decide +kernel⟩ _ limb0
  have lookup1 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 9 0 ⟨1, by decide +kernel⟩ _ limb1
  have lookup2 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 11 1 ⟨0, by decide +kernel⟩ _ limb2
  have lookup3 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 2 1 ⟨1, by decide +kernel⟩ _ limb3
  have l0 := (lookup_values (width := 10) (by norm_num [BLS12_381.scalarFieldSize]) lookup0).2
  have l1 := (lookup_values (width := 9) (by norm_num [BLS12_381.scalarFieldSize]) lookup1).2
  have l2 := (lookup_values (width := 11) (by norm_num [BLS12_381.scalarFieldSize]) lookup2).2
  have l3 := (lookup_values (width := 2) (by norm_num [BLS12_381.scalarFieldSize]) lookup3).2
  refine ⟨_, _, _, _, result.1, result.2.2.2.2.1.symm.trans result.2.1, ?_, ?_, ?_⟩
  · simpa [cellValue, aRegion_output, aeOutput, shaCell, circuit_norm,
      Gates.read, Synthesis.shaAdvice, Nat.cast_add] using result.2.2.2.2.1
  · have h := congrArg (fun n : Nat => (n : F)) result.2.2.2.1
    simp only [ZMod.natCast_zmod_val] at h
    rw [result.2.2.2.2.1] at h
    simpa [aRegion_output, aeOutput, shaCell, circuit_norm,
      Gates.read, Synthesis.shaAdvice, Nat.cast_add] using h
  · apply Vector.ext
    intro i hi
    interval_cases i <;>
      simpa [BitwiseGadgets.limbValues, aRegion_output, aeOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using (by assumption)

theorem eRegion_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7) (zeroValue : cellValue place env zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env cell < 2 ^ 32)
    (satisfied : RegionOperations.Constraints place self env
      ((eRegion summands zero).operations self)) :
    ERep place env ((eRegion summands zero).output self)
      ((summands.toList.map (cellValue place env)).sum % 2 ^ 32) := by
  simp only [eRegion, circuit_norm, true_and] at satisfied
  obtain ⟨gate, addition, limb0, limb1, limb2, limb3, limb4⟩ := satisfied
  obtain ⟨addGate, active2, carryTag, copies⟩ :=
    addMod_facts (place := place) (self := self) (env := env) summands zero size addition
  have h0 := (plainAndSpread_constraints place self env 7 0 0 _).mp limb0
  have h1 := (plainAndSpread_constraints place self env 12 0 1 _).mp limb1
  have h2 := (plainAndSpread_constraints place self env 2 1 0 _).mp limb2
  have h3 := (plainAndSpread_constraints place self env 5 1 1 _).mp limb3
  have h4 := (plainAndSpread_constraints place self env 6 2 0 _).mp limb4
  have bounded : ∀ n ∈ summandValues env (place self + 1 : Nat), n < 2 ^ 32 := by
    rw [copies]
    exact paddedValues_bounded summands zero zeroValue inputs
  have result := e_result (place := place) (self := self) (env := env)
    table h0.1 h2.1 active2 gate addGate ⟨h0.2, h1.2⟩ ⟨h2.2, h3.2⟩ ⟨h4.2, carryTag⟩ bounded
  have total : (summandValues env (place self + 1 : Nat)).sum =
      (summands.toList.map (cellValue place env)).sum := by
    rw [copies, paddedTerms_sum summands zero _ zeroValue]
  rw [total] at result
  have lookup0 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 7 0 ⟨0, by decide +kernel⟩ _ limb0
  have lookup1 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 12 0 ⟨1, by decide +kernel⟩ _ limb1
  have lookup2 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 2 1 ⟨0, by decide +kernel⟩ _ limb2
  have lookup3 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 5 1 ⟨1, by decide +kernel⟩ _ limb3
  have lookup4 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 6 2 ⟨0, by decide +kernel⟩ _ limb4
  have l0 := (lookup_values (width := 7) (by norm_num [BLS12_381.scalarFieldSize]) lookup0).2
  have l1 := (lookup_values (width := 12) (by norm_num [BLS12_381.scalarFieldSize]) lookup1).2
  have l2 := (lookup_values (width := 2) (by norm_num [BLS12_381.scalarFieldSize]) lookup2).2
  have l3 := (lookup_values (width := 5) (by norm_num [BLS12_381.scalarFieldSize]) lookup3).2
  have l4 := (lookup_values (width := 6) (by norm_num [BLS12_381.scalarFieldSize]) lookup4).2
  refine ⟨_, _, _, _, _, result.1, result.2.2.2.2.1.symm.trans result.2.1, ?_, ?_, ?_⟩
  · simpa [cellValue, eRegion_output, aeOutput, shaCell, circuit_norm,
      Gates.read, Synthesis.shaAdvice, Nat.cast_add] using result.2.2.2.2.1
  · have h := congrArg (fun n : Nat => (n : F)) result.2.2.2.1
    simp only [ZMod.natCast_zmod_val] at h
    rw [result.2.2.2.2.1] at h
    simpa [eRegion_output, aeOutput, shaCell, circuit_norm,
      Gates.read, Synthesis.shaAdvice, Nat.cast_add] using h
  · apply Vector.ext
    intro i hi
    interval_cases i <;>
      simpa [BitwiseGadgets.limbValues, eRegion_output, aeOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using (by assumption)

theorem messageRegion_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7) (zeroValue : cellValue place env zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env cell < 2 ^ 32)
    (satisfied : RegionOperations.Constraints place self env
      ((messageRegion summands zero).operations self)) :
    MessageRep place env ((messageRegion summands zero).output self)
      ((summands.toList.map (cellValue place env)).sum % 2 ^ 32) := by
  simp only [messageRegion, circuit_norm, and_true] at satisfied
  obtain ⟨gate, addition, limb0, limb1, limb2, limb3, limb4⟩ := satisfied
  obtain ⟨addGate, active2, carryTag, copies⟩ :=
    addMod_facts (place := place) (self := self) (env := env) summands zero size addition
  have h0 := (plainAndSpread_constraints place self env 12 0 0 _).mp limb0
  have h1 := (plainAndSpread_constraints place self env 7 0 1 _).mp limb1
  have h2 := (plainAndSpread_constraints place self env 3 1 0 _).mp limb2
  have h3 := (plainAndSpread_constraints place self env 4 1 1 _).mp limb3
  have h4 := (plainAndSpread_constraints place self env 3 2 0 _).mp limb4
  have bounded : ∀ n ∈ summandValues env (place self + 1 : Nat), n < 2 ^ 32 := by
    rw [copies]
    exact paddedValues_bounded summands zero zeroValue inputs
  have result := message_result (place := place) (self := self) (env := env)
    table h0.1 h2.1 active2 gate addGate ⟨h0.2, h1.2⟩ ⟨h2.2, h3.2⟩ ⟨h4.2, carryTag⟩ bounded
  have total : (summandValues env (place self + 1 : Nat)).sum =
      (summands.toList.map (cellValue place env)).sum := by
    rw [copies, paddedTerms_sum summands zero _ zeroValue]
  rw [total] at result
  have lookup0 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 12 0 ⟨0, by decide +kernel⟩ _ limb0
  have lookup1 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 7 0 ⟨1, by decide +kernel⟩ _ limb1
  have lookup2 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 3 1 ⟨0, by decide +kernel⟩ _ limb2
  have lookup3 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 4 1 ⟨1, by decide +kernel⟩ _ limb3
  have lookup4 := plainAndSpread_lookup (place := place) (self := self) (env := env)
    table 3 2 ⟨0, by decide +kernel⟩ _ limb4
  have l0 := (lookup_values (width := 12) (by norm_num [BLS12_381.scalarFieldSize]) lookup0).2
  have l1 := (lookup_values (width := 7) (by norm_num [BLS12_381.scalarFieldSize]) lookup1).2
  have l2 := (lookup_values (width := 3) (by norm_num [BLS12_381.scalarFieldSize]) lookup2).2
  have l3 := (lookup_values (width := 4) (by norm_num [BLS12_381.scalarFieldSize]) lookup3).2
  have l4 := (lookup_values (width := 3) (by norm_num [BLS12_381.scalarFieldSize]) lookup4).2
  have bitBounds := result.1
  simp only [messageValues, Decomposition.Bounded, Decomposition.messageLimbs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp] at bitBounds
  have b1 := congrArg (fun n : Nat => (n : F)) (Rotations.spread_one_bit bitBounds.2.1)
  have b2 := congrArg (fun n : Nat => (n : F)) (Rotations.spread_one_bit bitBounds.2.2.1)
  have b3 := congrArg (fun n : Nat => (n : F)) (Rotations.spread_one_bit bitBounds.2.2.2.1)
  simp only [ZMod.natCast_zmod_val] at b1 b2 b3
  refine ⟨_, _, _, _, _, _, _, _, result.1,
    result.2.2.2.1.symm.trans result.2.1, ?_, ?_⟩
  · simpa [cellValue, messageRegion_output, messageOutput, shaCell, circuit_norm,
      Gates.read, Synthesis.shaAdvice, Nat.cast_add] using result.2.2.2.1
  · apply Vector.ext
    intro i hi
    interval_cases i
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using l0
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using b1.symm
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using b2.symm
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using b3.symm
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using l1
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using l2
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add] using l3
    · simpa [BitwiseGadgets.limbValues, messageRegion_output, messageOutput, shaCell, circuit_norm,
        Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using l4

/-- Exact source execution, including the cached-zero allocation. -/
theorem prepareA_run (summands : Array (AssignedCell F)) (cache : Cache) :
    (WitnessCircuit.prepareA summands).run cache = (do
      let (zero, nextCache) ← (constant 0).run cache
      let output ← assignRegion "decompose A in 10-9-11-2" (aRegion summands zero)
      return (output, nextCache)) := by
  simp only [WitnessCircuit.prepareA, WitnessCircuit.prepare, prepareARegion_eq]
  rfl

/-- Soundness of the actual state-threaded source helper. All input and table
conditions are independent of its output; the cache invariant is preserved. -/
theorem prepareA_sound (summands : Array (AssignedCell F)) (cache : Cache)
    (self : RegionIndex) (env : Placed Environment F)
    (table : SpreadTable env.env) (cacheValid : Linear.CacheMeaning env cache)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env cell < 2 ^ 32)
    (satisfied : Constraints env.place env.env
      (((WitnessCircuit.prepareA summands).run cache).operations self) self) :
    let output := ((WitnessCircuit.prepareA summands).run cache).output self
    ARep env.place env.env output.1
      ((summands.toList.map (cellValue env.place env.env)).sum % 2 ^ 32) ∧
      Linear.CacheMeaning env output.2 := by
  rw [prepareA_run] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  rw [← Linear.constant_nextRegionIndex] at satisfied
  obtain ⟨constantConstraints, regionConstraints⟩ := satisfied
  obtain ⟨zeroValue, nextCache⟩ := Linear.constant_sound 0 cache self env cacheValid constantConstraints
  refine ⟨?_, nextCache⟩
  apply aRegion_sound (place := env.place) (env := env.env)
    table _ _ size ?_ inputs regionConstraints
  simp only [cellValue, zeroValue, Nat.cast_zero, ZMod.val_zero]

/-- Exact source execution, including the cached-zero allocation. -/
theorem prepareE_run (summands : Array (AssignedCell F)) (cache : Cache) :
    (WitnessCircuit.prepareE summands).run cache = (do
      let (zero, nextCache) ← (constant 0).run cache
      let output ← assignRegion "decompose E in 7-12-2-5-6" (eRegion summands zero)
      return (output, nextCache)) := by
  simp only [WitnessCircuit.prepareE, WitnessCircuit.prepare, prepareERegion_eq]
  rfl

/-- Soundness of the actual state-threaded source helper. All input and table
conditions are independent of its output; the cache invariant is preserved. -/
theorem prepareE_sound (summands : Array (AssignedCell F)) (cache : Cache)
    (self : RegionIndex) (env : Placed Environment F)
    (table : SpreadTable env.env) (cacheValid : Linear.CacheMeaning env cache)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env cell < 2 ^ 32)
    (satisfied : Constraints env.place env.env
      (((WitnessCircuit.prepareE summands).run cache).operations self) self) :
    let output := ((WitnessCircuit.prepareE summands).run cache).output self
    ERep env.place env.env output.1
      ((summands.toList.map (cellValue env.place env.env)).sum % 2 ^ 32) ∧
      Linear.CacheMeaning env output.2 := by
  rw [prepareE_run] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  rw [← Linear.constant_nextRegionIndex] at satisfied
  obtain ⟨constantConstraints, regionConstraints⟩ := satisfied
  obtain ⟨zeroValue, nextCache⟩ := Linear.constant_sound 0 cache self env cacheValid constantConstraints
  refine ⟨?_, nextCache⟩
  apply eRegion_sound (place := env.place) (env := env.env)
    table _ _ size ?_ inputs regionConstraints
  simp only [cellValue, zeroValue, Nat.cast_zero, ZMod.val_zero]

/-- Exact source execution, including the cached-zero allocation. -/
theorem prepareMessage_run (summands : Array (AssignedCell F)) (cache : Cache) :
    (WitnessCircuit.prepareMessage summands).run cache = (do
      let (zero, nextCache) ← (constant 0).run cache
      let output ← assignRegion "prepare message word" (messageRegion summands zero)
      return (output, nextCache)) := by
  simp only [WitnessCircuit.prepareMessage, prepareMessageRegion_eq]
  rfl

/-- Soundness of the actual state-threaded source helper. All input and table
conditions are independent of its output; the cache invariant is preserved. -/
theorem prepareMessage_sound (summands : Array (AssignedCell F)) (cache : Cache)
    (self : RegionIndex) (env : Placed Environment F)
    (table : SpreadTable env.env) (cacheValid : Linear.CacheMeaning env cache)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env cell < 2 ^ 32)
    (satisfied : Constraints env.place env.env
      (((WitnessCircuit.prepareMessage summands).run cache).operations self) self) :
    let output := ((WitnessCircuit.prepareMessage summands).run cache).output self
    MessageRep env.place env.env output.1
      ((summands.toList.map (cellValue env.place env.env)).sum % 2 ^ 32) ∧
      Linear.CacheMeaning env output.2 := by
  rw [prepareMessage_run] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  rw [← Linear.constant_nextRegionIndex] at satisfied
  obtain ⟨constantConstraints, regionConstraints⟩ := satisfied
  obtain ⟨zeroValue, nextCache⟩ := Linear.constant_sound 0 cache self env cacheValid constantConstraints
  refine ⟨?_, nextCache⟩
  apply messageRegion_sound (place := env.place) (env := env.env)
    table _ _ size ?_ inputs regionConstraints
  simp only [cellValue, zeroValue, Nat.cast_zero, ZMod.val_zero]

theorem ARep.bounded {place : RegionIndex → Nat} {env : Environment F}
    {word : Word} {n : Nat} (rep : ARep place env word n) : n < 2 ^ 32 := by
  obtain ⟨a, b, c, d, bounded, packed, _⟩ := rep
  rw [packed]
  simpa [Decomposition.aLimbs, Decomposition.width] using Decomposition.pack_lt _ bounded

theorem ERep.bounded {place : RegionIndex → Nat} {env : Environment F}
    {word : Word} {n : Nat} (rep : ERep place env word n) : n < 2 ^ 32 := by
  obtain ⟨a, b, c, d, e, bounded, packed, _⟩ := rep
  rw [packed]
  simpa [Decomposition.eLimbs, Decomposition.width] using Decomposition.pack_lt _ bounded

theorem MessageRep.bounded {place : RegionIndex → Nat} {env : Environment F}
    {word : Word} {n : Nat} (rep : MessageRep place env word n) : n < 2 ^ 32 := by
  obtain ⟨a, b, c, d, e, f, g, h, bounded, packed, _⟩ := rep
  rw [packed]
  simpa [Decomposition.messageLimbs, Decomposition.width] using Decomposition.pack_lt _ bounded

end Midnight.SHA256.Semantics.PrepareCircuit
