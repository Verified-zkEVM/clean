import Midnight.SHA256.Semantics.ChoiceGadget
import Midnight.SHA256.Semantics.ParityWitness

/-! Honest-witness completeness for the source bitwise gadgets. Bounds connect
32-bit input representations to the native 64-bit parity witness arithmetic. -/
namespace Midnight.SHA256.Semantics.BitwiseWitness
open Halo2 Gates WitnessCircuit ParityGadget ParityWitness BitwiseGadgets

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation

private theorem clean_sum (a b : Midnight.Keygen.E) : a + b = Halo2.Expression.add a b := rfl

private theorem clean_sub (a b : Midnight.Keygen.E) :
    a - b = Halo2.Expression.add a (Halo2.Expression.mul (Halo2.Expression.const (-1)) b) := rfl

private theorem clean_mul (a b : Midnight.Keygen.E) : a * b = Halo2.Expression.mul a b := rfl

/-- Every spread-encoded 32-bit word occupies a subset of the native even mask. -/
theorem spread_le_mask32 {word : Nat} (bound : word < 2^32) :
    spread word ≤ 0x5555555555555555 := by
  have h := spread_complement bound
  rw [spread_mask32] at h
  omega

theorem three_spreads_lt_u64 {a b c : Nat}
    (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) :
    spread a + spread b + spread c < 2^64 := by
  have h₀ := spread_le_mask32 ha
  have h₁ := spread_le_mask32 hb
  have h₂ := spread_le_mask32 hc
  norm_num at *
  omega

theorem spread_cast_val {word : Nat} (bound : word < 2^32) :
    (spread word:F).val = spread word := by
  apply ZMod.val_natCast_of_lt
  exact (spread_lt bound).trans (by decide +kernel)

/-- Converse of source Maj-row extraction. -/
theorem maj_equation_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (equation : Gates.read env (place self+row:Nat) 5 (-1) +
      Gates.read env (place self+row:Nat) 6 (-1) + Gates.read env (place self+row:Nat) 5 0 =
      parityPlane env (place self+row:Nat) 3 + 2*parityPlane env (place self+row:Nat) 1) :
    RegionOperations.Constraints place self env (activation 5 row) := by
  rw [activation_maj]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, majGate, majSpec,
    Midnight.Keygen.GateSpec.toClean, pow4ip, pow2ip, sumExpr,
    clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [Gates.read, parityPlane, Synthesis.shaAdvice] at equation
  linear_combination (norm := ring_nf) equation

theorem majorityRegion_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (a b c : AssignedCell F) (x y z : Nat) (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (ax : a.eval place env.toEnvironment = (spread x:F))
    (by_ : b.eval place env.toEnvironment = (spread y:F))
    (cz : c.eval place env.toEnvironment = (spread z:F))
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((majorityRegion a b c).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((majorityRegion a b c).operations self) := by
  simp only [majorityRegion, scopy, circuit_norm, activation_maj, true_and] at witnesses
  obtain ⟨ac, bc, cc, parity⟩ := witnesses
  have hsum : spread x + spread y + spread z < 2^64 := three_spreads_lt_u64 hx hy hz
  have evalSum : ((Witgen.U64ExprOver.add (.add (WitnessIR.readNat a) (WitnessIR.readNat b))
      (WitnessIR.readNat c)).eval {env := (⟨place,env⟩:Placed ProverEnvironment F)}).toNat =
      spread x + spread y + spread z := by
    simp only [Witgen.U64ExprOver.eval, UInt64.toNat_add, WitnessIR.eval_readNat,
      Halo2.WitgenEnv.readVar_halo2, ax, by_, cz, spread_cast_val hx, spread_cast_val hy,
      spread_cast_val hz]
    rw [Nat.mod_eq_of_lt (by omega : spread x < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : spread y < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : spread z < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : spread x + spread y < 2 ^ 64),
      Nat.mod_eq_of_lt hsum]
  have sumEquation := spread111110_sum (place := place) (self := self) (env := env)
    true 0 _ parity
  have complete := spread111110_complete (place := place) (self := self) (env := env)
    table true 0 _ parity
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 5 1) := by
    apply maj_equation_complete
    norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
    norm_num [Synthesis.shaAdvice, circuit_norm] at ac bc cc
    rw [ac, bc, cc, ax, by_, cz]
    rw [evalSum] at sumEquation
    simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, Nat.zero_add, ↓reduceIte] using
      sumEquation.symm
  simp only [majorityRegion, scopy, circuit_norm, true_and]
  exact ⟨gate, ac, bc, cc, complete⟩

/-- Honest execution satisfies the original source Build function and has its
SHA semantic output. -/
theorem majority_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (a b c : AssignedCell F) (cache : Cache) (x y z : Nat)
    (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (ax : a.eval place env.toEnvironment = (spread x:F))
    (by_ : b.eval place env.toEnvironment = (spread y:F))
    (cz : c.eval place env.toEnvironment = (spread z:F))
    (witnesses : ExtendsWitnesses place env
      (((WitnessCircuit.majority a b c).run cache).operations self) self) :
    Constraints place env.toEnvironment (((WitnessCircuit.majority a b c).run cache).operations self) self ∧
      ((((WitnessCircuit.majority a b c).run cache).output self).1.eval place env.toEnvironment).val =
        Specs.SHA256.Maj x y z := by
  have complete : Constraints place env.toEnvironment
      (((WitnessCircuit.majority a b c).run cache).operations self) self := by
    rw [majority_source] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    exact majorityRegion_complete table a b c x y z hx hy hz ax by_ cz witnesses
  exact ⟨complete, majority_sound table a b c cache x y z hx hy hz ax by_ cz complete⟩

/-- Evaluation of the actual serializable Sigma recipe on its source cells. -/
theorem weighted_eval {n : Nat} (recipe : Witness.Recipe n) (word : Word)
    (env : Placed ProverEnvironment F)
    (hlimbs : ∀ i : Fin n, (word.limbs[i.val]!.eval env.place env.env.toEnvironment).val < 2 ^ 64)
    (hsum : Witness.weighted recipe ((limbValues env.place env.env.toEnvironment word).map ZMod.val) < 2 ^ 64) :
    ((WitnessIR.weighted recipe (Vector.ofFn fun i:Fin n => WitnessIR.readNat word.limbs[i.val]!)).eval {env}).toNat =
      Witness.weighted recipe ((limbValues env.place env.env.toEnvironment word).map ZMod.val) := by
  rw [WitnessIR.eval_weighted]
  have hvec : (Vector.ofFn fun i:Fin n => WitnessIR.readNat word.limbs[i.val]!).map
      (fun expression => (expression.eval {env}).toNat) =
      (limbValues env.place env.env.toEnvironment word).map ZMod.val := by
    apply Vector.ext
    intro i hi
    simp only [limbValues, Vector.getElem_map, Vector.getElem_ofFn, WitnessIR.eval_readNat,
      Halo2.WitgenEnv.readVar_halo2]
    exact Nat.mod_eq_of_lt (hlimbs ⟨i, hi⟩)
  rw [hvec, Nat.mod_eq_of_lt hsum]

/-- The integer recipe's field image is the same polynomial on actual cells. -/
theorem weighted_eval_cast {n : Nat} (recipe : Witness.Recipe n) (word : Word)
    (env : Placed ProverEnvironment F)
    (hlimbs : ∀ i : Fin n, (word.limbs[i.val]!.eval env.place env.env.toEnvironment).val < 2 ^ 64)
    (hsum : Witness.weighted recipe ((limbValues env.place env.env.toEnvironment word).map ZMod.val) < 2 ^ 64) :
    (((WitnessIR.weighted recipe (Vector.ofFn fun i:Fin n => WitnessIR.readNat word.limbs[i.val]!)).eval {env}).toNat:F) =
      weightedField recipe (limbValues env.place env.env.toEnvironment word) := by
  rw [weighted_eval recipe word env hlimbs hsum, ← weightedField_cast]
  simp only [Vector.map_map, Function.comp_def, ZMod.natCast_zmod_val, Vector.map_id']

theorem bigSigma0_equation_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (equation : weightedField Witness.bigSigma0Recipe (bigSigma0Inputs env (place self+row:Nat)) =
      parityPlane env (place self+row:Nat) 1 + 2*parityPlane env (place self+row:Nat) 3) :
    RegionOperations.Constraints place self env (activation 7 row) := by
  rw [activation_bigSigma0]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, bigSigma0Gate, bigSigma0Spec,
    Midnight.Keygen.GateSpec.toClean, pow4ip, pow2ip, sumExpr,
    clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [weightedField, Witness.bigSigma0Recipe, bigSigma0Inputs,
    Gates.read, parityPlane, Synthesis.shaAdvice] at equation
  linear_combination (norm := ring_nf) equation

theorem bigSigma0_witness_eval (word : Word) (env : Placed ProverEnvironment F)
    (a b c d : Nat) (bounded : Decomposition.Bounded (Decomposition.aLimbs a b c d))
    (inputs : limbValues env.place env.env.toEnvironment word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F)]) :
    (((WitnessIR.weighted Witness.bigSigma0Recipe
      (Vector.ofFn fun i:Fin 4 => WitnessIR.readNat word.limbs[i.val]!)).eval {env}).toNat : F) =
      weightedField Witness.bigSigma0Recipe (limbValues env.place env.env.toEnvironment word) := by
  have small (bits value : Nat) (member : (bits,value) ∈ Decomposition.aLimbs a b c d)
      (width : bits ≤ 32) : value < 2^32 :=
    (bounded _ member).trans_le (Nat.pow_le_pow_right (by decide) width)
  have ha := small 10 a (by simp [Decomposition.aLimbs]) (by decide)
  have hb := small 9 b (by simp [Decomposition.aLimbs]) (by decide)
  have hc := small 11 c (by simp [Decomposition.aLimbs]) (by decide)
  have hd := small 2 d (by simp [Decomposition.aLimbs]) (by decide)
  have hlimbs : ∀ i : Fin 4, (word.limbs[i.val]!.eval env.place env.env.toEnvironment).val < 2 ^ 64 := by
    intro i
    have hi := congrArg (fun v => v[i.val]) inputs
    simp only [limbValues, Vector.getElem_ofFn] at hi
    rw [hi]
    fin_cases i
    · simpa [spread_cast_val ha] using spread_lt ha
    · simpa [spread_cast_val hb] using spread_lt hb
    · simpa [spread_cast_val hc] using spread_lt hc
    · simpa [spread_cast_val hd] using spread_lt hd
  apply weighted_eval_cast _ _ _ hlimbs
  rw [inputs]
  have vals : (#v[(spread a:F), (spread b:F), (spread c:F), (spread d:F)]).map ZMod.val =
      #v[spread a, spread b, spread c, spread d] := by
    ext i hi
    interval_cases i <;> simp [spread_cast_val ha, spread_cast_val hb, spread_cast_val hc, spread_cast_val hd]
  rw [vals]
  change Witness.spreadedBigSigma0 _ < _
  rw [Rotations.bigSigma0_recipe a b c d bounded]
  have packedBound : Decomposition.pack (Decomposition.aLimbs a b c d) < 2^32 := by
    simpa [Decomposition.width, Decomposition.aLimbs] using Decomposition.pack_lt _ bounded
  exact three_spreads_lt_u64 (Rotations.rotRight32_lt packedBound 2)
    (Rotations.rotRight32_lt packedBound 13) (Rotations.rotRight32_lt packedBound 22)

theorem bigSigma0Region_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word)
    (a b c d : Nat) (bounded : Decomposition.Bounded (Decomposition.aLimbs a b c d))
    (inputs : limbValues place env.toEnvironment word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F)])
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((bigSigma0Region word).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment ((bigSigma0Region word).operations self) := by
  simp only [bigSigma0Region, scopy, circuit_norm, activation_bigSigma0, true_and] at witnesses
  obtain ⟨h₀, h₁, h₂, h₃, parity⟩ := witnesses
  have sumEquation := spread111110_sum (place := place) (self := self) (env := env) false 0 _ parity
  have complete := spread111110_complete (place := place) (self := self) (env := env)
    table false 0 _ parity
  have copied : bigSigma0Inputs env.toEnvironment (place self+1:Nat) = limbValues place env.toEnvironment word := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa [bigSigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, circuit_norm] using h₀
    · simpa [bigSigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, circuit_norm] using h₁
    · simpa [bigSigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, circuit_norm] using h₂
    · simpa [bigSigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, circuit_norm] using h₃
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 7 1) := by
    apply bigSigma0_equation_complete
    rw [copied]
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      bigSigma0_witness_eval word ⟨place,env⟩ a b c d bounded inputs] using sumEquation.symm
  simp only [bigSigma0Region, scopy, circuit_norm, true_and]
  exact ⟨gate, h₀, h₁, h₂, h₃, complete⟩

theorem bigSigma0_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word) (cache : Cache)
    (a b c d : Nat) (bounded : Decomposition.Bounded (Decomposition.aLimbs a b c d))
    (inputs : limbValues place env.toEnvironment word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F)])
    (witnesses : ExtendsWitnesses place env
      (((WitnessCircuit.bigSigma0 word).run cache).operations self) self) :
    Constraints place env.toEnvironment (((WitnessCircuit.bigSigma0 word).run cache).operations self) self ∧
      ((((WitnessCircuit.bigSigma0 word).run cache).output self).1.eval place env.toEnvironment).val =
        Specs.SHA256.upperSigma0 (Decomposition.pack (Decomposition.aLimbs a b c d)) := by
  have complete : Constraints place env.toEnvironment
      (((WitnessCircuit.bigSigma0 word).run cache).operations self) self := by
    rw [bigSigma0_source] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    exact bigSigma0Region_complete table word a b c d bounded inputs witnesses
  exact ⟨complete, bigSigma0_sound table word cache a b c d bounded inputs complete⟩

theorem bigSigma1_equation_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (equation : weightedField Witness.bigSigma1Recipe (bigSigma1Inputs env (place self+row:Nat)) =
      parityPlane env (place self+row:Nat) 1 + 2*parityPlane env (place self+row:Nat) 3) :
    RegionOperations.Constraints place self env (activation 8 row) := by
  rw [activation_bigSigma1]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, bigSigma1Gate, bigSigma1Spec,
    Midnight.Keygen.GateSpec.toClean, pow4ip, pow2ip, sumExpr,
    clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [weightedField, Witness.bigSigma1Recipe, bigSigma1Inputs,
    Gates.read, parityPlane, Synthesis.shaAdvice] at equation
  linear_combination (norm := ring_nf) equation

theorem bigSigma1_witness_eval (word : Word) (env : Placed ProverEnvironment F)
    (a b c d e : Nat) (bounded : Decomposition.Bounded (Decomposition.eLimbs a b c d e))
    (inputs : limbValues env.place env.env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F)]) :
    (((WitnessIR.weighted Witness.bigSigma1Recipe
      (Vector.ofFn fun i:Fin 5 => WitnessIR.readNat word.limbs[i.val]!)).eval {env}).toNat : F) =
      weightedField Witness.bigSigma1Recipe (limbValues env.place env.env.toEnvironment word) := by
  have small (bits value : Nat) (member : (bits,value) ∈ Decomposition.eLimbs a b c d e)
      (width : bits ≤ 32) : value < 2^32 :=
    (bounded _ member).trans_le (Nat.pow_le_pow_right (by decide) width)
  have ha := small 7 a (by simp [Decomposition.eLimbs]) (by decide)
  have hb := small 12 b (by simp [Decomposition.eLimbs]) (by decide)
  have hc := small 2 c (by simp [Decomposition.eLimbs]) (by decide)
  have hd := small 5 d (by simp [Decomposition.eLimbs]) (by decide)
  have he := small 6 e (by simp [Decomposition.eLimbs]) (by decide)
  have hlimbs : ∀ i : Fin 5, (word.limbs[i.val]!.eval env.place env.env.toEnvironment).val < 2 ^ 64 := by
    intro i
    have hi := congrArg (fun v => v[i.val]) inputs
    simp only [limbValues, Vector.getElem_ofFn] at hi
    rw [hi]
    fin_cases i
    · simpa [spread_cast_val ha] using spread_lt ha
    · simpa [spread_cast_val hb] using spread_lt hb
    · simpa [spread_cast_val hc] using spread_lt hc
    · simpa [spread_cast_val hd] using spread_lt hd
    · simpa [spread_cast_val he] using spread_lt he
  apply weighted_eval_cast _ _ _ hlimbs
  rw [inputs]
  have vals : (#v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F)]).map ZMod.val = #v[spread a, spread b, spread c, spread d, spread e] := by
    ext i hi
    interval_cases i <;> simp [spread_cast_val ha, spread_cast_val hb, spread_cast_val hc, spread_cast_val hd, spread_cast_val he]
  rw [vals]
  change Witness.spreadedBigSigma1 _ < _
  rw [Rotations.bigSigma1_recipe a b c d e bounded]
  have packedBound : Decomposition.pack (Decomposition.eLimbs a b c d e) < 2^32 := by
    simpa [Decomposition.width, Decomposition.eLimbs] using Decomposition.pack_lt _ bounded
  exact three_spreads_lt_u64 (Rotations.rotRight32_lt packedBound 6)
    (Rotations.rotRight32_lt packedBound 11)
    (Rotations.rotRight32_lt packedBound 25)

theorem bigSigma1Region_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word)
    (a b c d e : Nat) (bounded : Decomposition.Bounded (Decomposition.eLimbs a b c d e))
    (inputs : limbValues place env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F)])
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((bigSigma1Region word).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment ((bigSigma1Region word).operations self) := by
  simp only [bigSigma1Region, scopy, circuit_norm, activation_bigSigma1, true_and] at witnesses
  obtain ⟨h0, h1, h2, h3, h4, parity⟩ := witnesses
  have sumEquation := spread111110_sum (place := place) (self := self) (env := env) false 0 _ parity
  have complete := spread111110_complete (place := place) (self := self) (env := env)
    table false 0 _ parity
  have copied : bigSigma1Inputs env.toEnvironment (place self+1:Nat) = limbValues place env.toEnvironment word := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa [bigSigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h0
    · simpa [bigSigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h1
    · simpa [bigSigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h2
    · simpa [bigSigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h3
    · simpa [bigSigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h4
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 8 1) := by
    apply bigSigma1_equation_complete
    rw [copied]
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      bigSigma1_witness_eval word ⟨place,env⟩ a b c d e bounded inputs] using sumEquation.symm
  simp only [bigSigma1Region, scopy, circuit_norm, true_and]
  exact ⟨gate, h0, h1, h2, h3, h4, complete⟩

theorem bigSigma1_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word) (cache : Cache)
    (a b c d e : Nat) (bounded : Decomposition.Bounded (Decomposition.eLimbs a b c d e))
    (inputs : limbValues place env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F)])
    (witnesses : ExtendsWitnesses place env
      (((WitnessCircuit.bigSigma1 word).run cache).operations self) self) :
    Constraints place env.toEnvironment (((WitnessCircuit.bigSigma1 word).run cache).operations self) self ∧
      ((((WitnessCircuit.bigSigma1 word).run cache).output self).1.eval place env.toEnvironment).val =
        Specs.SHA256.upperSigma1 (Decomposition.pack (Decomposition.eLimbs a b c d e)) := by
  have complete : Constraints place env.toEnvironment
      (((WitnessCircuit.bigSigma1 word).run cache).operations self) self := by
    rw [bigSigma1_source] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    exact bigSigma1Region_complete table word a b c d e bounded inputs witnesses
  exact ⟨complete, bigSigma1_sound table word cache a b c d e bounded inputs complete⟩

theorem sigma0_equation_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (equation : weightedField Witness.sigma0Recipe (sigma0Inputs env (place self+row:Nat)) =
      parityPlane env (place self+row:Nat) 1 + 2*parityPlane env (place self+row:Nat) 3) :
    RegionOperations.Constraints place self env (activation 9 row) := by
  rw [activation_sigma0]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, sigma0Gate, sigma0Spec,
    Midnight.Keygen.GateSpec.toClean, pow4ip, pow2ip, sumExpr,
    clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [weightedField, Witness.sigma0Recipe, sigma0Inputs,
    Gates.read, parityPlane, Synthesis.shaAdvice] at equation
  linear_combination (norm := ring_nf) equation

theorem sigma0_witness_eval (word : Word) (env : Placed ProverEnvironment F)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues env.place env.env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)]) :
    (((WitnessIR.weighted Witness.sigma0Recipe
      (Vector.ofFn fun i:Fin 8 => WitnessIR.readNat word.limbs[i.val]!)).eval {env}).toNat : F) =
      weightedField Witness.sigma0Recipe (limbValues env.place env.env.toEnvironment word) := by
  have small (bits value : Nat) (member : (bits,value) ∈ Decomposition.messageLimbs a b c d e f g h)
      (width : bits ≤ 32) : value < 2^32 :=
    (bounded _ member).trans_le (Nat.pow_le_pow_right (by decide) width)
  have ha := small 12 a (by simp [Decomposition.messageLimbs]) (by decide)
  have hb := small 1 b (by simp [Decomposition.messageLimbs]) (by decide)
  have hc := small 1 c (by simp [Decomposition.messageLimbs]) (by decide)
  have hd := small 1 d (by simp [Decomposition.messageLimbs]) (by decide)
  have he := small 7 e (by simp [Decomposition.messageLimbs]) (by decide)
  have hf := small 3 f (by simp [Decomposition.messageLimbs]) (by decide)
  have hg := small 4 g (by simp [Decomposition.messageLimbs]) (by decide)
  have hh := small 3 h (by simp [Decomposition.messageLimbs]) (by decide)
  have hlimbs : ∀ i : Fin 8, (word.limbs[i.val]!.eval env.place env.env.toEnvironment).val < 2 ^ 64 := by
    intro i
    have hi := congrArg (fun v => v[i.val]) inputs
    simp only [limbValues, Vector.getElem_ofFn] at hi
    rw [hi]
    fin_cases i
    · simpa [spread_cast_val ha] using spread_lt ha
    · simpa [spread_cast_val hb] using spread_lt hb
    · simpa [spread_cast_val hc] using spread_lt hc
    · simpa [spread_cast_val hd] using spread_lt hd
    · simpa [spread_cast_val he] using spread_lt he
    · simpa [spread_cast_val hf] using spread_lt hf
    · simpa [spread_cast_val hg] using spread_lt hg
    · simpa [spread_cast_val hh] using spread_lt hh
  apply weighted_eval_cast _ _ _ hlimbs
  rw [inputs]
  have vals : (#v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)]).map ZMod.val = #v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h] := by
    ext i hi
    interval_cases i <;> simp [spread_cast_val ha, spread_cast_val hb, spread_cast_val hc, spread_cast_val hd, spread_cast_val he, spread_cast_val hf, spread_cast_val hg, spread_cast_val hh]
  rw [vals]
  change Witness.spreadedSigma0 _ < _
  rw [Rotations.sigma0_recipe a b c d e f g h bounded]
  have packedBound : Decomposition.pack (Decomposition.messageLimbs a b c d e f g h) < 2^32 := by
    simpa [Decomposition.width, Decomposition.messageLimbs] using Decomposition.pack_lt _ bounded
  exact three_spreads_lt_u64 (Nat.div_le_self _ _ |>.trans_lt packedBound)
    (Rotations.rotRight32_lt packedBound 7)
    (Rotations.rotRight32_lt packedBound 18)

theorem sigma0Region_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((sigma0Region word).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment ((sigma0Region word).operations self) := by
  simp only [sigma0Region, scopy, circuit_norm, activation_sigma0, true_and] at witnesses
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, parity⟩ := witnesses
  have sumEquation := spread111110_sum (place := place) (self := self) (env := env) false 0 _ parity
  have complete := spread111110_complete (place := place) (self := self) (env := env)
    table false 0 _ parity
  have copied : sigma0Inputs env.toEnvironment (place self+1:Nat) = limbValues place env.toEnvironment word := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h0
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h1
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h2
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h3
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h4
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h5
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h6
    · simpa [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h7
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 9 1) := by
    apply sigma0_equation_complete
    rw [copied]
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      sigma0_witness_eval word ⟨place,env⟩ a b c d e f g h bounded inputs] using sumEquation.symm
  simp only [sigma0Region, scopy, circuit_norm, true_and]
  exact ⟨gate, h0, h1, h2, h3, h4, h5, h6, h7, complete⟩

theorem sigma0_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word) (cache : Cache)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (witnesses : ExtendsWitnesses place env
      (((WitnessCircuit.sigma0 word).run cache).operations self) self) :
    Constraints place env.toEnvironment (((WitnessCircuit.sigma0 word).run cache).operations self) self ∧
      ((((WitnessCircuit.sigma0 word).run cache).output self).1.eval place env.toEnvironment).val =
        Specs.SHA256.lowerSigma0 (Decomposition.pack (Decomposition.messageLimbs a b c d e f g h)) := by
  have complete : Constraints place env.toEnvironment
      (((WitnessCircuit.sigma0 word).run cache).operations self) self := by
    rw [sigma0_source] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    exact sigma0Region_complete table word a b c d e f g h bounded inputs witnesses
  exact ⟨complete, sigma0_sound table word cache a b c d e f g h bounded inputs complete⟩

theorem sigma1_equation_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (equation : weightedField Witness.sigma1Recipe (sigma1Inputs env (place self+row:Nat)) =
      parityPlane env (place self+row:Nat) 1 + 2*parityPlane env (place self+row:Nat) 3) :
    RegionOperations.Constraints place self env (activation 10 row) := by
  rw [activation_sigma1]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, sigma1Gate, sigma1Spec,
    Midnight.Keygen.GateSpec.toClean, pow4ip, pow2ip, sumExpr,
    clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [weightedField, Witness.sigma1Recipe, sigma1Inputs,
    Gates.read, parityPlane, Synthesis.shaAdvice] at equation
  linear_combination (norm := ring_nf) equation

theorem sigma1_witness_eval (word : Word) (env : Placed ProverEnvironment F)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues env.place env.env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)]) :
    (((WitnessIR.weighted Witness.sigma1Recipe
      (Vector.ofFn fun i:Fin 8 => WitnessIR.readNat word.limbs[i.val]!)).eval {env}).toNat : F) =
      weightedField Witness.sigma1Recipe (limbValues env.place env.env.toEnvironment word) := by
  have small (bits value : Nat) (member : (bits,value) ∈ Decomposition.messageLimbs a b c d e f g h)
      (width : bits ≤ 32) : value < 2^32 :=
    (bounded _ member).trans_le (Nat.pow_le_pow_right (by decide) width)
  have ha := small 12 a (by simp [Decomposition.messageLimbs]) (by decide)
  have hb := small 1 b (by simp [Decomposition.messageLimbs]) (by decide)
  have hc := small 1 c (by simp [Decomposition.messageLimbs]) (by decide)
  have hd := small 1 d (by simp [Decomposition.messageLimbs]) (by decide)
  have he := small 7 e (by simp [Decomposition.messageLimbs]) (by decide)
  have hf := small 3 f (by simp [Decomposition.messageLimbs]) (by decide)
  have hg := small 4 g (by simp [Decomposition.messageLimbs]) (by decide)
  have hh := small 3 h (by simp [Decomposition.messageLimbs]) (by decide)
  have hlimbs : ∀ i : Fin 8, (word.limbs[i.val]!.eval env.place env.env.toEnvironment).val < 2 ^ 64 := by
    intro i
    have hi := congrArg (fun v => v[i.val]) inputs
    simp only [limbValues, Vector.getElem_ofFn] at hi
    rw [hi]
    fin_cases i
    · simpa [spread_cast_val ha] using spread_lt ha
    · simpa [spread_cast_val hb] using spread_lt hb
    · simpa [spread_cast_val hc] using spread_lt hc
    · simpa [spread_cast_val hd] using spread_lt hd
    · simpa [spread_cast_val he] using spread_lt he
    · simpa [spread_cast_val hf] using spread_lt hf
    · simpa [spread_cast_val hg] using spread_lt hg
    · simpa [spread_cast_val hh] using spread_lt hh
  apply weighted_eval_cast _ _ _ hlimbs
  rw [inputs]
  have vals : (#v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)]).map ZMod.val = #v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h] := by
    ext i hi
    interval_cases i <;> simp [spread_cast_val ha, spread_cast_val hb, spread_cast_val hc, spread_cast_val hd, spread_cast_val he, spread_cast_val hf, spread_cast_val hg, spread_cast_val hh]
  rw [vals]
  change Witness.spreadedSigma1 _ < _
  rw [Rotations.sigma1_recipe a b c d e f g h bounded]
  have packedBound : Decomposition.pack (Decomposition.messageLimbs a b c d e f g h) < 2^32 := by
    simpa [Decomposition.width, Decomposition.messageLimbs] using Decomposition.pack_lt _ bounded
  exact three_spreads_lt_u64 (Nat.div_le_self _ _ |>.trans_lt packedBound)
    (Rotations.rotRight32_lt packedBound 17)
    (Rotations.rotRight32_lt packedBound 19)

theorem sigma1Region_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((sigma1Region word).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment ((sigma1Region word).operations self) := by
  simp only [sigma1Region, scopy, circuit_norm, activation_sigma1, true_and] at witnesses
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, parity⟩ := witnesses
  have sumEquation := spread111110_sum (place := place) (self := self) (env := env) false 0 _ parity
  have complete := spread111110_complete (place := place) (self := self) (env := env)
    table false 0 _ parity
  have copied : sigma1Inputs env.toEnvironment (place self+1:Nat) = limbValues place env.toEnvironment word := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h0
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h1
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h2
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h3
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h4
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h5
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h6
    · simpa [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc, circuit_norm] using h7
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 10 1) := by
    apply sigma1_equation_complete
    rw [copied]
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      sigma1_witness_eval word ⟨place,env⟩ a b c d e f g h bounded inputs] using sumEquation.symm
  simp only [sigma1Region, scopy, circuit_norm, true_and]
  exact ⟨gate, h0, h1, h2, h3, h4, h5, h6, h7, complete⟩

theorem sigma1_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment) (word : Word) (cache : Cache)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env.toEnvironment word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (witnesses : ExtendsWitnesses place env
      (((WitnessCircuit.sigma1 word).run cache).operations self) self) :
    Constraints place env.toEnvironment (((WitnessCircuit.sigma1 word).run cache).operations self) self ∧
      ((((WitnessCircuit.sigma1 word).run cache).output self).1.eval place env.toEnvironment).val =
        Specs.SHA256.lowerSigma1 (Decomposition.pack (Decomposition.messageLimbs a b c d e f g h)) := by
  have complete : Constraints place env.toEnvironment
      (((WitnessCircuit.sigma1 word).run cache).operations self) self := by
    rw [sigma1_source] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    exact sigma1Region_complete table word a b c d e f g h bounded inputs witnesses
  exact ⟨complete, sigma1_sound table word cache a b c d e f g h bounded inputs complete⟩

end Midnight.SHA256.Semantics.BitwiseWitness
