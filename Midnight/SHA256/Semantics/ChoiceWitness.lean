import Midnight.SHA256.Semantics.BitwiseWitness

/-! Honest completeness of both actual half-Ch gates and the source cache-aware
choice helper. The negated-spread program is proved to encode finite complement. -/
namespace Midnight.SHA256.Semantics.ChoiceWitness
open Halo2 Gates WitnessCircuit ParityGadget ParityWitness BitwiseWitness ChoiceGadget

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation

private theorem clean_sum (a b : Midnight.Keygen.E) : a + b = Halo2.Expression.add a b := rfl

private theorem clean_sub (a b : Midnight.Keygen.E) :
    a - b = Halo2.Expression.add a (Halo2.Expression.mul (Halo2.Expression.const (-1)) b) := rfl

private theorem clean_mul (a b : Midnight.Keygen.E) : a * b = Halo2.Expression.mul a b := rfl

theorem spread_xor (a b : Nat) : spread (a ^^^ b) = spread a ^^^ spread b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi : i = 2*(i/2)+i%2 := by omega
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · rw [hi, he, Nat.add_zero]
    simp only [Nat.testBit_xor, spread_testBit_even]
  · rw [hi, ho]
    simp only [Nat.testBit_xor, spread_testBit_odd, Bool.xor_false]

theorem negateSpread_spread (word : Nat) :
    Witness.negateSpread (spread word) = spread (complement 32 word) := by
  rw [Witness.negateSpread, Witness.evenMask, ← spread_mask32, ← spread_xor]
  rfl

theorem two_spreads_lt_u64 {a b : Nat} (ha : a < 2^32) (hb : b < 2^32) :
    spread a + spread b < 2^64 := by
  simpa only [spread_zero, Nat.add_zero] using three_spreads_lt_u64 ha hb (by decide : 0 < 2^32)

theorem halfCh_equations_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (equations :
      (Gates.read env (place self+row:Nat) 5 (-1) + Gates.read env (place self+row:Nat) 6 (-1) =
        parityPlane env (place self+row:Nat) 3 + 2*parityPlane env (place self+row:Nat) 1) ∧
      (Gates.read env (place self+row:Nat) 4 0 + Gates.read env (place self+row:Nat) 5 0 =
        Gates.read env (place self+row:Nat) 6 0)) :
    RegionOperations.Constraints place self env (activation 6 row) := by
  rw [activation_halfCh]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, halfChGate, halfChSpec,
    Midnight.Keygen.GateSpec.toClean, pow4ip, pow2ip, sumExpr,
    clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [Gates.read, parityPlane, Synthesis.shaAdvice] at equations
  constructor
  · linear_combination (norm := ring_nf) equations.1
  · linear_combination (norm := ring_nf) equations.2

theorem choiceRegion_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (mask e f g : AssignedCell F) (x y z : Nat)
    (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (maskValue : mask.eval place env.toEnvironment = (0x5555555555555555:F))
    (ex : e.eval place env.toEnvironment = (spread x:F))
    (fy : f.eval place env.toEnvironment = (spread y:F))
    (gz : g.eval place env.toEnvironment = (spread z:F))
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((choiceRegion mask e f g).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((choiceRegion mask e f g).operations self) := by
  simp only [choiceRegion, scopy, circuit_norm, activation_halfCh, true_and] at witnesses
  obtain ⟨ec₁, ec₂, fc, gc, ne, nc, mc, parity₁, efc, parity₂, ngc, out⟩ := witnesses
  have hx64 : spread x < 2 ^ 64 := by simpa using spread_lt hx
  have hy64 : spread y < 2 ^ 64 := by simpa using spread_lt hy
  have hz64 : spread z < 2 ^ 64 := by simpa using spread_lt hz
  have hnx64 : spread (complement 32 x) < 2 ^ 64 := by simpa using spread_lt (complement_lt hx)
  have hcol5 : Synthesis.shaAdvice[5]! = 3 := rfl
  have negated : env.advice ⟨3⟩ (place self+3:Nat) = (spread (complement 32 x):F) := by
    rw [WitnessIR.eval_program, WitnessIR.eval_negateSpread, WitnessIR.eval_readNat,
      Halo2.WitgenEnv.readVar_halo2, ex, spread_cast_val hx, Nat.mod_eq_of_lt hx64,
      negateSpread_spread] at ne
    simpa [Synthesis.shaAdvice] using ne
  have negated' := negated
  simp only [Nat.cast_add, Nat.cast_ofNat] at negated'
  have eval₁ : ((Witgen.U64ExprOver.add (WitnessIR.readNat e) (WitnessIR.readNat f)).eval
      {env := (⟨place,env⟩:Placed ProverEnvironment F)}).toNat = spread x + spread y := by
    have hxy := two_spreads_lt_u64 hx hy
    simp only [Witgen.U64ExprOver.eval, UInt64.toNat_add, WitnessIR.eval_readNat,
      Halo2.WitgenEnv.readVar_halo2, ex, fy, spread_cast_val hx, spread_cast_val hy]
    rw [Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hy64, Nat.mod_eq_of_lt hxy]
  have eval₂ : ((Witgen.U64ExprOver.add
      (WitnessIR.readNat (.of self 3 (⟨Synthesis.shaAdvice[5]!⟩:Column .advice)))
      (WitnessIR.readNat g)).eval {env := (⟨place,env⟩:Placed ProverEnvironment F)}).toNat =
      spread (complement 32 x) + spread z := by
    have hxz := two_spreads_lt_u64 (complement_lt hx) hz
    simp only [Witgen.U64ExprOver.eval, UInt64.toNat_add, WitnessIR.eval_readNat,
      Halo2.WitgenEnv.readVar_halo2, circuit_norm, hcol5, negated, gz,
      spread_cast_val (complement_lt hx), spread_cast_val hz]
  have sum₁ := spread111110_sum (place := place) (self := self) (env := env) true 0 _ parity₁
  have sum₂ := spread111110_sum (place := place) (self := self) (env := env) true 3 _ parity₂
  have efHonest := spread111110_honest (place := place) (self := self) (env := env) true 0 _ parity₁
  have ngHonest := spread111110_honest (place := place) (self := self) (env := env) true 3 _ parity₂
  have pc₁ := spread111110_complete (place := place) (self := self) (env := env) table true 0 _ parity₁
  have pc₂ := spread111110_complete (place := place) (self := self) (env := env) table true 3 _ parity₂
  have gate₁ : RegionOperations.Constraints place self env.toEnvironment (activation 6 1) := by
    apply halfCh_equations_complete
    constructor
    · norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
      norm_num [Synthesis.shaAdvice, circuit_norm] at ec₁ fc
      rw [ec₁, fc, ex, fy]
      rw [eval₁] at sum₁
      simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, ↓reduceIte] using sum₁.symm
    · norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
      norm_num [Synthesis.shaAdvice, circuit_norm] at efc ngc
      rw [efc, ngc]
      have hcol6 : Synthesis.shaAdvice[6]! = 4 := rfl
      simp only [spread111110_output, circuit_norm, ↓reduceIte, Nat.add_zero] at efHonest ngHonest
      have hefVal : (env.advice ⟨2⟩ (place self : Nat)).val < 2 ^ 32 := by
        rw [efHonest, ZMod.val_natCast_of_lt ((Witness.oddBits_lt _).trans (by decide +kernel : 2 ^ 32 < BLS12_381.scalarFieldSize))]
        exact Witness.oddBits_lt _
      have hngVal : (env.advice ⟨2⟩ (place self + 3 : Nat)).val < 2 ^ 32 := by
        rw [ngHonest, ZMod.val_natCast_of_lt ((Witness.oddBits_lt _).trans (by decide +kernel : 2 ^ 32 < BLS12_381.scalarFieldSize))]
        exact Witness.oddBits_lt _
      have hout : env.advice ⟨4⟩ (place self + 1 : Nat) =
          env.advice ⟨2⟩ (place self : Nat) + env.advice ⟨2⟩ (place self + 3 : Nat) := by
        rw [WitnessIR.eval_program] at out
        simp only [Witgen.U64ExprOver.eval, UInt64.toNat_add, WitnessIR.eval_readNat,
          Halo2.WitgenEnv.readVar_halo2, circuit_norm, hcol6, Nat.add_zero] at out
        simpa only [FiniteField.fromNat, Nat.cast_add, ZMod.natCast_zmod_val] using out
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hout.symm
  have gate₂ : RegionOperations.Constraints place self env.toEnvironment (activation 6 4) := by
    apply halfCh_equations_complete
    constructor
    · norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
      norm_num [Synthesis.shaAdvice, circuit_norm] at gc
      rw [gc, negated', gz]
      rw [eval₂] at sum₂
      have h31 : ((place self + (3 + 1) : Nat) : Int) = (place self : Int) + 4 := by omega
      simpa only [Nat.cast_add, h31, ↓reduceIte] using sum₂.symm
    · norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
      norm_num [Synthesis.shaAdvice, circuit_norm] at ec₂ nc mc
      rw [ec₂, nc, mc, ex, maskValue]
      have ng : env.advice ⟨3⟩ (↑(place self)+3) = (spread (complement 32 x):F) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using negated
      rw [ng]
      have complementEquation := congrArg (fun n:Nat => (n:F)) (spread_complement hx)
      rw [spread_mask32] at complementEquation
      simpa only [Nat.cast_add, Nat.cast_ofNat] using complementEquation
  simp only [choiceRegion, scopy, circuit_norm, true_and, and_true]
  exact ⟨gate₁, gate₂, ec₁, ec₂, fc, gc, nc, mc, pc₁, efc, pc₂, ngc⟩

/-- Honest original source execution, including its real mask cache branch. -/
theorem choice_complete (e f g : AssignedCell F) (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) (table : SpreadTable env.env.toEnvironment)
    (cacheValid : Linear.CacheMeaning env.toEnvironment cache)
    (x y z : Nat) (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (ex : e.eval env.place env.env.toEnvironment = (spread x:F))
    (fy : f.eval env.place env.env.toEnvironment = (spread y:F))
    (gz : g.eval env.place env.env.toEnvironment = (spread z:F))
    (witnesses : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.choice e f g).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment (((WitnessCircuit.choice e f g).run cache).operations self) self ∧
      (let output := ((WitnessCircuit.choice e f g).run cache).output self
       (output.1.eval env.place env.env.toEnvironment).val = Specs.SHA256.Ch x y z ∧
         Linear.CacheMeaning env.toEnvironment output.2) := by
  have complete : Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.choice e f g).run cache).operations self) self := by
    rw [choice_run] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    rw [← Linear.constant_nextRegionIndex] at witnesses ⊢
    obtain ⟨wc, wr⟩ := witnesses
    have cc := Linear.constant_constraints_of_witnesses 0x5555555555555555 cache self env wc
    have maskValue := (Linear.constant_sound 0x5555555555555555 cache self env.toEnvironment cacheValid cc).1
    exact ⟨cc, choiceRegion_complete table _ e f g x y z hx hy hz maskValue ex fy gz wr⟩
  exact ⟨complete, choice_sound e f g cache self env.toEnvironment table cacheValid
    x y z hx hy hz ex fy gz complete⟩

end Midnight.SHA256.Semantics.ChoiceWitness
