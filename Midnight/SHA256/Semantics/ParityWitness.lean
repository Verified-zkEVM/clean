import Midnight.SHA256.Semantics.ParityGadget
import Midnight.SHA256.Semantics.Prepare

/-! Honest witness contracts for the actual parity source operations. These
statements complement constraint soundness: witness expressions are used only
in this completeness direction. -/
namespace Midnight.SHA256.Semantics.ParityWitness
open Halo2 Gates WitnessCircuit ParityGadget

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation

private theorem clean_sum (a b : Midnight.Keygen.E) : a + b = Halo2.Expression.add a b := rfl

private theorem clean_sub (a b : Midnight.Keygen.E) :
    a - b = Halo2.Expression.add a (Halo2.Expression.mul (Halo2.Expression.const (-1)) b) := rfl

private theorem clean_mul (a b : Midnight.Keygen.E) : a * b = Halo2.Expression.mul a b := rfl

/-- Table membership for both tuples suffices for the actual selected lookup. -/
theorem activation_spread_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat} (table : SpreadTable env)
    (first : SpreadLookup (env.fixed ⟨0⟩ (place self+row:Nat))
      (env.advice ⟨6⟩ (place self+row:Nat)) (env.advice ⟨0⟩ (place self+row:Nat)))
    (second : SpreadLookup (env.fixed ⟨1⟩ (place self+row:Nat))
      (env.advice ⟨7⟩ (place self+row:Nat)) (env.advice ⟨1⟩ (place self+row:Nat))) :
    RegionOperations.Constraints place self env (activation 4 row) := by
  obtain ⟨r₀, hr₀, t₀, p₀, s₀⟩ := table.complete _ _ _ first
  obtain ⟨r₁, hr₁, t₁, p₁, s₁⟩ := table.complete _ _ _ second
  rw [activation_spread]
  simp only [RegionOperations.Constraints, RegionOperation.Constraints,
    spreadLookup0, spreadLookup1, circuit_norm, and_true]
  constructor
  · refine ⟨r₀, hr₀, ?_⟩
    simpa only [List.map_cons, List.map_nil, Expression.eval, Query.eval,
      Int.add_zero, List.cons.injEq, and_true] using ⟨t₀.symm, p₀.symm, s₀.symm⟩
  · refine ⟨r₁, hr₁, ?_⟩
    simpa only [List.map_cons, List.map_nil, Expression.eval, Query.eval,
      Int.add_zero, List.cons.injEq, and_true] using ⟨t₁.symm, p₁.symm, s₁.symm⟩

/-- Converse of the selected parity-row extraction, on its exact source AST. -/
theorem parity_equation_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (equation : (parityWord env (place self+row:Nat) 0:F) =
      Gates.read env (place self+row:Nat) 4 (-1)) :
    RegionOperations.Constraints place self env (activation 11 row) := by
  rw [activation_parity]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, parityGate, paritySpec,
    Midnight.Keygen.GateSpec.toClean, pow4ip, pow2ip, sumExpr,
    clean_sum, clean_sub, clean_mul, circuit_norm]
  rw [parityWord_cast] at equation
  norm_num [Gates.read, Synthesis.shaAdvice] at equation
  linear_combination (norm := ring_nf) equation

/-- Honest evaluation of the actual plain/spread helper, with its own fixed tag.
The spread program reads the newly assigned plain cell, as in the source. -/
theorem plainAndSpread_honest {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (width offset index : Nat) (value : U64Expr F)
    (hw : width ∈ spreadWidths)
    (bound : (value.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat < 2^width)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((plainAndSpread width offset index value).operations self)) :
    let output := (plainAndSpread width offset index value).output self
    env.fixed ⟨index⟩ (place self+offset:Nat) = (width:F) ∧
      output.plain.eval place env.toEnvironment =
        ((value.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat:F) ∧
      output.spread.eval place env.toEnvironment =
        (Witness.spread32 ((value.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat):F) := by
  simp only [plainAndSpread, circuit_norm, activation_spread, and_true, true_and] at witnesses
  obtain ⟨tag, plain, expanded⟩ := witnesses
  simp only [plainAndSpread_output, circuit_norm]
  have small : (value.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat <
      BLS12_381.scalarFieldSize := bound.trans_le
        ((Nat.pow_le_pow_right (by decide) (spreadWidth_le_twelve hw)).trans (by decide +kernel))
  have p : (AssignedCell.of self offset (⟨Synthesis.shaAdvice[2*index]!⟩ : Column .advice)).eval
      place env.toEnvironment = FiniteField.fromNat
        ((value.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat) := by
    simpa only [WitnessIR.eval_program, circuit_norm] using plain
  have e := WitnessIR.eval_spread_readNat_of_assigned value
    (AssignedCell.of self offset (⟨Synthesis.shaAdvice[2*index]!⟩ : Column .advice))
    ⟨place, env⟩ p small
  rw [e] at expanded
  exact ⟨tag, p, expanded⟩

/-- Complete one real batched lookup row after both source tuples have been
assigned honestly. A helper alone never assumes the other tuple is valid. -/
theorem lookup_row_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (offset width₀ width₁ : Nat) (value₀ value₁ : U64Expr F)
    (hw₀ : width₀ ∈ spreadWidths) (hw₁ : width₁ ∈ spreadWidths)
    (bound₀ : (value₀.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat < 2^width₀)
    (bound₁ : (value₁.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat < 2^width₁)
    (witness₀ : RegionOperations.ExtendsWitnesses place self env
      ((plainAndSpread width₀ offset 0 value₀).operations self))
    (witness₁ : RegionOperations.ExtendsWitnesses place self env
      ((plainAndSpread width₁ offset 1 value₁).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment (activation 4 offset) := by
  have h₀ := plainAndSpread_honest (place := place) (self := self) (env := env)
    width₀ offset 0 value₀ hw₀ bound₀ witness₀
  have h₁ := plainAndSpread_honest (place := place) (self := self) (env := env)
    width₁ offset 1 value₁ hw₁ bound₁ witness₁
  norm_num [plainAndSpread_output, Synthesis.shaAdvice, circuit_norm] at h₀ h₁
  apply activation_spread_complete (place := place) (self := self) (env := env.toEnvironment) table
  · simp only [Nat.cast_add]
    rw [h₀.1, h₀.2.1, h₀.2.2]
    exact Prepare.honest_spread_lookup _ _ hw₀ bound₀
  · simp only [Nat.cast_add]
    rw [h₁.1, h₁.2.1, h₁.2.2]
    exact Prepare.honest_spread_lookup _ _ hw₁ bound₁

/-- The limb expression used at each of the six source calls always fits its
width, for arbitrary (possibly much larger) input witness expressions. -/
theorem limb_bound (value : U64Expr F) (slice : Witness.Slice)
    (env : Placed ProverEnvironment F)
    (h1 : slice.1 < 64 := by decide) (h2 : slice.2 < 64 := by decide) :
    ((WitnessIR.limb value slice).eval { env }).toNat < 2^slice.2 := by
  rw [WitnessIR.eval_limb _ _ _ h1 h2]
  exact Witness.limb_lt _ _

/-- Honest evaluation of the source's returned advice cell, before imposing
any gate or lookup semantics. -/
theorem spread111110_honest {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (odd : Bool) (offset : Nat) (value : U64Expr F)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((spread111110 odd offset value).operations self)) :
    (((spread111110 odd offset value).output self).eval place env.toEnvironment) =
      ((if odd then Witness.oddBits else Witness.evenBits)
        ((value.eval { env := (⟨place, env⟩ : Placed ProverEnvironment F) }).toNat) : F) := by
  rw [spread111110_expanded] at witnesses
  cases odd
  all_goals
    simp only [expanded, Bool.false_eq_true, ↓reduceIte, circuit_norm,
      activation_parity, and_true, true_and] at witnesses
    have returned := witnesses.2.2.2.2.2.2
    simpa only [spread111110_output, circuit_norm, Bool.false_eq_true, ↓reduceIte,
      WitnessIR.eval_program, WitnessIR.eval_evenBits, WitnessIR.eval_oddBits,
      Synthesis.shaAdvice, show (#[6,0,7,1,2,3,4,5] : Array Nat)[4]! = 2 from rfl] using returned

/-- Reconstruction of the actual source parity gate from bounded honest limbs. -/
theorem parity_reconstruction {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (offset word : Nat) (bound : word < 2^32)
    (p₀ : env.advice ⟨6⟩ (place self+offset:Nat) = (Witness.limb word (21,11):F))
    (p₁ : env.advice ⟨6⟩ (place self+(offset+1):Nat) = (Witness.limb word (10,11):F))
    (p₂ : env.advice ⟨6⟩ (place self+(offset+2):Nat) = (Witness.limb word (0,10):F))
    (output : env.advice ⟨2⟩ (place self+offset:Nat) = (word:F)) :
    RegionOperations.Constraints place self env.toEnvironment (activation 11 (offset+1)) := by
  apply parity_equation_complete (place := place) (self := self) (env := env.toEnvironment)
  rw [parityWord_cast]
  norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] at p₀ p₁ p₂ output ⊢
  change 2097152 * env.advice ⟨6⟩ _ + 1024 * env.advice ⟨6⟩ _ + env.advice ⟨6⟩ _ = env.advice ⟨2⟩ _
  rw [p₀, p₁, p₂, output]
  have packed := congrArg (fun n:Nat => (n:F)) (Prepare.pack_parity word bound)
  norm_num [Prepare.parityLimbs, Decomposition.pack_parity, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow] at packed
  exact packed

/-- The actual 11/11/10 source fragment satisfies every selected gate and both
lookup tuples when its advice and fixed assignments follow their witness programs.
No bound on the original integer expression is needed: the source parity
extractors select its low 64 bits. -/
theorem spread111110_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (odd : Bool) (offset : Nat) (value : U64Expr F)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((spread111110 odd offset value).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((spread111110 odd offset value).operations self) := by
  have returned := spread111110_honest (place := place) (self := self) (env := env)
    odd offset value witnesses
  rw [spread111110_expanded] at witnesses ⊢
  cases odd
  all_goals
    simp only [expanded, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.sub_self,
      circuit_norm, activation_parity, and_true, true_and] at witnesses
    obtain ⟨w₀, w₁, w₂, w₃, w₄, w₅, _⟩ := witnesses
    simp [WitnessIR.limbs, Witness.parityLayout] at w₀ w₁ w₂ w₃ w₄ w₅
    have b₀ := limb_bound (WitnessIR.evenBits value) (21,11) ⟨place,env⟩
    have b₁ := limb_bound (WitnessIR.evenBits value) (10,11) ⟨place,env⟩
    have b₂ := limb_bound (WitnessIR.evenBits value) (0,10) ⟨place,env⟩
    have b₃ := limb_bound (WitnessIR.oddBits value) (21,11) ⟨place,env⟩
    have b₄ := limb_bound (WitnessIR.oddBits value) (10,11) ⟨place,env⟩
    have b₅ := limb_bound (WitnessIR.oddBits value) (0,10) ⟨place,env⟩
    have h₀ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 offset _ _ (by decide +kernel) b₀ w₀
    have h₁ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 (offset+1) _ _ (by decide +kernel) b₁ w₁
    have h₂ := plainAndSpread_honest (place := place) (self := self) (env := env)
      10 (offset+2) _ _ (by decide +kernel) b₂ w₂
    have h₃ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 offset _ _ (by decide +kernel) b₃ w₃
    have h₄ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 (offset+1) _ _ (by decide +kernel) b₄ w₄
    have h₅ := plainAndSpread_honest (place := place) (self := self) (env := env)
      10 (offset+2) _ _ (by decide +kernel) b₅ w₅
    simp only [expanded, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.sub_self,
      circuit_norm, plainAndSpread_constraints, and_true]
  · have l0 := lookup_row_complete (place := place) (self := self) (env := env)
      table offset 11 11 _ _ (by decide +kernel) (by decide +kernel) b₀ b₃ w₀ w₃
    have l1 := lookup_row_complete (place := place) (self := self) (env := env)
      table (offset+1) 11 11 _ _ (by decide +kernel) (by decide +kernel) b₁ b₄ w₁ w₄
    have l2 := lookup_row_complete (place := place) (self := self) (env := env)
      table (offset+2) 10 10 _ _ (by decide +kernel) (by decide +kernel) b₂ b₅ w₂ w₅
    have gate : RegionOperations.Constraints place self env.toEnvironment (activation 11 (offset+1)) := by
      rw [WitnessIR.eval_limb _ _ _ (by decide) (by decide), WitnessIR.eval_evenBits] at h₀ h₁ h₂
      norm_num [plainAndSpread_output, spread111110_output, Synthesis.shaAdvice, circuit_norm] at h₀ h₁ h₂ returned
      exact parity_reconstruction offset _ (Witness.evenBits_lt _)
        h₀.2.1 h₁.2.1 h₂.2.1 returned
    exact ⟨gate, ⟨l0, h₀.1⟩, ⟨l1, h₁.1⟩, ⟨l2, h₂.1⟩,
      ⟨l0, h₃.1⟩, ⟨l1, h₄.1⟩, ⟨l2, h₅.1⟩⟩
  · have l0 := lookup_row_complete (place := place) (self := self) (env := env)
      table offset 11 11 _ _ (by decide +kernel) (by decide +kernel) b₃ b₀ w₃ w₀
    have l1 := lookup_row_complete (place := place) (self := self) (env := env)
      table (offset+1) 11 11 _ _ (by decide +kernel) (by decide +kernel) b₄ b₁ w₄ w₁
    have l2 := lookup_row_complete (place := place) (self := self) (env := env)
      table (offset+2) 10 10 _ _ (by decide +kernel) (by decide +kernel) b₅ b₂ w₅ w₂
    have gate : RegionOperations.Constraints place self env.toEnvironment (activation 11 (offset+1)) := by
      rw [WitnessIR.eval_limb _ _ _ (by decide) (by decide), WitnessIR.eval_oddBits] at h₃ h₄ h₅
      norm_num [plainAndSpread_output, spread111110_output, Synthesis.shaAdvice, circuit_norm] at h₃ h₄ h₅ returned
      exact parity_reconstruction offset _ (Witness.oddBits_lt _)
        h₃.2.1 h₄.2.1 h₅.2.1 returned
    exact ⟨gate, ⟨l0, h₀.1⟩, ⟨l1, h₁.1⟩, ⟨l2, h₂.1⟩,
      ⟨l0, h₃.1⟩, ⟨l1, h₄.1⟩, ⟨l2, h₅.1⟩⟩

/-- Three honest spread limbs give the spread encoding of their bounded word. -/
theorem plane_of_honest_limbs (env : Environment F) (absolute : Int) (column : Fin 8)
    (word : Nat) (bound : word < 2^32)
    (h₀ : Gates.read env absolute column (-1) = (Witness.spread32 (Witness.limb word (21,11)):F))
    (h₁ : Gates.read env absolute column 0 = (Witness.spread32 (Witness.limb word (10,11)):F))
    (h₂ : Gates.read env absolute column 1 = (Witness.spread32 (Witness.limb word (0,10)):F)) :
    parityPlane env absolute column = (spread word:F) := by
  have limbSmall (slice : Witness.Slice) (hs : slice.2 ≤ 32) : Witness.limb word slice < 2^32 :=
    (Witness.limb_lt _ _).trans_le (Nat.pow_le_pow_right (by decide) hs)
  rw [Witness.spread32_eq_spread _ (limbSmall (21,11) (by decide))] at h₀
  rw [Witness.spread32_eq_spread _ (limbSmall (10,11) (by decide))] at h₁
  rw [Witness.spread32_eq_spread _ (limbSmall (0,10) (by decide))] at h₂
  unfold parityPlane
  rw [h₀, h₁, h₂]
  have packed := congrArg (fun n:Nat => (n:F))
    (Decomposition.spread_pack (Prepare.parityLimbs word) (Prepare.parity_bounded word))
  rw [Prepare.pack_parity word bound] at packed
  norm_num [Prepare.parityLimbs, Decomposition.packSpread, Decomposition.parityLimbs,
    Decomposition.width] at packed ⊢
  linear_combination (norm := ring_nf) -packed

/-- Both actual output planes reflect the source's integer parity extractors.
This is a witness theorem, separate from the adversarial constraint soundness. -/
theorem spread111110_planes {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (odd : Bool) (offset : Nat) (value : U64Expr F)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((spread111110 odd offset value).operations self)) :
    parityPlane env.toEnvironment (place self+(offset+1):Nat) (if odd then 3 else 1) =
      (spread (Witness.evenBits ((value.eval {env := (⟨place,env⟩:Placed ProverEnvironment F)}).toNat)):F) ∧
    parityPlane env.toEnvironment (place self+(offset+1):Nat) (if odd then 1 else 3) =
      (spread (Witness.oddBits ((value.eval {env := (⟨place,env⟩:Placed ProverEnvironment F)}).toNat)):F) := by
  rw [spread111110_expanded] at witnesses
  cases odd
  all_goals
    simp only [expanded, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.sub_self,
      circuit_norm, activation_parity, and_true, true_and] at witnesses
    obtain ⟨w₀, w₁, w₂, w₃, w₄, w₅, _⟩ := witnesses
    simp [WitnessIR.limbs, Witness.parityLayout] at w₀ w₁ w₂ w₃ w₄ w₅
    have h₀ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 offset _ _ (by decide +kernel) (limb_bound _ (21,11) ⟨place,env⟩) w₀
    have h₁ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 (offset+1) _ _ (by decide +kernel) (limb_bound _ (10,11) ⟨place,env⟩) w₁
    have h₂ := plainAndSpread_honest (place := place) (self := self) (env := env)
      10 (offset+2) _ _ (by decide +kernel) (limb_bound _ (0,10) ⟨place,env⟩) w₂
    have h₃ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 offset _ _ (by decide +kernel) (limb_bound _ (21,11) ⟨place,env⟩) w₃
    have h₄ := plainAndSpread_honest (place := place) (self := self) (env := env)
      11 (offset+1) _ _ (by decide +kernel) (limb_bound _ (10,11) ⟨place,env⟩) w₄
    have h₅ := plainAndSpread_honest (place := place) (self := self) (env := env)
      10 (offset+2) _ _ (by decide +kernel) (limb_bound _ (0,10) ⟨place,env⟩) w₅
    rw [WitnessIR.eval_limb _ _ _ (by decide) (by decide), WitnessIR.eval_evenBits] at h₀ h₁ h₂
    rw [WitnessIR.eval_limb _ _ _ (by decide) (by decide), WitnessIR.eval_oddBits] at h₃ h₄ h₅
    norm_num [plainAndSpread_output, Synthesis.shaAdvice, circuit_norm] at h₀ h₁ h₂ h₃ h₄ h₅
    constructor
    · apply plane_of_honest_limbs _ _ _ _ (Witness.evenBits_lt _)
      all_goals norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
      · exact h₀.2.2
      · exact h₁.2.2
      · exact h₂.2.2
    · apply plane_of_honest_limbs _ _ _ _ (Witness.oddBits_lt _)
      all_goals norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
      · exact h₃.2.2
      · exact h₄.2.2
      · exact h₅.2.2

/-- On a 64-bit input sum, the actual parity witness planes reconstruct that
sum exactly in the field; this discharges Maj/Sigma/half-Ch gate completeness. -/
theorem spread111110_sum {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (odd : Bool) (offset : Nat) (value : U64Expr F)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((spread111110 odd offset value).operations self)) :
    parityPlane env.toEnvironment (place self+(offset+1):Nat) (if odd then 3 else 1) +
      2 * parityPlane env.toEnvironment (place self+(offset+1):Nat) (if odd then 1 else 3) =
      ((value.eval {env := (⟨place,env⟩:Placed ProverEnvironment F)}).toNat:F) := by
  obtain ⟨he, ho⟩ := spread111110_planes (place := place) (self := self) (env := env)
    odd offset value witnesses
  rw [he, ho]
  have exactSum := congrArg (fun n:Nat => (n:F))
    (Witness.interleave_even_odd _
      (UInt64.toNat_lt (value.eval {env := (⟨place,env⟩:Placed ProverEnvironment F)})))
  simpa only [interleave, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using exactSum

end Midnight.SHA256.Semantics.ParityWitness
