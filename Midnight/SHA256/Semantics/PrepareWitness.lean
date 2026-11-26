import Midnight.SHA256.Semantics.PrepareCircuit
import Midnight.SHA256.Semantics.ParityWitness

/-! Honest-witness completeness of the native word preparation regions. -/
namespace Midnight.SHA256.Semantics.PrepareWitness
open Halo2 Gates PrepareGates PrepareCircuit WitnessCircuit WitnessPrepare ParityWitness
open Midnight.Keygen

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
set_option linter.constructorNameAsVariable false

private theorem clean_sum (a b : Midnight.Keygen.E) : a + b = Halo2.Expression.add a b := rfl

private theorem clean_sub (a b : Midnight.Keygen.E) :
    a - b = Halo2.Expression.add a (Halo2.Expression.mul (Halo2.Expression.const (-1)) b) := rfl

private theorem clean_mul (a b : Midnight.Keygen.E) : a * b = Halo2.Expression.mul a b := rfl

section GateConverses
variable {place : RegionIndex → Nat} {self : RegionIndex}
  {env : Environment F} {row : Nat}
local notation "r" => Gates.read env (place self + row : Nat)

theorem a_gate_complete
    (plain : (2 ^ 22 : F) * r 0 (-1) + 2 ^ 13 * r 2 (-1) + 2 ^ 2 * r 0 0 + r 2 0 = r 4 (-1))
    (expanded : (2 ^ 44 : F) * r 1 (-1) + 2 ^ 26 * r 3 (-1) + 2 ^ 4 * r 1 0 + r 3 0 = r 4 0) :
    RegionOperations.Constraints place self env (activation 12 row) := by
  rw [activation_a]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, aGate, aSpec,
    GateSpec.toClean, pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [Gates.read, Synthesis.shaAdvice] at plain expanded
  constructor
  · linear_combination (norm := ring_nf) plain
  · linear_combination (norm := ring_nf) expanded

theorem e_gate_complete
    (plain : (2 ^ 25 : F) * r 0 (-1) + 2 ^ 13 * r 2 (-1) + 2 ^ 11 * r 0 0 +
      2 ^ 6 * r 2 0 + r 0 1 = r 4 (-1))
    (expanded : (2 ^ 50 : F) * r 1 (-1) + 2 ^ 26 * r 3 (-1) + 2 ^ 22 * r 1 0 +
      2 ^ 12 * r 3 0 + r 1 1 = r 4 0) :
    RegionOperations.Constraints place self env (activation 13 row) := by
  rw [activation_e]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, eGate, eSpec,
    GateSpec.toClean, pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [Gates.read, Synthesis.shaAdvice] at plain expanded
  constructor
  · linear_combination (norm := ring_nf) plain
  · linear_combination (norm := ring_nf) expanded

theorem message_gate_complete
    (plain : (2 ^ 20 : F) * r 0 (-1) + 2 ^ 19 * r 7 (-1) + 2 ^ 18 * r 7 0 +
      2 ^ 17 * r 7 1 + 2 ^ 10 * r 2 (-1) + 2 ^ 7 * r 0 0 + 2 ^ 3 * r 2 0 + r 0 1 = r 4 (-1))
    (b : r 7 (-1) * (r 7 (-1) - 1) = 0)
    (c : r 7 0 * (r 7 0 - 1) = 0) (d : r 7 1 * (r 7 1 - 1) = 0) :
    RegionOperations.Constraints place self env (activation 14 row) := by
  rw [activation_message]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, messageGate, messageSpec,
    GateSpec.toClean, pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [Gates.read, Synthesis.shaAdvice] at plain b c d
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := ring_nf) plain
  · exact b
  · exact c
  · exact d

theorem addMod_gate_complete
    (equation : r 5 (-1) + r 6 (-1) + r 5 0 + r 6 0 + r 4 1 + r 5 1 + r 6 1 =
      r 4 (-1) + r 2 1 * (2 ^ 32 : F)) :
    RegionOperations.Constraints place self env (activation 15 row) := by
  rw [activation_addMod]
  norm_num [RegionOperations.Constraints, RegionOperation.Constraints, addModGate, addModSpec,
    GateSpec.toClean, pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm]
  norm_num [Gates.read, Synthesis.shaAdvice] at equation
  linear_combination (norm := ring_nf) equation

end GateConverses

theorem scopy_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (source : AssignedCell F) (index row : Nat)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((scopy source index row).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((scopy source index row).operations self) := by
  simpa only [scopy, circuit_norm, and_true, true_and, Halo2.eval_ofFExpr_zero,
    Witgen.FExprOver.eval, Halo2.WitgenEnv.readVar_halo2] using witnesses

def paddedValues (place : RegionIndex → Nat) (env : Environment F)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F) : List Nat :=
  (summands ++ Array.replicate (7 - summands.size) zero).toList.map (cellValue place env)

def summandPrograms (summands : Array (AssignedCell F)) (zero : AssignedCell F) : List (U64Expr F) :=
  (summands ++ Array.replicate (7 - summands.size) zero).toList.map WitnessIR.readNat

theorem summandPrograms_eval (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (env : Placed ProverEnvironment F)
    (zeroValue : cellValue env.place env.env.toEnvironment zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env.toEnvironment cell < 2 ^ 32) :
    (summandPrograms summands zero).map (fun expression => (expression.eval { env }).toNat) =
      paddedValues env.place env.env.toEnvironment summands zero := by
  simp only [summandPrograms, paddedValues, List.map_map, Function.comp_def,
    WitnessIR.eval_readNat, Halo2.WitgenEnv.readVar_halo2]
  apply List.map_congr_left
  intro cell hcell
  have hlt : cellValue env.place env.env.toEnvironment cell < 2 ^ 32 := by
    rw [Array.toList_append, List.mem_append] at hcell
    rcases hcell with hcell | hcell
    · exact inputs cell (Array.mem_def.mpr hcell)
    · simp only [Array.toList_replicate, List.mem_replicate] at hcell
      rw [hcell.2, zeroValue]
      decide
  exact Nat.mod_eq_of_lt (hlt.trans (by decide))

/-- The actual source remainder assignment, evaluated without any constraint
assumption. Its bound follows from modulo, so field interpretation is canonical. -/
theorem addMod_output_honest {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (zeroValue : cellValue place env.toEnvironment zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env.toEnvironment cell < 2 ^ 32)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((addMod summands zero).operations self)) :
    cellValue place env.toEnvironment ((addMod summands zero).output self) =
      Witness.sum32 (paddedValues place env.toEnvironment summands zero) := by
  rw [addMod_eq] at witnesses
  simp only [addModExpanded, circuit_norm, activation_addMod, true_and, and_true] at witnesses
  have returned := witnesses.2.2.2.2.2.2.2.2
  rw [WitnessIR.eval_program, WitnessIR.eval_sum32] at returned
  change env.advice ⟨2⟩ (place self : Nat) =
    (Witness.sum32 ((summandPrograms summands zero).map (fun expression =>
      (expression.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat)) : F) at returned
  rw [summandPrograms_eval summands zero ⟨place, env⟩ zeroValue inputs] at returned
  have small : Witness.sum32 (paddedValues place env.toEnvironment summands zero) <
      BLS12_381.scalarFieldSize := (Witness.sum32_lt _).trans (by decide +kernel)
  simpa only [cellValue, addMod_output, shaCell, circuit_norm, Synthesis.shaAdvice,
    Nat.add_zero, ZMod.val_natCast_of_lt small,
    show (#[6,0,7,1,2,3,4,5] : Array Nat)[4]! = 2 from rfl] using congrArg (fun v:F => v.val) returned

private theorem sum_lt_u64_of_le_seven {values : List Nat}
    (hcount : values.length ≤ 7) (hvalues : ∀ v ∈ values, v < Witness.wordModulus) :
    values.sum < 2 ^ 64 := by
  have hcarry := Witness.carry32_lt_eight values hcount hvalues
  have hdiv : values.sum / Witness.wordModulus < 8 := hcarry
  dsimp [Witness.wordModulus] at hdiv
  omega

/-- Completeness of the actual addition helper together with the other tuple
assigned on its last lookup row. The caller supplies that tuple's genuine
witness assignments and input bound, not an assumed lookup or gate equation. -/
theorem addMod_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7) (zeroValue : cellValue place env.toEnvironment zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env.toEnvironment cell < 2 ^ 32)
    (mateWidth : Nat) (mateValue : U64Expr F) (supported : mateWidth ∈ spreadWidths)
    (mateBound : (mateValue.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat < 2 ^ mateWidth)
    (mateWitness : RegionOperations.ExtendsWitnesses place self env
      ((plainAndSpread mateWidth 2 0 mateValue).operations self))
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((addMod summands zero).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((addMod summands zero).operations self) := by
  have output := addMod_output_honest (place := place) (self := self) (env := env)
    summands zero zeroValue inputs witnesses
  have hcount : (paddedValues place env.toEnvironment summands zero).length ≤ 7 := by
    simp only [paddedValues, List.length_map, Array.length_toList, paddedTerms_size summands zero size]
    exact Nat.le_refl 7
  have hvalues := paddedValues_bounded summands zero zeroValue inputs
  have hsumBound : ((summandPrograms summands zero).map fun expression =>
      (expression.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat).sum < 2 ^ 64 := by
    rw [summandPrograms_eval summands zero ⟨place, env⟩ zeroValue inputs]
    exact sum_lt_u64_of_le_seven hcount hvalues
  have carryBound : ((WitnessIR.carry32 (summandPrograms summands zero)).eval
      { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat < 2 ^ 3 := by
    rw [WitnessIR.eval_carry32 _ _ hsumBound, summandPrograms_eval summands zero ⟨place, env⟩ zeroValue inputs]
    exact Witness.carry32_lt_eight _ hcount hvalues
  have math := (Prepare.honest_addMod _ hcount hvalues).2.2
  rw [addMod_eq] at witnesses ⊢
  simp only [addModExpanded, circuit_norm, activation_addMod, true_and, and_true] at witnesses
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, carryWitness, _⟩ := witnesses
  have c0 := scopy_complete (place := place) (self := self) (env := env) _ 5 0 w0
  have c1 := scopy_complete (place := place) (self := self) (env := env) _ 6 0 w1
  have c2 := scopy_complete (place := place) (self := self) (env := env) _ 5 1 w2
  have c3 := scopy_complete (place := place) (self := self) (env := env) _ 6 1 w3
  have c4 := scopy_complete (place := place) (self := self) (env := env) _ 4 2 w4
  have c5 := scopy_complete (place := place) (self := self) (env := env) _ 5 2 w5
  have c6 := scopy_complete (place := place) (self := self) (env := env) _ 6 2 w6
  have carry := plainAndSpread_honest (place := place) (self := self) (env := env)
    3 2 1 _ (by decide +kernel) carryBound carryWitness
  have lookup := lookup_row_complete (place := place) (self := self) (env := env)
    table 2 mateWidth 3 _ _ supported (by decide +kernel) mateBound carryBound mateWitness carryWitness
  simp only [addModExpanded, circuit_norm, ParityGadget.plainAndSpread_constraints, and_true]
  refine ⟨?_, c0, c1, c2, c3, c4, c5, c6, lookup, carry.1⟩
  apply addMod_gate_complete (place := place) (self := self) (env := env.toEnvironment) (row := 1)
  have outputField := congrArg (fun n:Nat => (n:F)) output
  rw [WitnessIR.eval_carry32 _ _ hsumBound,
    summandPrograms_eval summands zero ⟨place, env⟩ zeroValue inputs] at carry
  norm_num [cellValue, addMod_output, shaCell, scopy, circuit_norm, Gates.read, Synthesis.shaAdvice,
    Nat.cast_add, Int.add_assoc, ParityGadget.plainAndSpread_output] at c0 c1 c2 c3 c4 c5 c6 carry outputField ⊢
  change env.advice ⟨3⟩ _ + env.advice ⟨4⟩ _ + env.advice ⟨3⟩ _ +
    env.advice ⟨4⟩ _ + env.advice ⟨2⟩ _ + env.advice ⟨3⟩ _ + env.advice ⟨4⟩ _ =
    env.advice ⟨2⟩ _ + env.advice ⟨7⟩ _ * (4294967296:F)
  rw [c0, c1, c2, c3, c4, c5, c6, outputField, carry.2.1]
  simp only [paddedValues, toList_seven _ (paddedTerms_size summands zero size),
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cellValue,
    Nat.cast_add, ZMod.natCast_zmod_val, add_zero] at math ⊢
  norm_num only [Nat.cast_ofNat] at math
  linear_combination (norm := ring_nf) math

/-- The actual limb helper assigns the mathematical spread of its bounded
integer limb. This rewrites the source spread computation once for all layouts. -/
theorem limb_honest {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (value : U64Expr F) (slice : Witness.Slice)
    (offset index : Nat) (supported : slice.2 ∈ spreadWidths)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((plainAndSpread slice.2 offset index (WitnessIR.limb value slice)).operations self))
    (h1 : slice.1 < 64 := by decide) (h2 : slice.2 < 64 := by decide) :
    let n := (value.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat
    let output := (plainAndSpread slice.2 offset index (WitnessIR.limb value slice)).output self
    env.fixed ⟨index⟩ (place self + offset : Nat) = (slice.2 : F) ∧
      output.plain.eval place env.toEnvironment = (Witness.limb n slice : F) ∧
      output.spread.eval place env.toEnvironment = (spread (Witness.limb n slice) : F) := by
  have h := plainAndSpread_honest (place := place) (self := self) (env := env)
    slice.2 offset index _ supported (limb_bound value slice ⟨place,env⟩ h1 h2) witnesses
  rw [WitnessIR.eval_limb _ _ _ h1 h2] at h
  have small : Witness.limb ((value.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat) slice < 2 ^ 32 :=
    (Witness.limb_lt _ _).trans_le
      (Nat.pow_le_pow_right (by decide) ((spreadWidth_le_twelve supported).trans (by decide)))
  rw [Witness.spread32_eq_spread _ small] at h
  exact h

theorem a_plain_field (word : Nat) (bound : word < 2 ^ 32) :
    (2 ^ 22 : F) * (Witness.limb word (22,10) : F) +
      2 ^ 13 * (Witness.limb word (13,9) : F) +
      2 ^ 2 * (Witness.limb word (2,11) : F) + (Witness.limb word (0,2) : F) = (word : F) := by
  have packed := congrArg (fun n:Nat => (n:F)) (Prepare.pack_a word bound)
  simpa only [Prepare.aLimbs, Decomposition.pack_a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat] using packed

theorem a_spread_field (word : Nat) (bound : word < 2 ^ 32) :
    (2 ^ 44 : F) * (spread (Witness.limb word (22,10)) : F) +
      2 ^ 26 * (spread (Witness.limb word (13,9)) : F) +
      2 ^ 4 * (spread (Witness.limb word (2,11)) : F) +
      (spread (Witness.limb word (0,2)) : F) = (Witness.spread32 word : F) := by
  have packed := congrArg (fun n:Nat => (n:F)) (Prepare.spread_a word bound)
  norm_num [Prepare.aLimbs, Decomposition.aLimbs, Decomposition.packSpread,
    Decomposition.width, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at packed ⊢
  linear_combination (norm := ring_nf) packed

theorem e_plain_field (word : Nat) (bound : word < 2 ^ 32) :
    (2 ^ 25 : F) * (Witness.limb word (25,7) : F) +
      2 ^ 13 * (Witness.limb word (13,12) : F) +
      2 ^ 11 * (Witness.limb word (11,2) : F) +
      2 ^ 6 * (Witness.limb word (6,5) : F) + (Witness.limb word (0,6) : F) = (word : F) := by
  have packed := congrArg (fun n:Nat => (n:F)) (Prepare.pack_e word bound)
  simpa only [Prepare.eLimbs, Decomposition.pack_e, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat] using packed

theorem e_spread_field (word : Nat) (bound : word < 2 ^ 32) :
    (2 ^ 50 : F) * (spread (Witness.limb word (25,7)) : F) +
      2 ^ 26 * (spread (Witness.limb word (13,12)) : F) +
      2 ^ 22 * (spread (Witness.limb word (11,2)) : F) +
      2 ^ 12 * (spread (Witness.limb word (6,5)) : F) +
      (spread (Witness.limb word (0,6)) : F) = (Witness.spread32 word : F) := by
  have packed := congrArg (fun n:Nat => (n:F)) (Prepare.spread_e word bound)
  norm_num [Prepare.eLimbs, Decomposition.eLimbs, Decomposition.packSpread,
    Decomposition.width, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at packed ⊢
  linear_combination (norm := ring_nf) packed

theorem message_plain_field (word : Nat) (bound : word < 2 ^ 32) :
    (2 ^ 20 : F) * (Witness.limb word (20,12) : F) +
      2 ^ 19 * (Witness.limb word (19,1) : F) +
      2 ^ 18 * (Witness.limb word (18,1) : F) +
      2 ^ 17 * (Witness.limb word (17,1) : F) +
      2 ^ 10 * (Witness.limb word (10,7) : F) +
      2 ^ 7 * (Witness.limb word (7,3) : F) +
      2 ^ 3 * (Witness.limb word (3,4) : F) + (Witness.limb word (0,3) : F) = (word : F) := by
  have packed := congrArg (fun n:Nat => (n:F)) (Prepare.pack_message word bound)
  simpa only [Prepare.messageLimbs, Decomposition.pack_message, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat] using packed

theorem one_bit_gate (word shift : Nat) :
    (Witness.limb word (shift,1) : F) * ((Witness.limb word (shift,1) : F) - 1) = 0 := by
  have bound := Witness.limb_lt word (shift,1)
  norm_num only [Nat.pow_one] at bound
  change Witness.limb word (shift,1) < 2 at bound
  have cases : Witness.limb word (shift,1) = 0 ∨ Witness.limb word (shift,1) = 1 := by omega
  rcases cases with h | h <;> simp only [h] <;> norm_num

/-- Actual A preparation satisfies all native gates, copies and both tuples of
every spread lookup row when its source witness programs are followed. -/
theorem aRegion_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7) (zeroValue : cellValue place env.toEnvironment zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env.toEnvironment cell < 2 ^ 32)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((aRegion summands zero).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((aRegion summands zero).operations self) := by
  simp only [aRegion, circuit_norm, activation_a, true_and] at witnesses
  obtain ⟨addition, expanded, limb0, limb1, limb2, limb3, limb4⟩ := witnesses
  let value := WitnessIR.readNat (shaCell self 4 0)
  let word := (value.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat
  have cellSmall : cellValue place env.toEnvironment (shaCell self 4 0) < 2 ^ 32 := by
    have h := (addMod_output_honest (place := place) (self := self) (env := env)
      summands zero zeroValue inputs addition).trans_lt (Witness.sum32_lt _)
    simpa only [cellValue, addMod_output, Witness.wordModulus] using h
  have wordEq : word = cellValue place env.toEnvironment (shaCell self 4 0) := by
    simpa only [word, value, WitnessIR.eval_readNat, Halo2.WitgenEnv.readVar_halo2, cellValue] using
      Nat.mod_eq_of_lt (cellSmall.trans (by decide))
  have wordBound : word < 2 ^ 32 := wordEq ▸ cellSmall
  have h0 := limb_honest (place := place) (self := self) (env := env)
    value (22,10) 0 0 (by decide +kernel) limb0
  have h1 := limb_honest (place := place) (self := self) (env := env)
    value (13,9) 0 1 (by decide +kernel) limb1
  have h2 := limb_honest (place := place) (self := self) (env := env)
    value (2,11) 1 0 (by decide +kernel) limb2
  have h3 := limb_honest (place := place) (self := self) (env := env)
    value (0,2) 1 1 (by decide +kernel) limb3
  have h4 := limb_honest (place := place) (self := self) (env := env)
    value (0,0) 2 0 (by decide +kernel) limb4
  have row0 := lookup_row_complete (place := place) (self := self) (env := env)
    table 0 10 9 _ _ (by decide +kernel) (by decide +kernel)
    (limb_bound value (22,10) ⟨place,env⟩) (limb_bound value (13,9) ⟨place,env⟩) limb0 limb1
  have row1 := lookup_row_complete (place := place) (self := self) (env := env)
    table 1 11 2 _ _ (by decide +kernel) (by decide +kernel)
    (limb_bound value (2,11) ⟨place,env⟩) (limb_bound value (0,2) ⟨place,env⟩) limb2 limb3
  have addConstraints := addMod_complete (place := place) (self := self) (env := env)
    table summands zero size zeroValue inputs 0 _ (by decide +kernel)
    (limb_bound value (0,0) ⟨place,env⟩) limb4 addition
  have row2 := (addMod_facts (place := place) (self := self) (env := env.toEnvironment)
    summands zero size addConstraints).2.1
  have plainField : (word:F) = env.advice ⟨2⟩ (place self : Nat) := by
    rw [wordEq]
    simp only [cellValue, shaCell, circuit_norm, Synthesis.shaAdvice, Nat.add_zero]
    rfl
  rw [WitnessIR.eval_program, WitnessIR.eval_spread32] at expanded
  change env.advice ⟨2⟩ (place self+1:Nat) = (Witness.spread32 word:F) at expanded
  norm_num [ParityGadget.plainAndSpread_output, Synthesis.shaAdvice, circuit_norm,
    Nat.cast_add] at h0 h1 h2 h3 h4 expanded plainField
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 12 1) := by
    apply a_gate_complete (place := place) (self := self) (env := env.toEnvironment) (row := 1)
    all_goals norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add]
    · change (4194304:F)*env.advice ⟨6⟩ _ + 8192*env.advice ⟨7⟩ _ +
        4*env.advice ⟨6⟩ _ + env.advice ⟨7⟩ _ = env.advice ⟨2⟩ _
      rw [h0.2.1, h1.2.1, h2.2.1, h3.2.1, ← plainField]
      exact a_plain_field word wordBound
    · change (17592186044416:F)*env.advice ⟨0⟩ _ + 67108864*env.advice ⟨1⟩ _ +
        16*env.advice ⟨0⟩ _ + env.advice ⟨1⟩ _ = env.advice ⟨2⟩ _
      rw [h0.2.2, h1.2.2, h2.2.2, h3.2.2, expanded]
      exact a_spread_field word wordBound
  simp only [aRegion, circuit_norm, ParityGadget.plainAndSpread_constraints, true_and]
  exact ⟨gate, addConstraints, ⟨row0, h0.1⟩, ⟨row0, h1.1⟩,
    ⟨row1, h2.1⟩, ⟨row1, h3.1⟩, ⟨row2, h4.1⟩⟩

/-- Actual E preparation satisfies all native gates, copies and both tuples of
every spread lookup row when its source witness programs are followed. -/
theorem eRegion_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7) (zeroValue : cellValue place env.toEnvironment zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env.toEnvironment cell < 2 ^ 32)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((eRegion summands zero).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((eRegion summands zero).operations self) := by
  simp only [eRegion, circuit_norm, activation_e, true_and] at witnesses
  obtain ⟨addition, expanded, limb0, limb1, limb2, limb3, limb4⟩ := witnesses
  let value := WitnessIR.readNat (shaCell self 4 0)
  let word := (value.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat
  have cellSmall : cellValue place env.toEnvironment (shaCell self 4 0) < 2 ^ 32 := by
    have h := (addMod_output_honest (place := place) (self := self) (env := env)
      summands zero zeroValue inputs addition).trans_lt (Witness.sum32_lt _)
    simpa only [cellValue, addMod_output, Witness.wordModulus] using h
  have wordEq : word = cellValue place env.toEnvironment (shaCell self 4 0) := by
    simpa only [word, value, WitnessIR.eval_readNat, Halo2.WitgenEnv.readVar_halo2, cellValue] using
      Nat.mod_eq_of_lt (cellSmall.trans (by decide))
  have wordBound : word < 2 ^ 32 := wordEq ▸ cellSmall
  have h0 := limb_honest (place := place) (self := self) (env := env)
    value (25,7) 0 0 (by decide +kernel) limb0
  have h1 := limb_honest (place := place) (self := self) (env := env)
    value (13,12) 0 1 (by decide +kernel) limb1
  have h2 := limb_honest (place := place) (self := self) (env := env)
    value (11,2) 1 0 (by decide +kernel) limb2
  have h3 := limb_honest (place := place) (self := self) (env := env)
    value (6,5) 1 1 (by decide +kernel) limb3
  have h4 := limb_honest (place := place) (self := self) (env := env)
    value (0,6) 2 0 (by decide +kernel) limb4
  have row0 := lookup_row_complete (place := place) (self := self) (env := env)
    table 0 7 12 _ _ (by decide +kernel) (by decide +kernel)
    (limb_bound value (25,7) ⟨place,env⟩) (limb_bound value (13,12) ⟨place,env⟩) limb0 limb1
  have row1 := lookup_row_complete (place := place) (self := self) (env := env)
    table 1 2 5 _ _ (by decide +kernel) (by decide +kernel)
    (limb_bound value (11,2) ⟨place,env⟩) (limb_bound value (6,5) ⟨place,env⟩) limb2 limb3
  have addConstraints := addMod_complete (place := place) (self := self) (env := env)
    table summands zero size zeroValue inputs 6 _ (by decide +kernel)
    (limb_bound value (0,6) ⟨place,env⟩) limb4 addition
  have row2 := (addMod_facts (place := place) (self := self) (env := env.toEnvironment)
    summands zero size addConstraints).2.1
  have plainField : (word:F) = env.advice ⟨2⟩ (place self : Nat) := by
    rw [wordEq]
    simp only [cellValue, shaCell, circuit_norm, Synthesis.shaAdvice, Nat.add_zero]
    rfl
  rw [WitnessIR.eval_program, WitnessIR.eval_spread32] at expanded
  change env.advice ⟨2⟩ (place self+1:Nat) = (Witness.spread32 word:F) at expanded
  norm_num [ParityGadget.plainAndSpread_output, Synthesis.shaAdvice, circuit_norm,
    Nat.cast_add] at h0 h1 h2 h3 h4 expanded plainField
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 13 1) := by
    apply e_gate_complete (place := place) (self := self) (env := env.toEnvironment) (row := 1)
    all_goals norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
    · change (33554432:F)*env.advice ⟨6⟩ _ + 8192*env.advice ⟨7⟩ _ +
        2048*env.advice ⟨6⟩ _ + 64*env.advice ⟨7⟩ _ + env.advice ⟨6⟩ _ = env.advice ⟨2⟩ _
      rw [h0.2.1, h1.2.1, h2.2.1, h3.2.1, h4.2.1, ← plainField]
      exact e_plain_field word wordBound
    · change (1125899906842624:F)*env.advice ⟨0⟩ _ + 67108864*env.advice ⟨1⟩ _ +
        4194304*env.advice ⟨0⟩ _ + 4096*env.advice ⟨1⟩ _ + env.advice ⟨0⟩ _ = env.advice ⟨2⟩ _
      rw [h0.2.2, h1.2.2, h2.2.2, h3.2.2, h4.2.2, expanded]
      exact e_spread_field word wordBound
  simp only [eRegion, circuit_norm, ParityGadget.plainAndSpread_constraints, true_and]
  exact ⟨gate, addConstraints, ⟨row0, h0.1⟩, ⟨row0, h1.1⟩,
    ⟨row1, h2.1⟩, ⟨row1, h3.1⟩, ⟨row2, h4.1⟩⟩

/-- The message preparation's three direct bit assignments meet the native
boolean gates; its remaining limbs and carry meet both tuples of each lookup. -/
theorem messageRegion_complete {place : RegionIndex → Nat} {self : RegionIndex}
    {env : ProverEnvironment F} (table : SpreadTable env.toEnvironment)
    (summands : Array (AssignedCell F)) (zero : AssignedCell F)
    (size : summands.size ≤ 7) (zeroValue : cellValue place env.toEnvironment zero = 0)
    (inputs : ∀ cell ∈ summands, cellValue place env.toEnvironment cell < 2 ^ 32)
    (witnesses : RegionOperations.ExtendsWitnesses place self env
      ((messageRegion summands zero).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((messageRegion summands zero).operations self) := by
  simp only [messageRegion, circuit_norm, activation_message, true_and, and_true] at witnesses
  obtain ⟨addition, limb0, limb1, limb2, limb3, limb4, bit1, bit2, bit3⟩ := witnesses
  let value := WitnessIR.readNat (shaCell self 4 0)
  let word := (value.eval { env := (⟨place,env⟩ : Placed ProverEnvironment F) }).toNat
  have cellSmall : cellValue place env.toEnvironment (shaCell self 4 0) < 2 ^ 32 := by
    have h := (addMod_output_honest (place := place) (self := self) (env := env)
      summands zero zeroValue inputs addition).trans_lt (Witness.sum32_lt _)
    simpa only [cellValue, addMod_output, Witness.wordModulus] using h
  have wordEq : word = cellValue place env.toEnvironment (shaCell self 4 0) := by
    simpa only [word, value, WitnessIR.eval_readNat, Halo2.WitgenEnv.readVar_halo2, cellValue] using
      Nat.mod_eq_of_lt (cellSmall.trans (by decide))
  have wordBound : word < 2 ^ 32 := wordEq ▸ cellSmall
  have h0 := limb_honest (place := place) (self := self) (env := env)
    value (20,12) 0 0 (by decide +kernel) limb0
  have h1 := limb_honest (place := place) (self := self) (env := env)
    value (10,7) 0 1 (by decide +kernel) limb1
  have h2 := limb_honest (place := place) (self := self) (env := env)
    value (7,3) 1 0 (by decide +kernel) limb2
  have h3 := limb_honest (place := place) (self := self) (env := env)
    value (3,4) 1 1 (by decide +kernel) limb3
  have h4 := limb_honest (place := place) (self := self) (env := env)
    value (0,3) 2 0 (by decide +kernel) limb4
  have row0 := lookup_row_complete (place := place) (self := self) (env := env)
    table 0 12 7 _ _ (by decide +kernel) (by decide +kernel)
    (limb_bound value (20,12) ⟨place,env⟩) (limb_bound value (10,7) ⟨place,env⟩) limb0 limb1
  have row1 := lookup_row_complete (place := place) (self := self) (env := env)
    table 1 3 4 _ _ (by decide +kernel) (by decide +kernel)
    (limb_bound value (7,3) ⟨place,env⟩) (limb_bound value (3,4) ⟨place,env⟩) limb2 limb3
  have addConstraints := addMod_complete (place := place) (self := self) (env := env)
    table summands zero size zeroValue inputs 3 _ (by decide +kernel)
    (limb_bound value (0,3) ⟨place,env⟩) limb4 addition
  have row2 := (addMod_facts (place := place) (self := self) (env := env.toEnvironment)
    summands zero size addConstraints).2.1
  have plainField : (word:F) = env.advice ⟨2⟩ (place self : Nat) := by
    rw [wordEq]
    simp only [cellValue, shaCell, circuit_norm, Synthesis.shaAdvice, Nat.add_zero]
    rfl
  rw [WitnessIR.eval_program, WitnessIR.eval_limb _ _ _ (by decide) (by decide)] at bit1 bit2 bit3
  change env.advice ⟨5⟩ (place self : Nat) = (Witness.limb word (19,1):F) at bit1
  change env.advice ⟨5⟩ (place self+1:Nat) = (Witness.limb word (18,1):F) at bit2
  change env.advice ⟨5⟩ (place self+2:Nat) = (Witness.limb word (17,1):F) at bit3
  norm_num [ParityGadget.plainAndSpread_output, Synthesis.shaAdvice, circuit_norm,
    Nat.cast_add] at h0 h1 h2 h3 h4 bit1 bit2 bit3 plainField
  have gate : RegionOperations.Constraints place self env.toEnvironment (activation 14 1) := by
    apply message_gate_complete (place := place) (self := self) (env := env.toEnvironment) (row := 1)
    · norm_num [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
      change (1048576:F)*env.advice ⟨6⟩ _ + 524288*env.advice ⟨5⟩ _ +
        262144*env.advice ⟨5⟩ _ + 131072*env.advice ⟨5⟩ _ + 1024*env.advice ⟨7⟩ _ +
        128*env.advice ⟨6⟩ _ + 8*env.advice ⟨7⟩ _ + env.advice ⟨6⟩ _ = env.advice ⟨2⟩ _
      rw [h0.2.1, bit1, bit2, bit3, h1.2.1, h2.2.1, h3.2.1, h4.2.1, ← plainField]
      exact message_plain_field word wordBound
    · have bit := one_bit_gate word 19
      rw [← bit1] at bit
      simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add] using bit
    · have bit := one_bit_gate word 18
      rw [← bit2] at bit
      simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add] using bit
    · have bit := one_bit_gate word 17
      rw [← bit3] at bit
      simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using bit
  simp only [messageRegion, circuit_norm, ParityGadget.plainAndSpread_constraints, and_true]
  exact ⟨gate, addConstraints, ⟨row0, h0.1⟩, ⟨row0, h1.1⟩,
    ⟨row1, h2.1⟩, ⟨row1, h3.1⟩, ⟨row2, h4.1⟩⟩

/-- Honest completeness of the original cache-threaded preparation source,
including a possible zero-constant allocation and the derived representation. -/
theorem prepareA_complete (summands : Array (AssignedCell F)) (cache : Cache)
    (self : RegionIndex) (env : Placed ProverEnvironment F)
    (table : SpreadTable env.env.toEnvironment)
    (cacheValid : Linear.CacheMeaning env.toEnvironment cache)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env.toEnvironment cell < 2 ^ 32)
    (witnesses : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.prepareA summands).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.prepareA summands).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.prepareA summands).run cache).output self
     ARep env.place env.env.toEnvironment output.1
       ((summands.toList.map (cellValue env.place env.env.toEnvironment)).sum % 2 ^ 32) ∧
       Linear.CacheMeaning env.toEnvironment output.2) := by
  have satisfied : Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.prepareA summands).run cache).operations self) self := by
    rw [prepareA_run] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    rw [← Linear.constant_nextRegionIndex] at witnesses ⊢
    obtain ⟨constantWitness, regionWitness⟩ := witnesses
    obtain ⟨constantConstraints, zeroValue, _⟩ :=
      Linear.constant_complete 0 cache self env cacheValid constantWitness
    refine ⟨constantConstraints, ?_⟩
    apply aRegion_complete (place := env.place) (env := env.env)
      table _ _ size ?_ inputs regionWitness
    simp only [cellValue, zeroValue, Nat.cast_zero, ZMod.val_zero]
  exact ⟨satisfied, prepareA_sound summands cache self env.toEnvironment
    table cacheValid size inputs satisfied⟩

/-- Honest completeness of the original cache-threaded preparation source,
including a possible zero-constant allocation and the derived representation. -/
theorem prepareE_complete (summands : Array (AssignedCell F)) (cache : Cache)
    (self : RegionIndex) (env : Placed ProverEnvironment F)
    (table : SpreadTable env.env.toEnvironment)
    (cacheValid : Linear.CacheMeaning env.toEnvironment cache)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env.toEnvironment cell < 2 ^ 32)
    (witnesses : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.prepareE summands).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.prepareE summands).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.prepareE summands).run cache).output self
     ERep env.place env.env.toEnvironment output.1
       ((summands.toList.map (cellValue env.place env.env.toEnvironment)).sum % 2 ^ 32) ∧
       Linear.CacheMeaning env.toEnvironment output.2) := by
  have satisfied : Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.prepareE summands).run cache).operations self) self := by
    rw [prepareE_run] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    rw [← Linear.constant_nextRegionIndex] at witnesses ⊢
    obtain ⟨constantWitness, regionWitness⟩ := witnesses
    obtain ⟨constantConstraints, zeroValue, _⟩ :=
      Linear.constant_complete 0 cache self env cacheValid constantWitness
    refine ⟨constantConstraints, ?_⟩
    apply eRegion_complete (place := env.place) (env := env.env)
      table _ _ size ?_ inputs regionWitness
    simp only [cellValue, zeroValue, Nat.cast_zero, ZMod.val_zero]
  exact ⟨satisfied, prepareE_sound summands cache self env.toEnvironment
    table cacheValid size inputs satisfied⟩

/-- Honest completeness of the original cache-threaded preparation source,
including a possible zero-constant allocation and the derived representation. -/
theorem prepareMessage_complete (summands : Array (AssignedCell F)) (cache : Cache)
    (self : RegionIndex) (env : Placed ProverEnvironment F)
    (table : SpreadTable env.env.toEnvironment)
    (cacheValid : Linear.CacheMeaning env.toEnvironment cache)
    (size : summands.size ≤ 7)
    (inputs : ∀ cell ∈ summands, cellValue env.place env.env.toEnvironment cell < 2 ^ 32)
    (witnesses : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.prepareMessage summands).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.prepareMessage summands).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.prepareMessage summands).run cache).output self
     MessageRep env.place env.env.toEnvironment output.1
       ((summands.toList.map (cellValue env.place env.env.toEnvironment)).sum % 2 ^ 32) ∧
       Linear.CacheMeaning env.toEnvironment output.2) := by
  have satisfied : Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.prepareMessage summands).run cache).operations self) self := by
    rw [prepareMessage_run] at witnesses ⊢
    simp only [circuit_norm, and_true] at witnesses ⊢
    rw [← Linear.constant_nextRegionIndex] at witnesses ⊢
    obtain ⟨constantWitness, regionWitness⟩ := witnesses
    obtain ⟨constantConstraints, zeroValue, _⟩ :=
      Linear.constant_complete 0 cache self env cacheValid constantWitness
    refine ⟨constantConstraints, ?_⟩
    apply messageRegion_complete (place := env.place) (env := env.env)
      table _ _ size ?_ inputs regionWitness
    simp only [cellValue, zeroValue, Nat.cast_zero, ZMod.val_zero]
  exact ⟨satisfied, prepareMessage_sound summands cache self env.toEnvironment
    table cacheValid size inputs satisfied⟩

end Midnight.SHA256.Semantics.PrepareWitness
