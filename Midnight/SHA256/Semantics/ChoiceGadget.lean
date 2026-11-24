import Midnight.SHA256.Semantics.BitwiseGadgets
import Midnight.SHA256.Semantics.Linear

/-! The actual two-half-Ch source region. The mask cell contract is supplied by
the shared constant-cache correctness theorem at the caller boundary. -/
namespace Midnight.SHA256.Semantics.ChoiceGadget
open Halo2 Gates WitnessCircuit ParityGadget

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation

private theorem clean_sum (a b : Midnight.Keygen.E) : a + b = Halo2.Expression.add a b := rfl

private theorem clean_sub (a b : Midnight.Keygen.E) :
    a - b = Halo2.Expression.add a (Halo2.Expression.mul (Halo2.Expression.const (-1)) b) := rfl

private theorem clean_mul (a b : Midnight.Keygen.E) : a * b = Halo2.Expression.mul a b := rfl

set_option linter.constructorNameAsVariable false in
theorem halfCh_equations {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 6 row)) :
    (Gates.read env (place self+row:Nat) 5 (-1) + Gates.read env (place self+row:Nat) 6 (-1) =
      parityPlane env (place self+row:Nat) 3 + 2*parityPlane env (place self+row:Nat) 1) ∧
    (Gates.read env (place self+row:Nat) 4 0 + Gates.read env (place self+row:Nat) 5 0 =
      Gates.read env (place self+row:Nat) 6 0) := by
  rw [activation_halfCh] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, halfChGate, halfChSpec, Midnight.Keygen.GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [Gates.read, parityPlane, Synthesis.shaAdvice]
  constructor
  · linear_combination (norm := ring_nf) h.1
  · linear_combination (norm := ring_nf) h.2

set_option linter.constructorNameAsVariable false in
theorem halfCh_and_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row x y : Nat}
    (hx : x < 2^32) (hy : y < 2^32)
    (xRead : Gates.read env (place self+row:Nat) 5 (-1) = (spread x:F))
    (yRead : Gates.read env (place self+row:Nat) 6 (-1) = (spread y:F))
    (gate : RegionOperations.Constraints place self env (activation 6 row))
    (outputGate : RegionOperations.Constraints place self env (activation 11 row))
    (oddLookups : ParityLookups env (place self+row:Nat) 0 1)
    (evenLookups : ParityLookups env (place self+row:Nat) 2 3) :
    (Gates.read env (place self+row:Nat) 4 (-1)).val = x &&& y := by
  obtain ⟨ob, op⟩ := parityLookups_sound (env := env) (absolute := (place self+row:Nat)) oddLookups
  obtain ⟨eb, ep⟩ := parityLookups_sound (env := env) (absolute := (place self+row:Nat)) evenLookups
  have equation := (halfCh_equations (place := place) (self := self) (env := env) (row := row) gate).1
  rw [xRead, yRead, ep, op] at equation
  have result := (spread_pair_field_sound hx hy eb ob sha256_parity_capacity equation).2
  rw [parity_output (place := place) (self := self) (env := env) (row := row) outputGate oddLookups]
  exact result

def choiceRegion (mask e f g : AssignedCell F) : Region (AssignedCell F) := do
  enable 6 1
  enable 6 4
  let _ ← scopy e 5 0
  let _ ← scopy e 4 4
  let _ ← scopy f 6 0
  let _ ← scopy g 6 3
  let ne ← sa 5 3 (WitnessIR.negateSpread (WitnessIR.readNat e))
  let _ ← scopy ne 5 4
  let _ ← scopy mask 6 4
  let ef ← spread111110 true 0 (.add (WitnessIR.readNat e) (WitnessIR.readNat f))
  let _ ← scopy ef 4 1
  let neg ← spread111110 true 3 (.add (WitnessIR.readNat ne) (WitnessIR.readNat g))
  let _ ← scopy neg 5 1
  sa 6 1 (.add (WitnessIR.readNat ef) (WitnessIR.readNat neg))

theorem choice_source (e f g : AssignedCell F) :
    WitnessCircuit.choice e f g = (do
      let mask ← constant 0x5555555555555555
      region "Ch(E, F, G)" (choiceRegion mask e f g)) := rfl

theorem choiceRegion_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (mask e f g : AssignedCell F)
    (x y z : Nat) (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (maskValue : mask.eval place env = (0x5555555555555555:F))
    (ex : e.eval place env = (spread x:F))
    (fy : f.eval place env = (spread y:F))
    (gz : g.eval place env = (spread z:F))
    (satisfied : RegionOperations.Constraints place self env
      ((choiceRegion mask e f g).operations self)) :
    (((choiceRegion mask e f g).output self).eval place env).val = Specs.SHA256.Ch x y z := by
  simp only [choiceRegion, scopy, circuit_norm, and_true, true_and] at satisfied
  obtain ⟨gate₁, gate₂, ec₁, ec₂, fc, gc, nc, mc, parity₁, efc, parity₂, ngc⟩ := satisfied
  obtain ⟨pg₁, odd₁, even₁⟩ := spread111110_facts
    (place := place) (self := self) (env := env) table true 0 _ parity₁
  obtain ⟨pg₂, odd₂, even₂⟩ := spread111110_facts
    (place := place) (self := self) (env := env) table true 3 _ parity₂
  have eq₁ := (halfCh_equations (place := place) (self := self) (env := env) (row := 1) gate₁).2
  have eq₂ := (halfCh_equations (place := place) (self := self) (env := env) (row := 4) gate₂).2
  have er : Gates.read env (place self+1:Nat) 5 (-1) = (spread x:F) := by
    simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using ec₁.trans ex
  have fr : Gates.read env (place self+1:Nat) 6 (-1) = (spread y:F) := by
    simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using fc.trans fy
  have gr : Gates.read env (place self+4:Nat) 6 (-1) = (spread z:F) := by
    simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using gc.trans gz
  have nr : Gates.read env (place self+4:Nat) 5 (-1) = (spread (complement 32 x):F) := by
    rw [spread_complement_field hx, spread_mask32]
    norm_num [Gates.read, Synthesis.shaAdvice, circuit_norm, Nat.cast_add, Int.add_assoc] at eq₂ nc ec₂ mc ⊢
    rw [nc, ec₂, mc, ex, maskValue] at eq₂
    linear_combination (norm := ring_nf) eq₂
  have first := halfCh_and_sound (place := place) (self := self) (env := env) (row := 1)
    hx hy er fr gate₁ pg₁ odd₁ even₁
  have second := halfCh_and_sound (place := place) (self := self) (env := env) (row := 4)
    (complement_lt hx) hz nr gr gate₂ pg₂ odd₂ even₂
  have result : env.advice ⟨4⟩ (place self+1:Nat) =
      ((x &&& y) + (complement 32 x &&& z) : Nat) := by
    have ff := congrArg (fun n:Nat => (n:F)) first
    have ss := congrArg (fun n:Nat => (n:F)) second
    norm_num [Gates.read, Synthesis.shaAdvice, circuit_norm, Nat.cast_add, Int.add_assoc] at eq₁ efc ngc ff ss ⊢
    rw [efc, ngc, ff, ss] at eq₁
    exact eq₁.symm
  have choiceBound : Specs.SHA256.Ch x y z < 2^32 := by
    exact Nat.xor_lt_two_pow ((Nat.and_le_left).trans_lt hx)
      ((Nat.and_le_right).trans_lt hz)
  rw [choice_add_eq_xor hx y z] at result
  change env.advice ⟨4⟩ (place self+1:Nat) = (Specs.SHA256.Ch x y z:F) at result
  have outValue := congrArg (fun v:F => v.val) result
  have small : Specs.SHA256.Ch x y z < BLS12_381.scalarFieldSize :=
    choiceBound.trans (by decide +kernel)
  rw [ZMod.val_natCast_of_lt small] at outValue
  simpa [choiceRegion, circuit_norm, Synthesis.shaAdvice] using outValue

/-- Exact cache-aware source execution, including a possible mask allocation. -/
theorem choice_run (e f g : AssignedCell F) (cache : Cache) :
    (WitnessCircuit.choice e f g).run cache = (do
      let (mask, nextCache) ← (constant 0x5555555555555555).run cache
      let output ← assignRegion "Ch(E, F, G)" (choiceRegion mask e f g)
      return (output, nextCache)) := by
  rw [choice_source]
  rfl

/-- Full original source helper soundness, including mask cache hits/misses and
preservation of the meaningful cache invariant. -/
theorem choice_sound (e f g : AssignedCell F) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (table : SpreadTable env.env)
    (cacheValid : Linear.CacheMeaning env cache)
    (x y z : Nat) (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (ex : e.eval env.place env.env = (spread x:F))
    (fy : f.eval env.place env.env = (spread y:F))
    (gz : g.eval env.place env.env = (spread z:F))
    (satisfied : Constraints env.place env.env
      (((WitnessCircuit.choice e f g).run cache).operations self) self) :
    let output := ((WitnessCircuit.choice e f g).run cache).output self
    (output.1.eval env.place env.env).val = Specs.SHA256.Ch x y z ∧
      Linear.CacheMeaning env output.2 := by
  rw [choice_run] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  rw [← Linear.constant_nextRegionIndex] at satisfied
  obtain ⟨constantConstraints, regionConstraints⟩ := satisfied
  obtain ⟨maskValue, nextCache⟩ := Linear.constant_sound 0x5555555555555555 cache self
    env cacheValid constantConstraints
  refine ⟨?_, nextCache⟩
  exact choiceRegion_sound (place := env.place) (env := env.env)
    table _ e f g x y z hx hy hz maskValue ex fy gz regionConstraints

end Midnight.SHA256.Semantics.ChoiceGadget
