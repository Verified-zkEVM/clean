import Midnight.SHA256.Semantics.ParityGadget

/-! Contracts of the actual source Maj and Sigma gadgets. Source equalities
connect the finite proof views below to the original witness-bearing program. -/
namespace Midnight.SHA256.Semantics.BitwiseGadgets
open Halo2 Gates WitnessCircuit ParityGadget

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
attribute [local cbv_opaque] WitnessCircuit.enable WitnessCircuit.sa WitnessCircuit.scopy
  WitnessCircuit.spread111110 WitnessIR.weighted WitnessIR.readNat HAppend.hAppend
  GetElem?.getElem! Vector.ofFn
attribute [local cbv_opaque] BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing

/-- A definitionally identical view of the source's single Maj region. -/
def majorityRegion (a b c : AssignedCell F) : Region (AssignedCell F) := do
  enable 5 1
  let _ ← scopy a 5 0
  let _ ← scopy b 6 0
  let _ ← scopy c 5 1
  spread111110 true 0 (.add (.add (WitnessIR.readNat a) (WitnessIR.readNat b))
    (WitnessIR.readNat c))

theorem majority_source (a b c : AssignedCell F) (cache : Cache) :
    (WitnessCircuit.majority a b c).run cache = (do
      let output ← assignRegion "Maj(A, B, C)" (majorityRegion a b c)
      return (output, cache)) := rfl

/-- Source-gadget soundness: copied spread values and the actual constraints
force the returned cell to the SHA majority function. -/
theorem majorityRegion_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (a b c : AssignedCell F)
    (x y z : Nat) (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (ax : a.eval place env = (spread x : F))
    (by_ : b.eval place env = (spread y : F))
    (cz : c.eval place env = (spread z : F))
    (satisfied : RegionOperations.Constraints place self env
      ((majorityRegion a b c).operations self)) :
    (((majorityRegion a b c).output self).eval place env).val = Specs.SHA256.Maj x y z := by
  simp only [majorityRegion, scopy, circuit_norm, true_and] at satisfied
  obtain ⟨gate, acopy, bcopy, ccopy, parity⟩ := satisfied
  obtain ⟨outputGate, oddLookups, evenLookups⟩ := spread111110_facts
    (place := place) (self := self) (env := env) table true 0 _ parity
  have aRead : Gates.read env (place self+1:Nat) 5 (-1) = (spread x : F) := by
    simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using acopy.trans ax
  have bRead : Gates.read env (place self+1:Nat) 6 (-1) = (spread y : F) := by
    simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using bcopy.trans by_
  have cRead : Gates.read env (place self+1:Nat) 5 0 = (spread z : F) := by
    simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using ccopy.trans cz
  have result := majority_row_sound (place := place) (self := self) (env := env) (row := 1)
    hx hy hz aRead bRead cRead gate outputGate oddLookups evenLookups
  simpa [majorityRegion, circuit_norm, Gates.read, Synthesis.shaAdvice,
    Nat.cast_add, Int.add_assoc] using result

/-- The soundness theorem directly for the original state-threaded source
function, preserving its actual region and returned cell. -/
theorem majority_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (a b c : AssignedCell F) (cache : Cache)
    (x y z : Nat) (hx : x < 2^32) (hy : y < 2^32) (hz : z < 2^32)
    (ax : a.eval place env = (spread x : F))
    (by_ : b.eval place env = (spread y : F))
    (cz : c.eval place env = (spread z : F))
    (satisfied : Constraints place env (((WitnessCircuit.majority a b c).run cache).operations self) self) :
    ((((WitnessCircuit.majority a b c).run cache).output self).1.eval place env).val =
      Specs.SHA256.Maj x y z := by
  rw [majority_source] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  exact majorityRegion_sound (place := place) (self := self) (env := env)
    table a b c x y z hx hy hz ax by_ cz satisfied

/-- Values of the actual source limb cells, without assuming honest advice. -/
def limbValues {n : Nat} (place : RegionIndex → Nat) (env : Environment F)
    (word : Word) : Vector F n :=
  Vector.ofFn fun i : Fin n => word.limbs[i.val]!.eval place env

def bigSigma0Region (word : Word) : Region (AssignedCell F) := do
  enable 7 1
  let _ ← scopy word.limbs[0]! 5 0
  let _ ← scopy word.limbs[1]! 6 0
  let _ ← scopy word.limbs[2]! 5 1
  let _ ← scopy word.limbs[3]! 6 1
  spread111110 false 0 (WitnessIR.weighted Witness.bigSigma0Recipe
    (Vector.ofFn fun i : Fin 4 => WitnessIR.readNat word.limbs[i.val]!))

theorem bigSigma0_source (word : Word) (cache : Cache) :
    (WitnessCircuit.bigSigma0 word).run cache = (do
      let output ← assignRegion "Σ₀(A)" (bigSigma0Region word)
      return (output, cache)) := by
  funext self
  unfold WitnessCircuit.bigSigma0 WitnessCircuit.sigma WitnessCircuit.region bigSigma0Region
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem bigSigma0Region_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (a b c d : Nat)
    (bounded : Decomposition.Bounded (Decomposition.aLimbs a b c d))
    (inputs : limbValues place env word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F)])
    (satisfied : RegionOperations.Constraints place self env
      ((bigSigma0Region word).operations self)) :
    (((bigSigma0Region word).output self).eval place env).val =
      Specs.SHA256.upperSigma0 (Decomposition.pack (Decomposition.aLimbs a b c d)) := by
  simp only [bigSigma0Region, scopy, circuit_norm, true_and] at satisfied
  obtain ⟨gate, h₀, h₁, h₂, h₃, parity⟩ := satisfied
  obtain ⟨outputGate, evenLookups, oddLookups⟩ := spread111110_facts
    (place := place) (self := self) (env := env) table false 0 _ parity
  have copied : bigSigma0Inputs env (place self+1:Nat) = limbValues place env word := by
    apply Vector.ext
    intro i hi
    interval_cases i <;>
      simp_all [bigSigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice,
        Nat.cast_add]
  have sourceInputs : bigSigma0Inputs env (place self+1:Nat) =
      (#v[spread a, spread b, spread c, spread d].map (fun n:Nat => (n:F))) := by
    simpa using copied.trans inputs
  have result := bigSigma0_row_sound (place := place) (self := self) (env := env) (row := 1)
    a b c d bounded sourceInputs gate outputGate evenLookups oddLookups
  simpa [bigSigma0Region, circuit_norm, Gates.read, Synthesis.shaAdvice,
    Nat.cast_add, Int.add_assoc] using result

theorem bigSigma0_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (cache : Cache)
    (a b c d : Nat) (bounded : Decomposition.Bounded (Decomposition.aLimbs a b c d))
    (inputs : limbValues place env word =
      #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F)])
    (satisfied : Constraints place env (((WitnessCircuit.bigSigma0 word).run cache).operations self) self) :
    ((((WitnessCircuit.bigSigma0 word).run cache).output self).1.eval place env).val =
      Specs.SHA256.upperSigma0 (Decomposition.pack (Decomposition.aLimbs a b c d)) := by
  rw [bigSigma0_source] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  exact bigSigma0Region_sound (place := place) (self := self) (env := env)
    table word a b c d bounded inputs satisfied

def bigSigma1Region (word : Word) : Region (AssignedCell F) := do
  enable 8 1
  let _ ← scopy word.limbs[0]! 5 0
  let _ ← scopy word.limbs[1]! 6 0
  let _ ← scopy word.limbs[2]! 5 1
  let _ ← scopy word.limbs[3]! 6 1
  let _ ← scopy word.limbs[4]! 5 2
  spread111110 false 0 (WitnessIR.weighted Witness.bigSigma1Recipe
    (Vector.ofFn fun i : Fin 5 => WitnessIR.readNat word.limbs[i.val]!))

theorem bigSigma1_source (word : Word) (cache : Cache) :
    (WitnessCircuit.bigSigma1 word).run cache = (do
      let output ← assignRegion "Σ₁(E)" (bigSigma1Region word)
      return (output, cache)) := by
  funext self
  unfold WitnessCircuit.bigSigma1 WitnessCircuit.sigma WitnessCircuit.region bigSigma1Region
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem bigSigma1Region_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (a b c d e : Nat)
    (bounded : Decomposition.Bounded (Decomposition.eLimbs a b c d e))
    (inputs : limbValues place env word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F)])
    (satisfied : RegionOperations.Constraints place self env
      ((bigSigma1Region word).operations self)) :
    (((bigSigma1Region word).output self).eval place env).val =
      Specs.SHA256.upperSigma1 (Decomposition.pack (Decomposition.eLimbs a b c d e)) := by
  simp only [bigSigma1Region, scopy, circuit_norm, true_and] at satisfied
  obtain ⟨gate, h0, h1, h2, h3, h4, parity⟩ := satisfied
  obtain ⟨outputGate, evenLookups, oddLookups⟩ := spread111110_facts
    (place := place) (self := self) (env := env) table false 0 _ parity
  have copied : bigSigma1Inputs env (place self+1:Nat) = limbValues place env word := by
    apply Vector.ext
    intro i hi
    interval_cases i <;>
      simp_all [bigSigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
  have sourceInputs : bigSigma1Inputs env (place self+1:Nat) =
      (#v[spread a, spread b, spread c, spread d, spread e].map (fun n:Nat => (n:F))) := by
    simpa using copied.trans inputs
  have result := bigSigma1_row_sound (place := place) (self := self) (env := env) (row := 1)
    a b c d e bounded sourceInputs gate outputGate evenLookups oddLookups
  simpa [bigSigma1Region, circuit_norm, Gates.read, Synthesis.shaAdvice,
    Nat.cast_add, Int.add_assoc] using result

theorem bigSigma1_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (cache : Cache)
    (a b c d e : Nat) (bounded : Decomposition.Bounded (Decomposition.eLimbs a b c d e))
    (inputs : limbValues place env word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F)])
    (satisfied : Constraints place env (((WitnessCircuit.bigSigma1 word).run cache).operations self) self) :
    ((((WitnessCircuit.bigSigma1 word).run cache).output self).1.eval place env).val =
      Specs.SHA256.upperSigma1 (Decomposition.pack (Decomposition.eLimbs a b c d e)) := by
  rw [bigSigma1_source] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  exact bigSigma1Region_sound (place := place) (self := self) (env := env)
    table word a b c d e bounded inputs satisfied

def sigma0Region (word : Word) : Region (AssignedCell F) := do
  enable 9 1
  let _ ← scopy word.limbs[0]! 5 0
  let _ ← scopy word.limbs[1]! 6 0
  let _ ← scopy word.limbs[2]! 4 1
  let _ ← scopy word.limbs[3]! 5 1
  let _ ← scopy word.limbs[4]! 6 1
  let _ ← scopy word.limbs[5]! 4 2
  let _ ← scopy word.limbs[6]! 5 2
  let _ ← scopy word.limbs[7]! 6 2
  spread111110 false 0 (WitnessIR.weighted Witness.sigma0Recipe
    (Vector.ofFn fun i : Fin 8 => WitnessIR.readNat word.limbs[i.val]!))

theorem sigma0_source (word : Word) (cache : Cache) :
    (WitnessCircuit.sigma0 word).run cache = (do
      let output ← assignRegion "σ₀(W)" (sigma0Region word)
      return (output, cache)) := by
  funext self
  unfold WitnessCircuit.sigma0 WitnessCircuit.sigma WitnessCircuit.region sigma0Region
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem sigma0Region_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (a b c d e f g h : Nat)
    (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (satisfied : RegionOperations.Constraints place self env
      ((sigma0Region word).operations self)) :
    (((sigma0Region word).output self).eval place env).val =
      Specs.SHA256.lowerSigma0 (Decomposition.pack (Decomposition.messageLimbs a b c d e f g h)) := by
  simp only [sigma0Region, scopy, circuit_norm, true_and] at satisfied
  obtain ⟨gate, h0, h1, h2, h3, h4, h5, h6, h7, parity⟩ := satisfied
  obtain ⟨outputGate, evenLookups, oddLookups⟩ := spread111110_facts
    (place := place) (self := self) (env := env) table false 0 _ parity
  have copied : sigma0Inputs env (place self+1:Nat) = limbValues place env word := by
    apply Vector.ext
    intro i hi
    interval_cases i <;>
      simp_all [sigma0Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
  have sourceInputs : sigma0Inputs env (place self+1:Nat) =
      (#v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h].map (fun n:Nat => (n:F))) := by
    simpa using copied.trans inputs
  have result := sigma0_row_sound (place := place) (self := self) (env := env) (row := 1)
    a b c d e f g h bounded sourceInputs gate outputGate evenLookups oddLookups
  simpa [sigma0Region, circuit_norm, Gates.read, Synthesis.shaAdvice,
    Nat.cast_add, Int.add_assoc] using result

theorem sigma0_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (cache : Cache)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (satisfied : Constraints place env (((WitnessCircuit.sigma0 word).run cache).operations self) self) :
    ((((WitnessCircuit.sigma0 word).run cache).output self).1.eval place env).val =
      Specs.SHA256.lowerSigma0 (Decomposition.pack (Decomposition.messageLimbs a b c d e f g h)) := by
  rw [sigma0_source] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  exact sigma0Region_sound (place := place) (self := self) (env := env)
    table word a b c d e f g h bounded inputs satisfied

def sigma1Region (word : Word) : Region (AssignedCell F) := do
  enable 10 1
  let _ ← scopy word.limbs[0]! 5 0
  let _ ← scopy word.limbs[1]! 6 0
  let _ ← scopy word.limbs[2]! 4 1
  let _ ← scopy word.limbs[3]! 5 1
  let _ ← scopy word.limbs[4]! 6 1
  let _ ← scopy word.limbs[5]! 4 2
  let _ ← scopy word.limbs[6]! 5 2
  let _ ← scopy word.limbs[7]! 6 2
  spread111110 false 0 (WitnessIR.weighted Witness.sigma1Recipe
    (Vector.ofFn fun i : Fin 8 => WitnessIR.readNat word.limbs[i.val]!))

theorem sigma1_source (word : Word) (cache : Cache) :
    (WitnessCircuit.sigma1 word).run cache = (do
      let output ← assignRegion "σ₁(W)" (sigma1Region word)
      return (output, cache)) := by
  funext self
  unfold WitnessCircuit.sigma1 WitnessCircuit.sigma WitnessCircuit.region sigma1Region
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem sigma1Region_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (a b c d e f g h : Nat)
    (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (satisfied : RegionOperations.Constraints place self env
      ((sigma1Region word).operations self)) :
    (((sigma1Region word).output self).eval place env).val =
      Specs.SHA256.lowerSigma1 (Decomposition.pack (Decomposition.messageLimbs a b c d e f g h)) := by
  simp only [sigma1Region, scopy, circuit_norm, true_and] at satisfied
  obtain ⟨gate, h0, h1, h2, h3, h4, h5, h6, h7, parity⟩ := satisfied
  obtain ⟨outputGate, evenLookups, oddLookups⟩ := spread111110_facts
    (place := place) (self := self) (env := env) table false 0 _ parity
  have copied : sigma1Inputs env (place self+1:Nat) = limbValues place env word := by
    apply Vector.ext
    intro i hi
    interval_cases i <;>
      simp_all [sigma1Inputs, limbValues, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc]
  have sourceInputs : sigma1Inputs env (place self+1:Nat) =
      (#v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h].map (fun n:Nat => (n:F))) := by
    simpa using copied.trans inputs
  have result := sigma1_row_sound (place := place) (self := self) (env := env) (row := 1)
    a b c d e f g h bounded sourceInputs gate outputGate evenLookups oddLookups
  change (env.advice ⟨2⟩ (place self : Nat)).val = _
  simpa [Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] using result

theorem sigma1_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (word : Word) (cache : Cache)
    (a b c d e f g h : Nat) (bounded : Decomposition.Bounded (Decomposition.messageLimbs a b c d e f g h))
    (inputs : limbValues place env word = #v[(spread a:F), (spread b:F), (spread c:F), (spread d:F), (spread e:F), (spread f:F), (spread g:F), (spread h:F)])
    (satisfied : Constraints place env (((WitnessCircuit.sigma1 word).run cache).operations self) self) :
    ((((WitnessCircuit.sigma1 word).run cache).output self).1.eval place env).val =
      Specs.SHA256.lowerSigma1 (Decomposition.pack (Decomposition.messageLimbs a b c d e f g h)) := by
  rw [sigma1_source] at satisfied ⊢
  simp only [circuit_norm, and_true] at satisfied ⊢
  exact sigma1Region_sound (place := place) (self := self) (env := env)
    table word a b c d e f g h bounded inputs satisfied

end Midnight.SHA256.Semantics.BitwiseGadgets
