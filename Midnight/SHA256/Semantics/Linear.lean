import Midnight.SHA256.Semantics.Arithmetic
import Midnight.SHA256.WitnessCircuit

/-! Semantics of the source constant cache and native linear-combination helper.
Filtering follows source cell identity, never the assigned advice value. -/
namespace Midnight.SHA256.Semantics.Linear
open Halo2

attribute [local cbv_opaque] Arithmetic.nativeGate Witgen.WitgenIROver.ofFExpr
attribute [local cbv_opaque]
  BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing

abbrev Cell := WitnessCircuit.Cell
abbrev Cache := WitnessCircuit.Cache

/-- Every cached key is canonical and its cell contains that field constant.
This invariant includes existing cache entries; it is not a claim that an advice
cell with the same value has the same address. -/
def CacheMeaning (env : Placed Environment F) (cache : Cache) : Prop :=
  ∀ entry ∈ cache, entry.1 < BLS12_381.scalarFieldSize ∧
    AssignedCell.eval env.place env.env entry.2 = (entry.1 : F)

@[simp] theorem cacheMeaning_nil (env : Placed Environment F) : CacheMeaning env [] := by
  simp [CacheMeaning]

/-- Exact state transition, including the native cache-hit shortcut. -/
theorem constant_run (n : Nat) (cache : Cache) :
    (WitnessCircuit.constant n).run cache =
      match cache.find? (fun entry => entry.1 == (n : F).val) with
      | some (_, cell) => pure (cell, cache)
      | none => do
        let cell ← assignRegion "Assign fixed" (assignFixed ⟨9⟩ 0 (n : F))
        return (cell, ((n : F).val, cell) :: cache) := by
  funext self
  unfold WitnessCircuit.constant
  rw [show (get : WitnessCircuit.Build WitnessCircuit.Cache) =
    (fun cache => pure (cache, cache)) from rfl]
  dsimp only [StateT.run, bind, pure, StateT.bind, StateT.pure, get, StateT.get]
  cases cache.find? (fun entry => entry.1 == (n : F).val) <;> rfl

theorem constant_sound (n : Nat) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env
      (((WitnessCircuit.constant n).run cache).operations self) self) :
    let output := ((WitnessCircuit.constant n).run cache).output self
    AssignedCell.eval env.place env.env output.1 = (n : F) ∧
      CacheMeaning env output.2 := by
  rw [constant_run] at hc ⊢
  cases hfind : cache.find? (fun entry => entry.1 == (n : F).val) with
  | some entry =>
    rcases entry with ⟨key, cell⟩
    simp only [circuit_norm]
    have hk : key = (n : F).val := by simpa using List.find?_some hfind
    have hv := (hcache (key, cell) (List.mem_of_find?_eq_some hfind)).2
    refine ⟨?_, hcache⟩
    simpa only [hk, ZMod.natCast_zmod_val] using hv
  | none =>
    simp only [hfind, circuit_norm] at hc ⊢
    refine ⟨hc, ?_⟩
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | hentry
    · refine ⟨ZMod.val_lt (n : F), ?_⟩
      simpa only [circuit_norm, ZMod.natCast_zmod_val] using hc
    · exact hcache entry hentry

/-- Constants have no private advice computation: their honest fixed assignment
already implies their constraint, for both cache-hit and cache-miss branches. -/
theorem constant_constraints_of_witnesses (n : Nat) (cache : Cache)
    (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hw : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.constant n).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.constant n).run cache).operations self) self := by
  rw [constant_run] at hw ⊢
  cases hfind : cache.find? (fun entry => entry.1 == (n : F).val) with
  | some entry => rcases entry with ⟨key, cell⟩; simp only [circuit_norm]
  | none => simpa only [hfind, circuit_norm] using hw

def filtered (zero : Cell) (input : Array (F × Cell)) : Array (F × Cell) :=
  input.filter fun (coefficient, cell) => coefficient != 0 && cell != zero

def dot (env : Placed Environment F) (terms : Array (F × Cell)) : F :=
  (terms.toList.map fun term => term.1 * AssignedCell.eval env.place env.env term.2).sum

theorem dot_filter (env : Placed Environment F) (zero : Cell)
    (hzero : AssignedCell.eval env.place env.env zero = 0) (input : Array (F × Cell)) :
    dot env (filtered zero input) = dot env input := by
  unfold dot filtered
  rw [Array.toList_filter]
  generalize input.toList = terms
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    rcases term with ⟨coefficient, cell⟩
    by_cases hc : coefficient = 0
    · simp [hc, ih]
    · by_cases hv : cell = zero
      · simp [hv, hzero, ih]
      · simp [hc, hv, ih]

/-- The source's non-shortcut region, retaining its exact auxiliary and copy loop. -/
def combinationRegion (terms : Array (F × Cell)) : RegionCircuit F Cell := do
  let values := terms.map fun (coefficient, cell) => (coefficient, (.expr cell : FExpr F))
  let resultValue := values.foldl (fun acc (coeff, value) => acc + .const coeff * value)
    (.const 0)
  let (result, assigned) ← WitnessCircuit.linearAux values resultValue 4
  for i in [:terms.size] do constrainEqual assigned[i]! terms[i]!.2
  return result

/-- The actual stateful source program, split only at its cache and shortcut branches. -/
theorem linearCombination_run (input : Array (F × Cell)) (cache : Cache) :
    (WitnessCircuit.linearCombination input).run cache = do
      let (zero, nextCache) ← (WitnessCircuit.constant 0).run cache
      let terms := filtered zero input
      if terms.isEmpty then return (zero, nextCache)
      if terms.size == 1 && terms[0]!.1 == 1 then return (terms[0]!.2, nextCache)
      let result ← assignRegion "Linear combination" (combinationRegion terms)
      return (result, nextCache) := by
  funext self
  unfold WitnessCircuit.linearCombination filtered combinationRegion
  dsimp only [StateT.run, bind, pure, StateT.bind, StateT.pure]
  split
  · rfl
  · split <;> rfl

private def stamp (coeff : Arithmetic.Inputs F) : RegionCircuit F Unit := do
  Arithmetic.nativeGate.enable 0
  let _ ← assignFixed ⟨4⟩ 0 (-1)
  let _ ← assignFixed ⟨5⟩ 0 coeff.a
  let _ ← assignFixed ⟨6⟩ 0 coeff.b
  let _ ← assignFixed ⟨7⟩ 0 coeff.c
  let _ ← assignFixed ⟨8⟩ 0 coeff.d
  let _ ← assignFixed ⟨0⟩ 0 0
  let _ ← assignFixed ⟨1⟩ 0 0
  let _ ← assignFixed ⟨2⟩ 0 0
  let _ ← assignFixed ⟨3⟩ 0 0
  return ()

private def region1 (a : F × Cell) : RegionCircuit F Cell := do
  let result ← assignAdvice ⟨0⟩ 0 (.ofFExpr (.const 0 + .const a.1 * .expr a.2))
  let acopy ← assignAdvice ⟨1⟩ 0 (.ofFExpr (.expr a.2))
  stamp ⟨a.1, 0, 0, 0⟩
  constrainEqual acopy a.2
  return result

private theorem combinationRegion_1 (a : F × Cell) :
    combinationRegion #[a] = region1 a := by
  funext self
  unfold combinationRegion WitnessCircuit.linearAux WitnessCircuit.custom
    WitnessCircuit.enable region1 stamp
  simp only [Arithmetic.activation_zero]
  cbv

private theorem region1_sound (a : F × Cell) (self : RegionIndex)
    (env : Placed Environment F)
    (hc : RegionOperations.Constraints env.place self env.env
      ((combinationRegion #[a]).operations self)) :
    AssignedCell.eval env.place env.env ((combinationRegion #[a]).output self) =
      dot env #[a] := by
  rw [combinationRegion_1] at hc ⊢
  simp only [region1, stamp, Arithmetic.nativeGate, dot, circuit_norm,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc ⊢
  rcases hc with ⟨hg, f4, f5, f6, f7, f8, f0, f1, f2, f3, acopy⟩
  rw [f4, f5, f6, f7, f8, f0, f1, f2, f3, acopy] at hg
  linear_combination -hg

private theorem region1_complete (a : F × Cell) (self : RegionIndex)
    (env : Placed ProverEnvironment F)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((combinationRegion #[a]).operations self)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((combinationRegion #[a]).operations self) := by
  rw [combinationRegion_1] at hw ⊢
  simp only [region1, stamp, Arithmetic.nativeGate, circuit_norm] at hw ⊢
  rcases hw with ⟨hr, avalue, f4, f5, f6, f7, f8, f0, f1, f2, f3⟩
  simp only [hr, avalue, f4, f5, f6, f7, f8, f0, f1, f2, f3, and_self, and_true]
  ring

private def region2 (a b : F × Cell) : RegionCircuit F Cell := do
  let result ← assignAdvice ⟨0⟩ 0 (.ofFExpr (.const 0 + .const a.1 * .expr a.2 + .const b.1 * .expr b.2))
  let acopy ← assignAdvice ⟨1⟩ 0 (.ofFExpr (.expr a.2))
  let bcopy ← assignAdvice ⟨2⟩ 0 (.ofFExpr (.expr b.2))
  stamp ⟨a.1, b.1, 0, 0⟩
  constrainEqual acopy a.2
  constrainEqual bcopy b.2
  return result

private theorem combinationRegion_2 (a b : F × Cell) :
    combinationRegion #[a, b] = region2 a b := by
  funext self
  unfold combinationRegion WitnessCircuit.linearAux WitnessCircuit.custom
    WitnessCircuit.enable region2 stamp
  simp only [Arithmetic.activation_zero]
  cbv

private theorem region2_sound (a b : F × Cell) (self : RegionIndex)
    (env : Placed Environment F)
    (hc : RegionOperations.Constraints env.place self env.env
      ((combinationRegion #[a, b]).operations self)) :
    AssignedCell.eval env.place env.env ((combinationRegion #[a, b]).output self) =
      dot env #[a, b] := by
  rw [combinationRegion_2] at hc ⊢
  simp only [region2, stamp, Arithmetic.nativeGate, dot, circuit_norm,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc ⊢
  rcases hc with ⟨hg, f4, f5, f6, f7, f8, f0, f1, f2, f3, acopy, bcopy⟩
  rw [f4, f5, f6, f7, f8, f0, f1, f2, f3, acopy, bcopy] at hg
  linear_combination -hg

private theorem region2_complete (a b : F × Cell) (self : RegionIndex)
    (env : Placed ProverEnvironment F)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((combinationRegion #[a, b]).operations self)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((combinationRegion #[a, b]).operations self) := by
  rw [combinationRegion_2] at hw ⊢
  simp only [region2, stamp, Arithmetic.nativeGate, circuit_norm] at hw ⊢
  rcases hw with ⟨hr, avalue, bvalue, f4, f5, f6, f7, f8, f0, f1, f2, f3⟩
  simp only [hr, avalue, bvalue, f4, f5, f6, f7, f8, f0, f1, f2, f3, and_self, and_true]
  ring

private def region3 (a b c : F × Cell) : RegionCircuit F Cell := do
  let result ← assignAdvice ⟨0⟩ 0 (.ofFExpr (.const 0 + .const a.1 * .expr a.2 + .const b.1 * .expr b.2 + .const c.1 * .expr c.2))
  let acopy ← assignAdvice ⟨1⟩ 0 (.ofFExpr (.expr a.2))
  let bcopy ← assignAdvice ⟨2⟩ 0 (.ofFExpr (.expr b.2))
  let ccopy ← assignAdvice ⟨3⟩ 0 (.ofFExpr (.expr c.2))
  stamp ⟨a.1, b.1, c.1, 0⟩
  constrainEqual acopy a.2
  constrainEqual bcopy b.2
  constrainEqual ccopy c.2
  return result

private theorem combinationRegion_3 (a b c : F × Cell) :
    combinationRegion #[a, b, c] = region3 a b c := by
  funext self
  unfold combinationRegion WitnessCircuit.linearAux WitnessCircuit.custom
    WitnessCircuit.enable region3 stamp
  simp only [Arithmetic.activation_zero]
  cbv

private theorem region3_sound (a b c : F × Cell) (self : RegionIndex)
    (env : Placed Environment F)
    (hc : RegionOperations.Constraints env.place self env.env
      ((combinationRegion #[a, b, c]).operations self)) :
    AssignedCell.eval env.place env.env ((combinationRegion #[a, b, c]).output self) =
      dot env #[a, b, c] := by
  rw [combinationRegion_3] at hc ⊢
  simp only [region3, stamp, Arithmetic.nativeGate, dot, circuit_norm,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc ⊢
  rcases hc with ⟨hg, f4, f5, f6, f7, f8, f0, f1, f2, f3, acopy, bcopy, ccopy⟩
  rw [f4, f5, f6, f7, f8, f0, f1, f2, f3, acopy, bcopy, ccopy] at hg
  linear_combination -hg

private theorem region3_complete (a b c : F × Cell) (self : RegionIndex)
    (env : Placed ProverEnvironment F)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((combinationRegion #[a, b, c]).operations self)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((combinationRegion #[a, b, c]).operations self) := by
  rw [combinationRegion_3] at hw ⊢
  simp only [region3, stamp, Arithmetic.nativeGate, circuit_norm] at hw ⊢
  rcases hw with ⟨hr, avalue, bvalue, cvalue, f4, f5, f6, f7, f8, f0, f1, f2, f3⟩
  simp only [hr, avalue, bvalue, cvalue, f4, f5, f6, f7, f8, f0, f1, f2, f3, and_self, and_true]
  ring

private theorem combinationRegion_4 (a b c d : F × Cell) :
    combinationRegion #[a, b, c, d] =
      Arithmetic.synthesize ⟨a.1, b.1, c.1, d.1⟩ 0 () 0 ⟨a.2, b.2, c.2, d.2⟩ := by
  funext self
  unfold combinationRegion WitnessCircuit.linearAux WitnessCircuit.custom
    WitnessCircuit.enable Arithmetic.synthesize Arithmetic.linearWitness
  simp only [Arithmetic.activation_zero]
  cbv

private theorem region4_sound (a b c d : F × Cell) (self : RegionIndex)
    (env : Placed Environment F)
    (hc : RegionOperations.Constraints env.place self env.env
      ((combinationRegion #[a, b, c, d]).operations self)) :
    AssignedCell.eval env.place env.env ((combinationRegion #[a, b, c, d]).output self) =
      dot env #[a, b, c, d] := by
  rw [combinationRegion_4] at hc ⊢
  have hs := (Arithmetic.linearCombination4 ⟨a.1, b.1, c.1, d.1⟩ 0).soundness
    () 0 self env ⟨a.2, b.2, c.2, d.2⟩ trivial trivial hc
  simp only [ElaboratedRegionCircuit.output_eq] at hs
  simpa [Arithmetic.linearCombination4, Arithmetic.linearValue, dot,
    ElaboratedRegionCircuit.output, circuit_norm,
    add_assoc] using hs

private theorem region4_complete (a b c d : F × Cell) (self : RegionIndex)
    (env : Placed ProverEnvironment F)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((combinationRegion #[a, b, c, d]).operations self)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((combinationRegion #[a, b, c, d]).operations self) := by
  rw [combinationRegion_4] at hw ⊢
  exact ((Arithmetic.linearCombination4 ⟨a.1, b.1, c.1, d.1⟩ 0).completeness
    () 0 self env ⟨a.2, b.2, c.2, d.2⟩ hw trivial trivial trivial).1

private theorem small_cases {α : Type} (terms : Array α)
    (hpos : 0 < terms.size) (hsize : terms.size ≤ 4) :
    (∃ a, terms = #[a]) ∨ (∃ a b, terms = #[a,b]) ∨
      (∃ a b c, terms = #[a,b,c]) ∨ (∃ a b c d, terms = #[a,b,c,d]) := by
  rcases terms with ⟨terms⟩
  cases terms with
  | nil => simp at hpos
  | cons a tail =>
    cases tail with
    | nil => exact Or.inl ⟨a, rfl⟩
    | cons b tail =>
      cases tail with
      | nil => exact Or.inr (Or.inl ⟨a,b,rfl⟩)
      | cons c tail =>
        cases tail with
        | nil => exact Or.inr (Or.inr (Or.inl ⟨a,b,c,rfl⟩))
        | cons d tail =>
          cases tail with
          | nil => exact Or.inr (Or.inr (Or.inr ⟨a,b,c,d,rfl⟩))
          | cons e tail => simp at hsize; omega

/-- Arbitrary coefficients and cell references, for every nonempty one-row
source auxiliary (one through four surviving terms). -/
theorem combinationRegion_sound (terms : Array (F × Cell))
    (hpos : 0 < terms.size) (hsize : terms.size ≤ 4)
    (self : RegionIndex) (env : Placed Environment F)
    (hc : RegionOperations.Constraints env.place self env.env
      ((combinationRegion terms).operations self)) :
    AssignedCell.eval env.place env.env ((combinationRegion terms).output self) = dot env terms := by
  rcases small_cases terms hpos hsize with ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ | ⟨a,b,c,d,rfl⟩
  · exact region1_sound a self env hc
  · exact region2_sound a b self env hc
  · exact region3_sound a b c self env hc
  · exact region4_sound a b c d self env hc

theorem combinationRegion_complete (terms : Array (F × Cell))
    (hpos : 0 < terms.size) (hsize : terms.size ≤ 4)
    (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((combinationRegion terms).operations self)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((combinationRegion terms).operations self) := by
  rcases small_cases terms hpos hsize with ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ | ⟨a,b,c,d,rfl⟩
  · exact region1_complete a self env hw
  · exact region2_complete a b self env hw
  · exact region3_complete a b c self env hw
  · exact region4_complete a b c d self env hw

/-- Native shortcuts after the cached zero has been retrieved. -/
def finish (zero : Cell) (terms : Array (F × Cell)) : Circuit F Cell := do
  if terms.isEmpty then return zero
  if terms.size == 1 && terms[0]!.1 == 1 then return terms[0]!.2
  assignRegion "Linear combination" (combinationRegion terms)

theorem finish_sound (zero : Cell) (terms : Array (F × Cell))
    (hsize : terms.size ≤ 4) (self : RegionIndex) (env : Placed Environment F)
    (hzero : AssignedCell.eval env.place env.env zero = 0)
    (hc : Constraints env.place env.env ((finish zero terms).operations self) self) :
    AssignedCell.eval env.place env.env ((finish zero terms).output self) = dot env terms := by
  cases he : terms.isEmpty with
  | true =>
    have ht := Array.empty_of_isEmpty he
    subst terms
    simpa [finish, dot, circuit_norm] using hzero
  | false =>
    have hpos : 0 < terms.size := by
      have hn : terms.size ≠ 0 := by
        intro h
        have ht := Array.size_eq_zero_iff.mp h
        subst terms
        contradiction
      omega
    cases hs : (terms.size == 1 && terms[0]!.1 == 1) with
    | true =>
      have hp : terms.size = 1 ∧ terms[0]!.1 = 1 := by simpa using hs
      rcases Array.size_eq_one_iff.mp hp.1 with ⟨a, rfl⟩
      have hv : a.1 = 1 := by simpa using hp.2
      simp [finish, hv, dot, circuit_norm]
    | false =>
      simp only [finish, he, hs, Bool.false_eq_true, ↓reduceIte, circuit_norm] at hc ⊢
      exact combinationRegion_sound terms hpos hsize self env hc

theorem finish_complete (zero : Cell) (terms : Array (F × Cell))
    (hsize : terms.size ≤ 4) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hw : ExtendsWitnesses env.place env.env ((finish zero terms).operations self) self) :
    Constraints env.place env.env.toEnvironment ((finish zero terms).operations self) self := by
  cases he : terms.isEmpty with
  | true => simp only [finish, he, ↓reduceIte, circuit_norm]
  | false =>
    have hpos : 0 < terms.size := by
      have hn : terms.size ≠ 0 := by
        intro h
        have ht := Array.size_eq_zero_iff.mp h
        subst terms
        contradiction
      omega
    cases hs : (terms.size == 1 && terms[0]!.1 == 1) with
    | true => simp only [finish, he, hs, Bool.false_eq_true, ↓reduceIte, circuit_norm]
    | false =>
      simp only [finish, he, hs, Bool.false_eq_true, ↓reduceIte, circuit_norm] at hw ⊢
      exact combinationRegion_complete terms hpos hsize self env hw

/-- Separates the actual cache transition from the actual arithmetic continuation;
no operation is discarded and the returned state is the source state. -/
theorem linearCombination_run_finish (input : Array (F × Cell)) (cache : Cache) :
    (WitnessCircuit.linearCombination input).run cache = do
      let (zero, nextCache) ← (WitnessCircuit.constant 0).run cache
      let result ← finish zero (filtered zero input)
      return (result, nextCache) := by
  rw [linearCombination_run]
  funext self
  dsimp only [bind, pure]
  unfold finish
  split
  · rfl
  · dsimp only [bind, pure]
    split <;> rfl

/-- The cache helper's returned region index is exactly its emitted region count. -/
theorem constant_nextRegionIndex (n : Nat) (cache : Cache) (self : RegionIndex) :
    ((WitnessCircuit.constant n).run cache).nextRegionIndex self =
      self + (((WitnessCircuit.constant n).run cache).operations self).regionCount := by
  rw [constant_run]
  cases cache.find? (fun entry => entry.1 == (n : F).val) with
  | some entry =>
    rcases entry with ⟨key, cell⟩
    simp only [circuit_norm, Operations.regionCount, Nat.add_zero]
  | none => simp only [circuit_norm, Operations.regionCount]

/-- Full source helper soundness, including cache hits/misses, zero-coefficient
and cached-zero address filtering, both shortcuts, and every one-row arithmetic
region. No equality of advice values is used to shortcut an advice assignment. -/
theorem linearCombination_sound (input : Array (F × Cell)) (hsize : input.size ≤ 4)
    (cache : Cache) (self : RegionIndex) (env : Placed Environment F)
    (hcache : CacheMeaning env cache)
    (hc : Constraints env.place env.env
      (((WitnessCircuit.linearCombination input).run cache).operations self) self) :
    let output := ((WitnessCircuit.linearCombination input).run cache).output self
    AssignedCell.eval env.place env.env output.1 = dot env input ∧ CacheMeaning env output.2 := by
  rw [linearCombination_run_finish] at hc ⊢
  simp only [circuit_norm] at hc ⊢
  rw [← constant_nextRegionIndex] at hc
  rcases hc with ⟨hc0, hcrest⟩
  obtain ⟨hzero, hnext⟩ := constant_sound 0 cache self env hcache hc0
  simp only [Nat.cast_zero] at hzero
  refine ⟨?_, hnext⟩
  exact (finish_sound _ _ (Array.size_filter_le.trans hsize) _ env hzero hcrest).trans
    (dot_filter env _ hzero input)

/-- Honest source witness completeness. CacheMeaning is needed only for the
postcondition, not for satisfaction of the emitted constraints: the arithmetic
witnesses read the exact cells that are copied by the source. -/
theorem linearCombination_constraints_of_witnesses
    (input : Array (F × Cell)) (hsize : input.size ≤ 4)
    (cache : Cache) (self : RegionIndex) (env : Placed ProverEnvironment F)
    (hw : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.linearCombination input).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.linearCombination input).run cache).operations self) self := by
  rw [linearCombination_run_finish] at hw ⊢
  simp only [circuit_norm] at hw ⊢
  rw [← constant_nextRegionIndex] at hw ⊢
  exact ⟨constant_constraints_of_witnesses 0 cache self env hw.1,
    finish_complete _ _ (Array.size_filter_le.trans hsize) _ env hw.2⟩

theorem constant_complete (n : Nat) (cache : Cache) (self : RegionIndex)
    (env : Placed ProverEnvironment F) (hcache : CacheMeaning env.toEnvironment cache)
    (hw : ExtendsWitnesses env.place env.env
      (((WitnessCircuit.constant n).run cache).operations self) self) :
    Constraints env.place env.env.toEnvironment
      (((WitnessCircuit.constant n).run cache).operations self) self ∧
    (let output := ((WitnessCircuit.constant n).run cache).output self
     AssignedCell.eval env.place env.env.toEnvironment output.1 = (n : F) ∧
       CacheMeaning env.toEnvironment output.2) := by
  have hc := constant_constraints_of_witnesses n cache self env hw
  exact ⟨hc, constant_sound n cache self env.toEnvironment hcache hc⟩

end Midnight.SHA256.Semantics.Linear
