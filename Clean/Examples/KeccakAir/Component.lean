/-
Plonky3's Keccak-f AIR as a two-row component. The circuit asserts the AIR's constraints, written
once in `Clean.Examples.KeccakAir.Air` for expressions and values, and its soundness is
`windowSpec_of_constraints`. Along a table, each row's spec gives the next row the invariant it
assumes: the step flags of a round `r`, and the state after `r` rounds of the row's preimage.
-/
module

public import Clean.Examples.KeccakAir.Soundness
public import Clean.Examples.KeccakAir.Witness
public import Clean.Air.FlatEnsemble

@[expose] public section

namespace KeccakAir
open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- Assert that every expression is zero. -/
def assertZeros (constraints : List (Expression (F p))) : Circuit (F p) Unit := fun _ =>
  ((), constraints.map Operation.assert)

section AssertZeros
variable (constraints : List (Expression (F p))) (offset : ℕ)

lemma assertZeros_localLength : Operations.localLength (constraints.map Operation.assert) = 0 := by
  induction constraints with
  | nil => rfl
  | cons _ _ ih => simpa [Operations.localLength] using ih

lemma assertZeros_forAll (condition : Condition (F p)) :
    Operations.forAll offset condition (constraints.map Operation.assert) ↔
      ∀ e ∈ constraints, condition.assert offset e := by
  induction constraints with
  | nil => simp [Operations.forAll]
  | cons _ _ ih => simp [Operations.forAll, ih]

lemma assertZeros_forAllNoOffset (condition : ConditionNoOffset (F p)) :
    Operations.forAllNoOffset condition (constraints.map Operation.assert) ↔
      ∀ e ∈ constraints, condition.assert e := by
  induction constraints with
  | nil => simp [Operations.forAllNoOffset]
  | cons _ _ ih => simp [Operations.forAllNoOffset, ih]

lemma assertZeros_interactions :
    Operations.interactions (constraints.map Operation.assert) = [] := by
  induction constraints with
  | nil => rfl
  | cons _ _ ih => simpa [Operations.interactions] using ih

end AssertZeros

lemma getElem_map_fin {α β : Type} {n : ℕ} (f : α → β) (v : Vector α n) (i : Fin n) :
    (v.map f)[i] = f v[i] := by
  simp

section Eval
variable (env : Environment (F p))

lemma eval_add (x y : Expression (F p)) : (x + y).eval env = x.eval env + y.eval env := rfl

lemma eval_mul (x y : Expression (F p)) : (x * y).eval env = x.eval env * y.eval env := rfl

lemma eval_sub (x y : Expression (F p)) : (x - y).eval env = x.eval env - y.eval env := by
  change x.eval env + -1 * y.eval env = _
  ring

lemma eval_one : (1 : Expression (F p)).eval env = 1 := rfl

lemma eval_two : (2 : Expression (F p)).eval env = 2 := rfl

lemma eval_four : (4 : Expression (F p)).eval env = 4 := rfl

lemma eval_boolCheck (x : Expression (F p)) : (boolCheck x).eval env = boolCheck (x.eval env) := by
  simp only [boolCheck, eval_mul, eval_sub, eval_one]

lemma eval_xor (x y : Expression (F p)) : (xor x y).eval env = xor (x.eval env) (y.eval env) := by
  simp only [xor, eval_add, eval_mul, eval_sub, eval_two]

lemma eval_andn (x y : Expression (F p)) :
    (andn x y).eval env = andn (x.eval env) (y.eval env) := by
  simp only [andn, eval_mul, eval_sub, eval_one]

lemma eval_horner (bit : Fin 16 → Expression (F p)) (n : ℕ) :
    (horner bit n).eval env = horner (fun k => (bit k).eval env) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [horner, eval_add, eval_mul, eval_two, ih]

lemma eval_limbOf (bit : Fin 64 → Expression (F p)) (limb : Fin 4) :
    (limbOf bit limb).eval env = limbOf (fun z => (bit z).eval env) limb := by
  simp only [limbOf, eval_horner]

lemma eval_iotaBit (flags : Vector (Expression (F p)) 24) (bit : Expression (F p)) (z : Fin 64) :
    (iotaBit flags bit z).eval env =
      iotaBit (flags.map (Expression.eval env)) (bit.eval env) z := by
  have hfold (rounds : List (Fin 24)) (sum : Expression (F p)) :
      (rounds.foldl (fun sum (r : Fin 24) => sum + flags[r]) sum).eval env =
        rounds.foldl (fun sum (r : Fin 24) => sum + (flags.map (Expression.eval env))[r])
          (sum.eval env) := by
    induction rounds generalizing sum with
    | nil => rfl
    | cons r rounds ih => simp only [List.foldl_cons, ih, eval_add, getElem_map_fin]
  unfold iotaBit
  split
  · rfl
  · simp only [eval_xor, hfold, getElem_map_fin]

lemma eval_transitionInPermutation (window : Window Row (Expression (F p))) :
    (transitionInPermutation window).eval env =
      transitionInPermutation (mapWindow (Expression.eval env) window) := by
  simp [transitionInPermutation, mapWindow, eval_mul, eval_sub, eval_one]

/-- The values of the constraints are the constraints of the values. -/
theorem map_eval_constraints (window : Window Row (Expression (F p))) :
    (constraints window).map (Expression.eval env) =
      constraints (mapWindow (Expression.eval env) window) := by
  simp only [constraints, roundFlagConstraints, preimageConstraints, exportConstraints,
    thetaColumnConstraints, thetaConstraints, parityConstraints, chiConstraints, iotaConstraints,
    outputConstraints, List.map_append, List.map_cons, List.map_nil, List.map_flatMap,
    List.map_map, Function.comp_def, eval_add, eval_mul, eval_sub, eval_one, eval_two,
    eval_four, eval_boolCheck, eval_xor, eval_andn, eval_limbOf, eval_iotaBit,
    eval_transitionInPermutation]
  simp [mapWindow, eval_xor]

lemma eval_window (window : Var (Window Row) (F p)) :
    eval env window = mapWindow (Expression.eval env) window := by
  obtain ⟨⟨⟩, ⟨⟩, _, _, _⟩ := window
  simp only [circuit_norm, mapWindow, Row.map]

end Eval

instance elaborated : ElaboratedCircuit (F p) (Window Row) unit
    (fun window => assertZeros (constraints window)) where
  localLength _ := 0
  localLength_eq _ _ := assertZeros_localLength _
  output _ _ := ()
  subcircuitsConsistent _ _ := by
    simp [Operations.SubcircuitsConsistent, assertZeros, Circuit.operations, assertZeros_forAll]
  channelsLawful := by
    simp only [ElaboratedCircuit.ChannelsLawful]
    intro window offset
    simp [assertZeros, Circuit.operations, Operations.ChannelsLawful,
      Operations.subcircuitChannelsWithGuarantees, Operations.InChannelsOrGuarantees,
      Operations.subcircuitChannelsLawful_iff_forAllNoOffset, assertZeros_forAllNoOffset,
      Function.comp_def]

/-- The constraints of a window, as expressions, hold if and only if the constraints of the
window's values hold. -/
lemma constraints_eval_iff (env : Environment (F p)) (window : Var (Window Row) (F p)) :
    (∀ e ∈ constraints window, env e = 0) ↔ ∀ e ∈ constraints (eval env window), e = 0 := by
  rw [eval_window, ← map_eval_constraints, List.forall_mem_map]

variable [large : Fact (2 ^ 16 < p)]

/-- One window of Plonky3's Keccak-f AIR. A row may assume that it carries the permutation's state
along unless it is the first row, and then computes a round of Keccak-f. -/
def circuit : GeneralFormalCircuit (F p) (Window Row) unit where
  name := "keccak"
  main window := assertZeros (constraints window)
  elaborated := elaborated
  Assumptions window _ := window.isFirstRow = 1 ∨ Carried window.current
  Spec window _ _ := WindowSpec window
  -- the honest prover's rows satisfy the constraints
  ProverAssumptions window _ _ := ∀ e ∈ constraints window, e = 0
  requirementsChannelsLawful _ _ := by
    simp [assertZeros, Circuit.operations, Operations.RequirementsChannelsLawful,
      Operations.subcircuitChannelsWithRequirements, Operations.InChannelsOrRequirements,
      Operations.shallowChannels, assertZeros_forAllNoOffset, Function.comp_def]
  soundness := by
    intro offset env window_var window h_input h_assumptions h_holds
    simp only [assertZeros, Circuit.operations, ConstraintsHold.Soundness,
      assertZeros_forAllNoOffset] at h_holds
    refine ⟨?_, ?_⟩
    · rw [constraints_eval_iff, h_input] at h_holds
      exact windowSpec_of_constraints large.elim window h_holds h_assumptions
    · simp [assertZeros, Circuit.operations, Operations.Requirements, assertZeros_forAllNoOffset]
  completeness := by
    intro offset env window_var _ window h_input h_assumptions
    simp only [assertZeros, Circuit.operations, ConstraintsHold.Completeness,
      assertZeros_forAllNoOffset]
    refine ⟨?_, trivial⟩
    rw [constraints_eval_iff, ← CircuitType.eval_var_prover_to_verifier, h_input]
    exact h_assumptions

/-- The Keccak-f AIR with `height` rows. The fixed columns are empty and only fix the height. The
rows are computed by `Witness.program`, 24 per permutation, whose inputs are the rows of the
prover's hint table `keccak`. -/
def component (height : UInt64) : Component (F p) where
  circuit := circuit
  fixedColumns := some { Row := unit, row _ := pure (), height }
  window := Window.layout Row
  circuit_assumptions_of_assumptions := by
    rintro i window data - - previous -
    rcases previous _ rfl with h_first | ⟨previous, output, h_next, h_transition, h_spec⟩
    · left
      simpa using h_first
    · right
      simp only [Window.layout_next, Window.layout_current, Window.layout_isTransition]
        at h_next h_transition
      have h_next : previous.next = window.current := by
        simpa only [ProvableType.fromElements_toElements] using congrArg fromElements h_next
      rw [← h_next]
      exact carried_of_windowSpec h_spec h_transition
  generation := .segments Witness.program

end KeccakAir
