/-
Plonky3's Keccak-f AIR as a two-row component. The circuit asserts the AIR's constraints, written
once in `Clean.Examples.KeccakAir.Air` for expressions and values, and its soundness is
`windowSpec_of_constraints`. Along a table, each row's spec gives the next row the invariant it
assumes: the step flags of a round `r`, and the state after `r` rounds of the row's preimage.
-/
module

public import Clean.Examples.KeccakAir.Soundness
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

section Map
variable {α β : Type} [Add α] [Sub α] [Mul α] [OfNat α 1] [OfNat α 2] [OfNat α 4]
  [Add β] [Sub β] [Mul β] [OfNat β 1] [OfNat β 2] [OfNat β 4]

/-- A map that commutes with the operations the constraints are written in. -/
structure IsHom (f : α → β) : Prop where
  add : ∀ x y, f (x + y) = f x + f y
  sub : ∀ x y, f (x - y) = f x - f y
  mul : ∀ x y, f (x * y) = f x * f y
  one : f 1 = 1
  two : f 2 = 2
  four : f 4 = 4

namespace IsHom
variable {f : α → β} (hf : IsHom f)
include hf

lemma map_boolCheck (x : α) : f (boolCheck x) = boolCheck (f x) := by
  simp only [boolCheck, hf.mul, hf.sub, hf.one]

lemma map_xor (x y : α) : f (xor x y) = xor (f x) (f y) := by
  simp only [xor, hf.add, hf.mul, hf.sub, hf.two]

lemma map_andn (x y : α) : f (andn x y) = andn (f x) (f y) := by
  simp only [andn, hf.mul, hf.sub, hf.one]

lemma map_horner (bit : Fin 16 → α) (n : ℕ) :
    f (horner bit n) = horner (fun k => f (bit k)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [horner, hf.add, hf.mul, hf.two, ih]

lemma map_limbOf (bit : Fin 64 → α) (limb : Fin 4) :
    f (limbOf bit limb) = limbOf (fun z => f (bit z)) limb := by
  simp only [limbOf, hf.map_horner]

lemma map_iotaBit (flags : Vector α 24) (bit : α) (z : Fin 64) :
    f (iotaBit flags bit z) = iotaBit (flags.map f) (f bit) z := by
  have hfold (rounds : List (Fin 24)) (sum : α) :
      f (rounds.foldl (fun sum (r : Fin 24) => sum + flags[r]) sum) =
        rounds.foldl (fun sum (r : Fin 24) => sum + (flags.map f)[r]) (f sum) := by
    induction rounds generalizing sum with
    | nil => rfl
    | cons r rounds ih => simp only [List.foldl_cons, ih, hf.add, getElem_map_fin]
  unfold iotaBit
  split
  · rfl
  · simp only [hf.map_xor, hfold, getElem_map_fin]

lemma map_transitionInPermutation (window : Window Row α) :
    f (transitionInPermutation window) = transitionInPermutation (mapWindow f window) := by
  simp [transitionInPermutation, mapWindow, hf.mul, hf.sub, hf.one]

/-- The images of the constraints are the constraints of the images. -/
theorem map_constraints (window : Window Row α) :
    (constraints window).map f = constraints (mapWindow f window) := by
  simp only [constraints, roundFlagConstraints, preimageConstraints, exportConstraints,
    thetaColumnConstraints, thetaConstraints, parityConstraints, chiConstraints, iotaConstraints,
    outputConstraints, List.map_append, List.map_cons, List.map_nil, List.map_flatMap,
    List.map_map, Function.comp_def, hf.add, hf.mul, hf.sub, hf.one, hf.two, hf.four,
    hf.map_boolCheck, hf.map_xor, hf.map_andn, hf.map_limbOf, hf.map_iotaBit,
    hf.map_transitionInPermutation]
  simp [mapWindow, hf.map_xor]

end IsHom
end Map

section Eval
variable (env : Environment (F p))

lemma eval_sub (x y : Expression (F p)) : (x - y).eval env = x.eval env - y.eval env := by
  change x.eval env + -1 * y.eval env = _
  ring

/-- Evaluation commutes with the operations of the constraints. -/
lemma isHom_eval : IsHom (Expression.eval (F := F p) env) :=
  ⟨fun _ _ => rfl, eval_sub env, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The values of the constraints are the constraints of the values. -/
theorem map_eval_constraints (window : Window Row (Expression (F p))) :
    (constraints window).map (Expression.eval env) =
      constraints (mapWindow (Expression.eval env) window) :=
  (isHom_eval env).map_constraints window

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

/-- The Keccak-f AIR with `height` rows. The fixed columns are empty and only fix the height. Each
row is copied from the prover's hint table `keccak`, which holds the trace. -/
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
  generation := .preallocated {
    Row
    row i := pure (fromElements (Vector.ofFn fun j => .hintGet "keccak" (size Row) i j))
    valid := by
      simp [Witgen.M.ValidForRow, pure, ProvableType.toElements_fromElements,
        Witgen.VExpr.validForRow, Witgen.FExpr.validForRow, Witgen.U64Expr.validForRow,
        Witgen.RowProgram.Source.allowsHints]
    counters := [] }

end KeccakAir
