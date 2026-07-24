import Clean.Halo2.Keygen.Semantics

/-!
# Selector-compressed gate semantics

Halo 2 replaces every configured selector with a root-finding expression over a
packed fixed column. At a row where a gate is enabled, that expression is nonzero
but need not evaluate to one. Consequently the verifier-side gate polynomial is a
nonzero scalar multiple of Clean's enabled-gate evaluation, not literally equal to
it.

This file isolates the generic algebra. `Expression.GatedBy selector` says that an
expression is linear in its own selector and independent of foreign selectors.
The main theorem then evaluates selector compression as the packed selector scale
times the ordinary enabled-gate valuation.
-/

namespace Halo2

namespace Expression

variable {F : Type} [Field F]

/-- Replace one selector's value while leaving every other query unchanged. -/
def replaceSelectorValue
    (selector : Selector) (value : F) (base : Query → F) : Query → F
  | .selector other =>
      if other.index = selector.index then value
      else base (.selector other)
  | query => base query

/--
The valuation used by Clean for one enabled gate: its own selector is one,
foreign selectors are zero, and ordinary queries retain their supplied values.
-/
def enabledGateValuation
    (selector : Selector) (base : Query → F) : Query → F
  | .selector other =>
      if other.index = selector.index then 1 else 0
  | query => base query

/--
An expression is gated by `selector` when changing that selector to `scale`
multiplies its enabled-gate evaluation by `scale`, independently of all foreign
selector values.
-/
def GatedBy (expression : Expression F Query) (selector : Selector) : Prop :=
  ∀ (base : Query → F) (scale : F),
    expression.eval (replaceSelectorValue selector scale base) =
      scale * expression.eval (enabledGateValuation selector base)

/--
A selector-free expression has the same evaluation under valuations agreeing on
fixed, advice, and instance queries.
-/
theorem eval_eq_of_selectorFree
    (expression : Expression F Query)
    (hfree : expression.SelectorFree)
    (left right : Query → F)
    (hfixed : ∀ column rotation,
      left (.fixed column rotation) = right (.fixed column rotation))
    (hadvice : ∀ column rotation,
      left (.advice column rotation) = right (.advice column rotation))
    (hinstance : ∀ column rotation,
      left (.instance column rotation) = right (.instance column rotation)) :
    expression.eval left = expression.eval right := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          simp [Expression.SelectorFree] at hfree
      | fixed column rotation =>
          exact hfixed column rotation
      | advice column rotation =>
          exact hadvice column rotation
      | «instance» column rotation =>
          exact hinstance column rotation
  | const value => rfl
  | add leftExpression rightExpression ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [eval, ihLeft hfree.1, ihRight hfree.2]
  | mul leftExpression rightExpression ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [eval, ihLeft hfree.1, ihRight hfree.2]

/-- A selector atom is gated by itself. -/
@[circuit_norm]
theorem gatedBy_querySelector (selector : Selector) :
    (querySelector (F := F) selector).GatedBy selector := by
  intro base scale
  simp [querySelector, eval, replaceSelectorValue,
    enabledGateValuation]

/-- Sums of expressions gated by the same selector remain gated. -/
@[circuit_norm]
theorem GatedBy.add
    {selector : Selector} {left right : Expression F Query}
    (hleft : left.GatedBy selector)
    (hright : right.GatedBy selector) :
    (left + right).GatedBy selector := by
  intro base scale
  simp only [GatedBy] at hleft hright ⊢
  simp only [eval, hleft, hright, mul_add]

/-- Multiplying a gated expression on the right by selector-free data preserves gating. -/
@[circuit_norm]
theorem GatedBy.mul_right
    {selector : Selector} {gated free : Expression F Query}
    (hgated : gated.GatedBy selector)
    (hfree : free.SelectorFree) :
    (gated * free).GatedBy selector := by
  intro base scale
  simp only [GatedBy] at hgated ⊢
  simp only [eval, hgated]
  have hfreeEval :
      free.eval (replaceSelectorValue selector scale base) =
        free.eval (enabledGateValuation selector base) := by
    apply eval_eq_of_selectorFree free hfree
    · intro _ _
      rfl
    · intro _ _
      rfl
    · intro _ _
      rfl
  rw [hfreeEval, mul_assoc]

/-- Multiplying selector-free data on the left by a gated expression preserves gating. -/
@[circuit_norm]
theorem GatedBy.mul_left
    {selector : Selector} {free gated : Expression F Query}
    (hfree : free.SelectorFree)
    (hgated : gated.GatedBy selector) :
    (free * gated).GatedBy selector := by
  intro base scale
  simp only [GatedBy] at hgated ⊢
  simp only [eval, hgated]
  have hfreeEval :
      free.eval (replaceSelectorValue selector scale base) =
        free.eval (enabledGateValuation selector base) := by
    apply eval_eq_of_selectorFree free hfree
    · intro _ _
      rfl
    · intro _ _
      rfl
    · intro _ _
      rfl
  rw [hfreeEval]
  ring

/--
Selector compression evaluates a gated expression as the packed selector's
root-finding value times the ordinary enabled-gate evaluation.
-/
theorem eval_substSelectorMap_eq_scale
    (map : ℕ → Option SelCompress)
    (valuation : Query → F)
    (expression : Expression F Query)
    (selector : Selector) (compressed : SelCompress)
    (hgated : expression.GatedBy selector)
    (hmap : map selector.index = some compressed) :
    (substSelectorMap map expression).eval valuation =
      (selReplacement compressed).eval valuation *
        expression.eval (enabledGateValuation selector valuation) := by
  rw [substSelectorMap_eval]
  let scale := (selReplacement compressed).eval valuation
  have hreplace :
      replaceSelectorValue selector scale
          (substValuation map valuation) =
        substValuation map valuation := by
    funext query
    cases query with
    | selector other =>
        by_cases hindex : other.index = selector.index
        · simp [replaceSelectorValue, substValuation, scale,
            hindex, hmap]
        · simp [replaceSelectorValue, hindex]
    | fixed column rotation => rfl
    | advice column rotation => rfl
    | «instance» column rotation => rfl
  have henabled :
      enabledGateValuation selector (substValuation map valuation) =
        enabledGateValuation selector valuation := by
    funext query
    cases query <;> rfl
  calc
    expression.eval (substValuation map valuation) =
        expression.eval
          (replaceSelectorValue selector scale
            (substValuation map valuation)) := by
              rw [hreplace]
    _ = scale * expression.eval
          (enabledGateValuation selector
            (substValuation map valuation)) :=
      hgated _ _
    _ = (selReplacement compressed).eval valuation *
          expression.eval
            (enabledGateValuation selector valuation) := by
      rw [henabled]

/--
If a verifier-side valuation agrees with a Clean environment on ordinary
queries, the enabled-gate valuation evaluates every expression exactly as
Clean's selector-one/foreign-selectors-zero valuation.
-/
theorem eval_enabledGateValuation_eq_queryEval
    (valuation : Query → F) (environment : Environment F)
    (selector : Selector) (row : ℤ)
    (expression : Expression F Query)
    (hfixed : ∀ column rotation,
      valuation (.fixed column rotation) =
        environment.fixed column (row + rotation))
    (hadvice : ∀ column rotation,
      valuation (.advice column rotation) =
        environment.advice column (row + rotation))
    (hinstance : ∀ column rotation,
      valuation (.instance column rotation) =
        environment.inst column (row + rotation)) :
    expression.eval (enabledGateValuation selector valuation) =
      expression.eval
        (Query.eval environment
          (fun index => if index = selector.index then 1 else 0) row) := by
  congr 1
  funext query
  cases query with
  | selector other =>
      simp [enabledGateValuation, Query.eval]
  | fixed column rotation =>
      exact hfixed column rotation
  | advice column rotation =>
      exact hadvice column rotation
  | «instance» column rotation =>
      exact hinstance column rotation

/--
The complete generic row-evaluation bridge for a selector-gated expression:
selector compression contributes only its explicit scale, while fixed, advice,
and instance query values come from the supplied Clean environment.
-/
theorem eval_substSelectorMap_eq_scale_queryEval
    (map : ℕ → Option SelCompress)
    (valuation : Query → F) (environment : Environment F)
    (expression : Expression F Query)
    (selector : Selector) (compressed : SelCompress) (row : ℤ)
    (hgated : expression.GatedBy selector)
    (hmap : map selector.index = some compressed)
    (hfixed : ∀ column rotation,
      valuation (.fixed column rotation) =
        environment.fixed column (row + rotation))
    (hadvice : ∀ column rotation,
      valuation (.advice column rotation) =
        environment.advice column (row + rotation))
    (hinstance : ∀ column rotation,
      valuation (.instance column rotation) =
        environment.inst column (row + rotation)) :
    (substSelectorMap map expression).eval valuation =
      (selReplacement compressed).eval valuation *
        expression.eval
          (Query.eval environment
            (fun index => if index = selector.index then 1 else 0) row) := by
  rw [eval_substSelectorMap_eq_scale map valuation expression
    selector compressed hgated hmap]
  rw [eval_enabledGateValuation_eq_queryEval valuation environment
    selector row expression hfixed hadvice hinstance]

end Expression

/--
Every configured custom-gate polynomial is linear in its own selector and
independent of foreign selectors, as required by selector compression.
-/
def Gate.WellFormed
    {F : Type} [Field F] (gate : Gate F) : Prop :=
  gate.constraints.Forall fun constraint =>
    constraint.poly.GatedBy gate.selector

/--
`Constraints.withSelector` constructs a well-formed gate from selector-free
ungated bodies.
-/
@[circuit_norm]
theorem Gate.wellFormed_of_withSelector
    {F : Type} [Field F]
    (name : String) (selector : Selector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (hfree : constraints.Forall fun constraint =>
      constraint.2.SelectorFree) :
    ({ name := name
       selector := selector
       queriedCells := queriedCells
       constraints := Constraints.withSelector selector constraints
         (List.forall_iff_forall_mem.mp hfree) } :
      Gate F).WellFormed := by
  rw [Gate.WellFormed, List.forall_iff_forall_mem]
  intro constraint hconstraint
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hconstraint
  apply Expression.GatedBy.mul_right
    (Expression.gatedBy_querySelector selector)
  exact List.forall_iff_forall_mem.mp hfree source hsource

def ConstraintSystem.GatesWellFormed
    {F : Type} [Field F] (cs : ConstraintSystem F) : Prop :=
  cs.gates.Forall Gate.WellFormed

namespace ConstraintSystem

variable {F : Type}

@[simp]
theorem queryAdviceIndex_gates
    (cs : ConstraintSystem F) (column : Column .advice)
    (rotation : Rotation) :
    (cs.queryAdviceIndex column rotation).gates = cs.gates := by
  simp only [queryAdviceIndex]
  split <;> rfl

@[simp]
theorem queryFixedIndex_gates
    (cs : ConstraintSystem F) (column : Column .fixed) :
    (cs.queryFixedIndex column).gates = cs.gates := by
  simp only [queryFixedIndex]
  split <;> rfl

@[simp]
theorem queryInstanceIndex_gates
    (cs : ConstraintSystem F) (column : Column .instance)
    (rotation : Rotation) :
    (cs.queryInstanceIndex column rotation).gates = cs.gates := by
  simp only [queryInstanceIndex]
  split <;> rfl

@[simp]
theorem queryAnyIndex_gates
    (cs : ConstraintSystem F) (column : AnyColumn) :
    (cs.queryAnyIndex column).gates = cs.gates := by
  cases column with
  | mk columnType index =>
      cases columnType <;> simp [queryAnyIndex]

@[simp]
theorem registerQueriedCell_gates
    (cs : ConstraintSystem F) (owner : String)
    (cell : Expression F Query) :
    (cs.registerQueriedCell owner cell).gates = cs.gates := by
  cases cell with
  | var query =>
      cases query <;> simp [registerQueriedCell]
  | const value =>
      rfl
  | add left right =>
      rfl
  | mul left right =>
      rfl

@[simp]
theorem registerQueriedCells_gates
    (cs : ConstraintSystem F) (owner : String)
    (cells : List (Expression F Query)) :
    (cs.registerQueriedCells owner cells).gates = cs.gates := by
  unfold registerQueriedCells
  induction cells generalizing cs with
  | nil => rfl
  | cons cell rest ih =>
      rw [List.foldl_cons, ih, registerQueriedCell_gates]

end ConstraintSystem

/-- The empty configure state has no malformed gates. -/
@[circuit_norm]
theorem ConstraintSystem.gatesWellFormed_empty
    {F : Type} [Field F] :
    ({} : ConstraintSystem F).GatesWellFormed := by
  simp [ConstraintSystem.GatesWellFormed]

/-- Registering a gate preserves the invariant exactly when that gate is well formed. -/
@[circuit_norm]
theorem ConstraintSystem.gatesWellFormed_createGate
    {F : Type} [Field F]
    (cs : ConstraintSystem F) (gate : Gate F) :
    ((createGate gate cs).2).GatesWellFormed ↔
      cs.GatesWellFormed ∧ gate.WellFormed := by
  change List.Forall Gate.WellFormed
      ((cs.registerQueriedCells gate.name gate.queriedCells).gates ++
        [gate]) ↔
    List.Forall Gate.WellFormed cs.gates ∧ gate.WellFormed
  rw [ConstraintSystem.registerQueriedCells_gates, List.forall_append]
  simp

namespace Configure

variable {F α β : Type} [Field F]

/--
A configure program preserves gate well-formedness for every incoming constraint
system.  This is the compositional proof interface for nested chip configuration:
the parent circuit need not evaluate the completed configure state.
-/
structure PreservesGateWellFormedness
    (program : Configure F α) : Prop where
  run : ∀ cs, cs.GatesWellFormed →
    (program cs).2.GatesWellFormed

namespace PreservesGateWellFormedness

@[circuit_norm]
theorem pure (value : α) :
    PreservesGateWellFormedness
      (pure value : Configure F α) := by
  constructor
  intro cs hcs
  exact hcs

@[circuit_norm]
theorem bind
    {program : Configure F α} {next : α → Configure F β}
    (hprogram : PreservesGateWellFormedness program)
    (hnext : ∀ value, PreservesGateWellFormedness (next value)) :
    PreservesGateWellFormedness (program >>= next) := by
  constructor
  intro cs hcs
  exact (hnext (program cs).1).run (program cs).2
    (hprogram.run cs hcs)

@[circuit_norm]
theorem map
    (function : α → β) {program : Configure F α}
    (hprogram : PreservesGateWellFormedness program) :
    PreservesGateWellFormedness (function <$> program) := by
  constructor
  intro cs hcs
  exact hprogram.run cs hcs

@[circuit_norm]
theorem adviceColumn :
    PreservesGateWellFormedness
      (Halo2.adviceColumn : Configure F (Column .advice)) := by
  constructor
  intro cs hcs
  exact hcs

@[circuit_norm]
theorem fixedColumn :
    PreservesGateWellFormedness
      (Halo2.fixedColumn : Configure F (Column .fixed)) := by
  constructor
  intro cs hcs
  exact hcs

@[circuit_norm]
theorem instanceColumn :
    PreservesGateWellFormedness
      (Halo2.instanceColumn : Configure F (Column .instance)) := by
  constructor
  intro cs hcs
  exact hcs

@[circuit_norm]
theorem selector :
    PreservesGateWellFormedness
      (Halo2.selector : Configure F Selector) := by
  constructor
  intro cs hcs
  exact hcs

@[circuit_norm]
theorem complexSelector :
    PreservesGateWellFormedness
      (Halo2.complexSelector : Configure F Selector) := by
  constructor
  intro cs hcs
  exact hcs

@[circuit_norm]
theorem enableEquality (column : AnyColumn) :
    PreservesGateWellFormedness
      (Halo2.enableEquality (F := F) column) := by
  constructor
  intro cs hcs
  simpa [Halo2.enableEquality, ConstraintSystem.GatesWellFormed] using hcs

@[circuit_norm]
theorem enableConstant (column : Column .fixed) :
    PreservesGateWellFormedness
      (Halo2.enableConstant (F := F) column) := by
  constructor
  intro cs hcs
  simpa [Halo2.enableConstant, ConstraintSystem.GatesWellFormed] using hcs

@[circuit_norm]
theorem lookupTableColumn :
    PreservesGateWellFormedness
      (Halo2.lookupTableColumn : Configure F TableColumn) :=
  bind fixedColumn fun _ => pure _

@[circuit_norm]
theorem createGate
    (gate : Gate F) (hgate : gate.WellFormed) :
    PreservesGateWellFormedness
      (Halo2.createGate gate) := by
  constructor
  intro cs hcs
  exact (ConstraintSystem.gatesWellFormed_createGate cs gate).2
    ⟨hcs, hgate⟩

/--
The standard leaf-chip configure pattern: allocate one simple selector, register
its locally certified gate, and return the selector-indexed config.
-/
@[circuit_norm]
theorem selectorCreateGate
    (gate : Selector → Gate F) (result : Selector → α)
    (hgate : ∀ selector, (gate selector).WellFormed) :
    PreservesGateWellFormedness (do
      let selector ← Halo2.selector
      Halo2.createGate (gate selector)
      return result selector) :=
  bind selector fun selector =>
    bind (createGate _ (hgate selector)) fun _ =>
      pure _

/-- Run a preserving configure program from Halo 2's empty initial state. -/
theorem fromEmpty
    {program : Configure F α}
    (hprogram : PreservesGateWellFormedness program) :
    (program {}).2.GatesWellFormed :=
  hprogram.run {} ConstraintSystem.gatesWellFormed_empty

@[circuit_norm]
theorem lookup
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn)) :
    PreservesGateWellFormedness
      (Halo2.lookup queriedCells tableMap) := by
  constructor
  intro cs hcs
  simp only [Halo2.lookup, ConstraintSystem.GatesWellFormed]
  have registerTableGates
      (state : ConstraintSystem F)
      (entries : List (Expression F Query × TableColumn)) :
      (entries.foldl
        (fun state entry =>
          state.queryFixedIndex entry.2.inner)
        state).gates = state.gates := by
    induction entries generalizing state with
    | nil => rfl
    | cons entry rest ih =>
        rw [List.foldl_cons, ih,
          ConstraintSystem.queryFixedIndex_gates]
  simpa [registerTableGates] using hcs

end PreservesGateWellFormedness

end Configure

namespace ConstraintSystem.GatesWellFormed

variable {F : Type} [Field F]

/-- A well-formed configured gate supplies gating for each of its constraints. -/
theorem constraint
    {cs : ConstraintSystem F} (hwellFormed : cs.GatesWellFormed)
    {gate : Gate F} (hgate : gate ∈ cs.gates)
    {constraint : Constraint F}
    (hconstraint : constraint ∈ gate.constraints) :
    constraint.poly.GatedBy gate.selector := by
  have hgateWellFormed :=
    List.forall_iff_forall_mem.mp hwellFormed gate hgate
  exact List.forall_iff_forall_mem.mp
    hgateWellFormed constraint hconstraint

end ConstraintSystem.GatesWellFormed

end Halo2
