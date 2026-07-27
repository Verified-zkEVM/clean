import Clean.Halo2.Configure
import Clean.Halo2.Provable
import Clean.Halo2.WitnessIR

/-!
# Halo2 synthesize-layer operations — DESIGN SKETCH

Port of the operation layer of `Clean/Circuit/Operations.lean` to halo2. Two levels of
operations, mirroring Rust's two synthesize APIs:

- Region level (Rust `Region<F>` methods): assignments, copies, gate enables — all at
  region-local rows. Region-level gadget composition (e.g.
  `add_incomplete.assign_region(…, offset, region)` called inside variable-base mul's
  big region) is row-offset-shifted, exactly Clean's offset-generic subcircuit pattern
  at row granularity.
- Layouter level (Rust `Layouter<F>`): creating regions, instance-column copies.
  Regions get indices from a threaded counter (prefix-computable, like Clean's offset);
  their *placement* `place : RegionIndex → ℕ` is a semantics parameter, computed at top
  level by the floor planner.

**The subcircuit mechanism** exists at *both* levels — it is what makes parent proofs
scale by isolating them from child circuit internals. Unlike main Clean (and per issue
Verified-zkEVM/clean#358), there is no `Subcircuit` type and no dedicated operation: a
subcircuit call simply *appends the child's operation list* (the monad's `bind` produces
`++`), so the operation enums are plain non-recursive lists. The proof boundary is not a
constructor but a *folded term*: the child ops appear in parent hypotheses as
`Constraints … ((child.call …).operations i)` with the list folded behind the
formal-circuit constant, isolated by the `constraints_append`/`regionCount_append`
lemma family. Consequences:

- There is a single ground-truth `Constraints` predicate. A subcircuit's constraints
  appear in parent hypotheses as one *opaque chunk* — never spilled into the parent's
  conjunction, because the folded call constant blocks list reduction.
- The contracts (`Spec`/`Assumptions`/prover variants) live on the formal-circuit
  packages, which provide per-circuit *forward lemmas*
  (`Constraints chunk → (Assumptions → Spec)` for soundness; the reverse direction for
  completeness). A custom tactic (`subcircuit_rw`) applies them — rewriting hypotheses
  to the weaker but higher-level spec form, which simp fundamentally cannot do. This
  replaces main Clean's `ConstraintsHold.Soundness`/`.Completeness` predicate variants.
- A layouter-level call advances the region counter by the child list's `regionCount`
  (per-circuit lemmas evaluate it to a literal); a region-level call contributes ops in
  the ambient region.
  TODO: the `SubcircuitsConsistent` discipline (cells in child ops reference the
  ambient region, by construction of the monad) ports with the formal-circuit layer.

Other key design points:

- **`enableGate` is itself subcircuit-like**: one operation that records the selector
  activation (for layout/VK compilation) *and* carries the gate's constraints (for
  semantics), so the semantics never needs the global `ConstraintSystem` threaded
  through. The bridge to the compiled CS's `∀ rows, guard·poly = 0` view is a
  once-per-circuit lemma at the VK boundary.
- **Assignments are witness-only**: `assignAdvice` creates a cell and its witness
  program (witgen IR over cell atoms; `.native` is the escape hatch); it adds no
  constraint. Copies and gate enables are the constraints.
- Lookups add no per-region operation: lookup arguments are CS-global and hold at every
  row. TODO: their satisfaction enters the top-level semantics with the lookup port.
- TODO: `Requirements`-style well-formedness (row bounds, no double assignment).

Rust reference: `halo2_proofs/src/circuit.rs` (`Region`, `Layouter`, `Cell`).
-/

namespace Halo2

variable {F : Type}

/-- An operation inside a region, at region-local rows. A region-level subcircuit call
appends the child fragment's operations (sharing the caller's region). Consistency of
subcircuit cells with the ambient region (`SubcircuitsConsistent` in main Clean) is
maintained by the circuit monad and ported with the formal-circuit layer. -/
inductive RegionOperation (F : Type) where
  /-- Witness a value into an advice cell at a local row. Rust: `region.assign_advice`.
  Adds no constraint. -/
  | assignAdvice : Column .advice → ℕ → WitgenIR F 1 → RegionOperation F
  /-- Assign a fixed cell. Rust: `region.assign_fixed`. Pins the fixed column's value
  (fixed values are circuit data; the assignment is checked by the semantics and feeds
  the VK's fixed columns). -/
  | assignFixed : Column .fixed → ℕ → F → RegionOperation F
  /-- Enable a gate at a local row. Rust: `selector.enable(region, offset)`. Records the
  activation of `gate.selector` and carries `gate.constraints` for semantics. -/
  | enableGate : Gate F → ℕ → RegionOperation F
  /-- Enable a lookup argument at a local row (the dual of `enableGate`). There is no
  single Rust method: a gadget "enables a lookup at a row" by enabling the complex
  selector(s) its input expressions are gated on; in the port
  `enableLookup arg enabled row` is the sugar the gadget's `synthesize` emits alongside
  those `enable`s. Carries the registered `LookupArgument` (its input/table tuples) for
  semantics plus `enabled`, the selectors turned on at *this* row. Unlike a gate — whose
  polynomials only ever contain its own single selector — a lookup input's gating
  selectors genuinely vary per enabled row (range-check: `q_lookup = 1` at every
  participating row, but `q_running` is 1 only at running-sum rows and 0 at short rows,
  selecting *which* word is looked up — `lookup-design.md` §1.4). So the activation
  valuation is the per-row `enabled ↦ 1, rest ↦ 0`, not a fixed own-selector device. -/
  | enableLookup : LookupArgument F → List Selector → ℕ → RegionOperation F
  /-- Copy constraint between two (possibly cross-region) cells.
  Rust: `region.constrain_equal`. -/
  | constrainEqual : Cell → Cell → RegionOperation F
  /-- Copy constraint against the constants column. Rust: `region.constrain_constant`. -/
  | constrainConstant : Cell → F → RegionOperation F
  /-- Copy constraint between a cell and an instance-column row, recorded inside the
  region (Rust: the copy half of `region.assign_advice_from_instance`). The instance row
  is absolute. Rust's fused `assign_advice_from_instance` is monad sugar — an
  `assignAdvice` witnessing the instance value plus this copy; see `Basic.lean`. -/
  | constrainInstance : Cell → Column .instance → ℕ → RegionOperation F

abbrev RegionOperations (F : Type) := List (RegionOperation F)

/-- A layouter-level operation: regions, instance copies, table loads. Subcircuit calls
contribute no operation of their own — they append the child gadget's operations. -/
inductive Operation (F : Type) where
  /-- A named region containing region-level operations. The region's index is not
  stored: like Clean's offsets, indices are recomputed by the semantics while folding. -/
  | region : String → RegionOperations F → Operation F
  /-- Copy constraint between a cell and an instance-column row.
  Rust: `layouter.constrain_instance`. -/
  | constrainInstance : Cell → Column .instance → ℕ → Operation F
  /-- Load a lookup table: fill a `TableColumn` (a fixed column) with `values` at absolute
  rows `[0, values.length)`, then default-fill every remaining usable row with the row-0
  value. Rust: `layouter.assign_table` (`table_layouter.rs`) + the floor planner's
  `fill_from_row` default-fill (`single_pass.rs:176-182`). Addresses absolute rows, so it
  is a layouter-level op, not a region op. See `lookup-design.md` §2.4. -/
  | loadTable : TableColumn → List F → Operation F

abbrev Operations (F : Type) := List (Operation F)

/-! ## Configure/synthesis registration -/

/--
Gate and lookup arguments supplied by a circuit's caller rather than created by the
circuit's own configure program.

This is the keygen analogue of an effect requirement: leaf region circuits commonly
receive an already-configured chip `Config` and use its arguments while contributing
no configure delta of their own.
-/
structure KeygenRequirements (F ConfigInput : Type) where
  gates : ConfigInput → List (Gate F) := fun _ => []
  lookups : ConfigInput → List (LookupArgument F) := fun _ => []

/--
Static registration of one region operation in explicit configure-produced gate and
lookup lists.

Assignments and copies need no configure-phase registration. Gate and lookup
activations must refer to arguments emitted by the same configure program.
-/
@[circuit_norm]
def RegionOperation.KeygenRegistered
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    RegionOperation F → Prop
  | .enableGate gate _ => gate ∈ gates
  | .enableLookup argument _ _ => argument ∈ lookups
  | _ => True

/-- Static registration of one layouter operation in explicit configure metadata. -/
@[circuit_norm]
def Operation.KeygenRegistered
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    Operation F → Prop
  | .region _ body =>
      body.Forall (RegionOperation.KeygenRegistered gates lookups)
  | _ => True

/--
Every gate and lookup emitted by a synthesis operation stream occurs in the supplied
configure-produced lists.
-/
def Operations.KeygenRegistered
    (operations : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) : Prop :=
  operations.Forall (Operation.KeygenRegistered gates lookups)

@[circuit_norm]
theorem Operations.KeygenRegistered.nil
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    Operations.KeygenRegistered [] gates lookups := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.append
    (left right : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    Operations.KeygenRegistered (left ++ right) gates lookups ↔
      Operations.KeygenRegistered left gates lookups ∧
        Operations.KeygenRegistered right gates lookups := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.region_cons
    (name : String) (body : RegionOperations F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    Operations.KeygenRegistered (.region name body :: rest) gates lookups ↔
      body.Forall (RegionOperation.KeygenRegistered gates lookups) ∧
        Operations.KeygenRegistered rest gates lookups := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.constrainInstance_cons
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    Operations.KeygenRegistered
        (.constrainInstance cell column row :: rest) gates lookups ↔
      Operations.KeygenRegistered rest gates lookups := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.loadTable_cons
    (table : TableColumn) (values : List F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    Operations.KeygenRegistered
        (.loadTable table values :: rest) gates lookups ↔
      Operations.KeygenRegistered rest gates lookups := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

/-- Registration is monotone in both configure-produced argument lists. -/
theorem Operations.KeygenRegistered.mono
    {operations : Operations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    (hregistered :
      operations.KeygenRegistered sourceGates sourceLookups)
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups) :
    operations.KeygenRegistered targetGates targetLookups := by
  rw [Operations.KeygenRegistered,
    List.forall_iff_forall_mem] at hregistered ⊢
  intro operation hoperation
  have hoperationRegistered := hregistered operation hoperation
  cases operation with
  | region name body =>
      rw [Operation.KeygenRegistered,
        List.forall_iff_forall_mem] at hoperationRegistered ⊢
      intro regionOperation hregionOperation
      have hregionRegistered :=
        hoperationRegistered regionOperation hregionOperation
      cases regionOperation with
      | enableGate gate row =>
          exact hgates gate hregionRegistered
      | enableLookup argument selectors row =>
          exact hlookups argument hregionRegistered
      | assignAdvice
      | assignFixed
      | constrainEqual
      | constrainConstant
      | constrainInstance =>
          trivial
  | constrainInstance
  | loadTable =>
      trivial

/-- Region-operation registration is monotone in both available argument lists. -/
theorem RegionOperations.keygenRegistered_mono
    {operations : RegionOperations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    (hregistered :
      operations.Forall
        (RegionOperation.KeygenRegistered sourceGates sourceLookups))
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups) :
    operations.Forall
      (RegionOperation.KeygenRegistered targetGates targetLookups) := by
  rw [List.forall_iff_forall_mem] at hregistered ⊢
  intro operation hoperation
  have hoperationRegistered := hregistered operation hoperation
  cases operation with
  | enableGate gate row =>
      exact hgates gate hoperationRegistered
  | enableLookup argument selectors row =>
      exact hlookups argument hoperationRegistered
  | assignAdvice
  | assignFixed
  | constrainEqual
  | constrainConstant
  | constrainInstance =>
      trivial

/--
Registration against a configure delta remains true after interpreting that delta
over any initial constraint system.
-/
theorem Operations.KeygenRegistered.applyConfigureDelta
    {operations : Operations F} {delta : ConfigureDelta F}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups) :
    operations.KeygenRegistered
      (delta.apply initial counts).gates
      (delta.apply initial counts).lookups := by
  apply hregistered.mono
  · intro gate hgate
    exact List.mem_append_right initial.gates hgate
  · intro argument hargument
    exact List.mem_append_right initial.lookups hargument

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def RegionOperation.KeygenCoherent
    (cs : ConstraintSystem F) : RegionOperation F → Prop :=
  RegionOperation.KeygenRegistered cs.gates cs.lookups

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def Operation.KeygenCoherent
    (cs : ConstraintSystem F) : Operation F → Prop :=
  Operation.KeygenRegistered cs.gates cs.lookups

/-- Every synthesis-enabled argument was registered in a constraint system. -/
def OperationsKeygenCoherent
    (cs : ConstraintSystem F) (operations : Operations F) : Prop :=
  operations.KeygenRegistered cs.gates cs.lookups

@[circuit_norm]
theorem OperationsKeygenCoherent.nil
    (cs : ConstraintSystem F) :
    OperationsKeygenCoherent cs [] := by
  exact Operations.KeygenRegistered.nil cs.gates cs.lookups

/-- Configure/synthesis coherence composes across operation-stream append. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.append
    (cs : ConstraintSystem F) (left right : Operations F) :
    OperationsKeygenCoherent cs (left ++ right) ↔
      OperationsKeygenCoherent cs left ∧
        OperationsKeygenCoherent cs right := by
  exact Operations.KeygenRegistered.append
    left right cs.gates cs.lookups

/-- A region is coherent exactly when each operation in its body is coherent. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.region_cons
    (cs : ConstraintSystem F) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.region name body :: rest) ↔
      body.Forall (RegionOperation.KeygenCoherent cs) ∧
        OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.region_cons
    name body rest cs.gates cs.lookups

@[circuit_norm]
theorem OperationsKeygenCoherent.constrainInstance_cons
    (cs : ConstraintSystem F) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : Operations F) :
    OperationsKeygenCoherent cs
        (.constrainInstance cell column row :: rest) ↔
      OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.constrainInstance_cons
    cell column row rest cs.gates cs.lookups

@[circuit_norm]
theorem OperationsKeygenCoherent.loadTable_cons
    (cs : ConstraintSystem F) (table : TableColumn)
    (values : List F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.loadTable table values :: rest) ↔
      OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.loadTable_cons
    table values rest cs.gates cs.lookups

/-- Delta registration supplies coherence in every interpreted configure result. -/
theorem Operations.KeygenRegistered.operationsKeygenCoherent_apply
    {operations : Operations F} {delta : ConfigureDelta F}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups) :
    OperationsKeygenCoherent (delta.apply initial counts) operations :=
  hregistered.applyConfigureDelta initial counts

/-! ## Selector activation vocabulary

These definitions describe the operation stream itself: which selector indices occur
syntactically in an expression, which selectors an operation enables, and which
operations activate a selector at a region-local row. Keeping them below the keygen
layer lets floor planning state its placement facts without importing keygen.
-/

/-- Selector indices occurring in an expression, with syntax-order multiplicity. -/
@[circuit_norm]
def Expression.selectorIndices : Expression F Query → List ℕ
  | .var (.selector selector) => [selector.index]
  | .var _ => []
  | .const _ => []
  | .add left right =>
      left.selectorIndices ++ right.selectorIndices
  | .mul left right =>
      left.selectorIndices ++ right.selectorIndices

/-- Membership in an enabled-selector list, by the index used by semantics. -/
@[circuit_norm]
def SelectorEnabledAtIndex
    (enabled : List Selector) (selector : ℕ) : Prop :=
  ∃ candidate ∈ enabled, candidate.index = selector

/-- An operation activates selector `selector` at region-local `row`. -/
@[circuit_norm]
def RegionOperation.ActivatesSelectorAt
    (selector row : ℕ) : RegionOperation F → Prop
  | .enableGate gate operationRow =>
      gate.selector.index = selector ∧ operationRow = row
  | .enableLookup _ enabled operationRow =>
      SelectorEnabledAtIndex enabled selector ∧ operationRow = row
  | _ => False

/-- Number of region indices a list of operations consumes (the `localLength`
analogue) — computed, not cached; per-circuit lemmas evaluate it to a literal. -/
def Operations.regionCount : Operations F → ℕ
  | [] => 0
  | .region _ _ :: ops => 1 + Operations.regionCount ops
  | .constrainInstance _ _ _ :: ops => Operations.regionCount ops
  | .loadTable _ _ :: ops => Operations.regionCount ops

section Semantics
variable [FiniteField F]

/-- Read a (possibly foreign) cell. NOT `@[circuit_norm]` (normal-form unification,
mirroring `AssignedCell.eval`): abstract cell reads stay folded; known-kind cells
reduce to the typed accessors via the `eval_of_*` rules below, so copy constraints
line up with the query/assigned-cell paths at the `env.advice` spelling. -/
def Cell.eval (place : RegionIndex → ℕ) (env : Environment F) (c : Cell) : F :=
  env.get c.column ((place c.regionIndex + c.rowOffset : ℕ) : ℤ)

omit [FiniteField F] in
/-- An assigned cell's `Cell.eval` is its `AssignedCell.eval` — ONE canonical folded
atom for abstract cell reads (copy constraints arrive at `Cell.eval x.cell`,
witness/assign facts at `AssignedCell.eval x`; without this they are separate folded
spellings that simp cannot cross). -/
@[circuit_norm]
lemma Cell.eval_cell [Field F] (place : RegionIndex → ℕ) (env : Environment F)
    (c : AssignedCell F) :
    Cell.eval place env c.cell = AssignedCell.eval place env c := rfl

omit [FiniteField F] in
@[circuit_norm]
lemma Cell.eval_of_advice (place : RegionIndex → ℕ) (env : Environment F)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    Cell.eval place env (.of self row col)
      = env.advice col ((place self + row : ℕ) : ℤ) := rfl

omit [FiniteField F] in
@[circuit_norm]
lemma Cell.eval_of_fixed (place : RegionIndex → ℕ) (env : Environment F)
    (self : RegionIndex) (row : ℕ) (col : Column .fixed) :
    Cell.eval place env (.of self row col)
      = env.fixed col ((place self + row : ℕ) : ℤ) := rfl

omit [FiniteField F] in
@[circuit_norm]
lemma Cell.eval_of_inst (place : RegionIndex → ℕ) (env : Environment F)
    (self : RegionIndex) (row : ℕ) (col : Column .instance) :
    Cell.eval place env (.of self row col)
      = env.inst col ((place self + row : ℕ) : ℤ) := rfl

/-- Constraints of one region operation, for a region with index `self`. A subcircuit
call's constraints are the *opaque chunk* `RegionOperations.Constraints … <folded child
ops>` — the proof boundary: parent hypotheses keep the chunk folded, and the per-circuit
forward lemmas (formal-circuit layer) rewrite it to the child's `Assumptions → Spec`. -/
def RegionOperation.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperation F → Prop
  | .assignAdvice _ _ _ => True
  | .assignFixed col row v => env.get col (place self + row : ℕ) = v
  | .enableGate gate row =>
      -- compiled polys vanish under `own selector ↦ 1`; sound because genuine selectors
      -- never occur in a foreign gate's polynomials (see halo2-selector-survey.md).
      -- `List.Forall` (not `∀ c ∈ …`) so `circuit_norm` reduces it to a clean conjunction.
      gate.constraints.Forall fun c =>
        c.poly.eval (Query.eval env (fun i => if i = gate.selector.index then 1 else 0)
          (place self + row : ℕ)) = 0
  | .enableLookup arg enabled row =>
      -- membership (not permutation): the input tuple at this row equals the table tuple
      -- at *some* usable table row (`lookup-design.md` §2.2). The witness is bounded by
      -- `env.usableRows` for faithfulness: the prover truncates the input expression and
      -- builds the table multiset over `usable_rows = n − (blinding + 1)` only
      -- (`lookup/prover.rs:573-585`), so blinding rows never participate on either side.
      -- ℕ-with-cast spelling: table rows share the `(↑(n : ℕ) : ℤ)` row normal form of
      -- all other reads. Inputs are evaluated under the local activation valuation
      -- `enabled ↦ 1, rest ↦ 0` — which selectors are on at this row decides *which* word
      -- the gated input expression reduces to (running-sum vs short row, §1.4); the table
      -- side is a rotation-0 fixed query, unaffected by the valuation.
      ∃ tableRow : ℕ, tableRow < env.usableRows ∧
        arg.inputs.map (Expression.eval (Query.eval env
          (fun i => if i ∈ enabled.map Selector.index then 1 else 0) (place self + row : ℕ)))
        = arg.tables.map (Expression.eval (Query.eval env
          (fun i => if i ∈ enabled.map Selector.index then 1 else 0) (tableRow : ℤ)))
  | .constrainEqual a b => a.eval place env = b.eval place env
  | .constrainConstant a v => a.eval place env = v
  | .constrainInstance cell instCol instRow =>
      cell.eval place env = env.get instCol (instRow : ℤ)

/-- Constraints of a list of region operations. -/
def RegionOperations.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperations F → Prop
  | [] => True
  | op :: ops =>
      op.Constraints place self env ∧ RegionOperations.Constraints place self env ops

/--
Ground truth: what it means that "constraints hold" on a sequence of operations,
*including* all constraints inside subcircuits (their ops are appended into the list).
The single satisfaction predicate (issue #358 — no separate `Soundness`/`Completeness`
views): `place` is the region placement (the analogue of main Clean's `offset`,
instantiated at top level with the floor planner's output), `i` the index of the next
region (threaded like Clean's offset). A folded subcircuit chunk in the middle of a
parent's list is isolated by `constraints_append`, advancing the region counter by the
chunk's `regionCount`.
-/
def Constraints (place : RegionIndex → ℕ) (env : Environment F) :
    Operations F → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops' :: ops, i =>
      ops'.Constraints place i env ∧ Constraints place env ops (i + 1)
  | .constrainInstance cell col row :: ops, i =>
      cell.eval place env = env.get col row ∧ Constraints place env ops i
  | .loadTable tbl values :: ops, i =>
      -- explicit block: rows `[0, values.length)` hold the loaded values
      (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
      -- default-fill (`lookup-design.md` §1.3.1): unused usable rows carry the row-0 value.
      -- Conditional on `values ≠ []` so an empty load imposes no bogus default.
      (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
        env.fixed tbl.inner (r : ℤ) = values[0]!) ∧
      Constraints place env ops i

/-- The witness condition for completeness: the environment assigns each advice cell
the value computed by its witness program (main Clean: `ExtendsVector`), and each fixed
cell the value the circuit assigns. The `assignFixed` clause mirrors its `Constraints`
equation — like `loadTable`'s witness clause (`ExtendsWitnesses` below): fixed-column
contents are circuit data the honest environment carries, so a completeness proof can
discharge the corresponding constraint (they are keygen-time assignments, not prover
witness choices). -/
def RegionOperation.ExtendsWitness (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : RegionOperation F → Prop
  | .assignAdvice col row compute =>
      env.get col (place self + row : ℕ) = (compute.eval ⟨place, env⟩)[0]
  | .assignFixed col row v => env.get col (place self + row : ℕ) = v
  | _ => True

/-- Witness condition for a list of region operations. -/
def RegionOperations.ExtendsWitnesses (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : RegionOperations F → Prop
  | [] => True
  | op :: ops =>
      op.ExtendsWitness place self env ∧ RegionOperations.ExtendsWitnesses place self env ops

/-- All-regions witness condition, threading the region counter like `Constraints`. -/
def ExtendsWitnesses (place : RegionIndex → ℕ) (env : ProverEnvironment F) :
    Operations F → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops' :: ops, i =>
      ops'.ExtendsWitnesses place i env ∧ ExtendsWitnesses place env ops (i + 1)
  | .constrainInstance _ _ _ :: ops, i => ExtendsWitnesses place env ops i
  | .loadTable tbl values :: ops, i =>
      -- The honest prover's environment holds exactly that column content: the explicit
      -- block plus the row-0 default-fill over the usable rows. Discharges the `loadTable`
      -- `Constraints` in the completeness proof of a table loader. See `lookup-design.md` §2.4.
      (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
      (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
        env.fixed tbl.inner (r : ℤ) = values[0]!) ∧
      ExtendsWitnesses place env ops i
end Semantics

end Halo2
