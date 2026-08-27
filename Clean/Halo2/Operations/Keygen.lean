import Clean.Halo2.Operations.Copy
import Clean.Halo2.SynthesisSummary.Operations

namespace Halo2

variable {F : Type}

/-! ## Configure/synthesis registration -/

/--
Gate, lookup, and equality-column capabilities supplied by a circuit's caller rather
than created by the circuit's own configure program.

This is the keygen analogue of an effect requirement: leaf region circuits commonly
receive an already-configured chip `Config` and use its arguments while contributing
no configure delta of their own.
-/
structure KeygenRequirements (F ConfigInput InputVar : Type) where
  /--
  Provenance required of configuration values borrowed from the caller. This stays
  folded across circuit boundaries; it never exposes a child's operation stream.
  -/
  configLawful : ConfigInput → Type := fun _ => Unit
  gates : ∀ input, configLawful input → List (Gate F) := fun _ _ => []
  lookups : ∀ input, configLawful input → List (LookupArgument F) := fun _ _ => []
  fixedColumns : ∀ input, configLawful input → List (Column .fixed) := fun _ _ => []
  constantColumns : ∀ input, configLawful input → List (Column .fixed) := fun _ _ => []
  permutationColumns : ∀ input, configLawful input → List AnyColumn := fun _ _ => []
  /-- Concrete caller-owned cells that synthesis may use in copy constraints. -/
  inputCells : ∀ configInput, configLawful configInput →
      InputVar → List Cell := fun _ _ _ => []

/-- Equality-enabled columns required by the concrete cells passed to synthesis. -/
def KeygenRequirements.inputPermutationColumns
    {ConfigInput InputVar : Type}
    (self : KeygenRequirements F ConfigInput InputVar)
    (configInput : ConfigInput) (configLawful : self.configLawful configInput)
    (input : InputVar) : List AnyColumn :=
  (self.inputCells configInput configLawful input).map Cell.column

/-- A configure input has no keygen requirements left for an enclosing circuit. -/
structure KeygenRequirements.EmptyAt
    {ConfigInput InputVar : Type}
    (self : KeygenRequirements F ConfigInput InputVar)
    (input : ConfigInput) where
  configLawful : self.configLawful input
  gates_eq : self.gates input configLawful = []
  lookups_eq : self.lookups input configLawful = []
  fixedColumns_eq : self.fixedColumns input configLawful = []
  constantColumns_eq : self.constantColumns input configLawful = []
  permutationColumns_eq : self.permutationColumns input configLawful = []
  inputCells_eq : ∀ inputVar,
    self.inputCells input configLawful inputVar = []

/--
Static registration of one region operation in explicit configure-produced gate and
lookup lists.

Assignments need no configure-phase registration. Gate and lookup activations must
refer to arguments emitted by configure; copy-like operations must use columns on
which configure enabled equality.
-/
@[circuit_norm]
def RegionOperation.KeygenRegistered
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    RegionOperation F → Prop
  | .assignFixed column _ _ => column ∈ fixedColumns
  | .enableGate gate _ => gate ∈ gates
  | .enableLookup argument _ _ => argument ∈ lookups
  | .constrainEqual left right =>
      left.column ∈ permutationColumns ∧ right.column ∈ permutationColumns
  | .constrainConstant cell _ => cell.column ∈ permutationColumns
  | .constrainInstance cell column _ =>
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns
  | _ => True

/-- Static registration of one layouter operation in explicit configure metadata. -/
@[circuit_norm]
def Operation.KeygenRegistered
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operation F → Prop
  | .region _ body =>
      body.Forall (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns)
  | .constrainInstance cell column _ =>
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns
  | .loadTable table _ => table.inner ∈ fixedColumns

/--
Every gate, lookup, and equality-dependent operation emitted by synthesis is covered
by the supplied configure-produced capabilities.
-/
def Operations.KeygenRegistered
    (operations : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) : Prop :=
  operations.Forall (Operation.KeygenRegistered gates lookups fixedColumns
    permutationColumns)

@[circuit_norm]
theorem Operations.KeygenRegistered.nil
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered [] gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.append
    (left right : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered (left ++ right) gates lookups fixedColumns
        permutationColumns ↔
      Operations.KeygenRegistered left gates lookups fixedColumns permutationColumns ∧
        Operations.KeygenRegistered right gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.region_cons
    (name : String) (body : RegionOperations F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered (.region name body :: rest) gates lookups fixedColumns
        permutationColumns ↔
      body.Forall (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns) ∧
        Operations.KeygenRegistered rest gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.constrainInstance_cons
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered
        (.constrainInstance cell column row :: rest) gates lookups fixedColumns
          permutationColumns ↔
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns ∧
        Operations.KeygenRegistered rest gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered, and_assoc]

@[circuit_norm]
theorem Operations.KeygenRegistered.loadTable_cons
    (table : TableColumn) (values : List F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered
        (.loadTable table values :: rest) gates lookups fixedColumns permutationColumns ↔
      table.inner ∈ fixedColumns ∧
        Operations.KeygenRegistered rest gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

/-- Registration is monotone in both configure-produced argument lists. -/
theorem Operations.KeygenRegistered.mono
    {operations : Operations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    {sourceFixedColumns targetFixedColumns : List (Column .fixed)}
    {sourcePermutationColumns targetPermutationColumns : List AnyColumn}
    (hregistered :
      operations.KeygenRegistered sourceGates sourceLookups sourceFixedColumns
        sourcePermutationColumns)
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ sourceFixedColumns → column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ sourcePermutationColumns → column ∈ targetPermutationColumns) :
    operations.KeygenRegistered targetGates targetLookups targetFixedColumns
      targetPermutationColumns := by
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
          =>
          trivial
      | assignFixed column row value =>
          exact hfixedColumns column hregionRegistered
      | constrainEqual left right =>
          exact ⟨hpermutationColumns left.column hregionRegistered.1,
            hpermutationColumns right.column hregionRegistered.2⟩
      | constrainConstant cell value =>
          exact hpermutationColumns cell.column hregionRegistered
      | constrainInstance cell column row =>
          exact ⟨hpermutationColumns cell.column hregionRegistered.1,
            hpermutationColumns column.toAny hregionRegistered.2⟩
  | constrainInstance cell column row =>
      exact ⟨hpermutationColumns cell.column hoperationRegistered.1,
        hpermutationColumns column.toAny hoperationRegistered.2⟩
  | loadTable =>
      exact hfixedColumns _ hoperationRegistered

/-- Region-operation registration is monotone in both available argument lists. -/
theorem RegionOperations.keygenRegistered_mono
    {operations : RegionOperations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    {sourceFixedColumns targetFixedColumns : List (Column .fixed)}
    {sourcePermutationColumns targetPermutationColumns : List AnyColumn}
    (hregistered :
      operations.Forall
        (RegionOperation.KeygenRegistered sourceGates sourceLookups
          sourceFixedColumns sourcePermutationColumns))
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ sourceFixedColumns → column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ sourcePermutationColumns → column ∈ targetPermutationColumns) :
    operations.Forall
      (RegionOperation.KeygenRegistered targetGates targetLookups
        targetFixedColumns targetPermutationColumns) := by
  rw [List.forall_iff_forall_mem] at hregistered ⊢
  intro operation hoperation
  have hoperationRegistered := hregistered operation hoperation
  cases operation with
  | enableGate gate row =>
      exact hgates gate hoperationRegistered
  | enableLookup argument selectors row =>
      exact hlookups argument hoperationRegistered
  | assignAdvice
      =>
      trivial
  | assignFixed column row value =>
      exact hfixedColumns column hoperationRegistered
  | constrainEqual left right =>
      exact ⟨hpermutationColumns left.column hoperationRegistered.1,
        hpermutationColumns right.column hoperationRegistered.2⟩
  | constrainConstant cell value =>
      exact hpermutationColumns cell.column hoperationRegistered
  | constrainInstance cell column row =>
      exact ⟨hpermutationColumns cell.column hoperationRegistered.1,
        hpermutationColumns column.toAny hoperationRegistered.2⟩

/--
Registration against a configure delta remains true after interpreting that delta
over any initial constraint system.
-/
theorem Operations.KeygenRegistered.applyConfigureDelta
    {operations : Operations F} {delta : ConfigureDelta F}
    {fixedColumns : List (Column .fixed)}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups
        fixedColumns delta.permutationRequests)
    (hfixedColumns : ∀ column ∈ fixedColumns,
      column.index < counts.numFixedColumns) :
    operations.KeygenRegistered
      (delta.apply initial counts).gates
      (delta.apply initial counts).lookups
      (delta.apply initial counts).fixedColumns
      (delta.apply initial counts).permutationColumns := by
  apply hregistered.mono
  · intro gate hgate
    exact List.mem_append_right initial.gates hgate
  · intro argument hargument
    exact List.mem_append_right initial.lookups hargument
  · intro column hcolumn
    rw [ConstraintSystem.mem_fixedColumns_iff]
    exact hfixedColumns column hcolumn
  · intro column hcolumn
    rw [ConfigureDelta.apply, mem_appendFirstEncounters]
    exact Or.inr hcolumn

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def RegionOperation.KeygenCoherent
    (cs : ConstraintSystem F) : RegionOperation F → Prop :=
  RegionOperation.KeygenRegistered cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def Operation.KeygenCoherent
    (cs : ConstraintSystem F) : Operation F → Prop :=
  Operation.KeygenRegistered cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

/-- Every synthesis-enabled argument was registered in a constraint system. -/
def OperationsKeygenCoherent
    (cs : ConstraintSystem F) (operations : Operations F) : Prop :=
  operations.KeygenRegistered cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.nil
    (cs : ConstraintSystem F) :
    OperationsKeygenCoherent cs [] := by
  exact Operations.KeygenRegistered.nil cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

/-- Configure/synthesis coherence composes across operation-stream append. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.append
    (cs : ConstraintSystem F) (left right : Operations F) :
    OperationsKeygenCoherent cs (left ++ right) ↔
      OperationsKeygenCoherent cs left ∧
        OperationsKeygenCoherent cs right := by
  exact Operations.KeygenRegistered.append
    left right cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

/-- A region is coherent exactly when each operation in its body is coherent. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.region_cons
    (cs : ConstraintSystem F) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.region name body :: rest) ↔
      body.Forall (RegionOperation.KeygenCoherent cs) ∧
        OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.region_cons
    name body rest cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.constrainInstance_cons
    (cs : ConstraintSystem F) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : Operations F) :
    OperationsKeygenCoherent cs
        (.constrainInstance cell column row :: rest) ↔
      cell.column ∈ cs.permutationColumns ∧
        column.toAny ∈ cs.permutationColumns ∧
        OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.constrainInstance_cons
    cell column row rest cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.loadTable_cons
    (cs : ConstraintSystem F) (table : TableColumn)
    (values : List F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.loadTable table values :: rest) ↔
      table.inner ∈ cs.fixedColumns ∧ OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.loadTable_cons
    table values rest cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

/-- Delta registration supplies coherence in every interpreted configure result. -/
theorem Operations.KeygenRegistered.operationsKeygenCoherent_apply
    {operations : Operations F} {delta : ConfigureDelta F}
    {fixedColumns : List (Column .fixed)}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups
        fixedColumns delta.permutationRequests)
    (hfixedColumns : ∀ column ∈ fixedColumns,
      column.index < counts.numFixedColumns) :
    OperationsKeygenCoherent (delta.apply initial counts) operations :=
  hregistered.applyConfigureDelta initial counts hfixedColumns

end Halo2
