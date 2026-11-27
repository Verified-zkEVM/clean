module

public import Clean.Halo2.TopLevel
public import Clean.Halo2.WitnessExecution

@[expose] public section

/-!
# Top-level constructive witness generation and existential completeness

Connects `Clean.Halo2.WitnessExecution` to `TopLevelCircuit`:
- `TopLevelCircuit.tablesLoaded` proves every `loadTable` equation already holds in the circuit's
  canonical fixed columns.
- `TopLevelCircuit.fixedAssignment_eq_fixedValue` proves every `assignFixed` in `self.operations`
  agrees with `self.fixedValue` at the circuit's V1 placement.
- `TopLevelCircuit.proverAssignment` runs `Execute.run` from the circuit's fixed columns and public
  instances, returning a `ProofAssignment F`.
- `TopLevelCircuit.exists_witness` and `TopLevelCircuit.exists_completeness` eliminate the vacuity
  gap: given `ComputableWitnesses` and `WritesConsistent`, a satisfying `ProofAssignment F`
  actually exists.
-/

namespace Halo2.TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

omit [FiniteField F] in
private theorem mem_tableAssignments_of_mem_loadTable
    (usable : ℕ) (ops : Operations F)
    {table : TableColumn} {values : List F}
    (hload : .loadTable table values ∈ ops)
    {entry : Layout.FixedAssignment F}
    (hentry : entry ∈ Layout.tableColumnAssignments usable table.inner.index values) :
    entry ∈ Layout.tableAssignments usable ops := by
  induction ops with
  | nil => simp at hload
  | cons op rest ih =>
    rcases List.mem_cons.mp hload with rfl | htail
    · simp only [Layout.tableAssignments, List.mem_append]
      exact Or.inl hentry
    · cases op with
      | loadTable _ _ =>
        simp only [Layout.tableAssignments, List.mem_append]
        exact Or.inr (ih htail)
      | region _ _ | constrainInstance _ _ _ =>
        exact ih htail

private theorem mem_regionAssignments_of_mem_assignments_fixed
    (starts : List ℕ) (ops : Operations F) (self : RegionIndex)
    {a : Assignment F}
    (ha : a ∈ ops.assignments (fun r => starts.getD r 0) self)
    (hfixed : a.destination.1.kind = .fixed) :
    ∃ v : F, ∃ row : ℕ,
      a.destination.2 = (row : ℤ) ∧
      (∀ env : ProverEnvironment F, (a.program.eval ⟨fun r => starts.getD r 0, env⟩)[0] = v) ∧
      (a.destination.1.index, row, v) ∈
        Layout.regionAssignments starts (indexedRegions ops self).1 := by
  induction ops generalizing self with
  | nil => simp [Operations.assignments] at ha
  | cons op rest ih =>
    cases op with
    | region name body =>
      simp only [Operations.assignments, List.mem_append] at ha
      rcases ha with hbody | htail
      · have hreg : ∃ v : F, ∃ row : ℕ,
            a.destination.2 = (row : ℤ) ∧
            (∀ env : ProverEnvironment F,
              (a.program.eval ⟨fun r => starts.getD r 0, env⟩)[0] = v) ∧
            ∃ col : Column .fixed, ∃ localRow : ℕ,
              a.destination.1 = col.toAny ∧
              row = starts.getD self 0 + localRow ∧
              .assignFixed col localRow v ∈ body := by
          clear ih
          induction body with
          | nil => simp [RegionOperations.assignments] at hbody
          | cons rop rrest rih =>
            cases rop with
            | assignAdvice col localRow prog =>
              rcases List.mem_cons.mp hbody with rfl | hr
              · cases hfixed
              · obtain ⟨v, row, hrow, hval, c, lr, hc, hlr, hmem⟩ := rih hr
                exact ⟨v, row, hrow, hval, c, lr, hc, hlr, List.mem_cons_of_mem _ hmem⟩
            | assignFixed col localRow v =>
              rcases List.mem_cons.mp hbody with rfl | hr
              · refine ⟨v, starts.getD self 0 + localRow, rfl, ?_, col, localRow, rfl, rfl,
                  List.mem_cons_self⟩
                intro env
                simp [Halo2.eval_ofFExpr_zero, Witgen.FExprOver.eval]
              · obtain ⟨v', row, hrow, hval, c, lr, hc, hlr, hmem⟩ := rih hr
                exact ⟨v', row, hrow, hval, c, lr, hc, hlr, List.mem_cons_of_mem _ hmem⟩
            | enableGate _ _ | enableLookup _ _ _ | constrainEqual _ _
            | constrainConstant _ _ | constrainInstance _ _ _ =>
              obtain ⟨v, row, hrow, hval, c, lr, hc, hlr, hmem⟩ := rih hbody
              exact ⟨v, row, hrow, hval, c, lr, hc, hlr, List.mem_cons_of_mem _ hmem⟩
        obtain ⟨v, row, hrow, hval, col, localRow, hcol, hlr, hmem⟩ := hreg
        refine ⟨v, row, hrow, hval, ?_⟩
        simp only [indexedRegions, Layout.regionAssignments, List.flatMap_cons, List.mem_append]
        left
        rw [List.mem_filterMap]
        refine ⟨.assignFixed col localRow v, hmem, ?_⟩
        simp only [Layout.place, hcol, Column.toAny, hlr]
      · obtain ⟨v, row, hrow, hval, hmem⟩ := ih (self + 1) htail
        refine ⟨v, row, hrow, hval, ?_⟩
        simp only [indexedRegions, Layout.regionAssignments, List.flatMap_cons, List.mem_append]
        exact Or.inr hmem
    | constrainInstance _ _ _ | loadTable _ _ =>
      exact ih self ha

private theorem natMod_natCast_eq_of_lt {r n : ℕ} (hlt : r < n) :
    (r : ℤ).natMod n = r := by
  unfold Int.natMod
  norm_cast
  exact Nat.mod_eq_of_lt hlt

/-- Every `loadTable` in a top-level circuit is already satisfied by its compiled fixed columns. -/
theorem tablesLoaded
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) :
    self.operations.TablesLoaded (self.environment assignment) := by
  let _ : TopLevelShape self :=
    ⟨TopLevelCompilation.circuitShape self.formalCircuit self.publicInputLayout, rfl⟩
  have husable_eq : (self.environment assignment).usableRows =
      self.usableRowsAt self.domainExponent := by
    simp only [environment_usableRows, usableRowsAt, blindingFactors]
    rw [self.domainExponent_eq_compiled]
  have husable_le_n : self.usableRowsAt self.domainExponent ≤ self.n :=
    self.usableRowsAt_domainExponent_le_n
  suffices h : ∀ ops : Operations F,
      (∀ tbl values, .loadTable tbl values ∈ ops → .loadTable tbl values ∈ self.operations) →
      ops.TablesLoaded (self.environment assignment) from
    h self.operations (fun _ _ hmem => hmem)
  intro ops hops
  induction ops with
  | nil => trivial
  | cons op rest ih =>
    cases op with
    | region _ _ | constrainInstance _ _ _ =>
      exact ih (fun tbl vals hmem => hops tbl vals (List.mem_cons_of_mem _ hmem))
    | loadTable table values =>
      have hload : .loadTable table values ∈ self.operations :=
        hops table values List.mem_cons_self
      refine ⟨⟨?_, ?_⟩, ih (fun tbl vals hmem => hops tbl vals (List.mem_cons_of_mem _ hmem))⟩
      · intro r hr
        have hmem_col : (table.inner.index, r, values[r]!) ∈
            Layout.tableColumnAssignments
              (self.usableRowsAt self.domainExponent) table.inner.index values := by
          simp only [Layout.tableColumnAssignments, List.mem_append]
          left
          rw [List.mem_map]
          refine ⟨(values[r], r), ?_, ?_⟩
          · have hzip : (values[r], r) = values.zipIdx[r]'(by simp [hr]) := by
              simp
            rw [hzip]
            exact List.getElem_mem _
          · simp [hr]
        have hraw : (table.inner.index, r, values[r]!) ∈
            Layout.rawAssignments (self.usableRowsAt self.domainExponent)
              self.selectorMap self.constraintSystem self.operations := by
          simp only [Layout.rawAssignments, List.mem_append]
          exact Or.inl (Or.inl (Or.inl
            (mem_tableAssignments_of_mem_loadTable _ self.operations hload hmem_col)))
        have hlt_n : r < self.n := (self.fixedAssignment_bounds_of_mem_raw _ hraw).2
        rw [self.environment_fixed, self.fixedValue_eq_fixedRows_getD,
          natMod_natCast_eq_of_lt hlt_n]
        exact self.fixedRows_getD_getD_eq_of_mem_raw _ hraw
      · intro hne r hge hr
        rw [husable_eq] at hr
        cases values with
        | nil => exact False.elim (hne rfl)
        | cons first tail =>
          have hmem_col : (table.inner.index, r, first) ∈
              Layout.tableColumnAssignments
                (self.usableRowsAt self.domainExponent) table.inner.index (first :: tail) := by
            simp only [Layout.tableColumnAssignments, List.mem_append]
            right
            rw [List.mem_map]
            refine ⟨r - (first :: tail).length, ?_, ?_⟩
            · rw [List.mem_range]
              omega
            · simp only [Prod.mk.injEq, true_and, and_true]
              omega
          have hraw : (table.inner.index, r, first) ∈
              Layout.rawAssignments (self.usableRowsAt self.domainExponent)
                self.selectorMap self.constraintSystem self.operations := by
            simp only [Layout.rawAssignments, List.mem_append]
            exact Or.inl (Or.inl (Or.inl
              (mem_tableAssignments_of_mem_loadTable _ self.operations hload hmem_col)))
          have hlt_n : r < self.n := (self.fixedAssignment_bounds_of_mem_raw _ hraw).2
          rw [self.environment_fixed, self.fixedValue_eq_fixedRows_getD,
            natMod_natCast_eq_of_lt hlt_n]
          simpa using self.fixedRows_getD_getD_eq_of_mem_raw _ hraw

/-- Every `assignFixed` in a top-level circuit's flattened assignments evaluates to the circuit's
canonical compiled `fixedValue` at that cell. -/
theorem fixedAssignment_eq_fixedValue
    (self : TopLevelCircuit F Config PublicInput)
    (a : Assignment F)
    (ha : a ∈ self.operations.assignments self.placement 0)
    (hfixed : a.destination.1.kind = .fixed)
    (env : ProverEnvironment F) :
    (a.program.eval ⟨self.placement, env⟩)[0] =
      self.fixedValue ⟨a.destination.1.index⟩ a.destination.2 := by
  let _ : TopLevelShape self :=
    ⟨TopLevelCompilation.circuitShape self.formalCircuit self.publicInputLayout, rfl⟩
  have hplace : self.placement = fun r => (FloorPlanner.V1.starts self.operations).getD r 0 := rfl
  rw [hplace] at ha ⊢
  obtain ⟨v, row, hrow, hval, hreg⟩ :=
    mem_regionAssignments_of_mem_assignments_fixed
      (FloorPlanner.V1.starts self.operations) self.operations 0 ha hfixed
  have hraw : (a.destination.1.index, row, v) ∈
      Layout.rawAssignments (self.usableRowsAt self.domainExponent)
        self.selectorMap self.constraintSystem self.operations := by
    simp only [Layout.rawAssignments, List.mem_append]
    exact Or.inr hreg
  have hlt_n : row < self.n := (self.fixedAssignment_bounds_of_mem_raw _ hraw).2
  rw [hval env, hrow, self.fixedValue_eq_fixedRows_getD, natMod_natCast_eq_of_lt hlt_n]
  exact (self.fixedRows_getD_getD_eq_of_mem_raw _ hraw).symm

/-- Construct the honest prover's `ProofAssignment F` by running `Execute.run` over the circuit's
flattened assignments, seeded with the public instances `inst` and the circuit's compiled fixed
columns. -/
def proverAssignment
    (self : TopLevelCircuit F Config PublicInput)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F) :
    ProofAssignment F :=
  let seed : ProofAssignment F := ⟨fun _ _ => 0, inst⟩
  let finalEnv := Execute.run self.placement
    (self.operations.assignments self.placement 0)
    (self.proverEnvironment seed hint)
  { advice := fun column row => finalEnv.advice column row
    inst := inst }

@[simp] theorem proverAssignment_inst
    (self : TopLevelCircuit F Config PublicInput)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F) :
    (self.proverAssignment inst hint).inst = inst := rfl

private theorem run_preserves_fixed
    (self : TopLevelCircuit F Config PublicInput)
    (assignments : List (Assignment F))
    (hsub : ∀ a ∈ assignments, a ∈ self.operations.assignments self.placement 0)
    (env : ProverEnvironment F)
    (hfixed_env : ∀ col : Column .fixed, ∀ row : ℤ,
      env.fixed col row = self.fixedValue col row)
    (col : Column .fixed) (row : ℤ) :
    (Execute.run self.placement assignments env).fixed col row =
      self.fixedValue col row := by
  induction assignments generalizing env with
  | nil => exact hfixed_env col row
  | cons a rest ih =>
    apply ih (fun b hb => hsub b (List.mem_cons_of_mem _ hb))
    intro c r
    change (env.write a.destination (a.program.eval ⟨self.placement, env⟩)[0]).read
      (c.toAny, r) = self.fixedValue c r
    by_cases h : (c.toAny, r) = a.destination
    · rw [h, ProverEnvironment.read_write_same]
      have hkind : a.destination.1.kind = .fixed := by
        have hk := congrArg (fun p : Address => p.1.kind) h.symm
        exact hk
      have heq := self.fixedAssignment_eq_fixedValue a (hsub a List.mem_cons_self) hkind env
      rw [heq]
      have hidx : (⟨a.destination.1.index⟩ : Column .fixed) = c := by
        cases c
        have hi := congrArg (fun p : Address => p.1.index) h.symm
        simpa [Column.toAny] using hi
      have hrow : a.destination.2 = r := (congrArg Prod.snd h).symm
      rw [hidx, hrow]
    · rw [ProverEnvironment.read_write_other env a.destination (c.toAny, r) _ h]
      exact hfixed_env c r

omit [FiniteField F] in
private theorem proverEnvironment_ext {left right : ProverEnvironment F}
    (hget : ∀ col row, left.get col row = right.get col row)
    (husable : left.usableRows = right.usableRows)
    (hhint : left.hint = right.hint) :
    left = right := by
  cases left with
  | mk lEnv lHint =>
    cases right with
    | mk rEnv rHint =>
      cases lEnv with
      | mk lGet lUsable =>
        cases rEnv with
        | mk rGet rUsable =>
          have h1 : lGet = rGet := funext fun col => funext fun row => hget col row
          have h2 : lUsable = rUsable := husable
          have h3 : lHint = rHint := hhint
          subst h1 h2 h3
          rfl

/-- `self.proverEnvironment (self.proverAssignment inst hint) hint` is definitionally equal to the
environment produced by `Execute.run`. -/
theorem proverEnvironment_proverAssignment_eq_run
    (self : TopLevelCircuit F Config PublicInput)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F) :
    self.proverEnvironment (self.proverAssignment inst hint) hint =
      Execute.run self.placement
        (self.operations.assignments self.placement 0)
        (self.proverEnvironment ⟨fun _ _ => 0, inst⟩ hint) := by
  let seed : ProofAssignment F := ⟨fun _ _ => 0, inst⟩
  apply proverEnvironment_ext
  · intro col row
    cases col with
    | mk kind idx =>
      cases kind with
      | advice => rfl
      | fixed =>
        change self.fixedValue ⟨idx⟩ row =
          (Execute.run self.placement (self.operations.assignments self.placement 0)
            (self.proverEnvironment seed hint)).fixed ⟨idx⟩ row
        exact (run_preserves_fixed self
          (self.operations.assignments self.placement 0)
          (fun _ h => h)
          (self.proverEnvironment seed hint)
          (fun c r => self.environment_fixed seed c r)
          ⟨idx⟩ row).symm
      | «instance» =>
        change inst ⟨idx⟩ row =
          (Execute.run self.placement (self.operations.assignments self.placement 0)
            (self.proverEnvironment seed hint)).inst ⟨idx⟩ row
        exact (Execute.run_instance self.placement 0 self.operations
          (self.proverEnvironment seed hint) ⟨idx⟩ row).symm
  · exact (Execute.run_usableRows self.placement
      (self.operations.assignments self.placement 0)
      (self.proverEnvironment seed hint)).symm
  · exact (Execute.run_hint self.placement
      (self.operations.assignments self.placement 0)
      (self.proverEnvironment seed hint)).symm

/-- Given `ComputableWitnesses` and `WritesConsistent` (for any initial determined set `S₀`
consisting of non-advice cells, such as `Determined.nonAdvice`, `Determined.instances`, or
`Determined.empty`), `self.proverAssignment inst hint` satisfies `ExtendsWitnesses`. -/
theorem proverAssignment_extendsWitnesses
    (self : TopLevelCircuit F Config PublicInput)
    (S₀ : Address → Prop)
    (hcomp : self.operations.ComputableWitnesses self.placement S₀ 0)
    (hcons : self.operations.WritesConsistent self.placement S₀ 0)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F) :
    ExtendsWitnesses self.placement
      (self.proverEnvironment (self.proverAssignment inst hint) hint)
      self.operations 0 := by
  rw [self.proverEnvironment_proverAssignment_eq_run inst hint]
  let seed : ProofAssignment F := ⟨fun _ _ => 0, inst⟩
  apply (Execute.run_extendsWitnesses self.placement 0 self.operations S₀
    (self.proverEnvironment seed hint) hcomp hcons ?_ ?_ ?_).2
  · intro a ha hS env _
    have hfixed : a.destination.1.kind = .fixed := hcons.initialDisjoint a ha hS
    rw [self.fixedAssignment_eq_fixedValue a ha hfixed env]
    cases hcol : a.destination.1 with
    | mk kind idx =>
      simp only [hcol] at hfixed
      subst hfixed
      simp [ProverEnvironment.read, hcol, proverEnvironment, TopLevelCompilation.proverEnvironment,
        TopLevelCompilation.environment, TopLevelCompilation.environmentAt,
        fixedValue, TopLevelCompilation.fixedValue]
  · exact self.tablesLoaded seed
  · exact self.operations.assignments_separate_tables self.placement 0
      self.constraintSystem.constants self.fixedWritesLawful

/-- Existential witness construction for any `TopLevelCircuit` with `ComputableWitnesses` and
`WritesConsistent`. -/
theorem exists_witness
    (self : TopLevelCircuit F Config PublicInput)
    (S₀ : Address → Prop)
    (hcomp : self.operations.ComputableWitnesses self.placement S₀ 0)
    (hcons : self.operations.WritesConsistent self.placement S₀ 0)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F) :
    ∃ assignment : ProofAssignment F,
      assignment.inst = inst ∧
      ExtendsWitnesses self.placement
        (self.proverEnvironment assignment hint) self.operations 0 :=
  ⟨self.proverAssignment inst hint, rfl,
    self.proverAssignment_extendsWitnesses S₀ hcomp hcons inst hint⟩

/-- Non-vacuous existential top-level completeness: given `ComputableWitnesses`,
`WritesConsistent`, and `ProverAssumptions` on the constructively generated proof assignment, there
exists a `ProofAssignment F` with public instances `inst` satisfying `ExtendsWitnesses`,
`Constraints`, and `ProverSpec`. -/
theorem exists_completeness
    (self : TopLevelCircuit F Config PublicInput)
    (S₀ : Address → Prop)
    (hcomp : self.operations.ComputableWitnesses self.placement S₀ 0)
    (hcons : self.operations.WritesConsistent self.placement S₀ 0)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F)
    (hprover : self.formalCircuit.ProverAssumptions
      (eval (self.placedProverEnvironment (self.proverAssignment inst hint) hint)
        (show Var unit F from ()))
      (self.formalCircuit.extract self.config () 0
        (self.placedEnvironment (self.proverAssignment inst hint)))
      hint) :
    ∃ assignment : ProofAssignment F,
      assignment.inst = inst ∧
      ExtendsWitnesses self.placement
        (self.proverEnvironment assignment hint) self.operations 0 ∧
      Constraints self.placement (self.environment assignment)
        self.operations 0 ∧
      self.formalCircuit.ProverSpec
        (eval (self.placedProverEnvironment assignment hint)
          (show Var unit F from ()))
        (eval (self.placedProverEnvironment assignment hint)
          (self.formalCircuit.output self.config () 0))
        (self.formalCircuit.extract self.config () 0
          (self.placedEnvironment assignment))
        hint := by
  let assignment := self.proverAssignment inst hint
  have hwitnesses := self.proverAssignment_extendsWitnesses S₀ hcomp hcons inst hint
  have hcomplete := self.completeness assignment hint hwitnesses hprover
  exact ⟨assignment, rfl, hwitnesses, hcomplete.1, hcomplete.2⟩

/-- Kernel-reducible `Fast.orderedAdvice` discharges `ComputableWitnesses` and `WritesConsistent`
for any `TopLevelCircuit` (automatically handling repeated equal-valued `assignFixed` pins via
`fixedAssignment_eq_fixedValue`). -/
theorem computable_and_consistent_of_orderedAdvice
    (self : TopLevelCircuit F Config PublicInput)
    (hacc : Fast.orderedAdvice self.placement ∅
      (self.operations.assignments self.placement 0) = true) :
    self.operations.ComputableWitnesses self.placement Determined.nonAdvice 0 ∧
      self.operations.WritesConsistent self.placement Determined.nonAdvice 0 := by
  apply Fast.orderedAdvice_sound self.placement
    (self.operations.assignments self.placement 0) hacc
  intro a ha b hb hdest hfixed env
  rw [self.fixedAssignment_eq_fixedValue a ha hfixed env,
    self.fixedAssignment_eq_fixedValue b hb (hdest ▸ hfixed) env, hdest]

end Halo2.TopLevelCircuit
