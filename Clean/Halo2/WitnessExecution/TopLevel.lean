module

public import Clean.Halo2.Compiler.Fixed
public import Clean.Halo2.TopLevel
public import Clean.Halo2.WitnessExecution
public import Clean.Halo2.WitnessExecution.Bridge

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
- `TopLevelCircuit.exists_witness_of` and `TopLevelCircuit.exists_completeness_of` eliminate the
  vacuity gap: given `ComputableWitnesses` and `WritesConsistent`, a satisfying `ProofAssignment F`
  actually exists.
-/

namespace Halo2.TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

private theorem tablesLoaded_of_fixedRequirements
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex)
    (hreqs : (operationFixedRequirements ops i).Forall (FixedRequirement.Satisfied place env)) :
    ops.TablesLoaded env := by
  induction ops generalizing i with
  | nil => trivial
  | cons op rest ih =>
    cases op with
    | region _ body =>
      simp only [operationFixedRequirements, List.forall_append] at hreqs
      exact ih (i + 1) hreqs.2
    | constrainInstance _ _ _ =>
      exact ih i hreqs
    | loadTable table values =>
      simp only [operationFixedRequirements, List.forall_cons, FixedRequirement.Satisfied] at hreqs
      exact ⟨hreqs.1, ih i hreqs.2⟩

private theorem mem_regionFixedRequirements_of_mem_assignments_fixed
    (place : RegionIndex → ℕ) (self : RegionIndex) (body : RegionOperations F)
    {a : Assignment F}
    (ha : a ∈ body.assignments place self)
    (hfixed : a.destination.1.kind = .fixed) :
    ∃ (col : Column .fixed) (localRow : ℕ) (v : F),
      a.destination = (col.toAny, ((place self + localRow : ℕ) : ℤ)) ∧
      (∀ env : ProverEnvironment F, (a.program.eval ⟨place, env⟩)[0] = v) ∧
      FixedRequirement.assignment self col localRow v ∈ regionFixedRequirements self body := by
  induction body with
  | nil => simp [RegionOperations.assignments] at ha
  | cons op rest ih =>
    cases op with
    | assignAdvice _ _ _ =>
      rcases List.mem_cons.mp ha with rfl | htail
      · cases hfixed
      · exact ih htail
    | assignFixed col localRow v =>
      rcases List.mem_cons.mp ha with rfl | htail
      · refine ⟨col, localRow, v, rfl, ?_, List.mem_cons_self⟩
        intro env
        simp [eval_ofFExpr_zero, Witgen.FExprOver.eval]
      · obtain ⟨c, lr, val, hdest, hval, hmem⟩ := ih htail
        exact ⟨c, lr, val, hdest, hval, List.mem_cons_of_mem _ hmem⟩
    | enableGate _ _ | enableLookup _ _ _ | constrainEqual _ _
    | constrainConstant _ _ | constrainInstance _ _ _ =>
      exact ih ha

private theorem mem_operationFixedRequirements_of_mem_assignments_fixed
    (place : RegionIndex → ℕ) (ops : Operations F) (i : RegionIndex)
    {a : Assignment F}
    (ha : a ∈ ops.assignments place i)
    (hfixed : a.destination.1.kind = .fixed) :
    ∃ (region : RegionIndex) (col : Column .fixed) (localRow : ℕ) (v : F),
      a.destination = (col.toAny, ((place region + localRow : ℕ) : ℤ)) ∧
      (∀ env : ProverEnvironment F, (a.program.eval ⟨place, env⟩)[0] = v) ∧
      FixedRequirement.assignment region col localRow v ∈ operationFixedRequirements ops i := by
  induction ops generalizing i with
  | nil => simp [Operations.assignments] at ha
  | cons op rest ih =>
    cases op with
    | region _ body =>
      simp only [Operations.assignments, List.mem_append] at ha
      rcases ha with hbody | htail
      · obtain ⟨col, localRow, v, hdest, hval, hmem⟩ :=
          mem_regionFixedRequirements_of_mem_assignments_fixed place i body hbody hfixed
        exact ⟨i, col, localRow, v, hdest, hval, List.mem_append_left _ hmem⟩
      · obtain ⟨region, col, localRow, v, hdest, hval, hmem⟩ := ih (i + 1) htail
        exact ⟨region, col, localRow, v, hdest, hval, List.mem_append_right _ hmem⟩
    | constrainInstance _ _ _ =>
      exact ih i ha
    | loadTable _ _ =>
      obtain ⟨region, col, localRow, v, hdest, hval, hmem⟩ := ih i ha
      exact ⟨region, col, localRow, v, hdest, hval, List.mem_cons_of_mem _ hmem⟩

/-- Every `loadTable` in a top-level circuit is already satisfied by its compiled fixed columns. -/
theorem tablesLoaded
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) :
    self.operations.TablesLoaded (self.environment assignment) := by
  let _ : TopLevelShape self :=
    ⟨TopLevelCompilation.circuitShape self.formalCircuit self.publicInputLayout, rfl⟩
  exact tablesLoaded_of_fixedRequirements self.placement (self.environment assignment)
    self.operations 0
    ((CircuitConstraintFamily.fixed_constraints_iff_requirements
      self.placement (self.environment assignment) self.operations 0).mp
      (self.fixed_constraints assignment))

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
  obtain ⟨region, col, localRow, v, hdest, hval, hmem⟩ :=
    mem_operationFixedRequirements_of_mem_assignments_fixed
      self.placement self.operations 0 ha hfixed
  let seed : ProofAssignment F := ⟨fun _ _ => 0, fun _ _ => 0⟩
  have hreqs := (CircuitConstraintFamily.fixed_constraints_iff_requirements
    self.placement (self.environment seed) self.operations 0).mp
    (self.fixed_constraints seed)
  have hsat : (self.environment seed).fixed col ((self.placement region + localRow : ℕ) : ℤ) = v :=
    List.forall_iff_forall_mem.mp hreqs _ hmem
  rw [self.environment_fixed] at hsat
  rw [hval env, hdest]
  exact hsat.symm

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

/-- `self.proverEnvironment (self.proverAssignment inst hint) hint` is extensionally equal to the
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

/-- Automatic compositional `ComputableWitnesses` for any `TopLevelCircuit`, derived directly from
its elaborated `ConsumedCellsAssigned` provenance certificate. -/
theorem computableWitnesses
    (self : TopLevelCircuit F Config PublicInput) :
    self.operations.ComputableWitnesses self.placement Determined.nonAdvice 0 :=
  Operations.computableWitnesses_of_consumedCellsAssigned self.placement self.operations
    self.operationsConsumedCellsAssigned

/-- Automatic compositional `WritesConsistent` for any `TopLevelCircuit`, derived from per-region
`AdviceWritesConsistent`, V1 floor-planner `SharedColumnIntervalsDisjoint`, and compiled fixed-value
agreement. -/
theorem writesConsistent
    (self : TopLevelCircuit F Config PublicInput) :
    self.operations.WritesConsistent self.placement Determined.nonAdvice 0 := by
  have hdisjoint :
      FloorPlanner.SharedColumnIntervalsDisjoint (FloorPlanner.measureRegions self.operations)
        (FloorPlanner.V1.starts self.operations) := by
    rw [FloorPlanner.V1.starts, FloorPlanner.V1.planOperations_eq]
    exact FloorPlanner.V1.planCandidate_measureRegions_sharedColumnIntervalsDisjoint self.operations
  exact Operations.writesConsistent_of_adviceWritesConsistent
    (FloorPlanner.V1.starts self.operations) self.operations
    self.operationsAdviceWritesConsistent hdisjoint fun a ha b hb hdest hfixed env => by
      change (a.program.eval ⟨self.placement, env⟩)[0] = (b.program.eval ⟨self.placement, env⟩)[0]
      rw [self.fixedAssignment_eq_fixedValue a ha hfixed env,
        self.fixedAssignment_eq_fixedValue b hb (hdest ▸ hfixed) env, hdest]

/-- Explicit-premise variant of `proverAssignment_extendsWitnesses`: given `ComputableWitnesses`
and `WritesConsistent` for an arbitrary initial determined set `S₀`, `self.proverAssignment`
satisfies `ExtendsWitnesses`. -/
theorem proverAssignment_extendsWitnesses_of
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

/-- Automatic witness extension for any `TopLevelCircuit`: `self.proverAssignment inst hint`
satisfies `ExtendsWitnesses` with no manual ordering or consistency hypotheses. -/
theorem proverAssignment_extendsWitnesses
    (self : TopLevelCircuit F Config PublicInput)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F) :
    ExtendsWitnesses self.placement
      (self.proverEnvironment (self.proverAssignment inst hint) hint)
      self.operations 0 :=
  self.proverAssignment_extendsWitnesses_of Determined.nonAdvice
    self.computableWitnesses self.writesConsistent inst hint

/-- Explicit-premise existential witness construction for a `TopLevelCircuit`. -/
theorem exists_witness_of
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
    self.proverAssignment_extendsWitnesses_of S₀ hcomp hcons inst hint⟩

/-- Automatic existential witness construction for any `TopLevelCircuit`. -/
theorem exists_witness
    (self : TopLevelCircuit F Config PublicInput)
    (inst : Column .instance → ℤ → F) (hint : ProverHint F) :
    ∃ assignment : ProofAssignment F,
      assignment.inst = inst ∧
      ExtendsWitnesses self.placement
        (self.proverEnvironment assignment hint) self.operations 0 :=
  ⟨self.proverAssignment inst hint, rfl,
    self.proverAssignment_extendsWitnesses inst hint⟩

/-- Explicit-premise non-vacuous existential top-level completeness. -/
theorem exists_completeness_of
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
  have hwitnesses := self.proverAssignment_extendsWitnesses_of S₀ hcomp hcons inst hint
  have hcomplete := self.completeness assignment hint hwitnesses hprover
  exact ⟨assignment, rfl, hwitnesses, hcomplete.1, hcomplete.2⟩

/-- Automatic non-vacuous existential top-level completeness for any `TopLevelCircuit`: given only
`ProverAssumptions` on the constructively generated proof assignment, there exists a
`ProofAssignment F` with public instances `inst` satisfying `ExtendsWitnesses`, `Constraints`, and
`ProverSpec`. -/
theorem exists_completeness
    (self : TopLevelCircuit F Config PublicInput)
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
        hint :=
  self.exists_completeness_of Determined.nonAdvice
    self.computableWitnesses self.writesConsistent inst hint hprover

/-- Kernel-reducible `Fast.orderedAdvice` discharges `ComputableWitnesses` and `WritesConsistent`
for any `TopLevelCircuit` (automatically handling repeated equal-valued `assignFixed` pins via
`fixedAssignment_eq_fixedValue`). -/
theorem computableWitnesses_and_writesConsistent_of_orderedAdvice
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
