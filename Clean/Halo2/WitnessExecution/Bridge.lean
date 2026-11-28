module

public import Clean.Halo2.WitnessExecution
public import Clean.Halo2.Operations.Consumption
public import Clean.Halo2.Operations.AdviceWrites
public import Clean.Halo2.Keygen.FloorPlanner.V1Correctness

@[expose] public section

/-!
# Compositional bridge to `ComputableWitnesses` and `WritesConsistent`

Connects the compositional keygen/elaboration invariants to the execution-level predicates of
`Clean.Halo2.WitnessExecution`:
- `Operations.computableWitnesses_of_readsAssigned` /
  `Operations.computableWitnesses_of_consumedCellsAssigned`: compositional read provenance
  (`ConsumedCellsAssigned 0 []`) implies `Operations.ComputableWitnesses place Determined.nonAdvice 0`
  for every placement `place`, covering both structured `WitgenIR` and `.native` callbacks certified
  via `WitnessSupport`.
- `Operations.writesConsistent_of_adviceWritesConsistent`: per-region `AdviceWritesConsistent`
  combined with floor-planner `SharedColumnIntervalsDisjoint` (and agreement of repeated fixed
  writes) implies `Operations.WritesConsistent (fun r => starts.getD r 0) Determined.nonAdvice 0`.
-/

namespace Halo2

variable {F : Type}

/-! ## Helpers on `Assignments.ComputableWitnesses` -/

section ComputableBridge

variable [FiniteField F]

theorem Assignments.ComputableWitnesses.mono {place : RegionIndex → ℕ}
    {S S' : Address → Prop} {assignments : List (Assignment F)}
    (hcomp : Assignments.ComputableWitnesses place S assignments)
    (hsub : ∀ addr, S addr → S' addr) :
    Assignments.ComputableWitnesses place S' assignments := by
  induction assignments generalizing S S' with
  | nil => trivial
  | cons a rest ih =>
    rcases hcomp with ⟨ha, hrest⟩
    refine ⟨fun left right hagree => ha left right (hagree.mono hsub), ?_⟩
    exact ih hrest fun addr h => h.elim Or.inl (fun hs => Or.inr (hsub addr hs))

theorem Assignments.ComputableWitnesses.append {place : RegionIndex → ℕ}
    {S : Address → Prop} {first second : List (Assignment F)}
    (hfirst : Assignments.ComputableWitnesses place S first)
    (hsecond : Assignments.ComputableWitnesses place
      (fun addr => (∃ a ∈ first, addr = a.destination) ∨ S addr) second) :
    Assignments.ComputableWitnesses place S (first ++ second) := by
  induction first generalizing S with
  | nil =>
    exact hsecond.mono fun addr h => by
      rcases h with ⟨_, ha, _⟩ | hS
      · cases ha
      · exact hS
  | cons a rest ih =>
    rcases hfirst with ⟨ha, hrest⟩
    refine ⟨ha, ih hrest ?_⟩
    exact hsecond.mono fun addr h => by
      rcases h with ⟨b, hb, rfl⟩ | hS
      · rcases List.mem_cons.mp hb with rfl | htail
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl ⟨b, htail, rfl⟩
      · exact Or.inr (Or.inr hS)

/-- Physical address set determined by initial set `S₀` together with the region-relative cells in
`available`. -/
def determinedFrom (place : RegionIndex → ℕ) (S₀ : Address → Prop)
    (available : List Cell) : Address → Prop :=
  fun addr =>
    S₀ addr ∨ ∃ c ∈ available, (c.column, (c.row place : ℤ)) = addr

omit [FiniteField F] in
private theorem exists_mem_regionAssignments_of_mem_assignedCells
    (place : RegionIndex → ℕ) (self : RegionIndex) (body : RegionOperations F)
    {c : Cell} (hc : c ∈ body.assignedCells self) :
    ∃ a ∈ body.assignments place self,
      (c.column, (c.row place : ℤ)) = a.destination := by
  induction body with
  | nil => simp [RegionOperations.assignedCells] at hc
  | cons op rest ih =>
    cases op with
    | assignAdvice column row prog =>
      simp only [RegionOperations.assignedCells_cons, RegionOperation.assignedCells,
        List.singleton_append, List.mem_cons] at hc
      rcases hc with rfl | htail
      · exact ⟨⟨(column.toAny, (place self + row : ℕ)), prog⟩, List.mem_cons_self, rfl⟩
      · obtain ⟨a, ha, heq⟩ := ih htail
        exact ⟨a, List.mem_cons_of_mem _ ha, heq⟩
    | assignFixed column row value =>
      simp only [RegionOperations.assignedCells_cons, RegionOperation.assignedCells,
        List.singleton_append, List.mem_cons] at hc
      rcases hc with rfl | htail
      · exact ⟨⟨(column.toAny, (place self + row : ℕ)), .ofFExpr (.const value)⟩,
          List.mem_cons_self, rfl⟩
      · obtain ⟨a, ha, heq⟩ := ih htail
        exact ⟨a, List.mem_cons_of_mem _ ha, heq⟩
    | enableGate _ _ | enableLookup _ _ _ | constrainEqual _ _
    | constrainConstant _ _ | constrainInstance _ _ _ =>
      simp only [RegionOperations.assignedCells_cons, RegionOperation.assignedCells,
        List.nil_append] at hc
      exact ih hc

private theorem witnessFunctionAgreement_of_agreesOn
    (place : RegionIndex → ℕ) (S₀ S : Address → Prop)
    (hnonAdvice : ∀ addr, Determined.nonAdvice addr → S₀ addr)
    (available : List Cell)
    (hsub : ∀ addr, determinedFrom place S₀ available addr → S addr)
    (reads : List (AssignedCell F))
    (hreads : ∀ c ∈ reads, c.cell.column.kind = .advice → c.cell ∈ available)
    {left right : ProverEnvironment F}
    (hagree : AgreesOn S left right) :
    WitnessFunctionAgreement reads ⟨place, left⟩ ⟨place, right⟩ where
  cellValues := by
    intro cell hcell
    by_cases hadv : cell.cell.column.kind = .advice
    · have hmem : cell.cell ∈ available := hreads cell hcell hadv
      have hS : S (AssignedCell.address place cell) :=
        hsub _ (Or.inr ⟨cell.cell, hmem, rfl⟩)
      exact hagree.2.2 (AssignedCell.address place cell) hS
    · have hS : S (AssignedCell.address place cell) :=
        hsub _ (Or.inl (hnonAdvice (AssignedCell.address place cell) hadv))
      exact hagree.2.2 (AssignedCell.address place cell) hS
  indexed := rfl
  data := rfl
  hints := hagree.1
  locals := rfl
  index := rfl
  place := rfl
  usableRows := hagree.2.1
  nonAdvice := by
    intro col row hkind
    exact hagree.2.2 (col, row) (hsub (col, row) (Or.inl (hnonAdvice (col, row) hkind)))

/-- Compositional region read provenance implies flat `ComputableWitnesses`. -/
theorem RegionOperations.computableWitnesses_of_readsAssigned
    (place : RegionIndex → ℕ) (S₀ S : Address → Prop)
    (hnonAdvice : ∀ addr, Determined.nonAdvice addr → S₀ addr)
    (self : RegionIndex) (available : List Cell) (body : RegionOperations F)
    (hsub : ∀ addr, determinedFrom place S₀ available addr → S addr)
    (hreads : body.AssignedFrom RegionOperation.Reads self available) :
    Assignments.ComputableWitnesses place S (body.assignments place self) := by
  induction body generalizing available S with
  | nil => trivial
  | cons op rest ih =>
    rw [RegionOperations.assignedFrom_cons_iff] at hreads
    rcases hreads with ⟨⟨cs, hcs_mem, hcs_avail⟩, hrest⟩
    cases op with
    | assignAdvice column row prog =>
      obtain ⟨reads, hsupport, hcover⟩ := hcs_mem
      refine ⟨?_, ?_⟩
      · intro left right hagree
        have hreads_avail : ∀ c ∈ reads, c.cell.column.kind = .advice → c.cell ∈ available :=
          fun c hc hadv => hcs_avail c.cell (hcover c hc hadv)
        exact hsupport ⟨place, left⟩ ⟨place, right⟩
          (witnessFunctionAgreement_of_agreesOn place S₀ S hnonAdvice available hsub reads
            hreads_avail hagree)
      · apply ih (fun addr => addr = (column.toAny, ((place self + row : ℕ) : ℤ)) ∨ S addr)
          ([Cell.of self row column] ++ available) _ hrest
        intro addr hdet
        rcases hdet with hS0 | ⟨c, hc, rfl⟩
        · exact Or.inr (hsub addr (Or.inl hS0))
        · rw [List.mem_append] at hc
          rcases hc with hnew | hold
          · simp only [List.mem_singleton] at hnew
            subst hnew
            exact Or.inl rfl
          · exact Or.inr (hsub _ (Or.inr ⟨c, hold, rfl⟩))
    | assignFixed column row value =>
      refine ⟨?_, ?_⟩
      · intro left right _
        simp [Halo2.eval_ofFExpr_zero, Witgen.FExprOver.eval]
      · apply ih (fun addr => addr = (column.toAny, ((place self + row : ℕ) : ℤ)) ∨ S addr)
          ([Cell.of self row column] ++ available) _ hrest
        intro addr hdet
        rcases hdet with hS0 | ⟨c, hc, rfl⟩
        · exact Or.inr (hsub addr (Or.inl hS0))
        · rw [List.mem_append] at hc
          rcases hc with hnew | hold
          · simp only [List.mem_singleton] at hnew
            subst hnew
            exact Or.inl rfl
          · exact Or.inr (hsub _ (Or.inr ⟨c, hold, rfl⟩))
    | enableGate _ _ | enableLookup _ _ _ | constrainEqual _ _
    | constrainConstant _ _ | constrainInstance _ _ _ =>
      simp only [RegionOperation.assignedCells] at hrest
      exact ih S available hsub (by simpa only [List.nil_append] using hrest)

/-- Compositional layouter read provenance implies flat `ComputableWitnesses`. -/
theorem Operations.computableWitnesses_of_readsAssigned
    (place : RegionIndex → ℕ) (S₀ S : Address → Prop)
    (hnonAdvice : ∀ addr, Determined.nonAdvice addr → S₀ addr)
    (self : RegionIndex) (available : List Cell) (ops : Operations F)
    (hsub : ∀ addr, determinedFrom place S₀ available addr → S addr)
    (hreads : ops.AssignedFrom RegionOperation.Reads self available) :
    Assignments.ComputableWitnesses place S (ops.assignments place self) := by
  induction ops generalizing self available S with
  | nil => trivial
  | cons op rest ih =>
    cases op with
    | region name body =>
      rw [Operations.assignedFrom_region_iff] at hreads
      rcases hreads with ⟨hbody, hrest⟩
      simp only [Operations.assignments]
      apply Assignments.ComputableWitnesses.append
      · exact RegionOperations.computableWitnesses_of_readsAssigned place S₀ S hnonAdvice self
          available body hsub hbody
      · apply ih (fun addr => (∃ a ∈ body.assignments place self, addr = a.destination) ∨ S addr)
          (self + 1) (body.assignedCellsAfter self available) _ hrest
        intro addr hdet
        rcases hdet with hS0 | ⟨c, hc, rfl⟩
        · exact Or.inr (hsub addr (Or.inl hS0))
        · rw [RegionOperations.mem_assignedCellsAfter_iff, List.mem_append] at hc
          rcases hc with hold | hnew
          · exact Or.inr (hsub _ (Or.inr ⟨c, hold, rfl⟩))
          · obtain ⟨a, ha, heq⟩ :=
              exists_mem_regionAssignments_of_mem_assignedCells place self body hnew
            exact Or.inl ⟨a, ha, heq⟩
    | constrainInstance cell col row =>
      rw [Operations.assignedFrom_constrainInstance_iff] at hreads
      exact ih S self available hsub hreads.2
    | loadTable table values =>
      rw [Operations.assignedFrom_loadTable_iff] at hreads
      exact ih S self available hsub hreads

/-- Closed compositional consumption provenance (`ConsumedCellsAssigned 0 []`) implies
`Operations.ComputableWitnesses` for any placement `place`. -/
theorem Operations.computableWitnesses_of_consumedCellsAssigned
    (place : RegionIndex → ℕ) (ops : Operations F)
    (hconsumed : ops.ConsumedCellsAssigned 0 []) :
    ops.ComputableWitnesses place Determined.nonAdvice 0 :=
  Operations.computableWitnesses_of_readsAssigned place Determined.nonAdvice Determined.nonAdvice
    (fun _ h => h) 0 [] ops
    (fun _ h => h.elim id (fun ⟨_, hmem, _⟩ => nomatch hmem))
    (Operations.readsAssigned_of_consumed ops 0 [] hconsumed)

end ComputableBridge

/-! ## Bridge from `AdviceWritesConsistent` + `SharedColumnIntervalsDisjoint` to `WritesConsistent` -/

section WritesConsistentBridge

private theorem exists_assignAdvice_of_mem_regionAssignments
    (place : RegionIndex → ℕ) (self : RegionIndex) (body : RegionOperations F)
    {a : Assignment F} (ha : a ∈ body.assignments place self)
    (hadvice : a.destination.1.kind = .advice) :
    ∃ (col : Column .advice) (localRow : ℕ),
      a.destination = (col.toAny, ((place self + localRow : ℕ) : ℤ)) ∧
      .assignAdvice col localRow a.program ∈ body := by
  induction body with
  | nil => simp [RegionOperations.assignments] at ha
  | cons op rest ih =>
    cases op with
    | assignAdvice col localRow prog =>
      rcases List.mem_cons.mp ha with rfl | htail
      · exact ⟨col, localRow, rfl, List.mem_cons_self⟩
      · obtain ⟨c, r, hdest, hmem⟩ := ih htail
        exact ⟨c, r, hdest, List.mem_cons_of_mem _ hmem⟩
    | assignFixed col localRow val =>
      rcases List.mem_cons.mp ha with rfl | htail
      · cases hadvice
      · obtain ⟨c, r, hdest, hmem⟩ := ih htail
        exact ⟨c, r, hdest, List.mem_cons_of_mem _ hmem⟩
    | enableGate _ _ | enableLookup _ _ _ | constrainEqual _ _
    | constrainConstant _ _ | constrainInstance _ _ _ =>
      obtain ⟨c, r, hdest, hmem⟩ := ih ha
      exact ⟨c, r, hdest, List.mem_cons_of_mem _ hmem⟩

private theorem mem_adviceWrites_of_mem_regionAssignments
    (place : RegionIndex → ℕ) (self : RegionIndex) (body : RegionOperations F)
    {a : Assignment F} (ha : a ∈ body.assignments place self)
    (hadvice : a.destination.1.kind = .advice) :
    ∃ (col : Column .advice) (localRow : ℕ),
      a.destination = (col.toAny, ((place self + localRow : ℕ) : ℤ)) ∧
      (col, localRow) ∈ body.adviceWrites := by
  obtain ⟨col, localRow, hdest, hmem⟩ :=
    exists_assignAdvice_of_mem_regionAssignments place self body ha hadvice
  exact ⟨col, localRow, hdest, RegionOperations.mem_adviceWrites_iff.mpr ⟨a.program, hmem⟩⟩

private theorem eval_of_isSelfCopy [FiniteField F]
    (place : RegionIndex → ℕ) (self : RegionIndex) (col : Column .advice) (row : ℕ)
    (prog : WitgenIR F 1)
    (hself : RegionOperation.IsSelfCopy self (.assignAdvice col row prog))
    (env : ProverEnvironment F) :
    (prog.eval ⟨place, env⟩)[0] = env.read (col.toAny, ((place self + row : ℕ) : ℤ)) := by
  unfold RegionOperation.IsSelfCopy RegionOperation.isSelfCopy at hself
  split at hself
  · rename_i _ col' row' v heq
    cases heq
    split at hself
    · rename_i src hv0
      simp only [decide_eq_true_eq] at hself
      simp only [Witgen.WitgenIROver.eval, Witgen.evalSteps, Witgen.VExprOver.eval,
        Vector.getElem_map, hv0, Witgen.FExprOver.eval, Witgen.WitgenEnv.readVar,
        AssignedCell.eval, hself, Cell.of, Cell.row, Column.toAny, ProverEnvironment.read]
    · cases hself
  · cases hself

private theorem regionAssignments_advice_consistent [FiniteField F]
    (place : RegionIndex → ℕ) (self : RegionIndex) (body : RegionOperations F)
    (hcons : body.AdviceWritesConsistent self) :
    (body.assignments place self).Pairwise fun a b =>
      a.destination = b.destination →
        a.destination.1.kind = .fixed ∨
        (∀ env : ProverEnvironment F,
          (a.program.eval ⟨place, env⟩)[0] = (b.program.eval ⟨place, env⟩)[0]) ∨
        (∀ env : ProverEnvironment F,
          (b.program.eval ⟨place, env⟩)[0] = env.read b.destination) := by
  induction body with
  | nil => exact List.Pairwise.nil
  | cons op rest ih =>
    cases op with
    | assignAdvice col localRow prog =>
      cases hcons with | assignAdvice hop hrest =>
      simp only [RegionOperations.assignments, List.pairwise_cons]
      refine ⟨?_, ih hrest⟩
      intro b hb hdest
      have hbadvice : b.destination.1.kind = .advice :=
        congrArg (fun p : Address => p.1.kind) hdest.symm
      obtain ⟨bcol, brow, hbdest, hbmem⟩ :=
        exists_assignAdvice_of_mem_regionAssignments place self rest hb hbadvice
      rw [hbdest, Prod.mk.injEq] at hdest
      have hcolEq : col = bcol := by
        cases col
        cases bcol
        simpa [Column.toAny] using hdest.1
      have hrowEq : localRow = brow := by
        have hnat : place self + localRow = place self + brow := Int.ofNat.inj hdest.2
        omega
      subst hcolEq hrowEq
      rcases hop b.program hbmem with hprogEq | hself
      · exact Or.inr (Or.inl fun env => hprogEq ⟨place, env⟩)
      · exact Or.inr (Or.inr fun env => by
          rw [hbdest]
          exact eval_of_isSelfCopy place self col localRow b.program hself env)
    | assignFixed col localRow val =>
      cases hcons with | assignFixed hrest =>
      simp only [RegionOperations.assignments, List.pairwise_cons]
      exact ⟨fun _ _ _ => Or.inl rfl, ih hrest⟩
    | enableGate _ _ =>
      cases hcons with | enableGate hrest => exact ih hrest
    | enableLookup _ _ _ =>
      cases hcons with | enableLookup hrest => exact ih hrest
    | constrainEqual _ _ =>
      cases hcons with | constrainEqual hrest => exact ih hrest
    | constrainConstant _ _ =>
      cases hcons with | constrainConstant hrest => exact ih hrest
    | constrainInstance _ _ _ =>
      cases hcons with | constrainInstance hrest => exact ih hrest

private theorem operations_assignments_eq_indexedRegions_flatMap
    (place : RegionIndex → ℕ) (ops : Operations F) (i₀ : RegionIndex) :
    ops.assignments place i₀ =
      (indexedRegions ops i₀).1.flatMap fun p => p.2.assignments place p.1 := by
  induction ops generalizing i₀ with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | region name body =>
      simp only [Operations.assignments, indexedRegions, List.flatMap_cons, ih]
    | constrainInstance _ _ _ | loadTable _ _ =>
      exact ih i₀

private theorem indexedRegions_forall_adviceWritesConsistent [FiniteField F]
    (ops : Operations F) (i₀ : RegionIndex) (hcons : ops.AdviceWritesConsistentFrom i₀) :
    (indexedRegions ops i₀).1.Forall fun p => p.2.AdviceWritesConsistent p.1 := by
  induction ops generalizing i₀ with
  | nil => simp [indexedRegions]
  | cons op rest ih =>
    cases op with
    | region name body =>
      rw [Operations.adviceWritesConsistentFrom_region_cons] at hcons
      simp only [indexedRegions, List.forall_cons]
      exact ⟨hcons.1, ih (i₀ + 1) hcons.2⟩
    | constrainInstance _ _ _ =>
      rw [Operations.adviceWritesConsistentFrom_constrainInstance_cons] at hcons
      exact ih i₀ hcons
    | loadTable _ _ =>
      rw [Operations.adviceWritesConsistentFrom_loadTable_cons] at hcons
      exact ih i₀ hcons

private theorem indexedRegions_fst_ge
    (ops : Operations F) (i₀ : RegionIndex) :
    ∀ p ∈ (indexedRegions ops i₀).1, i₀ ≤ p.1 := by
  induction ops generalizing i₀ with
  | nil => intro _ h; simp [indexedRegions] at h
  | cons op rest ih =>
    cases op with
    | region name body =>
      intro p hp
      simp only [indexedRegions, List.mem_cons] at hp
      rcases hp with rfl | htail
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (ih (i₀ + 1) p htail)
    | constrainInstance _ _ _ | loadTable _ _ =>
      exact ih i₀

private theorem indexedRegions_pairwise_lt
    (ops : Operations F) (i₀ : RegionIndex) :
    (indexedRegions ops i₀).1.Pairwise fun left right => left.1 < right.1 := by
  induction ops generalizing i₀ with
  | nil => simp [indexedRegions]
  | cons op rest ih =>
    cases op with
    | region name body =>
      simp only [indexedRegions, List.pairwise_cons]
      refine ⟨fun p hp => ?_, ih (i₀ + 1)⟩
      exact Nat.lt_of_succ_le (indexedRegions_fst_ge rest (i₀ + 1) p hp)
    | constrainInstance _ _ _ | loadTable _ _ =>
      exact ih i₀

/-- Per-region `AdviceWritesConsistent` + floor-planner `SharedColumnIntervalsDisjoint` guarantees
that any two assignments targeting the same physical address target a fixed column, compute the
same value in every environment, or the later assignment is an idempotent self-copy. -/
theorem Operations.assignments_pairwise_consistent_of_adviceWritesConsistent [FiniteField F]
    (starts : List ℕ) (ops : Operations F)
    (hcons : ops.AdviceWritesConsistent)
    (hdisjoint : FloorPlanner.SharedColumnIntervalsDisjoint (FloorPlanner.measureRegions ops) starts) :
    (ops.assignments (fun r => starts.getD r 0) 0).Pairwise fun a b =>
      a.destination = b.destination →
        a.destination.1.kind = .fixed ∨
        (∀ env : ProverEnvironment F,
          (a.program.eval ⟨fun r => starts.getD r 0, env⟩)[0] =
            (b.program.eval ⟨fun r => starts.getD r 0, env⟩)[0]) ∨
        (∀ env : ProverEnvironment F,
          (b.program.eval ⟨fun r => starts.getD r 0, env⟩)[0] = env.read b.destination) := by
  let place : RegionIndex → ℕ := fun r => starts.getD r 0
  rw [operations_assignments_eq_indexedRegions_flatMap place ops 0]
  have hallCons := List.forall_iff_forall_mem.mp
    (indexedRegions_forall_adviceWritesConsistent ops 0 hcons)
  have hlt := indexedRegions_pairwise_lt ops 0
  apply List.pairwise_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro p hp
    exact regionAssignments_advice_consistent place p.1 p.2 (hallCons p hp)
  · refine hlt.imp_of_mem ?_
    intro left right hleft hright hindexLt a ha b hb hdest
    have hnotInst := RegionOperations.assignments_not_instance place left.1 left.2 a ha
    cases hkind : a.destination.1.kind with
    | fixed => exact Or.inl rfl
    | «instance» => exact False.elim (hnotInst hkind)
    | advice =>
      exfalso
      have hbadvice : b.destination.1.kind = .advice := by
        rw [← hdest]
        exact hkind
      obtain ⟨acol, arow, hadest, hamem⟩ :=
        mem_adviceWrites_of_mem_regionAssignments place left.1 left.2 ha hkind
      obtain ⟨bcol, brow, hbdest, hbmem⟩ :=
        mem_adviceWrites_of_mem_regionAssignments place right.1 right.2 hb hbadvice
      have hcolEq : acol = bcol := by
        rw [hadest, hbdest, Prod.mk.injEq] at hdest
        cases acol
        cases bcol
        simpa [Column.toAny] using hdest.1
      subst hcolEq
      have hrowEq : starts.getD left.1 0 + arow = starts.getD right.1 0 + brow := by
        rw [hadest, hbdest, Prod.mk.injEq] at hdest
        exact Int.ofNat.inj hdest.2
      have haSummary := RegionOperations.mem_synthesisSummary_of_mem_adviceWrites hamem
      have hbSummary := RegionOperations.mem_synthesisSummary_of_mem_adviceWrites hbmem
      have hleftShape : FloorPlanner.measureRegion left.1 left.2 ∈ FloorPlanner.measureRegions ops :=
        List.mem_map.mpr ⟨left, hleft, rfl⟩
      have hrightShape : FloorPlanner.measureRegion right.1 right.2 ∈ FloorPlanner.measureRegions ops :=
        List.mem_map.mpr ⟨right, hright, rfl⟩
      have hne : (FloorPlanner.measureRegion left.1 left.2).index ≠
          (FloorPlanner.measureRegion right.1 right.2).index :=
        Nat.ne_of_lt hindexLt
      have hsep := hdisjoint hleftShape hrightShape hne haSummary.1 hbSummary.1
      simp only [FloorPlanner.measureRegion, FloorPlanner.RowIntervalsDisjoint] at hsep
      have haLt : arow < (FloorPlanner.regionSynthesisSummary left.2).rowCount := haSummary.2
      have hbLt : brow < (FloorPlanner.regionSynthesisSummary right.2).rowCount := hbSummary.2
      omega

/-- General cross-region bridge: per-region `AdviceWritesConsistent`, floor-planner
`SharedColumnIntervalsDisjoint`, and agreement of repeated fixed writes imply
`Operations.WritesConsistent`. Works for any floor planner (V1, Simple, etc.). -/
theorem Operations.writesConsistent_of_adviceWritesConsistent [FiniteField F]
    (starts : List ℕ) (ops : Operations F)
    (hcons : ops.AdviceWritesConsistent)
    (hdisjoint : FloorPlanner.SharedColumnIntervalsDisjoint (FloorPlanner.measureRegions ops) starts)
    (hfixedAgree : ∀ a ∈ ops.assignments (fun r => starts.getD r 0) 0,
      ∀ b ∈ ops.assignments (fun r => starts.getD r 0) 0,
      a.destination = b.destination → a.destination.1.kind = .fixed →
      ∀ env : ProverEnvironment F,
        (a.program.eval ⟨fun r => starts.getD r 0, env⟩)[0] =
        (b.program.eval ⟨fun r => starts.getD r 0, env⟩)[0]) :
    ops.WritesConsistent (fun r => starts.getD r 0) Determined.nonAdvice 0 where
  initialDisjoint := by
    intro a ha hnonAdv
    have hnotInst := ops.assignments_not_instance (fun r => starts.getD r 0) 0 a ha
    cases hkind : a.destination.1.kind with
    | fixed => rfl
    | advice => exact False.elim (hnonAdv hkind)
    | «instance» => exact False.elim (hnotInst hkind)
  pairwiseConsistent := by
    have hpair := Operations.assignments_pairwise_consistent_of_adviceWritesConsistent
      starts ops hcons hdisjoint
    refine hpair.imp_of_mem ?_
    intro a b ha hb hconsPair hdest
    rcases hconsPair hdest with hkind | hprog | hself
    · exact Or.inl (hfixedAgree a ha b hb hdest hkind)
    · exact Or.inl hprog
    · exact Or.inr hself

/-- Specialization of `writesConsistent_of_adviceWritesConsistent` when every region satisfies the
stronger `AdviceWritesDistinct`. -/
theorem Operations.writesConsistent_of_adviceWritesDistinct [FiniteField F]
    (starts : List ℕ) (ops : Operations F)
    (hdistinct : ops.AdviceWritesDistinct)
    (hdisjoint : FloorPlanner.SharedColumnIntervalsDisjoint (FloorPlanner.measureRegions ops) starts)
    (hfixedAgree : ∀ a ∈ ops.assignments (fun r => starts.getD r 0) 0,
      ∀ b ∈ ops.assignments (fun r => starts.getD r 0) 0,
      a.destination = b.destination → a.destination.1.kind = .fixed →
      ∀ env : ProverEnvironment F,
        (a.program.eval ⟨fun r => starts.getD r 0, env⟩)[0] =
        (b.program.eval ⟨fun r => starts.getD r 0, env⟩)[0]) :
    ops.WritesConsistent (fun r => starts.getD r 0) Determined.nonAdvice 0 :=
  Operations.writesConsistent_of_adviceWritesConsistent starts ops (hdistinct.toConsistent 0)
    hdisjoint hfixedAgree

end WritesConsistentBridge

end Halo2
