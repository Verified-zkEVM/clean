module

public import Clean.Circuit.WitnessReads
public import Clean.Halo2.Operations
public import Clean.Halo2.Operations.FixedWrites
public import Std.Data.TreeSet.Lemmas

@[expose] public section

/-!
# Halo2 witness execution, `ComputableWitnesses`, and `WritesConsistent`

Closes the vacuous-completeness gap for Halo2 circuits by connecting `ExtendsWitnesses` to an
executable sequential witness runner (`Execute.run`).

- **Address & flat assignment layer**: `Operations.assignments` flattens `.assignAdvice` and
  `.assignFixed` operations in op-fold order, and `Operations.extendsWitnesses_iff` characterizes
  `ExtendsWitnesses` as satisfaction of those assignments together with `Operations.TablesLoaded`.
- **Semantic predicates**:
  - `ComputableWitnesses`: walking the assignment stream from an initial determined cell set `S₀`,
    every assignment's witness program is `AgreesOn S`-invariant (its value depends only on `hint`,
    `usableRows`, `S₀`, and cells written earlier in the stream).
  - `WritesConsistent`: advice writes are pairwise distinct (no advice clobber) and never overwrite
    initially determined advice cells; repeated fixed writes are allowed iff they agree on their
    written value (e.g. boundary fixed re-pins).
- **Executable runner**: `Execute.run` evaluates each assignment sequentially and updates the
  prover environment. Under `ComputableWitnesses ∧ WritesConsistent` (plus initial consistency on
  any pre-seeded fixed cells), `Execute.run` preserves `S₀` and satisfies all assignment equations
  and `ExtendsWitnesses`.
- **Kernel-reducible checker (`Fast`)**: balanced-tree (`Std.TreeSet`) checkers `Fast.ordered`,
  `Fast.orderedWith`, and `Fast.orderedAdvice` over the full structured `WitgenIR` (via
  `Clean.Circuit.WitnessReads`) that discharge `ComputableWitnesses ∧ WritesConsistent`.
-/

namespace Halo2

variable {F : Type}

/-! ## Addresses and prover environment reads/writes -/

/-- A physical cell address `(column, absolute row)` in a Halo2 environment. -/
abbrev Address := AnyColumn × ℤ

/-- Resolve an `AssignedCell` to its physical `Address` under `place` (using `Cell.row`, so
instance cells resolve to their absolute `rowOffset` independent of `place`). -/
def AssignedCell.address (place : RegionIndex → ℕ) (cell : AssignedCell F) : Address :=
  (cell.cell.column, (cell.cell.row place : ℤ))

/-- Read a physical cell address from a prover environment. -/
def ProverEnvironment.read (env : ProverEnvironment F) (addr : Address) : F :=
  env.get addr.1 addr.2

/-- Update a single physical cell address in a prover environment.

Reference functional update used by `Execute.run`: chaining `n` updates builds `n`-deep nested
closures (quadratic aggregate lookup cost). Production witness generation should use a flat
array or hash map rather than this specification helper. -/
def ProverEnvironment.write (env : ProverEnvironment F) (addr : Address) (value : F) :
    ProverEnvironment F :=
  { env with get := fun column row => if (column, row) = addr then value else env.get column row }

@[simp] theorem ProverEnvironment.read_write_same (env : ProverEnvironment F)
    (addr : Address) (value : F) :
    (env.write addr value).read addr = value := by
  simp [ProverEnvironment.read, ProverEnvironment.write]

theorem ProverEnvironment.read_write_other (env : ProverEnvironment F)
    (addr other : Address) (value : F) (hne : other ≠ addr) :
    (env.write addr value).read other = env.read other := by
  simp only [ProverEnvironment.read, ProverEnvironment.write, Prod.mk.eta, ite_eq_right hne]

@[simp] theorem ProverEnvironment.write_hint (env : ProverEnvironment F)
    (addr : Address) (value : F) :
    (env.write addr value).hint = env.hint := rfl

@[simp] theorem ProverEnvironment.write_usableRows (env : ProverEnvironment F)
    (addr : Address) (value : F) :
    (env.write addr value).usableRows = env.usableRows := rfl

/-! ## Environment agreement on a determined cell set -/

/-- Two prover environments agree on a determined cell set `S` when they carry the same hint,
the same usable-row bound, and identical cell values on every address in `S`. -/
def AgreesOn (S : Address → Prop) (left right : ProverEnvironment F) : Prop :=
  left.hint = right.hint ∧
  left.usableRows = right.usableRows ∧
  ∀ addr, S addr → left.read addr = right.read addr

namespace AgreesOn

theorem refl (S : Address → Prop) (env : ProverEnvironment F) : AgreesOn S env env :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem symm {S : Address → Prop} {left right : ProverEnvironment F}
    (h : AgreesOn S left right) : AgreesOn S right left :=
  ⟨h.1.symm, h.2.1.symm, fun addr haddr => (h.2.2 addr haddr).symm⟩

theorem trans {S : Address → Prop} {a b c : ProverEnvironment F}
    (hab : AgreesOn S a b) (hbc : AgreesOn S b c) : AgreesOn S a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1,
    fun addr haddr => (hab.2.2 addr haddr).trans (hbc.2.2 addr haddr)⟩

theorem mono {S S' : Address → Prop} {left right : ProverEnvironment F}
    (h : AgreesOn S left right) (hsub : ∀ addr, S' addr → S addr) :
    AgreesOn S' left right :=
  ⟨h.1, h.2.1, fun addr haddr => h.2.2 addr (hsub addr haddr)⟩

theorem write_of_not_mem {S : Address → Prop} (env : ProverEnvironment F)
    (addr : Address) (value : F) (hnot : ¬ S addr) :
    AgreesOn S env (env.write addr value) := by
  refine ⟨rfl, rfl, fun other hother => ?_⟩
  have hne : other ≠ addr := fun heq => hnot (heq ▸ hother)
  exact (env.read_write_other addr other value hne).symm

theorem write_of_eq {S : Address → Prop} (env : ProverEnvironment F)
    (addr : Address) (value : F) (heq : value = env.read addr) :
    AgreesOn S env (env.write addr value) := by
  refine ⟨rfl, rfl, fun other _ => ?_⟩
  by_cases h : other = addr
  · subst h
    simp [heq]
  · exact (env.read_write_other addr other value h).symm

end AgreesOn

/-! Standard initial determined address sets for witness computation. -/
namespace Determined

/-- No cells are pre-determined: every read must come from an earlier assignment. -/
def empty : Address → Prop := fun _ => False

/-- Public instance cells are pre-determined. -/
def instances : Address → Prop := fun addr => addr.1.kind = .instance

/-- Both public instance and fixed/table cells are pre-determined. -/
def nonAdvice : Address → Prop := fun addr => addr.1.kind ≠ .advice

end Determined

/-! ## Flat scalar assignments and extraction from `Operations` -/

/-- A flattened scalar cell assignment: destination physical address and 1-element witness IR. -/
structure Assignment (F : Type) where
  destination : Address
  program : WitgenIR F 1

/-- Flatten all `assignAdvice` and `assignFixed` operations in a single region. -/
def RegionOperations.assignments (place : RegionIndex → ℕ) (self : RegionIndex) :
    RegionOperations F → List (Assignment F)
  | [] => []
  | .assignAdvice column row program :: rest =>
      ⟨(column, (place self + row : ℕ)), program⟩ :: RegionOperations.assignments place self rest
  | .assignFixed column row value :: rest =>
      ⟨(column, (place self + row : ℕ)), .ofFExpr (.const value)⟩ ::
        RegionOperations.assignments place self rest
  | _ :: rest => RegionOperations.assignments place self rest

/-- Flatten all `assignAdvice` and `assignFixed` operations in a layouter stream in op-fold order. -/
def Operations.assignments (place : RegionIndex → ℕ) :
    Operations F → RegionIndex → List (Assignment F)
  | [], _ => []
  | .region _ body :: rest, self =>
      body.assignments place self ++ Operations.assignments place rest (self + 1)
  | _ :: rest, self => Operations.assignments place rest self

/-- Every `loadTable` operation in `ops` is satisfied by `env`. -/
def Operations.TablesLoaded [FiniteField F] (env : Environment F) : Operations F → Prop
  | [] => True
  | .loadTable table values :: rest => TableLoaded env table values ∧ Operations.TablesLoaded env rest
  | _ :: rest => Operations.TablesLoaded env rest

theorem RegionOperations.assignments_append (place : RegionIndex → ℕ) (self : RegionIndex)
    (left right : RegionOperations F) :
    (left ++ right).assignments place self =
      left.assignments place self ++ right.assignments place self := by
  induction left with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp only [List.cons_append, RegionOperations.assignments, ih]

theorem Operations.assignments_append (place : RegionIndex → ℕ)
    (left right : Operations F) (self : RegionIndex) :
    (left ++ right).assignments place self =
      left.assignments place self ++ right.assignments place (self + left.regionCount) := by
  induction left generalizing self with
  | nil => simp [Operations.assignments, Operations.regionCount]
  | cons op rest ih =>
    cases op with
    | region _ body =>
      simp only [List.cons_append, Operations.assignments, Operations.regionCount, ih,
        List.append_assoc]
      congr 2
      exact congrArg (Operations.assignments place right)
        (Nat.add_assoc self 1 (Operations.regionCount rest))
    | constrainInstance _ _ _ =>
      exact ih self
    | loadTable _ _ =>
      exact ih self

theorem RegionOperations.assignments_not_instance (place : RegionIndex → ℕ) (self : RegionIndex)
    (ops : RegionOperations F) (assignment : Assignment F)
    (hmem : assignment ∈ ops.assignments place self) :
    assignment.destination.1.kind ≠ .instance := by
  induction ops with
  | nil => simp [RegionOperations.assignments] at hmem
  | cons op rest ih =>
    cases op with
    | assignAdvice _ _ _ =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · intro h; cases h
      · exact ih htail
    | assignFixed _ _ _ =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · intro h; cases h
      · exact ih htail
    | enableGate _ _ | enableLookup _ _ _ | constrainEqual _ _
    | constrainConstant _ _ | constrainInstance _ _ _ =>
      exact ih hmem

theorem Operations.assignments_not_instance (place : RegionIndex → ℕ) (self : RegionIndex)
    (ops : Operations F) (assignment : Assignment F)
    (hmem : assignment ∈ ops.assignments place self) :
    assignment.destination.1.kind ≠ .instance := by
  induction ops generalizing self with
  | nil => simp [Operations.assignments] at hmem
  | cons op rest ih =>
    cases op with
    | region _ body =>
      rcases List.mem_append.mp hmem with hhead | htail
      · exact body.assignments_not_instance place self assignment hhead
      · exact ih (self + 1) htail
    | _ => exact ih self hmem

theorem RegionOperations.assignments_column (place : RegionIndex → ℕ) (self : RegionIndex)
    (ops : RegionOperations F) (assignment : Assignment F)
    (hmem : assignment ∈ ops.assignments place self) :
    assignment.destination.1.kind = .advice ∨
      ∃ column ∈ ops.fixedColumns, assignment.destination.1 = column.toAny := by
  induction ops with
  | nil => simp [RegionOperations.assignments] at hmem
  | cons op rest ih =>
    cases op with
    | assignAdvice _ _ _ =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Or.inl rfl
      · exact ih htail
    | assignFixed column _ _ =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Or.inr ⟨column, List.mem_cons_self, rfl⟩
      · rcases ih htail with hadvice | ⟨col, hcol, heq⟩
        · exact Or.inl hadvice
        · exact Or.inr ⟨col, List.mem_cons_of_mem column hcol, heq⟩
    | _ => exact ih hmem

theorem Operations.assignments_column (place : RegionIndex → ℕ) (self : RegionIndex)
    (ops : Operations F) (assignment : Assignment F)
    (hmem : assignment ∈ ops.assignments place self) :
    assignment.destination.1.kind = .advice ∨
      ∃ column ∈ ops.regionFixedColumns, assignment.destination.1 = column.toAny := by
  induction ops generalizing self with
  | nil => simp [Operations.assignments] at hmem
  | cons op rest ih =>
    cases op with
    | region _ body =>
      rcases List.mem_append.mp hmem with hhead | htail
      · rcases body.assignments_column place self assignment hhead with hadvice | ⟨col, hcol, heq⟩
        · exact Or.inl hadvice
        · exact Or.inr ⟨col, List.mem_append_left _ hcol, heq⟩
      · rcases ih (self + 1) htail with hadvice | ⟨col, hcol, heq⟩
        · exact Or.inl hadvice
        · exact Or.inr ⟨col, List.mem_append_right _ hcol, heq⟩
    | _ => exact ih self hmem

/-- `FixedWritesLawful` guarantees that no flattened scalar assignment targets any loaded lookup
table column. -/
theorem Operations.assignments_separate_tables (place : RegionIndex → ℕ) (self : RegionIndex)
    (ops : Operations F) (constants : List (Column .fixed))
    (hlawful : ops.FixedWritesLawful constants) :
    ∀ assignment ∈ ops.assignments place self,
      assignment.destination.1 ∉ ops.loadedTableColumns.map Column.toAny := by
  intro assignment hmem htable
  obtain ⟨tableCol, htableCol, heq⟩ := List.mem_map.mp htable
  rcases ops.assignments_column place self assignment hmem with hadvice | ⟨col, hcol, hcolEq⟩
  · have hkind := congrArg AnyColumn.kind heq
    rw [hadvice] at hkind
    cases hkind
  · have hsame : tableCol = col := by
      cases tableCol
      cases col
      simpa only [Column.toAny, AnyColumn.mk.injEq, true_and, Column.mk.injEq] using
        heq.trans hcolEq
    subst col
    exact List.disjoint_left.mp hlawful.loadedTableColumns_disjoint_regionFixedColumns htableCol hcol

section Semantics

variable [FiniteField F]

/-- Every assignment equation in a flat assignment list holds in `env`. -/
def Assignments.Satisfies (place : RegionIndex → ℕ) (env : ProverEnvironment F)
    (assignments : List (Assignment F)) : Prop :=
  ∀ assignment ∈ assignments,
    env.read assignment.destination = (assignment.program.eval ⟨place, env⟩)[0]

theorem Assignments.satisfies_cons (place : RegionIndex → ℕ) (env : ProverEnvironment F)
    (assignment : Assignment F) (rest : List (Assignment F)) :
    Assignments.Satisfies place env (assignment :: rest) ↔
      env.read assignment.destination = (assignment.program.eval ⟨place, env⟩)[0] ∧
        Assignments.Satisfies place env rest := by
  simp [Assignments.Satisfies, List.mem_cons, forall_eq_or_imp]

theorem Assignments.satisfies_append (place : RegionIndex → ℕ) (env : ProverEnvironment F)
    (first second : List (Assignment F)) :
    Assignments.Satisfies place env (first ++ second) ↔
      Assignments.Satisfies place env first ∧ Assignments.Satisfies place env second := by
  simp only [Assignments.Satisfies, List.mem_append, or_imp, forall_and]

theorem RegionOperations.satisfies_assignments_iff (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) (ops : RegionOperations F) :
    Assignments.Satisfies place env (ops.assignments place self) ↔
      RegionOperations.ExtendsWitnesses place self env ops := by
  induction ops with
  | nil => simp [Assignments.Satisfies, RegionOperations.assignments, RegionOperations.ExtendsWitnesses]
  | cons op rest ih =>
    cases op <;> simp only [RegionOperations.assignments, RegionOperations.ExtendsWitnesses,
      RegionOperation.ExtendsWitness, Assignments.satisfies_cons, ProverEnvironment.read,
      eval_ofFExpr_zero, Witgen.FExprOver.eval, true_and, ih]

/-- `ExtendsWitnesses` on an `Operations` stream is equivalent to satisfying all flattened scalar
assignments together with all `loadTable` equations. -/
theorem Operations.extendsWitnesses_iff (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) (ops : Operations F) :
    ExtendsWitnesses place env ops self ↔
      Assignments.Satisfies place env (ops.assignments place self) ∧
        ops.TablesLoaded env.toEnvironment := by
  induction ops generalizing self with
  | nil => simp [ExtendsWitnesses, Assignments.Satisfies, Operations.assignments, Operations.TablesLoaded]
  | cons op rest ih =>
    cases op with
    | region _ body =>
      simp only [ExtendsWitnesses, Operations.assignments, Operations.TablesLoaded,
        Assignments.satisfies_append, RegionOperations.satisfies_assignments_iff, ih, and_assoc]
    | constrainInstance _ _ _ =>
      exact ih self
    | loadTable _ _ =>
      simp only [ExtendsWitnesses, Operations.assignments, Operations.TablesLoaded, TableLoaded, ih]
      tauto

theorem Operations.tablesLoaded_append (env : Environment F) (left right : Operations F) :
    Operations.TablesLoaded env (left ++ right) ↔
      Operations.TablesLoaded env left ∧ Operations.TablesLoaded env right := by
  induction left with
  | nil => simp [Operations.TablesLoaded]
  | cons op rest ih =>
    cases op <;> simp only [List.cons_append, Operations.TablesLoaded, ih, and_assoc]

theorem Operations.tablesLoaded_congr (left right : Environment F) (ops : Operations F)
    (hrows : left.usableRows = right.usableRows)
    (hcolumns : ∀ column ∈ ops.loadedTableColumns.map Column.toAny, ∀ row : ℤ,
      left.get column row = right.get column row) :
    Operations.TablesLoaded left ops ↔ Operations.TablesLoaded right ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | region _ _ | constrainInstance _ _ _ => exact ih hcolumns
    | loadTable table values =>
      have htail := ih fun col hcol => hcolumns col (by
        rw [Operations.loadedTableColumns_loadTable_cons, List.map_append]
        exact List.mem_append_right _ hcol)
      by_cases hempty : values = []
      · subst hempty
        simp [Operations.TablesLoaded, TableLoaded, htail]
      · have hcol := hcolumns table.inner.toAny (by
          simp [Operations.loadedTableColumns_loadTable_cons, hempty])
        simp only [Operations.TablesLoaded, TableLoaded, Environment.fixed, hcol, hrows, htail]

/-! ## `ComputableWitnesses` and `WritesConsistent` -/

/-- A flat assignment list has computable witnesses from initial determined cell set `S` when each
assignment's program depends only on `hint`, `usableRows`, `S`, and earlier destinations. -/
def Assignments.ComputableWitnesses (place : RegionIndex → ℕ)
    (S : Address → Prop) : List (Assignment F) → Prop
  | [] => True
  | assignment :: rest =>
      (∀ left right : ProverEnvironment F,
        AgreesOn S left right →
        (assignment.program.eval ⟨place, left⟩)[0] =
          (assignment.program.eval ⟨place, right⟩)[0]) ∧
      Assignments.ComputableWitnesses place
        (fun addr => addr = assignment.destination ∨ S addr) rest

/-- A flat assignment list has consistent writes relative to initial determined set `S₀` when:
- no assignment writes to a non-fixed cell already in `S₀`; and
- advice writes are pairwise distinct (no advice clobber), while repeated fixed writes to the same
  physical address must agree on their value in every environment. -/
structure Assignments.WritesConsistent (place : RegionIndex → ℕ)
    (S₀ : Address → Prop) (assignments : List (Assignment F)) : Prop where
  initialDisjoint : ∀ a ∈ assignments, S₀ a.destination → a.destination.1.kind = .fixed
  adviceUnique : assignments.Pairwise fun a b =>
    a.destination = b.destination →
      a.destination.1.kind = .fixed ∧
      ∀ env : ProverEnvironment F,
        (a.program.eval ⟨place, env⟩)[0] = (b.program.eval ⟨place, env⟩)[0]

/-- `ComputableWitnesses` at the `Operations` level (flat write-trace order). -/
def Operations.ComputableWitnesses (place : RegionIndex → ℕ)
    (S₀ : Address → Prop) (ops : Operations F) (i₀ : RegionIndex := 0) : Prop :=
  Assignments.ComputableWitnesses place S₀ (ops.assignments place i₀)

/-- `WritesConsistent` at the `Operations` level (flat write-trace order). -/
def Operations.WritesConsistent (place : RegionIndex → ℕ)
    (S₀ : Address → Prop) (ops : Operations F) (i₀ : RegionIndex := 0) : Prop :=
  Assignments.WritesConsistent place S₀ (ops.assignments place i₀)

/-- Canonical top-level alias for `Operations.ComputableWitnesses`. -/
abbrev ComputableWitnesses (place : RegionIndex → ℕ)
    (S₀ : Address → Prop) (ops : Operations F) (i₀ : RegionIndex := 0) : Prop :=
  Operations.ComputableWitnesses place S₀ ops i₀

/-- Canonical top-level alias for `Operations.WritesConsistent`. -/
abbrev WritesConsistent (place : RegionIndex → ℕ)
    (S₀ : Address → Prop) (ops : Operations F) (i₀ : RegionIndex := 0) : Prop :=
  Operations.WritesConsistent place S₀ ops i₀

/-- In Halo2, syntactic read acceptance implies `AgreesOn`-invariance of `WitgenIR.eval`. -/
theorem program_eval_eq_of_readsAccepted (place : RegionIndex → ℕ)
    (S : Address → Prop) (allowed : AssignedCell F → Bool)
    (hallowed : ∀ cell, allowed cell = true → S (AssignedCell.address place cell))
    (program : WitgenIR F 1)
    (haccepted : Witgen.readsAccepted allowed (Witgen.programReads program) = true)
    (left right : ProverEnvironment F) (hagree : AgreesOn S left right) :
    (program.eval ⟨place, left⟩)[0] = (program.eval ⟨place, right⟩)[0] := by
  have heval : program.eval ⟨place, left⟩ = program.eval ⟨place, right⟩ := by
    apply Witgen.readsAccepted_programReads_eval allowed program haccepted ⟨place, left⟩ ⟨place, right⟩
    · intro cell hcell
      exact hagree.2.2 (AssignedCell.address place cell) (hallowed cell hcell)
    · rfl
    · rfl
    · exact hagree.1
  exact congrArg (fun v : Vector F 1 => v[0]) heval

/-- Strictly distinct destinations disjoint from `S₀` imply `WritesConsistent`. -/
theorem Assignments.WritesConsistent.of_disjoint_nodup (place : RegionIndex → ℕ)
    (S₀ : Address → Prop) (assignments : List (Assignment F))
    (hdisjoint : ∀ a ∈ assignments, ¬ S₀ a.destination)
    (hnodup : (assignments.map Assignment.destination).Nodup) :
    Assignments.WritesConsistent place S₀ assignments where
  initialDisjoint := fun a hmem hS => False.elim (hdisjoint a hmem hS)
  adviceUnique := by
    rw [List.Nodup, List.pairwise_map] at hnodup
    exact hnodup.imp fun hne heq => False.elim (hne heq)

/-! ## Executable sequential witness runner (`Execute`) -/

namespace Execute

/-- Execute one scalar assignment, writing its computed value into the environment. -/
def step (place : RegionIndex → ℕ) (env : ProverEnvironment F) (assignment : Assignment F) :
    ProverEnvironment F :=
  env.write assignment.destination (assignment.program.eval ⟨place, env⟩)[0]

/-- Reference sequential witness executor: executes a flat assignment stream left to right by
chaining `ProverEnvironment.write` updates.

Intended as a clean specification/proof runner rather than a high-throughput prover: nested closure
updates give `O(n²)` aggregate lookup cost over `n` assignments, so production witness generation
should evaluate into a flat array or map. -/
def run (place : RegionIndex → ℕ) :
    List (Assignment F) → ProverEnvironment F → ProverEnvironment F
  | [], env => env
  | assignment :: rest, env => run place rest (step place env assignment)

@[simp] theorem run_nil (place : RegionIndex → ℕ) (env : ProverEnvironment F) :
    run place [] env = env := rfl

@[simp] theorem run_cons (place : RegionIndex → ℕ) (assignment : Assignment F)
    (rest : List (Assignment F)) (env : ProverEnvironment F) :
    run place (assignment :: rest) env = run place rest (step place env assignment) := rfl

@[simp] theorem run_hint (place : RegionIndex → ℕ) (assignments : List (Assignment F))
    (env : ProverEnvironment F) :
    (run place assignments env).hint = env.hint := by
  induction assignments generalizing env with
  | nil => rfl
  | cons assignment rest ih => exact ih (step place env assignment)

@[simp] theorem run_usableRows (place : RegionIndex → ℕ) (assignments : List (Assignment F))
    (env : ProverEnvironment F) :
    (run place assignments env).usableRows = env.usableRows := by
  induction assignments generalizing env with
  | nil => rfl
  | cons assignment rest ih => exact ih (step place env assignment)

/-- Addresses outside the write set are untouched by `Execute.run`. -/
theorem run_preserves_unwritten (place : RegionIndex → ℕ) (assignments : List (Assignment F))
    (env : ProverEnvironment F) (addr : Address)
    (hunwritten : ∀ assignment ∈ assignments, addr ≠ assignment.destination) :
    (run place assignments env).read addr = env.read addr := by
  induction assignments generalizing env with
  | nil => rfl
  | cons assignment rest ih =>
    have htail := ih (step place env assignment)
      (fun next hmem => hunwritten next (List.mem_cons_of_mem _ hmem))
    exact htail.trans (env.read_write_other assignment.destination addr _
      (hunwritten assignment List.mem_cons_self))

/-- `Execute.run` on `Operations.assignments` never modifies instance columns. -/
theorem run_instance (place : RegionIndex → ℕ) (self : RegionIndex)
    (ops : Operations F) (initial : ProverEnvironment F) (column : Column .instance) (row : ℤ) :
    (run place (ops.assignments place self) initial).inst column row = initial.inst column row := by
  apply run_preserves_unwritten place (ops.assignments place self) initial (column.toAny, row)
  intro assignment hmem heq
  have hkind := congrArg (fun addr : Address => addr.1.kind) heq
  exact ops.assignments_not_instance place self assignment hmem hkind.symm

/-- Core soundness theorem for `Execute.run`: under `ComputableWitnesses`, `WritesConsistent`, and
agreement of `initial` with any assignment targeting an initially determined fixed cell, sequential
execution preserves `S` and satisfies every assignment equation in the final environment. -/
theorem run_agreesOn_and_satisfies (place : RegionIndex → ℕ) (assignments : List (Assignment F))
    (S : Address → Prop) (initial : ProverEnvironment F)
    (hcomp : Assignments.ComputableWitnesses place S assignments)
    (hcons : Assignments.WritesConsistent place S assignments)
    (hinit : ∀ a ∈ assignments, S a.destination →
      ∀ env : ProverEnvironment F, AgreesOn S initial env →
        (a.program.eval ⟨place, env⟩)[0] = initial.read a.destination) :
    AgreesOn S initial (run place assignments initial) ∧
      Assignments.Satisfies place (run place assignments initial) assignments := by
  induction assignments generalizing S initial with
  | nil =>
    exact ⟨AgreesOn.refl S initial, fun _ hmem => False.elim (List.not_mem_nil hmem)⟩
  | cons assignment rest ih =>
    rcases hcomp with ⟨ha_comp, hrest_comp⟩
    have hpair := List.pairwise_cons.mp hcons.adviceUnique
    let S' : Address → Prop := fun addr => addr = assignment.destination ∨ S addr
    let env₁ := step place initial assignment
    have hstep_agree : AgreesOn S initial env₁ := by
      by_cases hS : S assignment.destination
      · exact AgreesOn.write_of_eq initial assignment.destination _
          (hinit assignment List.mem_cons_self hS initial (AgreesOn.refl S initial))
      · exact AgreesOn.write_of_not_mem initial assignment.destination _ hS
    have hrest_cons : Assignments.WritesConsistent place S' rest := by
      refine ⟨?_, hpair.2⟩
      intro b hb hS'
      rcases hS' with heq | hS
      · have hfixed := (hpair.1 b hb heq.symm).1
        rw [heq]
        exact hfixed
      · exact hcons.initialDisjoint b (List.mem_cons_of_mem _ hb) hS
    have hrest_init : ∀ b ∈ rest, S' b.destination →
        ∀ env : ProverEnvironment F, AgreesOn S' env₁ env →
          (b.program.eval ⟨place, env⟩)[0] = env₁.read b.destination := by
      intro b hb hS' env hagree'
      have hagreeS : AgreesOn S initial env :=
        hstep_agree.trans (hagree'.mono fun _ h => Or.inr h)
      rcases hS' with heq | hS
      · have hvalEq := (hpair.1 b hb heq.symm).2 env
        have haEq := ha_comp initial env hagreeS
        rw [← hvalEq, ← haEq, heq]
        exact (ProverEnvironment.read_write_same initial assignment.destination _).symm
      · have hbInit := hinit b (List.mem_cons_of_mem _ hb) hS env hagreeS
        rw [hbInit]
        exact hstep_agree.2.2 b.destination hS
    obtain ⟨hrest_agree, hrest_sat⟩ := ih S' env₁ hrest_comp hrest_cons hrest_init
    have hfinal_agree : AgreesOn S initial (run place (assignment :: rest) initial) :=
      hstep_agree.trans (hrest_agree.mono fun _ h => Or.inr h)
    refine ⟨hfinal_agree, ?_⟩
    apply (Assignments.satisfies_cons place _ assignment rest).mpr
    refine ⟨?_, hrest_sat⟩
    have hdest : (run place rest env₁).read assignment.destination =
        env₁.read assignment.destination :=
      (hrest_agree.2.2 assignment.destination (Or.inl rfl)).symm
    have hprog : (assignment.program.eval ⟨place, initial⟩)[0] =
        (assignment.program.eval ⟨place, run place (assignment :: rest) initial⟩)[0] :=
      ha_comp initial (run place (assignment :: rest) initial) hfinal_agree
    exact hdest.trans ((ProverEnvironment.read_write_same initial assignment.destination _).trans hprog)

/-- Specialized soundness when no assignment targets an initially determined cell in `S₀`. -/
theorem run_agreesOn_and_satisfies_of_disjoint (place : RegionIndex → ℕ)
    (assignments : List (Assignment F)) (S₀ : Address → Prop) (initial : ProverEnvironment F)
    (hcomp : Assignments.ComputableWitnesses place S₀ assignments)
    (hcons : Assignments.WritesConsistent place S₀ assignments)
    (hdisjoint : ∀ a ∈ assignments, ¬ S₀ a.destination) :
    AgreesOn S₀ initial (run place assignments initial) ∧
      Assignments.Satisfies place (run place assignments initial) assignments :=
  run_agreesOn_and_satisfies place assignments S₀ initial hcomp hcons
    (fun a hmem hS => False.elim (hdisjoint a hmem hS))

/-- `Execute.run` constructs a prover environment satisfying `ExtendsWitnesses` on `ops`. -/
theorem run_extendsWitnesses (place : RegionIndex → ℕ) (i₀ : RegionIndex)
    (ops : Operations F) (S₀ : Address → Prop) (initial : ProverEnvironment F)
    (hcomp : Operations.ComputableWitnesses place S₀ ops i₀)
    (hcons : Operations.WritesConsistent place S₀ ops i₀)
    (hinit : ∀ a ∈ ops.assignments place i₀, S₀ a.destination →
      ∀ env : ProverEnvironment F, AgreesOn S₀ initial env →
        (a.program.eval ⟨place, env⟩)[0] = initial.read a.destination)
    (htables : ops.TablesLoaded initial.toEnvironment)
    (hseparate : ∀ a ∈ ops.assignments place i₀,
      a.destination.1 ∉ ops.loadedTableColumns.map Column.toAny) :
    AgreesOn S₀ initial (run place (ops.assignments place i₀) initial) ∧
      ExtendsWitnesses place (run place (ops.assignments place i₀) initial) ops i₀ := by
  obtain ⟨hagree, hsat⟩ :=
    run_agreesOn_and_satisfies place (ops.assignments place i₀) S₀ initial hcomp hcons hinit
  refine ⟨hagree, (ops.extendsWitnesses_iff place i₀ _).mpr ⟨hsat, ?_⟩⟩
  apply (ops.tablesLoaded_congr
    (run place (ops.assignments place i₀) initial).toEnvironment
    initial.toEnvironment (run_usableRows place _ initial) ?_).mpr htables
  intro column hcol row
  apply run_preserves_unwritten place (ops.assignments place i₀) initial (column, row)
  intro assignment hmem heq
  exact hseparate assignment hmem (congrArg Prod.fst heq ▸ hcol)

/-- Existential payoff theorem at the `Operations` level: given `ComputableWitnesses` and
`WritesConsistent`, there exists a prover environment extending `initial` on `S₀` that satisfies
`ExtendsWitnesses`. -/
theorem exists_extendsWitnesses (place : RegionIndex → ℕ) (i₀ : RegionIndex)
    (ops : Operations F) (S₀ : Address → Prop) (initial : ProverEnvironment F)
    (hcomp : Operations.ComputableWitnesses place S₀ ops i₀)
    (hcons : Operations.WritesConsistent place S₀ ops i₀)
    (hinit : ∀ a ∈ ops.assignments place i₀, S₀ a.destination →
      ∀ env : ProverEnvironment F, AgreesOn S₀ initial env →
        (a.program.eval ⟨place, env⟩)[0] = initial.read a.destination)
    (htables : ops.TablesLoaded initial.toEnvironment)
    (hseparate : ∀ a ∈ ops.assignments place i₀,
      a.destination.1 ∉ ops.loadedTableColumns.map Column.toAny) :
    ∃ env : ProverEnvironment F,
      AgreesOn S₀ initial env ∧ ExtendsWitnesses place env ops i₀ :=
  ⟨run place (ops.assignments place i₀) initial,
    run_extendsWitnesses place i₀ ops S₀ initial hcomp hcons hinit htables hseparate⟩

end Execute

/-! ## Kernel-reducible balanced-tree checker (`Fast`) -/

namespace Fast

attribute [local instance] lexOrd

/-- Comparable key for a physical cell address; reduces in Lean's kernel. -/
abbrev Key := ℕ × ℕ × ℤ

/-- Encode a physical address as an ordered triple `(kindTag, columnIndex, row)`. -/
def key (addr : Address) : Key :=
  ((match addr.1.kind with | .advice => 0 | .fixed => 1 | .instance => 2),
    addr.1.index, addr.2)

theorem key_injective : Function.Injective key := by
  rintro ⟨⟨leftKind, leftIndex⟩, leftRow⟩ ⟨⟨rightKind, rightIndex⟩, rightRow⟩ heq
  cases leftKind <;> cases rightKind <;> simp_all [key]

/-- Kernel-reducible ordered dependency & freshness checker over the full structured `WitgenIR`,
parameterized by an initial pre-determined address predicate `seed`. -/
def orderedWith (seed : Address → Bool) (place : RegionIndex → ℕ) :
    Std.TreeSet Key → List (Assignment F) → Bool
  | _, [] => true
  | known, assignment :: rest =>
      !seed assignment.destination &&
      !known.contains (key assignment.destination) &&
      Witgen.readsAccepted
        (fun cell =>
          let addr := AssignedCell.address place cell
          seed addr || known.contains (key addr))
        (Witgen.programReads assignment.program) &&
      orderedWith seed place (known.insert (key assignment.destination)) rest

/-- Kernel-reducible ordered dependency & freshness checker with no pre-seeded cells (`seed = false`).
Every read must refer to an assignment appearing earlier in the stream, and every destination must
be fresh. -/
def ordered (place : RegionIndex → ℕ) : Std.TreeSet Key → List (Assignment F) → Bool
  | _, [] => true
  | known, assignment :: rest =>
      !known.contains (key assignment.destination) &&
      Witgen.readsAccepted
        (fun cell => known.contains (key (AssignedCell.address place cell)))
        (Witgen.programReads assignment.program) &&
      ordered place (known.insert (key assignment.destination)) rest

omit [FiniteField F] in
theorem ordered_eq_orderedWith_false (place : RegionIndex → ℕ)
    (known : Std.TreeSet Key) (assignments : List (Assignment F)) :
    ordered place known assignments = orderedWith (fun _ => false) place known assignments := by
  induction assignments generalizing known with
  | nil => rfl
  | cons assignment rest ih =>
    simp only [ordered, orderedWith, Bool.not_false, Bool.true_and, Bool.false_or, ih]

/-- Kernel-reducible advice-only checker where all fixed and instance cells are pre-determined.
Checks that advice destinations are pairwise distinct and that every structured witness program
reads only non-advice cells or earlier advice cells. Fixed writes are not required to be
deduplicated (allowing repeated equal-valued `assignFixed` pins verified separately). -/
def orderedAdvice (place : RegionIndex → ℕ) : Std.TreeSet Key → List (Assignment F) → Bool
  | _, [] => true
  | known, assignment :: rest =>
      match assignment.destination.1.kind with
      | .advice =>
          !known.contains (key assignment.destination) &&
          Witgen.readsAccepted
            (fun cell =>
              let addr := AssignedCell.address place cell
              addr.1.kind != .advice || known.contains (key addr))
            (Witgen.programReads assignment.program) &&
          orderedAdvice place (known.insert (key assignment.destination)) rest
      | .fixed =>
          Witgen.readsAccepted
            (fun cell =>
              let addr := AssignedCell.address place cell
              addr.1.kind != .advice || known.contains (key addr))
            (Witgen.programReads assignment.program) &&
          orderedAdvice place known rest
      | .instance => false

private theorem orderedWith_sound_aux (seed : Address → Bool) (place : RegionIndex → ℕ)
    (assignments : List (Assignment F)) (known : Std.TreeSet Key)
    (S : Address → Prop)
    (hS : ∀ addr, S addr ↔ seed addr = true ∨ known.contains (key addr) = true)
    (hacc : orderedWith seed place known assignments = true) :
    Assignments.ComputableWitnesses place S assignments ∧
      (∀ a ∈ assignments, ¬ S a.destination) ∧
      (assignments.map Assignment.destination).Nodup := by
  induction assignments generalizing known S with
  | nil =>
    exact ⟨trivial, fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩
  | cons assignment rest ih =>
    simp only [orderedWith, Bool.and_eq_true, Bool.not_eq_true'] at hacc
    rcases hacc with ⟨⟨⟨hnotSeed, hnotKnown⟩, hreads⟩, hrest⟩
    have hfresh : ¬ S assignment.destination := by
      rw [hS]
      simp [hnotSeed, hnotKnown]
    let S' : Address → Prop := fun addr => addr = assignment.destination ∨ S addr
    have hS' : ∀ addr, S' addr ↔
        seed addr = true ∨ (known.insert (key assignment.destination)).contains (key addr) = true := by
      intro addr
      simp only [S', hS, Std.TreeSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
        Std.compare_eq_iff_eq, key_injective.eq_iff]
      constructor
      · rintro (rfl | hseed | hknown)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hseed
        · exact Or.inr (Or.inr hknown)
      · rintro (hseed | heq | hknown)
        · exact Or.inr (Or.inl hseed)
        · exact Or.inl heq.symm
        · exact Or.inr (Or.inr hknown)
    obtain ⟨hrest_comp, hrest_disj, hrest_nodup⟩ :=
      ih (known.insert (key assignment.destination)) S' hS' hrest
    refine ⟨⟨?_, hrest_comp⟩, ?_, ?_⟩
    · intro left right hagree
      apply program_eval_eq_of_readsAccepted place S _ _ assignment.program hreads left right hagree
      intro cell hcell
      rw [hS]
      simpa only [Bool.or_eq_true] using hcell
    · intro a hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact hfresh
      · exact fun hSa => hrest_disj a htail (Or.inr hSa)
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hrest_nodup⟩
      intro hmem
      obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hmem
      exact hrest_disj b hb (Or.inl hbeq)

/-- `Fast.orderedWith` proves `ComputableWitnesses`, `WritesConsistent`, and disjointness from the
initial seed predicate. -/
theorem orderedWith_sound (seed : Address → Bool) (place : RegionIndex → ℕ)
    (assignments : List (Assignment F))
    (hacc : orderedWith seed place ∅ assignments = true) :
    Assignments.ComputableWitnesses place (fun addr => seed addr = true) assignments ∧
      Assignments.WritesConsistent place (fun addr => seed addr = true) assignments ∧
      (∀ a ∈ assignments, seed a.destination ≠ true) := by
  have hS : ∀ addr, (seed addr = true) ↔
      seed addr = true ∨ (∅ : Std.TreeSet Key).contains (key addr) = true := by
    intro addr
    simp
  obtain ⟨hcomp, hdisj, hnodup⟩ := orderedWith_sound_aux seed place assignments ∅ _ hS hacc
  exact ⟨hcomp, Assignments.WritesConsistent.of_disjoint_nodup place _ assignments hdisj hnodup,
    hdisj⟩

/-- `Fast.ordered` (empty seed) proves `ComputableWitnesses` and `WritesConsistent` from
`Determined.empty`. -/
theorem ordered_sound (place : RegionIndex → ℕ) (assignments : List (Assignment F))
    (hacc : ordered place ∅ assignments = true) :
    Assignments.ComputableWitnesses place Determined.empty assignments ∧
      Assignments.WritesConsistent place Determined.empty assignments := by
  rw [ordered_eq_orderedWith_false] at hacc
  have hS : ∀ addr, Determined.empty addr ↔
      (fun _ : Address => false) addr = true ∨ (∅ : Std.TreeSet Key).contains (key addr) = true := by
    intro addr
    simp [Determined.empty]
  obtain ⟨hcomp, hdisj, hnodup⟩ :=
    orderedWith_sound_aux (fun _ => false) place assignments ∅ Determined.empty hS hacc
  exact ⟨hcomp, Assignments.WritesConsistent.of_disjoint_nodup place _ assignments hdisj hnodup⟩

/-- `Fast.orderedWith` seeded with instance columns proves `ComputableWitnesses` and
`WritesConsistent` from `Determined.instances`. -/
theorem ordered_instances_sound (place : RegionIndex → ℕ) (assignments : List (Assignment F))
    (hacc : orderedWith (fun addr => addr.1.kind == .instance) place ∅ assignments = true) :
    Assignments.ComputableWitnesses place Determined.instances assignments ∧
      Assignments.WritesConsistent place Determined.instances assignments ∧
      (∀ a ∈ assignments, ¬ Determined.instances a.destination) := by
  have hS : ∀ addr, Determined.instances addr ↔
      (addr.1.kind == .instance) = true ∨ (∅ : Std.TreeSet Key).contains (key addr) = true := by
    intro addr
    simp [Determined.instances]
  obtain ⟨hcomp, hdisj, hnodup⟩ :=
    orderedWith_sound_aux (fun addr => addr.1.kind == .instance) place assignments ∅
      Determined.instances hS hacc
  exact ⟨hcomp, Assignments.WritesConsistent.of_disjoint_nodup place _ assignments hdisj hnodup,
    hdisj⟩

private theorem orderedAdvice_sound_aux (place : RegionIndex → ℕ)
    (assignments : List (Assignment F)) (known : Std.TreeSet Key)
    (S : Address → Prop)
    (hS : ∀ addr, S addr ↔ addr.1.kind ≠ .advice ∨ known.contains (key addr) = true)
    (hacc : orderedAdvice place known assignments = true) :
    Assignments.ComputableWitnesses place S assignments ∧
      (∀ a ∈ assignments, a.destination.1.kind ≠ .instance) ∧
      (∀ a ∈ assignments, a.destination.1.kind = .advice → ¬ known.contains (key a.destination) = true) ∧
      assignments.Pairwise fun a b => a.destination = b.destination → a.destination.1.kind = .fixed := by
  induction assignments generalizing known S with
  | nil =>
    exact ⟨trivial, fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h), List.Pairwise.nil⟩
  | cons assignment rest ih =>
    cases hkind : assignment.destination.1.kind with
    | «instance» =>
      simp [orderedAdvice, hkind] at hacc
    | fixed =>
      simp only [orderedAdvice, hkind, Bool.and_eq_true] at hacc
      rcases hacc with ⟨hreads, hrest⟩
      let S' : Address → Prop := fun addr => addr = assignment.destination ∨ S addr
      have hS' : ∀ addr, S' addr ↔ addr.1.kind ≠ .advice ∨ known.contains (key addr) = true := by
        intro addr
        simp only [S', hS]
        constructor
        · rintro (rfl | h)
          · exact Or.inl (by simp [hkind])
          · exact h
        · exact Or.inr
      obtain ⟨hrest_comp, hrest_notInst, hrest_fresh, hrest_pair⟩ := ih known S' hS' hrest
      refine ⟨⟨?_, hrest_comp⟩, ?_, ?_, ?_⟩
      · intro left right hagree
        apply program_eval_eq_of_readsAccepted place S _ _ assignment.program hreads left right hagree
        intro cell hcell
        rw [hS]
        simpa only [Bool.or_eq_true, bne_iff_ne] using hcell
      · intro a hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · simp [hkind]
        · exact hrest_notInst a htail
      · intro a hmem hadv
        rcases List.mem_cons.mp hmem with rfl | htail
        · simp [hkind] at hadv
        · exact hrest_fresh a htail hadv
      · exact List.pairwise_cons.mpr ⟨fun _ _ _ => hkind, hrest_pair⟩
    | advice =>
      simp only [orderedAdvice, hkind, Bool.and_eq_true, Bool.not_eq_true'] at hacc
      rcases hacc with ⟨⟨hnotKnown, hreads⟩, hrest⟩
      let S' : Address → Prop := fun addr => addr = assignment.destination ∨ S addr
      have hS' : ∀ addr, S' addr ↔
          addr.1.kind ≠ .advice ∨ (known.insert (key assignment.destination)).contains (key addr) = true := by
        intro addr
        simp only [S', hS, Std.TreeSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
          Std.compare_eq_iff_eq, key_injective.eq_iff]
        constructor
        · rintro (rfl | hnon | hknown)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hnon
          · exact Or.inr (Or.inr hknown)
        · rintro (hnon | heq | hknown)
          · exact Or.inr (Or.inl hnon)
          · exact Or.inl heq.symm
          · exact Or.inr (Or.inr hknown)
      obtain ⟨hrest_comp, hrest_notInst, hrest_fresh, hrest_pair⟩ :=
        ih (known.insert (key assignment.destination)) S' hS' hrest
      refine ⟨⟨?_, hrest_comp⟩, ?_, ?_, ?_⟩
      · intro left right hagree
        apply program_eval_eq_of_readsAccepted place S _ _ assignment.program hreads left right hagree
        intro cell hcell
        rw [hS]
        simpa only [Bool.or_eq_true, bne_iff_ne] using hcell
      · intro a hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · simp [hkind]
        · exact hrest_notInst a htail
      · intro a hmem hadv
        rcases List.mem_cons.mp hmem with rfl | htail
        · simp [hnotKnown]
        · intro hcont
          apply hrest_fresh a htail hadv
          simp [Std.TreeSet.contains_insert, hcont]
      · refine List.pairwise_cons.mpr ⟨?_, hrest_pair⟩
        intro b hb heq
        exfalso
        apply hrest_fresh b hb (heq ▸ hkind)
        simp [Std.TreeSet.contains_insert, ← heq]

/-- `Fast.orderedAdvice` together with agreement of repeated fixed writes proves
`ComputableWitnesses` and `WritesConsistent` from `Determined.nonAdvice`. -/
theorem orderedAdvice_sound (place : RegionIndex → ℕ) (assignments : List (Assignment F))
    (hacc : orderedAdvice place ∅ assignments = true)
    (hfixedAgree : ∀ a ∈ assignments, ∀ b ∈ assignments,
      a.destination = b.destination → a.destination.1.kind = .fixed →
      ∀ env : ProverEnvironment F,
        (a.program.eval ⟨place, env⟩)[0] = (b.program.eval ⟨place, env⟩)[0]) :
    Assignments.ComputableWitnesses place Determined.nonAdvice assignments ∧
      Assignments.WritesConsistent place Determined.nonAdvice assignments := by
  have hS : ∀ addr, Determined.nonAdvice addr ↔
      addr.1.kind ≠ .advice ∨ (∅ : Std.TreeSet Key).contains (key addr) = true := by
    intro addr
    simp [Determined.nonAdvice]
  obtain ⟨hcomp, hnotInst, _, hpair⟩ :=
    orderedAdvice_sound_aux place assignments ∅ Determined.nonAdvice hS hacc
  refine ⟨hcomp, ?_, ?_⟩
  · intro a hmem hnonAdv
    have hni := hnotInst a hmem
    cases hk : a.destination.1.kind with
    | advice => exact False.elim (hnonAdv hk)
    | fixed => rfl
    | «instance» => exact False.elim (hni hk)
  · exact List.Pairwise.imp_of_mem (fun {a b} ha hb h => fun heq =>
      ⟨h heq, hfixedAgree a ha b hb heq (h heq)⟩) hpair

end Fast

end Semantics

end Halo2
