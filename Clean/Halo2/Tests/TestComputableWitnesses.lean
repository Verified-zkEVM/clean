module

public import Clean.Halo2

@[expose] public section

/-!
# Regression tests for `Halo2.ComputableWitnesses`, `WritesConsistent`, and `Fast.ordered`

Self-contained positive and negative tests covering:
1. A multi-step structured `WitgenIR` circuit (`letF`, `letU`, `BExpr`, `ite`, `hintGet`,
   earlier advice cell, fixed cell, and instance cell) certified by `decide +kernel`, proving
   `ComputableWitnesses ∧ WritesConsistent` and existential completeness.
2. Negative test 1: self-referential witness rejected by `Fast.ordered` and `¬ ComputableWitnesses`.
3. Negative test 2: forward read rejected by `Fast.ordered` and `¬ ComputableWitnesses`.
4. Negative test 3: advice clobber (double write) rejected by `Fast.ordered` and
   `¬ WritesConsistent`.
5. Negative test 4: `.native` escape hatch rejected by `Witgen.programReads` and `Fast.ordered`.
-/

namespace Halo2.Tests.TestComputableWitnesses

abbrev TestField := F 101

instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private def colA : Column .advice := ⟨0⟩
private def colB : Column .advice := ⟨1⟩
private def colF : Column .fixed := ⟨0⟩
private def colI : Column .instance := ⟨0⟩
private def testSel : Selector := ⟨0, true⟩

private def addGate : Gate TestField :=
  Gate.withSelector "add_fixed" testSel
    [queryAdvice colA 0, queryFixed colF, queryAdvice colB 0]
    [("sum", queryAdvice colA 0 + queryFixed colF - queryAdvice colB 0)]

private def testPlace : RegionIndex → ℕ := fun r => r * 4

/-! ## 1. Positive test: full structured `WitgenIR` + existential completeness -/

/-- A multi-step Halo2 circuit using `assignFixed`, `hintGet`, `letF`, `letU`, `BExpr`, `ite`,
reading an earlier advice cell, a fixed cell, and an instance cell, and enforcing a gate. -/
private def positiveCircuit : Circuit TestField Unit :=
  assignRegion "positive" fun self =>
    let fixedCell : AssignedCell TestField := .of self 0 colF
    let instCell : AssignedCell TestField := .of self 0 colI
    let advCell0 : AssignedCell TestField := .of self 0 colA
    let hintCell : WitgenIR TestField 1 :=
      .ir
        [ .letF (.hintGet "secret" 1 (.const 0) ⟨0, by decide⟩)
        , .letU (.ite (.lt (.val (.localVar 0)) (.const 50))
            (.add (.val (.localVar 0)) (.const 1))
            (.val (.localVar 0)))
        ]
        (.lit #v[
          .ite (.feq (.expr fixedCell) (.const 7))
            (.add (.ofU64 (.localVar 1)) (.expr instCell))
            (.const 0)])
    let advProg1 : WitgenIR TestField 1 :=
      .ofFExpr (.add (.expr advCell0) (.expr fixedCell))
    ((), [
      .assignFixed colF 0 7,
      .assignAdvice colA 0 hintCell,
      .assignAdvice colB 0 advProg1,
      .enableGate addGate 0
    ])

private def positiveOps : Operations TestField := positiveCircuit.operations 0

private theorem positive_fast_ordered_instances :
    Fast.orderedWith (fun addr => addr.1.kind == .instance) testPlace ∅
      (positiveOps.assignments testPlace 0) = true := by
  decide +kernel

private theorem positive_computable_and_consistent :
    Operations.ComputableWitnesses testPlace Determined.instances positiveOps 0 ∧
      Operations.WritesConsistent testPlace Determined.instances positiveOps 0 := by
  have h := Fast.ordered_instances_sound testPlace (positiveOps.assignments testPlace 0)
    positive_fast_ordered_instances
  exact ⟨h.1, h.2.1⟩

/-- Existential completeness on the positive circuit: for every public instance and prover hint,
there exists an environment extending the public instances that satisfies both `ExtendsWitnesses`
and `Constraints`. -/
private theorem positive_exists_completeness
    (inst : Column .instance → ℤ → TestField) (hint : ProverHint TestField) :
    ∃ env : ProverEnvironment TestField,
      (∀ col row, env.inst col row = inst col row) ∧
      ExtendsWitnesses testPlace env positiveOps 0 ∧
      Constraints testPlace env.toEnvironment positiveOps 0 := by
  have hsound := Fast.ordered_instances_sound testPlace (positiveOps.assignments testPlace 0)
    positive_fast_ordered_instances
  let seed : ProverEnvironment TestField :=
    { get := fun col row =>
        match col.kind with
        | .instance => inst ⟨col.index⟩ row
        | _ => 0
      usableRows := 16
      hint := hint }
  have hrun := Execute.run_extendsWitnesses testPlace 0 positiveOps Determined.instances seed
    hsound.1 hsound.2.1
    (fun a hmem hS => False.elim (hsound.2.2 a hmem hS))
    trivial
    (fun _ _ hmem => by simp [positiveOps, positiveCircuit, Circuit.operations, assignRegion,
      Operations.loadedTableColumns] at hmem)
  let env := Execute.run testPlace (positiveOps.assignments testPlace 0) seed
  refine ⟨env, ?_, hrun.2, ?_⟩
  · intro col row
    exact Execute.run_instance testPlace 0 positiveOps seed col row
  · have hw : ExtendsWitnesses testPlace env positiveOps 0 := hrun.2
    simp only [positiveOps, positiveCircuit, Circuit.operations, assignRegion,
      ExtendsWitnesses, RegionOperations.ExtendsWitnesses, RegionOperation.ExtendsWitness,
      Constraints, RegionOperations.Constraints, RegionOperation.Constraints,
      addGate, Gate.withSelector, List.map_cons, List.map_nil, List.Forall,
      querySelector, queryAdvice, queryFixed, testPlace, colA, colB, colF, testSel,
      circuit_norm, Nat.zero_mul, Nat.cast_zero, add_zero, ↓reduceIte, one_mul,
      true_and, and_true] at hw ⊢
    rcases hw with ⟨hfixed, _, hadv1⟩
    refine ⟨hfixed, ?_⟩
    rw [hadv1]
    ring

/-- Zero-seed `Fast.ordered` also certifies structured `WitgenIR` programs reading only earlier
assignments (fixed and advice) and hints. -/
private def zeroSeedOps : Operations TestField :=
  [ .region "zero_seed" [
      .assignFixed colF 0 5,
      .assignAdvice colA 0
        (.ir [.letF (.hintGet "h" 1 (.const 0) ⟨0, by decide⟩)]
          (.lit #v[.add (.localVar 0) (.expr (.of 0 0 colF))])),
      .assignAdvice colB 0
        (.ir [.letU (.val (.expr (.of 0 0 colA)))]
          (.lit #v[.ofU64 (.ite (.neq (.localVar 0) (.const 0)) (.const 1) (.const 2))]))
    ] ]

private theorem zeroSeed_fast_ordered :
    Fast.ordered testPlace ∅ (zeroSeedOps.assignments testPlace 0) = true := by
  decide +kernel

private theorem zeroSeed_computable_and_consistent :
    Operations.ComputableWitnesses testPlace Determined.empty zeroSeedOps 0 ∧
      Operations.WritesConsistent testPlace Determined.empty zeroSeedOps 0 :=
  Fast.ordered_sound testPlace (zeroSeedOps.assignments testPlace 0) zeroSeed_fast_ordered

/-! ## 2. Negative test 1: self-referential witness -/

private def selfRefOps : Operations TestField :=
  [ .region "self_ref" [
      .assignAdvice colA 0 (.ofFExpr (.add (.expr (.of 0 0 colA)) (.const 1)))
    ] ]

private theorem selfRef_fast_rejected :
    Fast.ordered testPlace ∅ (selfRefOps.assignments testPlace 0) = false := by
  decide +kernel

private theorem selfRef_not_computable :
    ¬ Operations.ComputableWitnesses testPlace Determined.empty selfRefOps 0 := by
  intro hcomp
  rcases hcomp with ⟨hstep, _⟩
  let env0 : ProverEnvironment TestField :=
    { get := fun _ _ => 0, usableRows := 8, hint := ProverHint.empty TestField }
  let env1 : ProverEnvironment TestField :=
    { get := fun _ _ => 1, usableRows := 8, hint := ProverHint.empty TestField }
  have hagree : AgreesOn Determined.empty env0 env1 :=
    ⟨rfl, rfl, fun _ h => False.elim h⟩
  have heq := hstep env0 env1 hagree
  simp [eval_ofFExpr_zero, Witgen.FExprOver.eval, WitgenEnv.readVar_halo2,
    AssignedCell.eval, AssignedCell.of, Cell.of, env0, env1] at heq

/-! ## 3. Negative test 2: forward read -/

private def forwardReadOps : Operations TestField :=
  [ .region "forward_read" [
      .assignAdvice colA 0 (.ofFExpr (.expr (.of 0 1 colA))),
      .assignAdvice colA 1 (.ofFExpr (.const 42))
    ] ]

private theorem forwardRead_fast_rejected :
    Fast.ordered testPlace ∅ (forwardReadOps.assignments testPlace 0) = false := by
  decide +kernel

private theorem forwardRead_not_computable :
    ¬ Operations.ComputableWitnesses testPlace Determined.empty forwardReadOps 0 := by
  intro hcomp
  rcases hcomp with ⟨hstep, _⟩
  let env0 : ProverEnvironment TestField :=
    { get := fun _ _ => 0, usableRows := 8, hint := ProverHint.empty TestField }
  let env1 : ProverEnvironment TestField :=
    { get := fun _ _ => 1, usableRows := 8, hint := ProverHint.empty TestField }
  have hagree : AgreesOn Determined.empty env0 env1 :=
    ⟨rfl, rfl, fun _ h => False.elim h⟩
  have heq := hstep env0 env1 hagree
  simp [eval_ofFExpr_zero, Witgen.FExprOver.eval, WitgenEnv.readVar_halo2,
    AssignedCell.eval, AssignedCell.of, Cell.of, env0, env1] at heq

/-! ## 4. Negative test 3: advice clobber / double write -/

private def clobberOps : Operations TestField :=
  [ .region "clobber" [
      .assignAdvice colA 0 (.ofFExpr (.const 0)),
      .assignAdvice colA 0 (.ofFExpr (.const 1))
    ] ]

private theorem clobber_fast_rejected :
    Fast.ordered testPlace ∅ (clobberOps.assignments testPlace 0) = false := by
  decide +kernel

private theorem clobber_not_writesConsistent :
    ¬ Operations.WritesConsistent testPlace Determined.empty clobberOps 0 := by
  intro hcons
  have hpair := List.pairwise_cons.mp hcons.pairwiseConsistent
  rcases hpair.1 ⟨(colA, (testPlace 0 + 0 : ℕ)), .ofFExpr (.const 1)⟩
      List.mem_cons_self rfl with hval | hself
  · let zeroEnv : ProverEnvironment TestField :=
      { get := fun _ _ => 0, usableRows := 8, hint := ProverHint.empty TestField }
    have hzero := hval zeroEnv
    simp [Halo2.eval_ofFExpr_zero, Witgen.FExprOver.eval] at hzero
  · let zeroEnv : ProverEnvironment TestField :=
      { get := fun _ _ => 0, usableRows := 8, hint := ProverHint.empty TestField }
    have hzero := hself zeroEnv
    simp [Halo2.eval_ofFExpr_zero, Witgen.FExprOver.eval, ProverEnvironment.read, zeroEnv] at hzero

/-! ## 4b. Positive test: idempotent self-copy satisfies `WritesConsistent` -/

private def selfCopyOps : Operations TestField :=
  [ .region "self_copy" [
      .assignAdvice colA 0 (.ofFExpr (.const 7)),
      .assignAdvice colA 0 (.ofFExpr (.expr (AssignedCell.of 0 0 colA)))
    ] ]

private theorem selfCopy_writesConsistent :
    Operations.WritesConsistent testPlace Determined.empty selfCopyOps 0 := by
  refine ⟨fun _ _ h => False.elim h, ?_⟩
  simp only [selfCopyOps, Operations.assignments, RegionOperations.assignments, List.append_nil,
    List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil, false_implies,
    implies_true, List.Pairwise.nil, and_true, true_implies]
  right
  intro env
  simp [Halo2.eval_ofFExpr_zero, Witgen.FExprOver.eval, Witgen.WitgenEnv.readVar,
    AssignedCell.eval, AssignedCell.of, Cell.of, Cell.row, Column.toAny, ProverEnvironment.read]

/-! ## 5. Negative test 4: `.native` escape hatch -/

private def nativeProg : WitgenIR TestField 1 :=
  .native fun _ => #v[0]

private def nativeOps : Operations TestField :=
  [ .region "native_escape" [
      .assignAdvice colA 0 nativeProg
    ] ]

private theorem native_reads_none :
    Witgen.programReads nativeProg = none := rfl

private theorem native_fast_rejected :
    Fast.ordered testPlace ∅ (nativeOps.assignments testPlace 0) = false := by
  decide +kernel

end Halo2.Tests.TestComputableWitnesses
