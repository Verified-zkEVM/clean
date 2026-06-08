import Clean.Halo2.Formal

namespace Halo2.Examples.Tiny

open Halo2
open scoped Halo2

structure Config where
  a : Column .advice
  s : Selector
deriving DecidableEq, Repr

def configure {F : Type} [Field F] : Configure F Config := do
  let a ← adviceColumn
  let s ← selector
  let config := { a, s }

  createGate "tiny transition" do
    let s ← querySelector config.s
    let aCur ← queryAdvice config.a 0
    let aNext ← queryAdvice config.a 1
    s * (aCur * aNext - aCur) === 0

  return config

def formalGate {F : Type} [Field F] : FormalGate F Config where
  name := "tiny transition"
  configure
  Spec config env :=
    let s := (.var { index := .selector config.s } : Expression F)
    let aCur := (.var { index := .advice config.a 0 } : Expression F)
    let aNext := (.var { index := .advice config.a 1 } : Expression F)
    env (s * (aCur * aNext - aCur)) = 0
  soundness := by
    intro env _ h_holds
    simp only [Gate.Constraints, Constraint.Holds, Configure.gate, Configure.state, configure,
      adviceColumn, selector, createGate, Configure.output,
      assertEq, assertZero, querySelector, queryAdvice,
      Configure.run_def, Configure.bind_def, Configure.pure_def,
      VirtualCells.run_def, VirtualCells.bind_def,
      List.push_toArray, List.nil_append, List.cons_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
      List.getElem_toArray, List.getElem_cons_zero, Option.getD_some, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq, ExpressionWithLocation.eval,
      neg_mul, one_mul, mul_zero, add_zero] at h_holds ⊢
    exact h_holds
  completeness := by
    intro env _ h_spec constraint h_constraint
    simp [Configure.gate, Configure.state, configure,
      adviceColumn, selector, createGate,
      assertEq, assertZero, querySelector, queryAdvice,
      Configure.run_def, Configure.bind_def, Configure.pure_def,
      VirtualCells.run_def, VirtualCells.bind_def]
      at h_constraint
    subst constraint
    simpa [Configure.output, configure, adviceColumn, selector, Configure.run_def, Configure.bind_def,
      Configure.pure_def, Constraint.Holds, ExpressionWithLocation.eval] using h_spec

def configured {F : Type} [Field F] : ConfigureState F :=
  (configure (F := F)).run {} |>.2

def config {F : Type} [Field F] : Config :=
  (configure (F := F)).run {} |>.1

example {F : Type} [Field F] : (configured (F := F)).nextAdvice = 1 := rfl

example {F : Type} [Field F] : (configured (F := F)).nextSelector = 1 := rfl

example {F : Type} [Field F] : (configured (F := F)).gates.size = 1 := rfl

example {F : Type} [Field F] :
    (configured (F := F)).gates[0]?.map (fun gate => gate.queriedSelectors.size) = some 1 := rfl

example {F : Type} [Field F] :
    (configured (F := F)).gates[0]?.map (fun gate => gate.queriedCells.size) = some 2 := rfl

example {F : Type} [Field F] :
    (configured (F := F)).gates[0]?.map (fun gate => gate.constraints.size) = some 1 := rfl

end Halo2.Examples.Tiny
