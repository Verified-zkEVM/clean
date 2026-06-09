import Clean.Halo2.Formal

namespace Halo2.Examples.Tiny

open Halo2
open scoped Halo2

structure Config where
  a : Column .advice
  s : Selector
deriving DecidableEq, Repr

structure Inputs (F : Type) where
  s : F
  aCur : F
  aNext : F

instance : ProvableType Inputs where
  size := 3
  toElements inputs := #v[inputs.s, inputs.aCur, inputs.aNext]
  fromElements v := {
    s := v[0]
    aCur := v[1]
    aNext := v[2]
  }

def configure {F : Type} [Field F] : Configure F Config := do
  let a ← adviceColumn
  let s ← selector
  let config := { a, s }

  createGate "tiny transition" do
    let inputs ← registerInputs ({
      s := ← querySelector config.s
      aCur := ← queryAdvice config.a 0
      aNext := ← queryAdvice config.a 1
    } : Inputs (Expression F))
    inputs.s * (inputs.aCur * inputs.aNext - inputs.aCur) === 0

  return config

def formalGate {F : Type} [Field F] : FormalGate F Config Inputs where
  name := "tiny transition"
  configure
  Spec _ input := input.s * (input.aCur * input.aNext - input.aCur) = 0
  soundness := by
    intro env _ h_holds
    simp only [Gate.Constraints, Configure.gate, Configure.state, configure, registerInputs,
      Gate.RegisteredInputs, Gate.evalInputs, Gate.registeredInputExpressions,
      Gate.registeredInputExpressions_of_toElements, explicit_provable_type,
      assertEq, assertZero, queryAdvice, querySelector, Configure.pure_def,
      Configure.bind_def, createGate, VirtualCells.run_def, VirtualCells.bind_def,
      selector, adviceColumn, Configure.run_def, Array.mem_def, Array.toList_push,
      List.mem_toArray, List.mem_append, List.mem_singleton, List.not_mem_nil, forall_eq,
      toElements, fromElements, Vector.map_mk, Vector.getElem_mk, List.getElem_toArray,
      Vector.getElem_ofFn, Array.map_empty, Array.map_push, Array.getElem_map,
      List.getElem_cons_zero, List.getElem_cons_succ, getElem?_pos, Option.bind_some,
      Option.getD_some, List.push_toArray, List.nil_append, List.cons_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one,
      Constraint.Holds, ExpressionWithLocation.eval, sub_eq_add_neg,
      neg_mul, one_mul, mul_zero, add_zero, mul_eq_zero, Fin.getElem?_fin,
      List.getElem?_toArray, List.map_toArray, List.map_cons, List.map_nil] at h_holds ⊢
    -- TODO Vector.getElem_ofFn didn't fire!!
    exact h_holds
  completeness := by
    intro env _ h_spec
    simp only [Gate.Constraints, Configure.gate, Configure.state, configure, registerInputs,
      Gate.RegisteredInputs, Gate.evalInputs, Gate.registeredInputExpressions,
      Gate.registeredInputExpressions_of_toElements, explicit_provable_type,
      assertEq, assertZero, queryAdvice, querySelector, Configure.pure_def,
      Configure.bind_def, createGate, VirtualCells.run_def, VirtualCells.bind_def,
      selector, adviceColumn, Configure.run_def, Array.mem_def, Array.toList_push,
      List.mem_toArray, List.mem_append, List.mem_singleton, List.not_mem_nil, forall_eq,
      toElements, fromElements, Vector.map_mk, Vector.getElem_mk, List.getElem_toArray,
      Vector.getElem_ofFn, Array.map_empty, Array.map_push, Array.getElem_map,
      List.getElem_cons_zero, List.getElem_cons_succ, getElem?_pos, Option.bind_some,
      Option.getD_some, List.push_toArray, List.nil_append, List.cons_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one,
      Constraint.Holds, ExpressionWithLocation.eval, sub_eq_add_neg,
      neg_mul, one_mul, mul_zero, add_zero, mul_eq_zero, Fin.getElem?_fin,
      List.getElem?_toArray, List.map_toArray, List.map_cons, List.map_nil] at h_spec ⊢
    exact h_spec

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
