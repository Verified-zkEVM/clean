import Clean.Gadgets.Xor.Xor32
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Rotation32.Rotation32
import Clean.Specs.BLAKE3
import Clean.Utils.Tactics

namespace Gadgets.BLAKE3.G
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (g)

structure Inputs (F : Type) where
  state : BLAKE3State F
  x : U32 F
  y : U32 F
deriving ProvableStruct

def main (a b c d : Fin 16) (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { state, x, y } := input

  let state_a ← Addition32.circuit ⟨state[a], ← Addition32.circuit ⟨state[b], x⟩⟩

  let state_d ← Rotation32.circuit 16 <|
    ← Xor32.circuit ⟨state[d], state_a⟩

  let state_c ← Addition32.circuit ⟨state[c], state_d⟩

  let state_b ← Rotation32.circuit 12 <|
    ← Xor32.circuit ⟨state[b], state_c⟩

  let state_a ← Addition32.circuit ⟨state_a, ← Addition32.circuit ⟨state_b, y⟩⟩

  let state_d ← Rotation32.circuit 8 <|
    ← Xor32.circuit ⟨state_d, state_a⟩

  let state_c ← Addition32.circuit ⟨state_c, state_d⟩

  let state_b ← Rotation32.circuit 7 <|
    ← Xor32.circuit ⟨state_b, state_c⟩

  return state
    |>.set a state_a
    |>.set b state_b
    |>.set c state_c
    |>.set d state_d

@[computable_witnesses_metadata]
def output (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (i₀ : ℕ) : Vector (U32 (Expression (F p))) 16 :=
  (state : Vector (U32 (Expression (F p))) 16)
    |>.set a (⟨var ⟨i₀ + 56⟩, var ⟨i₀ + 58⟩, var ⟨i₀ + 60⟩, var ⟨i₀ + 62⟩⟩) a.is_lt
    |>.set b (Rotation32.output 7 (i₀ + 88)) b.is_lt
    |>.set c (⟨var ⟨i₀ + 76⟩, var ⟨i₀ + 78⟩, var ⟨i₀ + 80⟩, var ⟨i₀ + 82⟩⟩) c.is_lt
    |>.set d (Rotation32.output 8 (i₀ + 68)) d.is_lt

instance elaborated (a b c d : Fin 16): ElaboratedCircuit (F p) Inputs BLAKE3State (main a b c d) := by
  elaborate_circuit_with {
    output inputs i0 := output a b c d inputs.state i0
  }

def Assumptions (input : Inputs (F p)) :=
  let { state, x, y } := input
  state.Normalized ∧ x.Normalized ∧ y.Normalized

def Spec (a b c d : Fin 16) (input : Inputs (F p)) (out : BLAKE3State (F p)) :=
  let { state, x, y } := input
  out.value = g state.value a b c d x.value y.value ∧ out.Normalized

theorem soundness (a b c d : Fin 16) : Soundness (F p) (main a b c d) Assumptions (Spec a b c d) := by
  circuit_proof_start [output, BLAKE3State.Normalized, Xor32.circuit, Addition32.circuit,
    Rotation32.circuit, Rotation32.elaborated, and_imp,
    Addition32.Assumptions, Addition32.Spec, Rotation32.Assumptions, Rotation32.Spec,
    Xor32.Assumptions, Xor32.Spec, getElem_eval_vector]

  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h_holds

  -- resolve all chains of assumptions, fortunately this is easy
  simp_all only [forall_const]

  -- In c9, c11, c12, and c14, we now have the correct hypotheses regarding the
  -- updated values in the output state.
  -- From this point onward, we need to prove that the updated values are consistent with the spec.
  -- Unfortunately, this is not trivial because we do not require that a, b, c, and d are distinct.
  -- Therefore, there could be overwriting of values in the state update chain, requiring
  -- case-by-case reasoning on the indices.
  -- NOTE: This is not a bug, we are following the BLAKE specification of the g function verbatim.
  -- See, for example, https://www.ietf.org/archive/id/draft-aumasson-blake3-00.html#name-quarter-round-function-g
  constructor
  · ext i hi
    simp only [BLAKE3State.value, eval_vector, Vector.map_set, Vector.map_map, ↓Vector.getElem_set,
      Vector.getElem_map, g, Fin.getElem_fin, add32]
    repeat' split
    · rw [c11.left]
    · simp only [circuit_norm]
      rw [c12.left]
    · rw [c14.left]
    · simp only [circuit_norm]
      rw [c9.left]
    · rw [Function.comp_apply, ←h_input.left, getElem_eval_vector]

  · intro i
    simp only [eval_vector, Vector.map_set, ↓Vector.getElem_set]
    repeat' split
    · exact c11.right
    · simp only [U32.Normalized, explicit_provable_type, Vector.map_mk, List.map_toArray,
        List.map_cons, List.map_nil, fromElements] at c12 ⊢
      simp +arith only [Nat.reducePow, Nat.add_mod_mod, Nat.reduceMod] at c12 ⊢
      exact c12.right
    · exact c14.right
    · simp only [U32.Normalized, explicit_provable_type, Vector.map_mk, List.map_toArray,
        List.map_cons, List.map_nil, fromElements] at c9 ⊢
      simp +arith only [Nat.reducePow, Nat.add_mod_mod, Nat.reduceMod] at c9 ⊢
      exact c9.right
    · simp only [Vector.getElem_map, getElem_eval_vector, h_input, h_assumptions]

theorem completeness (a b c d : Fin 16) : Completeness (F p) (main a b c d) Assumptions := by
  circuit_proof_start [BLAKE3State.Normalized]

  dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit] at h_env ⊢
  simp only [circuit_norm, and_imp,
    Addition32.Assumptions, Addition32.Spec, Rotation32.Assumptions, Rotation32.Spec,
    Xor32.Assumptions, Xor32.Spec, getElem_eval_vector] at h_env ⊢

  -- resolve all chains of assumptions
  simp_all only [forall_const, and_true]

omit p_large_enough in
lemma state_elem_congr {env env' : ProverEnvironment (F p)}
    {state : BLAKE3State (Expression (F p))}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state) (i : Fin 16) :
    eval env.toEnvironment state[(i : ℕ)] = eval env'.toEnvironment state[(i : ℕ)] :=
  (getElem_eval_vector env.toEnvironment state i.val i.isLt).trans
    ((congrArg (fun s : BLAKE3State (F p) => s[i]) h1).trans
      (getElem_eval_vector env'.toEnvironment state i.val i.isLt).symm)
private def out1 (_a b _c _d : Fin 16) (state : BLAKE3State (Expression (F p))) (x _y : U32 (Expression (F p))) (n : ℕ) := (Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n
private def out2 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Addition32.circuit (p:=p)).output ⟨state[a], out1 a b c d state x y n⟩ (n + 8)
private def out3 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Xor32.circuit (p:=p)).output ⟨state[d], out2 a b c d state x y n⟩ (n + 16)
private def out4 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Rotation32.circuit (p:=p) 16).output (out3 a b c d state x y n) (n + 20)
private def out5 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Addition32.circuit (p:=p)).output ⟨state[c], out4 a b c d state x y n⟩ (n + 28)
private def out6 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Xor32.circuit (p:=p)).output ⟨state[b], out5 a b c d state x y n⟩ (n + 36)
private def out7 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Rotation32.circuit (p:=p) 12).output (out6 a b c d state x y n) (n + 40)
private def out8 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Addition32.circuit (p:=p)).output ⟨out7 a b c d state x y n, y⟩ (n + 48)
private def out9 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Addition32.circuit (p:=p)).output ⟨out2 a b c d state x y n, out8 a b c d state x y n⟩ (n + 56)
private def out10 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Xor32.circuit (p:=p)).output ⟨out4 a b c d state x y n, out9 a b c d state x y n⟩ (n + 64)
private def out11 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Rotation32.circuit (p:=p) 8).output (out10 a b c d state x y n) (n + 68)
private def out12 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Addition32.circuit (p:=p)).output ⟨out5 a b c d state x y n, out11 a b c d state x y n⟩ (n + 76)
private def out13 (a b c d : Fin 16) (state : BLAKE3State (Expression (F p))) (x y : U32 (Expression (F p))) (n : ℕ) := (Xor32.circuit (p:=p)).output ⟨out7 a b c d state x y n, out12 a b c d state x y n⟩ (n + 84)

section
variable {env env' : ProverEnvironment (F p)} {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))} {x y : U32 (Expression (F p))} {n : ℕ}
variable (h1 : eval env.toEnvironment state = eval env'.toEnvironment state) (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x) (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
include h1 h2 h3

omit h3 in private lemma node1_out_congr (h_agrees : env.AgreesBelow (n + 8) env') : eval env.toEnvironment (out1 a b c d state x y n) = eval env'.toEnvironment (out1 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 b, h2⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
omit h3 in private lemma node2_out_congr (h_agrees : env.AgreesBelow (n + 16) env') : eval env.toEnvironment (out2 a b c d state x y n) = eval env'.toEnvironment (out2 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 a, node1_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
omit h3 in private lemma node3_out_congr (h_agrees : env.AgreesBelow (n + 20) env') : eval env.toEnvironment (out3 a b c d state x y n) = eval env'.toEnvironment (out3 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 d, node2_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
omit h3 in private lemma node4_out_congr (h_agrees : env.AgreesBelow (n + 28) env') : eval env.toEnvironment (out4 a b c d state x y n) = eval env'.toEnvironment (out4 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (node3_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
omit h3 in private lemma node5_out_congr (h_agrees : env.AgreesBelow (n + 36) env') : eval env.toEnvironment (out5 a b c d state x y n) = eval env'.toEnvironment (out5 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 c, node4_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
omit h3 in private lemma node6_out_congr (h_agrees : env.AgreesBelow (n + 40) env') : eval env.toEnvironment (out6 a b c d state x y n) = eval env'.toEnvironment (out6 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 b, node5_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
omit h3 in private lemma node7_out_congr (h_agrees : env.AgreesBelow (n + 48) env') : eval env.toEnvironment (out7 a b c d state x y n) = eval env'.toEnvironment (out7 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (node6_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
private lemma node8_out_congr (h_agrees : env.AgreesBelow (n + 56) env') : eval env.toEnvironment (out8 a b c d state x y n) = eval env'.toEnvironment (out8 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨node7_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)), h3⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
private lemma node9_out_congr (h_agrees : env.AgreesBelow (n + 64) env') : eval env.toEnvironment (out9 a b c d state x y n) = eval env'.toEnvironment (out9 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨node2_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)), node8_out_congr h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
private lemma node10_out_congr (h_agrees : env.AgreesBelow (n + 68) env') : eval env.toEnvironment (out10 a b c d state x y n) = eval env'.toEnvironment (out10 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨node4_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)), node9_out_congr h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
private lemma node11_out_congr (h_agrees : env.AgreesBelow (n + 76) env') : eval env.toEnvironment (out11 a b c d state x y n) = eval env'.toEnvironment (out11 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (node10_out_congr h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
private lemma node12_out_congr (h_agrees : env.AgreesBelow (n + 84) env') : eval env.toEnvironment (out12 a b c d state x y n) = eval env'.toEnvironment (out12 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨node5_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)), node11_out_congr h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))
private lemma node13_out_congr (h_agrees : env.AgreesBelow (n + 88) env') : eval env.toEnvironment (out13 a b c d state x y n) = eval env'.toEnvironment (out13 a b c d state x y n) := FormalCircuit.output_of_input_eq _ (by simp only [circuit_norm]; exact ⟨node7_out_congr h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)), node12_out_congr h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩) (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [ComputableWitnesses.reduceLocalLength]; omega))

end

set_option maxRecDepth 2048 in
omit p_large_enough in
/-- Env-agreement transfers to the output state: the four set slots are fresh witness
windows below the bound, the remaining entries evaluate through the input state. -/
lemma output_eval_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h_agrees : env.AgreesBelow (n + 96) env') :
    eval env.toEnvironment (output a b c d state n) =
      eval env'.toEnvironment (output a b c d state n) := by
  simp only [circuit_norm, eval_vector]
  refine Vector.ext fun j hj => ?_
  simp only [output, Vector.getElem_map, Vector.getElem_set]
  split_ifs <;>
    first
      | (simp only [circuit_norm, Rotation32.output, Rotation32Bits.output,
           U32.ByteVector.eval_fromLimbs]
         first
           | (refine congrArg U32.fromLimbs (Vector.ext fun i hi => ?_)
              simp only [Vector.getElem_map, Vector.getElem_ofFn, circuit_norm]
              grind)
           | grind)
      | (exact (getElem_eval_vector env.toEnvironment state j (by omega)).trans
          ((congrArg (fun s : BLAKE3State (F p) => s[j]'(by omega)) h1).trans
            (getElem_eval_vector env'.toEnvironment state j (by omega)).symm))

def circuit (a b c d : Fin 16) : FormalCircuit (F p) Inputs BLAKE3State where
  main := main a b c d
  elaborated := elaborated a b c d
  Assumptions
  Spec := Spec a b c d
  soundness := soundness a b c d
  completeness := completeness a b c d
  computableWitnesses := by
    rintro n ⟨state, x, y⟩ env env'
    simp only [circuit_norm, main, ComputableWitnesses.reduceLocalLength]
    refine ⟨?_, fun h h_agrees => output_eval_congr h.1 h_agrees⟩
    and_intros <;>
      exact fun h => FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by omega) fun h_agrees => by
          obtain ⟨h1, h2, h3⟩ := h
          try have p1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p9 := node9_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p10 := node10_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p11 := node11_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p12 := node12_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have p13 := node13_out_congr (a := a) (b := b) (c := c) (d := d) (y := y) (n := n) h1 h2 h3 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try simp only [circuit_norm, out13, out12, out11, out10, out9, out8, out7, out6, out5, out4, out3, out2, out1] at *
          (try and_intros) <;> first | assumption | grind

end Gadgets.BLAKE3.G
