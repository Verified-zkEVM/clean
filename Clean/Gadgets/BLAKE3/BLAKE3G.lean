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

private lemma state_elem_congr {env env' : ProverEnvironment (F p)}
    {state : BLAKE3State (Expression (F p))}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state) (i : Fin 16) :
    eval env.toEnvironment state[(i : ℕ)] = eval env'.toEnvironment state[(i : ℕ)] :=
  (getElem_eval_vector env.toEnvironment state i.val i.isLt).trans
    ((congrArg (fun s : BLAKE3State (F p) => s[i]) h1).trans
      (getElem_eval_vector env'.toEnvironment state i.val i.isLt).symm)

private lemma node1_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 8) env') :
    eval env.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n) =
      eval env'.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 b, h2⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node2_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 16) env') :
    eval env.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)) =
      eval env'.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 a, o1⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node3_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 20) env') :
    eval env.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) =
      eval env'.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 d, o2⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node4_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 28) env') :
    eval env.toEnvironment
        ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)) =
      eval env'.toEnvironment
        ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    o3
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node5_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 36) env') :
    eval env.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)) =
      eval env'.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 c, o4⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node6_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 40) env') :
    eval env.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) =
      eval env'.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨state_elem_congr h1 b, o5⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node7_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 48) env') :
    eval env.toEnvironment
        ((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)) =
      eval env'.toEnvironment
        ((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    o6
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node8_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 56) env') :
    eval env.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48)) =
      eval env'.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨o7, h3⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node9_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 64) env') :
    eval env.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56)) =
      eval env'.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨o2, o8⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node10_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 68) env') :
    eval env.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) =
      eval env'.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o9 := node9_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨o4, o9⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node11_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 76) env') :
    eval env.toEnvironment
        ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68)) =
      eval env'.toEnvironment
        ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o9 := node9_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o10 := node10_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    o10
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node12_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 84) env') :
    eval env.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)), ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68))⟩ (n + 76)) =
      eval env'.toEnvironment
        ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)), ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68))⟩ (n + 76)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o9 := node9_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o10 := node10_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o11 := node11_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨o5, o11⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node13_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 88) env') :
    eval env.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)), ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68))⟩ (n + 76))⟩ (n + 84)) =
      eval env'.toEnvironment
        ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)), ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68))⟩ (n + 76))⟩ (n + 84)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o9 := node9_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o10 := node10_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o11 := node11_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o12 := node12_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    (by simp only [circuit_norm]; exact ⟨o7, o12⟩)
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

private lemma node14_out_congr {env env' : ProverEnvironment (F p)}
    {a b c d : Fin 16} {state : BLAKE3State (Expression (F p))}
    {x y : U32 (Expression (F p))} {n : ℕ}
    (h1 : eval env.toEnvironment state = eval env'.toEnvironment state)
    (h2 : (eval env.toEnvironment x : U32 (F p)) = eval env'.toEnvironment x)
    (h3 : (eval env.toEnvironment y : U32 (F p)) = eval env'.toEnvironment y)
    (h_agrees : env.AgreesBelow (n + 96) env') :
    eval env.toEnvironment
        ((Rotation32.circuit (p:=p) 7).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)), ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68))⟩ (n + 76))⟩ (n + 84)) (n + 88)) =
      eval env'.toEnvironment
        ((Rotation32.circuit (p:=p) 7).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28)), ((Rotation32.circuit (p:=p) 8).output ((Xor32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20)), ((Addition32.circuit (p:=p)).output ⟨((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8)), ((Addition32.circuit (p:=p)).output ⟨((Rotation32.circuit (p:=p) 12).output ((Xor32.circuit (p:=p)).output ⟨state[b], ((Addition32.circuit (p:=p)).output ⟨state[c], ((Rotation32.circuit (p:=p) 16).output ((Xor32.circuit (p:=p)).output ⟨state[d], ((Addition32.circuit (p:=p)).output ⟨state[a], ((Addition32.circuit (p:=p)).output ⟨state[b], x⟩ n)⟩ (n + 8))⟩ (n + 16)) (n + 20))⟩ (n + 28))⟩ (n + 36)) (n + 40)), y⟩ (n + 48))⟩ (n + 56))⟩ (n + 64)) (n + 68))⟩ (n + 76))⟩ (n + 84)) (n + 88)) := by
  have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
  have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
  have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
    fun _ _ => rfl
  have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o9 := node9_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o10 := node10_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o11 := node11_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o12 := node12_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  have o13 := node13_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h1 h2 h3
    (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
  exact FormalCircuit.output_of_input_eq _
    o13
    (ProverEnvironment.agreesBelow_of_le h_agrees
      (by first | omega | (simp only [eA, eX, eR]; omega)))

set_option maxRecDepth 2048 in
/-- Env-agreement transfers to the output state: the four set slots are fresh witness
windows below the bound, the remaining entries evaluate through the input state. -/
private lemma output_eval_congr {env env' : ProverEnvironment (F p)}
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
    intro n input env env'
    obtain ⟨state, x, y⟩ := input
    have eA : ∀ v, (Addition32.circuit (p:=p)).localLength v = 8 := fun _ => rfl
    have eX : ∀ v, (Xor32.circuit (p:=p)).localLength v = 4 := fun _ => rfl
    have eR : ∀ (k : Fin 32) v, (Rotation32.circuit (p:=p) k).localLength v = 8 :=
      fun _ _ => rfl
    simp only [circuit_norm, main, eA, eX, eR]
    refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
             fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
             fun h => ?_, fun h => ?_⟩, fun h h_agrees => ?_⟩
    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o1 := node1_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o3 := node3_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          first
            | exact o3
            | ((try and_intros) <;> grind)

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o6 := node6_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          first
            | exact o6
            | ((try and_intros) <;> grind)

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o2 := node2_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have o8 := node8_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o4 := node4_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have o9 := node9_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o10 := node10_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          first
            | exact o10
            | ((try and_intros) <;> grind)

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o5 := node5_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have o11 := node11_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o7 := node7_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          try have o12 := node12_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          (try and_intros) <;> grind

    · exact FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eX, eR]; try omega)) fun h_agrees => by
          try have o13 := node13_out_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h.2.1 h.2.2 (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))
          simp only [circuit_norm]
          first
            | exact o13
            | ((try and_intros) <;> grind)

    · -- output
      exact output_eval_congr (a := a) (b := b) (c := c) (d := d) (n := n) h.1 h_agrees

end Gadgets.BLAKE3.G
