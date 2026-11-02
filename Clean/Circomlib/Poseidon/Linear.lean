module

public import Batteries.Data.Fin.Fold
public import Clean.Circuit
public import Clean.Specs.PoseidonOptimized
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

namespace Circomlib.Poseidon

open Specs.Poseidon (F ark mix)
open Specs.PoseidonOptimized (Params)

namespace Linear

/-- A circuit-level dot product, shared by the dense and sparse linear layers. -/
def dot {t : ℕ} (coefficients : Vector ℕ t)
    (state : Vector (Expression F) t) : Expression F :=
  Fin.foldl t (fun acc j =>
    acc + Expression.const (coefficients[j.val] : F) * state[j.val]) 0

/-- Evaluation commutes with the circuit-level dot product. -/
theorem eval_dot {t : ℕ} (env : Environment F) (coefficients : Vector ℕ t)
    (state : Vector (Expression F) t) :
    Expression.eval env (dot coefficients state) =
      Fin.foldl t (fun acc j =>
        acc + (coefficients[j.val] : F) * Expression.eval env state[j.val]) 0 := by
  unfold dot
  rw [eval_foldl]
  · simp [circuit_norm]
  · intro e i
    simp [circuit_norm]

private theorem foldl_eq_range {n : ℕ} {A : Type} (f : A → Fin n → A) (init : A) :
    Fin.foldl n f init =
      (List.range n).foldl (fun acc i => if hi : i < n then f acc ⟨i, hi⟩ else acc) init := by
  rw [Fin.foldl_eq_foldl_finRange, ← List.map_coe_finRange_eq_range, List.foldl_map]
  simp

/-- The shared dot product is one column of the specification's matrix product. -/
theorem dot_eq_mix_column {t : ℕ} (matrix : Vector (Vector ℕ t) t)
    (state : Vector F t) (column : Fin t) :
    Fin.foldl t (fun acc row =>
      acc + (matrix[row.val][column.val] : F) * state[row.val]) 0 =
      (mix matrix state)[column.val] := by
  rw [foldl_eq_range]
  simp [Specs.Poseidon.mix]

end Linear

namespace InitialArk

def main {t : ℕ} (params : Params t)
    (input : Vector (Expression F) (t - 1)) : Circuit F (Vector (Expression F) t) := do
  let state : Vector (Expression F) t := Vector.ofFn fun i =>
    if hi : i.val = 0 then
      0
    else
      input[i.val - 1]'(by omega)
  let output : Vector (Expression F) t <== Vector.ofFn fun (i : Fin t) =>
    state[i] + Expression.const
      (params.C[i.val]'(by have := params.two_le_width; omega) : F)
  return output

def Spec {t : ℕ} (params : Params t)
    (input : Vector F (t - 1)) (output : Vector F t) : Prop :=
  output = ark params.C 0 (Specs.PoseidonOptimized.initialState input)

instance elaborated {t : ℕ} (params : Params t) :
    ElaboratedCircuit F (fields (t - 1)) (fields t) (main params) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) :
    Soundness F (Input := fields (t - 1)) (Output := fields t)
      (main params) (fun _ => True) (Spec params) := by
  circuit_proof_start
  rw [h_holds]
  ext i hi
  have hc : i < 8 * t + params.nPartial := by
    have := params.two_le_width
    omega
  by_cases hi0 : i = 0
  · simp [Specs.Poseidon.ark, Specs.PoseidonOptimized.initialState, hi0,
      circuit_norm]
    omega
  · simp [Specs.Poseidon.ark, Specs.PoseidonOptimized.initialState, hi0, hc,
      circuit_norm, ← h_input]

theorem completeness {t : ℕ} (params : Params t) :
    Completeness F (Input := fields (t - 1)) (Output := fields t)
      (main params) (fun _ => True) := by
  circuit_proof_start
  rw [Vector.ext_iff]
  intro i hi
  simp [circuit_norm, h_env ⟨i, hi⟩]

def circuit {t : ℕ} (params : Params t) :
    FormalCircuit F (fields (t - 1)) (fields t) where
  main := main params
  elaborated := elaborated params
  Spec := Spec params
  soundness := soundness params
  completeness := completeness params

end InitialArk

namespace Mix

def main {t : ℕ} (matrix : Vector (Vector ℕ t) t)
    (input : Vector (Expression F) t) : Circuit F (Vector (Expression F) t) := do
  let output : Vector (Expression F) t <== Vector.ofFn fun column =>
    Linear.dot (Vector.ofFn fun row => matrix[row.val][column.val]) input
  return output

def Spec {t : ℕ} (matrix : Vector (Vector ℕ t) t)
    (input output : Vector F t) : Prop :=
  output = mix matrix input

instance elaborated {t : ℕ} (matrix : Vector (Vector ℕ t) t) :
    ElaboratedCircuit F (fields t) (fields t) (main matrix) := by
  elaborate_circuit

theorem soundness {t : ℕ} (matrix : Vector (Vector ℕ t) t) :
    Soundness F (Input := fields t) (Output := fields t)
      (main matrix) (fun _ => True) (Spec matrix) := by
  circuit_proof_start
  rw [h_holds]
  simp_rw [Vector.ext_iff, Vector.getElem_map] at h_input
  ext column hcolumn
  rw [Vector.getElem_map, Vector.getElem_ofFn, Linear.eval_dot]
  simp_rw [h_input]
  simp_rw [Vector.getElem_ofFn]
  exact Linear.dot_eq_mix_column matrix input ⟨column, hcolumn⟩

theorem completeness {t : ℕ} (matrix : Vector (Vector ℕ t) t) :
    Completeness F (Input := fields t) (Output := fields t)
      (main matrix) (fun _ => True) := by
  circuit_proof_start
  rw [Vector.ext_iff]
  intro i hi
  simp [circuit_norm, h_env ⟨i, hi⟩]

def circuit {t : ℕ} (matrix : Vector (Vector ℕ t) t) :
    FormalCircuit F (fields t) (fields t) where
  main := main matrix
  elaborated := elaborated matrix
  Spec := Spec matrix
  soundness := soundness matrix
  completeness := completeness matrix

end Mix

namespace MixS

def firstRow {t : ℕ} (params : Params t) (round : Fin params.nPartial) :
    Vector ℕ t :=
  let constants := Specs.PoseidonOptimized.sparseRoundConstants params round
  Vector.ofFn fun i => constants[i.val]'(by
    have := params.two_le_width
    omega)

def main {t : ℕ} (params : Params t) (round : Fin params.nPartial)
    (input : Vector (Expression F) t) : Circuit F (Vector (Expression F) t) := do
  let constants := Specs.PoseidonOptimized.sparseRoundConstants params round
  let output : Vector (Expression F) t <== Vector.ofFn fun i =>
    if hi : i.val = 0 then
      Linear.dot (firstRow params round) input
    else
      input[i.val] + input[0]'(by have := params.two_le_width; omega) *
        Expression.const (constants[t + i.val - 1]'(by
          have := params.two_le_width
          omega) : F)
  return output

def Spec {t : ℕ} (params : Params t) (round : Fin params.nPartial)
    (input output : Vector F t) : Prop :=
  output = Specs.PoseidonOptimized.mixS params round input

instance elaborated {t : ℕ} (params : Params t) (round : Fin params.nPartial) :
    ElaboratedCircuit F (fields t) (fields t) (main params round) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) (round : Fin params.nPartial) :
    Soundness F (Input := fields t) (Output := fields t)
      (main params round) (fun _ => True) (Spec params round) := by
  circuit_proof_start
  rw [h_holds]
  simp_rw [Vector.ext_iff, Vector.getElem_map] at h_input
  ext i hi
  by_cases hi0 : i = 0
  · simp [Specs.PoseidonOptimized.mixS, hi0, circuit_norm, Linear.eval_dot,
      firstRow, h_input]
  · simp [Specs.PoseidonOptimized.mixS, hi0, circuit_norm, h_input]

theorem completeness {t : ℕ} (params : Params t) (round : Fin params.nPartial) :
    Completeness F (Input := fields t) (Output := fields t)
      (main params round) (fun _ => True) := by
  circuit_proof_start
  rw [Vector.ext_iff]
  intro i hi
  simp [circuit_norm, h_env ⟨i, hi⟩]

def circuit {t : ℕ} (params : Params t) (round : Fin params.nPartial) :
    FormalCircuit F (fields t) (fields t) where
  main := main params round
  elaborated := elaborated params round
  Spec := Spec params round
  soundness := soundness params round
  completeness := completeness params round

end MixS

namespace MixLast

def coefficients {t : ℕ} (params : Params t) : Vector ℕ t :=
  Vector.ofFn fun row => params.M[row.val][0]'(by
    have := params.two_le_width
    omega)

def main {t : ℕ} (params : Params t) (input : Vector (Expression F) t) :
    Circuit F (Expression F) := do
  let output <== Linear.dot (coefficients params) input
  return output

def Spec {t : ℕ} (params : Params t) (input : Vector F t) (output : F) : Prop :=
  output = (mix params.M input)[0]'(by
    have := params.two_le_width
    omega)

instance elaborated {t : ℕ} (params : Params t) :
    ElaboratedCircuit F (fields t) field (main params) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) :
    Soundness F (Input := fields t) (Output := field)
      (main params) (fun _ => True) (Spec params) := by
  circuit_proof_start
  simp_rw [Vector.ext_iff, Vector.getElem_map] at h_input
  rw [h_holds, Linear.eval_dot]
  simp_rw [h_input]
  simp only [coefficients, Vector.getElem_ofFn]
  exact Linear.dot_eq_mix_column params.M input ⟨0, by
    have := params.two_le_width
    omega⟩

theorem completeness {t : ℕ} (params : Params t) :
    Completeness F (Input := fields t) (Output := field)
      (main params) (fun _ => True) := by
  circuit_proof_start
  simp_all [circuit_norm]

def circuit {t : ℕ} (params : Params t) :
    FormalCircuit F (fields t) field where
  main := main params
  elaborated := elaborated params
  Spec := Spec params
  soundness := soundness params
  completeness := completeness params

end MixLast

end Circomlib.Poseidon
