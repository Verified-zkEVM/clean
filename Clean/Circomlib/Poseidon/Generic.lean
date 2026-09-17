module

public import Clean.Circomlib.Poseidon.Repeat

@[expose] public section

namespace Circomlib.Poseidon

open Specs.Poseidon (F)
open Specs.PoseidonOptimized (Params)

/-- The optimized circomlib Poseidon circuit at arbitrary supported state
width. Its input arity is `t - 1`, with a zero capacity element. -/
def main {t : ℕ} (params : Params t)
    (input : Vector (Expression F) (t - 1)) : Circuit F (Expression F) := do
  let state ← InitialArk.circuit params input
  let state ← ApplyFullRounds.circuit params params.M 3 t (by omega) state
  let state ← FullRound.circuit params params.P (4 * t) (by omega) state
  let state ← ApplyPartialRounds.circuit params params.nPartial (5 * t) 0
    (by omega) (by omega) state
  let state ← ApplyFullRounds.circuit params params.M 3 (5 * t + params.nPartial)
    (by omega) state
  FinalRound.circuit params state

def Spec {t : ℕ} (params : Params t)
    (input : Vector F (t - 1)) (output : F) : Prop :=
  output = Specs.PoseidonOptimized.poseidon params input

instance elaborated {t : ℕ} (params : Params t) :
    ElaboratedCircuit F (fields (t - 1)) field (main params) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) :
    Soundness F (Input := fields (t - 1)) (Output := field)
      (main params) (fun _ => True) (Spec params) := by
  circuit_proof_start [InitialArk.circuit, InitialArk.Spec,
    ApplyFullRounds.circuit, ApplyFullRounds.Spec,
    FullRound.circuit, FullRound.Spec,
    ApplyPartialRounds.circuit, ApplyPartialRounds.Spec,
    FinalRound.circuit, FinalRound.Spec]
  simp only [Specs.PoseidonOptimized.poseidon,
    Specs.PoseidonOptimized.permutation] at h_holds ⊢
  simp +arith only [circuit_norm, Specs.PoseidonOptimized.fullRounds] at h_holds ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h_holds
  rw [h5]
  simp only [h4, h3, h2, h1, h0]

theorem completeness {t : ℕ} (params : Params t) :
    Completeness F (Input := fields (t - 1)) (Output := field)
      (main params) (fun _ => True) := by
  circuit_proof_start [InitialArk.circuit, ApplyFullRounds.circuit,
    FullRound.circuit, ApplyPartialRounds.circuit, FinalRound.circuit]

/-- A single verified Poseidon circuit covers every arity represented by a
valid optimized parameter bundle. -/
def circuit {t : ℕ} (params : Params t) :
    FormalCircuit F (fields (t - 1)) field where
  main := main params
  elaborated := elaborated params
  Spec := Spec params
  soundness := soundness params
  completeness := completeness params

end Circomlib.Poseidon
