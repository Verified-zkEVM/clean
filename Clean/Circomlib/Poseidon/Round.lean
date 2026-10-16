module

public import Clean.Circuit.Loops
public import Clean.Circomlib.Poseidon.Linear
public import Clean.Circomlib.Poseidon.Sigma

@[expose] public section

namespace Circomlib.Poseidon

open Specs.Poseidon (F)
open Specs.PoseidonOptimized (Params)

namespace FullRound

def main {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t) (offset : ℕ)
    (hOffset : offset + t ≤ 8 * t + params.nPartial)
    (input : Vector (Expression F) t) : Circuit F (Vector (Expression F) t) := do
  let sboxed ← Circuit.map input fun x => Sigma.circuit x
  let arked := Vector.ofFn fun i =>
    sboxed[i.val] + Expression.const
      (params.C[offset + i.val]'(by omega) : F)
  Mix.circuit matrix arked

def Spec {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t) (offset : ℕ)
    (input output : Vector F t) : Prop :=
  output = Specs.PoseidonOptimized.denseRound params matrix offset input

instance elaborated {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t) (offset : ℕ)
    (hOffset : offset + t ≤ 8 * t + params.nPartial) :
    ElaboratedCircuit F (fields t) (fields t) (main params matrix offset hOffset) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t) (offset : ℕ)
    (hOffset : offset + t ≤ 8 * t + params.nPartial) :
    Soundness F (Input := fields t) (Output := fields t)
      (main params matrix offset hOffset) (fun _ => True) (Spec params matrix offset) := by
  circuit_proof_start [Sigma.circuit, Mix.circuit, Mix.Spec]
  rw [h_holds.2]
  simp_rw [Vector.ext_iff, Vector.getElem_map] at h_input
  unfold Specs.PoseidonOptimized.denseRound
  apply congrArg (Specs.Poseidon.mix matrix)
  ext i hi
  have hc : offset + i < 8 * t + params.nPartial := by omega
  simp [Specs.Poseidon.ark, Specs.Poseidon.sboxFull, Specs.Poseidon.sigma,
    h_holds.1 ⟨i, hi⟩, h_input, hc, circuit_norm]

theorem completeness {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t) (offset : ℕ)
    (hOffset : offset + t ≤ 8 * t + params.nPartial) :
    Completeness F (Input := fields t) (Output := fields t)
      (main params matrix offset hOffset) (fun _ => True) := by
  circuit_proof_start [Sigma.circuit, Mix.circuit]

def circuit {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t) (offset : ℕ)
    (hOffset : offset + t ≤ 8 * t + params.nPartial) :
    FormalCircuit F (fields t) (fields t) where
  main := main params matrix offset hOffset
  elaborated := elaborated params matrix offset hOffset
  Spec := Spec params matrix offset
  soundness := soundness params matrix offset hOffset
  completeness := completeness params matrix offset hOffset

end FullRound

namespace PartialRound

def main {t : ℕ} (params : Params t) (cOffset : ℕ)
    (hOffset : cOffset < 8 * t + params.nPartial)
    (round : Fin params.nPartial) (input : Vector (Expression F) t) :
    Circuit F (Vector (Expression F) t) := do
  let sbox0 ← Sigma.circuit (input[0]'(by
    have := params.two_le_width
    omega))
  let ark0 <== sbox0 + Expression.const (params.C[cOffset]'hOffset : F)
  let arked := Vector.ofFn fun i =>
    if hi : i.val = 0 then
      ark0
    else
      input[i.val]
  MixS.circuit params round arked

def Spec {t : ℕ} (params : Params t) (cOffset : ℕ)
    (round : Fin params.nPartial) (input output : Vector F t) : Prop :=
  output = Specs.PoseidonOptimized.partialRound params cOffset round.val input round.isLt

instance elaborated {t : ℕ} (params : Params t) (cOffset : ℕ)
    (hOffset : cOffset < 8 * t + params.nPartial) (round : Fin params.nPartial) :
    ElaboratedCircuit F (fields t) (fields t) (main params cOffset hOffset round) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) (cOffset : ℕ)
    (hOffset : cOffset < 8 * t + params.nPartial) (round : Fin params.nPartial) :
    Soundness F (Input := fields t) (Output := fields t)
      (main params cOffset hOffset round) (fun _ => True) (Spec params cOffset round) := by
  circuit_proof_start [Sigma.circuit, MixS.circuit, MixS.Spec]
  obtain ⟨hSigma, hArk, hMix⟩ := h_holds
  rw [hMix]
  simp_rw [Vector.ext_iff, Vector.getElem_map] at h_input
  unfold Specs.PoseidonOptimized.partialRound
  simp only [dif_pos hOffset]
  apply congrArg (Specs.PoseidonOptimized.mixS params round)
  ext i hi
  by_cases hi0 : i = 0
  · simp [hi0, Specs.Poseidon.sigma, hSigma, hArk, h_input, circuit_norm]
  · simp [hi0, h_input, circuit_norm]

theorem completeness {t : ℕ} (params : Params t) (cOffset : ℕ)
    (hOffset : cOffset < 8 * t + params.nPartial) (round : Fin params.nPartial) :
    Completeness F (Input := fields t) (Output := fields t)
      (main params cOffset hOffset round) (fun _ => True) := by
  circuit_proof_start [Sigma.circuit, MixS.circuit]
  exact h_env.2.1

def circuit {t : ℕ} (params : Params t) (cOffset : ℕ)
    (hOffset : cOffset < 8 * t + params.nPartial) (round : Fin params.nPartial) :
    FormalCircuit F (fields t) (fields t) where
  main := main params cOffset hOffset round
  elaborated := elaborated params cOffset hOffset round
  Spec := Spec params cOffset round
  soundness := soundness params cOffset hOffset round
  completeness := completeness params cOffset hOffset round

end PartialRound

namespace FinalRound

/-- Apply the final full S-box layer and compute only the first coordinate of
the dense mix, which is the Poseidon hash output. -/
def main {t : ℕ} (params : Params t) (input : Vector (Expression F) t) :
    Circuit F (Expression F) := do
  let sboxed ← Circuit.map input fun x => Sigma.circuit x
  MixLast.circuit params sboxed

def Spec {t : ℕ} (params : Params t) (input : Vector F t) (output : F) : Prop :=
  output = (Specs.Poseidon.mix params.M (Specs.Poseidon.sboxFull input))[0]'(by
    have := params.two_le_width
    omega)

instance elaborated {t : ℕ} (params : Params t) :
    ElaboratedCircuit F (fields t) field (main params) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) :
    Soundness F (Input := fields t) (Output := field)
      (main params) (fun _ => True) (Spec params) := by
  circuit_proof_start [Sigma.circuit, MixLast.circuit, MixLast.Spec]
  rw [h_holds.2]
  simp_rw [Vector.ext_iff, Vector.getElem_map] at h_input
  apply congrArg fun state => (Specs.Poseidon.mix params.M state)[0]'(by
    have := params.two_le_width
    omega)
  ext i hi
  simp [Specs.Poseidon.sboxFull, Specs.Poseidon.sigma,
    h_holds.1 ⟨i, hi⟩, h_input, circuit_norm]

theorem completeness {t : ℕ} (params : Params t) :
    Completeness F (Input := fields t) (Output := field)
      (main params) (fun _ => True) := by
  circuit_proof_start [Sigma.circuit, MixLast.circuit]

def circuit {t : ℕ} (params : Params t) :
    FormalCircuit F (fields t) field where
  main := main params
  elaborated := elaborated params
  Spec := Spec params
  soundness := soundness params
  completeness := completeness params

end FinalRound

end Circomlib.Poseidon
