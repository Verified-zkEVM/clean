module

public import Clean.Circomlib.Poseidon.Round

@[expose] public section

namespace Circomlib.Poseidon

open Specs.Poseidon (F)
open Specs.PoseidonOptimized (Params)

/-- Value of a folded circuit state after `k` rounds. The stride and output
offset are supplied by the repeated child circuit's elaborated layout. -/
def envState {t : ℕ} (env : Environment F) (input : Vector F t) (base stride outputOffset k : ℕ) :
    Vector F t :=
  if k = 0 then input
  else Vector.map (Expression.eval env) <|
    Vector.mapRange t fun i => var { index := base + (k - 1) * stride + outputOffset + i }

private lemma denseRounds_induction {t : ℕ} (params : Params t)
    (matrix : Vector (Vector ℕ t) t) (nRounds offset : ℕ)
    (states : ℕ → Vector F t)
    (hRound : ∀ (i : ℕ), i < nRounds →
      states (i + 1) = Specs.PoseidonOptimized.denseRound params matrix
        (offset + i * t) (states i)) :
    states nRounds =
      Specs.PoseidonOptimized.denseRounds params matrix nRounds offset (states 0) := by
  induction nRounds generalizing offset states with
  | zero => simp [Specs.PoseidonOptimized.denseRounds]
  | succ n ih =>
      simp only [Specs.PoseidonOptimized.denseRounds]
      have h0 := hRound 0 (by omega)
      simp only [zero_mul, Nat.add_zero] at h0
      rw [← h0]
      apply ih (offset + t) (fun i => states (i + 1))
      intro i hi
      have hi' := hRound (i + 1) (by omega)
      convert hi' using 2
      all_goals ring

namespace ApplyFullRounds

def main {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (nRounds offset : ℕ) [NeZero nRounds] (hOffset : offset + nRounds * t ≤ 8 * t + params.nPartial)
    (input : Vector (Expression F) t) : Circuit F (Vector (Expression F) t) :=
  Circuit.foldlRange nRounds input
    (fun state round =>
      FullRound.circuit params matrix (offset + round.val * t) (by
        have hMul : (round.val + 1) * t ≤ nRounds * t :=
          Nat.mul_le_mul_right t (by omega)
        calc
          offset + round.val * t + t = offset + (round.val + 1) * t := by ring
          _ ≤ offset + nRounds * t := Nat.add_le_add_left hMul offset
          _ ≤ 8 * t + params.nPartial := hOffset) state)
    (by
      intro pair n
      simp only [circuit_norm, FullRound.circuit])
    ⟨4 * t, by
      intro pair n
      simp only [circuit_norm, FullRound.circuit]
      ring⟩

def Spec {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (nRounds offset : ℕ) (input output : Vector F t) : Prop :=
  output = Specs.PoseidonOptimized.denseRounds params matrix nRounds offset input

instance elaborated {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (nRounds offset : ℕ) [NeZero nRounds] (hOffset : offset + nRounds * t ≤ 8 * t + params.nPartial) :
    ElaboratedCircuit F (fields t) (fields t)
      (main params matrix nRounds offset hOffset) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (nRounds offset : ℕ) [NeZero nRounds] (hOffset : offset + nRounds * t ≤ 8 * t + params.nPartial) :
    Soundness F (Input := fields t) (Output := fields t)
      (main params matrix nRounds offset hOffset) (fun _ => True)
      (Spec params matrix nRounds offset) := by
  circuit_proof_start [FullRound.circuit, FullRound.Spec]
  obtain ⟨h0, hSucc⟩ := h_holds
  let state := envState env input i₀ (t * 3 + t) (t * 3)
  have hRound : ∀ (k : ℕ), k < nRounds →
      state (k + 1) = Specs.PoseidonOptimized.denseRound params matrix
        (offset + k * t) (state k) := by
    intro k hk
    rcases k with _ | j
    · simpa [state, envState, circuit_norm] using h0
    · simp only [state, envState, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
      convert hSucc j hk using 1
      all_goals simp [circuit_norm]
  have hFinal := denseRounds_induction params matrix nRounds offset state hRound
  simp [state, envState, circuit_norm, NeZero.ne nRounds] at hFinal ⊢
  convert hFinal using 1

theorem completeness {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (nRounds offset : ℕ) [NeZero nRounds] (hOffset : offset + nRounds * t ≤ 8 * t + params.nPartial) :
    Completeness F (Input := fields t) (Output := fields t)
      (main params matrix nRounds offset hOffset) (fun _ => True) := by
  circuit_proof_start [FullRound.circuit]

def circuit {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (nRounds offset : ℕ) [NeZero nRounds] (hOffset : offset + nRounds * t ≤ 8 * t + params.nPartial) :
    FormalCircuit F (fields t) (fields t) where
  main := main params matrix nRounds offset hOffset
  elaborated := elaborated params matrix nRounds offset hOffset
  Spec := Spec params matrix nRounds offset
  soundness := soundness params matrix nRounds offset hOffset
  completeness := completeness params matrix nRounds offset hOffset
  computableWitnesses := by
    have := Nat.le_mul_of_pos_left (t * 3 + t) (NeZero.pos nRounds)
    computable_witnesses [FullRound.circuit, add_one_mul, Nat.sub_one_mul]

end ApplyFullRounds

private lemma partialRounds_induction {t : ℕ} (params : Params t)
    (nRounds cOffset sRound : ℕ) (hRounds : sRound + nRounds ≤ params.nPartial)
    (states : ℕ → Vector F t)
    (hRound : ∀ (i : ℕ) (hi : i < nRounds),
      states (i + 1) = Specs.PoseidonOptimized.partialRound params
        (cOffset + i) (sRound + i) (states i) (by omega)) :
    states nRounds = Specs.PoseidonOptimized.partialRounds params
      nRounds cOffset sRound (states 0) hRounds := by
  induction nRounds generalizing cOffset sRound states with
  | zero => simp [Specs.PoseidonOptimized.partialRounds]
  | succ n ih =>
      simp only [Specs.PoseidonOptimized.partialRounds]
      have h0 := hRound 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [← h0]
      apply ih (cOffset + 1) (sRound + 1) (by omega) (fun i => states (i + 1))
      intro i hi
      have hi' := hRound (i + 1) (by omega)
      convert hi' using 2 <;> omega

namespace ApplyPartialRounds

def main {t : ℕ} (params : Params t) (nRounds cOffset sRound : ℕ) [NeZero nRounds]
    (hRounds : sRound + nRounds ≤ params.nPartial)
    (hOffset : cOffset + nRounds ≤ 8 * t + params.nPartial)
    (input : Vector (Expression F) t) : Circuit F (Vector (Expression F) t) :=
  Circuit.foldlRange nRounds input
    (fun state round =>
      PartialRound.circuit params (cOffset + round.val) (by
        have := round.isLt
        omega) ⟨sRound + round.val, by
          have := round.isLt
          omega⟩ state)
    (by
      intro pair n
      simp only [circuit_norm, PartialRound.circuit])
    ⟨t + 4, by
      intro pair n
      simp only [circuit_norm, PartialRound.circuit]
      ring⟩

def Spec {t : ℕ} (params : Params t) (nRounds cOffset sRound : ℕ)
    (hRounds : sRound + nRounds ≤ params.nPartial)
    (input output : Vector F t) : Prop :=
  output = Specs.PoseidonOptimized.partialRounds params
    nRounds cOffset sRound input hRounds

instance elaborated {t : ℕ} (params : Params t) (nRounds cOffset sRound : ℕ) [NeZero nRounds]
    (hRounds : sRound + nRounds ≤ params.nPartial)
    (hOffset : cOffset + nRounds ≤ 8 * t + params.nPartial) :
    ElaboratedCircuit F (fields t) (fields t)
      (main params nRounds cOffset sRound hRounds hOffset) := by
  elaborate_circuit

theorem soundness {t : ℕ} (params : Params t) (nRounds cOffset sRound : ℕ) [NeZero nRounds]
    (hRounds : sRound + nRounds ≤ params.nPartial)
    (hOffset : cOffset + nRounds ≤ 8 * t + params.nPartial) :
    Soundness F (Input := fields t) (Output := fields t)
      (main params nRounds cOffset sRound hRounds hOffset) (fun _ => True)
      (Spec params nRounds cOffset sRound hRounds) := by
  circuit_proof_start [PartialRound.circuit, PartialRound.Spec]
  obtain ⟨h0, hSucc⟩ := h_holds
  let state := envState env input i₀ (3 + (1 + t)) (3 + 1)
  have hRound : ∀ (k : ℕ) (hk : k < nRounds),
      state (k + 1) = Specs.PoseidonOptimized.partialRound params
        (cOffset + k) (sRound + k) (state k) (by omega) := by
    intro k hk
    rcases k with _ | j
    · simpa [state, envState, circuit_norm] using h0
    · simp only [state, envState, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
      convert hSucc j hk using 1
      all_goals simp [circuit_norm]
  have hFinal := partialRounds_induction params nRounds cOffset sRound hRounds state hRound
  simp [state, envState, circuit_norm, NeZero.ne nRounds] at hFinal ⊢
  convert hFinal using 1

theorem completeness {t : ℕ} (params : Params t) (nRounds cOffset sRound : ℕ) [NeZero nRounds]
    (hRounds : sRound + nRounds ≤ params.nPartial)
    (hOffset : cOffset + nRounds ≤ 8 * t + params.nPartial) :
    Completeness F (Input := fields t) (Output := fields t)
      (main params nRounds cOffset sRound hRounds hOffset) (fun _ => True) := by
  circuit_proof_start [PartialRound.circuit]

def circuit {t : ℕ} (params : Params t) (nRounds cOffset sRound : ℕ) [NeZero nRounds]
    (hRounds : sRound + nRounds ≤ params.nPartial)
    (hOffset : cOffset + nRounds ≤ 8 * t + params.nPartial) :
    FormalCircuit F (fields t) (fields t) where
  main := main params nRounds cOffset sRound hRounds hOffset
  elaborated := elaborated params nRounds cOffset sRound hRounds hOffset
  Spec := Spec params nRounds cOffset sRound hRounds
  soundness := soundness params nRounds cOffset sRound hRounds hOffset
  completeness := completeness params nRounds cOffset sRound hRounds hOffset
  computableWitnesses := by
    have := Nat.le_mul_of_pos_left (3 + (1 + t)) (NeZero.pos nRounds)
    computable_witnesses [PartialRound.circuit, add_one_mul, Nat.sub_one_mul]

end ApplyPartialRounds

end Circomlib.Poseidon
