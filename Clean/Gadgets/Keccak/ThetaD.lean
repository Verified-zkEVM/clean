import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaD
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (row : Var KeccakRow (F p)) : Circuit sentences (Var KeccakRow (F p)) := do
  let c0 ← Rotation64.circuit order (64 - 1) row[1]
  let c0 ← Xor64.circuit order ⟨row[4], c0⟩

  let c1 ← Rotation64.circuit order (64 - 1) row[2]
  let c1 ← Xor64.circuit order ⟨row[0], c1⟩

  let c2 ← Rotation64.circuit order (64 - 1) row[3]
  let c2 ← Xor64.circuit order ⟨row[1], c2⟩

  let c3 ← Rotation64.circuit order (64 - 1) row[4]
  let c3 ← Xor64.circuit order ⟨row[2], c3⟩

  let c4 ← Rotation64.circuit order (64 - 1) row[0]
  let c4 ← Xor64.circuit order ⟨row[3], c4⟩

  return #v[c0, c1, c2, c3, c4]

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences KeccakRow KeccakRow where
  main := main order
  localLength _ := 120
  yields _ _ _ := ∅
  yields_eq := by
    intro env input offset
    simp only [main, circuit_norm, ElaboratedCircuit.yields_eq]
    simp [Rotation64.circuit, Rotation64.elaborated, Xor64.circuit, Xor64.elaborated]

def Assumptions (state : KeccakRow (F p)) := state.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (state : KeccakRow (F p)) := Assumptions state

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (row : KeccakRow (F p)) (out : KeccakRow (F p)) : Prop :=
  out.Normalized
  ∧ out.value = Specs.Keccak256.thetaD row.value

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro i0 env yields checked row_var row h_input row_norm h_holds
  simp only [circuit_norm, eval_vector] at h_input
  dsimp only [Assumptions] at row_norm
  dsimp only [circuit_norm, Spec, elaborated, main, Xor64.circuit, Xor64.elaborated, Rotation64.circuit, Rotation64.elaborated] at h_holds ⊢
  simp only [circuit_norm, Xor64.Assumptions, Xor64.Spec, Rotation64.Assumptions, Rotation64.Spec] at h_holds
  simp only [zero_sub, Fin.coe_neg_one, and_imp, add_assoc, Nat.reduceAdd] at h_holds
  simp only [circuit_norm, KeccakRow.normalized_iff, KeccakRow.value, eval_vector]

  have s (i : ℕ) (hi : i < 5) : eval env (row_var[i]) = row[i] := by
    rw [←h_input, Vector.getElem_map]

  simp only [s] at h_holds
  obtain ⟨ h_rot0, h_xor0, h_rot1, h_xor1, h_rot2, h_xor2, h_rot3, h_xor3, h_rot4, h_xor4 ⟩ := h_holds

  specialize h_rot0 (row_norm 1)
  specialize h_xor0 (row_norm 4) h_rot0.2.2

  specialize h_rot1 (row_norm 2)
  specialize h_xor1 (row_norm 0) h_rot1.2.2

  specialize h_rot2 (row_norm 3)
  specialize h_xor2 (row_norm 1) h_rot2.2.2

  specialize h_rot3 (row_norm 4)
  specialize h_xor3 (row_norm 2) h_rot3.2.2

  specialize h_rot4 (row_norm 0)
  specialize h_xor4 (row_norm 3) h_rot4.2.2

  simp [Specs.Keccak256.thetaD, h_xor0.2, h_xor1.2, h_xor2.2, h_xor3.2, h_xor4.2,
    h_rot0.2.1, h_rot1.2.1, h_rot2.2.1, h_rot3.2.1, h_rot4.2.1, rotLeft64]

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  intro i0 env yields row_var h_env row h_input h_assumptions
  simp only [CompletenessAssumptions, Assumptions, KeccakRow.normalized_iff] at h_assumptions
  dsimp only [circuit_norm, elaborated, main, Xor64.circuit, Xor64.elaborated, Rotation64.circuit, Rotation64.elaborated] at h_env ⊢
  simp_all only [circuit_norm, getElem_eval_vector,
    Xor64.CompletenessAssumptions, Xor64.Assumptions, Xor64.Spec, Rotation64.CompletenessAssumptions, Rotation64.Assumptions, Rotation64.Spec,
    add_assoc, seval, true_and, true_implies]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order KeccakRow KeccakRow :=
  { elaborated := elaborated order
    Assumptions
    CompletenessAssumptions
    Spec
    soundness := soundness order
    completeness := completeness order
    completenessAssumptions_implies_assumptions := fun _ _ h => h }

end Gadgets.Keccak256.ThetaD
