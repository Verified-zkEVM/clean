import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Addition32.Theorems
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState

namespace Gadgets.Keccak.ThetaC
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)
open Clean.Gadgets.Keccak256

@[reducible] def Outputs := ProvableVector U64 5
-- note: `reducible` is needed for type class inference, i.e. `ProvableType KeccakState`

def theta_c (state : Var KeccakState (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  -- TODO would be nice to have a for loop of length 5 here
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 0), (state.get 1)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 2)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 3)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 4)⟩

  let c1 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 5), (state.get 6)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 7)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 8)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 9)⟩

  let c2 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 10), (state.get 11)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 12)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 13)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 14)⟩

  let c3 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 15), (state.get 16)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 17)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 18)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 19)⟩

  let c4 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 20), (state.get 21)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 22)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 23)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 24)⟩
  return #v[c0, c1, c2, c3, c4]

def assumptions (state : KeccakState (F p)) : Prop :=
  ∀ i : Fin 25, state[i].is_normalized

def spec (state : KeccakState (F p)) (out: Outputs (F p)) : Prop :=
  let h_norm := out[0].is_normalized ∧ out[1].is_normalized ∧
                out[2].is_normalized ∧ out[3].is_normalized ∧ out[4].is_normalized

  let h_xor0 :=
    out[0].value = (state[0].value |>.xor state[1].value |>.xor state[2].value |>.xor state[3].value |>.xor state[4].value)
  let h_xor1 :=
    out[1].value = (state[5].value |>.xor state[6].value |>.xor state[7].value |>.xor state[8].value |>.xor state[9].value)
  let h_xor2 :=
    out[2].value = (state[10].value |>.xor state[11].value |>.xor state[12].value |>.xor state[13].value |>.xor state[14].value)
  let h_xor3 :=
    out[3].value = (state[15].value |>.xor state[16].value |>.xor state[17].value |>.xor state[18].value |>.xor state[19].value)
  let h_xor4 :=
    out[4].value = (state[20].value |>.xor state[21].value |>.xor state[22].value |>.xor state[23].value |>.xor state[24].value)

  h_norm ∧ (h_xor0 ∧ h_xor1 ∧ h_xor2 ∧ h_xor3 ∧ h_xor4)

-- #eval! theta_c (p:=p_babybear) default |>.operations.local_length
-- #eval! theta_c (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState (Var Outputs (F p)) where
  main := theta_c
  local_length _ := 160
  output _ i0 := #v[
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 152)
  ]

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds
  simp only [circuit_norm] at h_input
  dsimp only [assumptions] at state_norm
  dsimp only [circuit_norm, theta_c, Xor.circuit] at h_holds
  simp only [circuit_norm, subcircuit_norm] at h_holds
  dsimp only [Xor.assumptions, Xor.spec] at h_holds
  simp [add_assoc, and_assoc] at h_holds

  -- TODO: we desperately need some abstraction here
  have s0 : eval env (state_var[0]) = state[0] := by rw [←h_input, Vector.getElem_map]
  have s1 : eval env (state_var[1]) = state[1] := by rw [←h_input, Vector.getElem_map]
  have s2 : eval env (state_var[2]) = state[2] := by rw [←h_input, Vector.getElem_map]
  have s3 : eval env (state_var[@Fin.val 25 3]) = state[3] := by rw [←h_input, Vector.getElem_map]; rfl
  have s4 : eval env (state_var[@Fin.val 25 4]) = state[4] := by rw [←h_input, Vector.getElem_map]; rfl
  have s5 : eval env (state_var[@Fin.val 25 5]) = state[5] := by rw [←h_input, Vector.getElem_map]; rfl
  have s6 : eval env (state_var[@Fin.val 25 6]) = state[6] := by rw [←h_input, Vector.getElem_map]; rfl
  have s7 : eval env (state_var[@Fin.val 25 7]) = state[7] := by rw [←h_input, Vector.getElem_map]; rfl
  have s8 : eval env (state_var[@Fin.val 25 8]) = state[8] := by rw [←h_input, Vector.getElem_map]; rfl
  have s9 : eval env (state_var[@Fin.val 25 9]) = state[9] := by rw [←h_input, Vector.getElem_map]; rfl
  have s10 : eval env (state_var[@Fin.val 25 10]) = state[10] := by rw [←h_input, Vector.getElem_map]; rfl
  have s11 : eval env (state_var[@Fin.val 25 11]) = state[11] := by rw [←h_input, Vector.getElem_map]; rfl
  have s12 : eval env (state_var[@Fin.val 25 12]) = state[12] := by rw [←h_input, Vector.getElem_map]; rfl
  have s13 : eval env (state_var[@Fin.val 25 13]) = state[13] := by rw [←h_input, Vector.getElem_map]; rfl
  have s14 : eval env (state_var[@Fin.val 25 14]) = state[14] := by rw [←h_input, Vector.getElem_map]; rfl
  have s15 : eval env (state_var[@Fin.val 25 15]) = state[15] := by rw [←h_input, Vector.getElem_map]; rfl
  have s16 : eval env (state_var[@Fin.val 25 16]) = state[16] := by rw [←h_input, Vector.getElem_map]; rfl
  have s17 : eval env (state_var[@Fin.val 25 17]) = state[17] := by rw [←h_input, Vector.getElem_map]; rfl
  have s18 : eval env (state_var[@Fin.val 25 18]) = state[18] := by rw [←h_input, Vector.getElem_map]; rfl
  have s19 : eval env (state_var[@Fin.val 25 19]) = state[19] := by rw [←h_input, Vector.getElem_map]; rfl
  have s20 : eval env (state_var[@Fin.val 25 20]) = state[20] := by rw [←h_input, Vector.getElem_map]; rfl
  have s21 : eval env (state_var[@Fin.val 25 21]) = state[21] := by rw [←h_input, Vector.getElem_map]; rfl
  have s22 : eval env (state_var[@Fin.val 25 22]) = state[22] := by rw [←h_input, Vector.getElem_map]; rfl
  have s23 : eval env (state_var[@Fin.val 25 23]) = state[23] := by rw [←h_input, Vector.getElem_map]; rfl
  have s24 : eval env (state_var[@Fin.val 25 24]) = state[24] := by rw [←h_input, Vector.getElem_map]; rfl
  rw [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13,
      s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24] at h_holds
  clear s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17
    s18 s19 s20 s21 s22 s23 s24

  simp [circuit_norm, spec]

  -- TODO ideally we would do this proof once and not 5 times!
  -- out0 spec
  set out0 := eval env <| var_from_offset U64 (i0 + 24)
  obtain ⟨ h00, h01, h02, h03, h_holds ⟩ := h_holds
  obtain ⟨ xor00, norm00 ⟩ := h00 (state_norm 0) (state_norm 1)
  obtain ⟨ xor01, norm01 ⟩ := h01 norm00 (state_norm 2)
  obtain ⟨ xor02, norm02 ⟩ := h02 norm01 (state_norm 3)
  obtain ⟨ xor0, norm0 ⟩ := h03 norm02 (state_norm 4)
  rw [xor02, xor01, xor00] at xor0
  clear h00 h01 h02 h03 norm00 norm01 norm02 xor00 xor01 xor02

  -- out1 spec
  set out1 := eval env <| var_from_offset U64 (i0 + 56)
  obtain ⟨ h10, h11, h12, h13, h_holds ⟩ := h_holds
  obtain ⟨ xor10, norm10 ⟩ := h10 (state_norm 5) (state_norm 6)
  obtain ⟨ xor11, norm11 ⟩ := h11 norm10 (state_norm 7)
  obtain ⟨ xor12, norm12 ⟩ := h12 norm11 (state_norm 8)
  obtain ⟨ xor1, norm1 ⟩ := h13 norm12 (state_norm 9)
  rw [xor12, xor11, xor10] at xor1
  clear h10 h11 h12 h13 norm10 norm11 norm12 xor10 xor11 xor12

  -- out2 spec
  set out2 := eval env <| var_from_offset U64 (i0 + 88)
  obtain ⟨ h20, h21, h22, h23, h_holds ⟩ := h_holds
  obtain ⟨ xor20, norm20 ⟩ := h20 (state_norm 10) (state_norm 11)
  obtain ⟨ xor21, norm21 ⟩ := h21 norm20 (state_norm 12)
  obtain ⟨ xor22, norm22 ⟩ := h22 norm21 (state_norm 13)
  obtain ⟨ xor2, norm2 ⟩ := h23 norm22 (state_norm 14)
  rw [xor22, xor21, xor20] at xor2
  clear h20 h21 h22 h23 norm20 norm21 norm22 xor20 xor21 xor22

  -- out3 spec
  set out3 := eval env <| var_from_offset U64 (i0 + 120)
  obtain ⟨ h30, h31, h32, h33, h_holds ⟩ := h_holds
  obtain ⟨ xor30, norm30 ⟩ := h30 (state_norm 15) (state_norm 16)
  obtain ⟨ xor31, norm31 ⟩ := h31 norm30 (state_norm 17)
  obtain ⟨ xor32, norm32 ⟩ := h32 norm31 (state_norm 18)
  obtain ⟨ xor3, norm3 ⟩ := h33 norm32 (state_norm 19)
  rw [xor32, xor31, xor30] at xor3
  clear h30 h31 h32 h33 norm30 norm31 norm32 xor30 xor31 xor32

  -- out4 spec
  set out4 := eval env <| var_from_offset U64 (i0 + 152)
  obtain ⟨ h40, h41, h42, h43 ⟩ := h_holds
  obtain ⟨ xor40, norm40 ⟩ := h40 (state_norm 20) (state_norm 21)
  obtain ⟨ xor41, norm41 ⟩ := h41 norm40 (state_norm 22)
  obtain ⟨ xor42, norm42 ⟩ := h42 norm41 (state_norm 23)
  obtain ⟨ xor4, norm4 ⟩ := h43 norm42 (state_norm 24)
  rw [xor42, xor41, xor40] at xor4
  clear h40 h41 h42 h43 norm40 norm41 norm42 xor40 xor41 xor42

  exact ⟨
    ⟨ norm0, norm1, norm2, norm3, norm4 ⟩,
    ⟨ xor0, xor1, xor2, xor3, xor4 ⟩
  ⟩

theorem completeness : Completeness (F p) Outputs assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm] at h_input
  dsimp only [circuit_norm, theta_c, Xor.circuit]
  simp only [circuit_norm, subcircuit_norm]
  dsimp only [Xor.assumptions, Xor.spec]
  simp [add_assoc]
  sorry

def circuit : FormalCircuit (F p) KeccakState Outputs where
  main := theta_c
  assumptions
  spec
  soundness
  completeness
end Gadgets.Keccak.ThetaC
