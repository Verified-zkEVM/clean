import Clean.Gadgets.Addition32.Addition32Full
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes
import Clean.Circuit.StructuralLemmas

namespace Gadgets.Addition32
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F

instance : ProvableStruct Inputs where
  components := [U32, U32]
  toComponents := fun {x, y} => .cons x ( .cons y .nil)
  fromComponents := fun (.cons x ( .cons y .nil)) => ⟨ x, y ⟩

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let ⟨x, y⟩ := input
  let ⟨z, _⟩ ← Addition32Full.circuit {x, y, carryIn := 0}
  return z

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z: U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = (x.value + y.value) % 2^32 ∧ z.Normalized

-- def c := main (p:=p_babybear) default
-- #eval c.localLength
-- #eval c.output
instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main := main
  localLength _ := 8
  output _ i0 := ⟨var ⟨i0⟩, var ⟨i0 + 2⟩, var ⟨i0 + 4⟩, var ⟨i0 + 6⟩ ⟩

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ ⟨ x, y, carry_in ⟩ h_inputs as h
  rw [←elaborated.output_eq] -- replace explicit output with internal output, which is derived from the subcircuit
  simp_all [circuit_norm, Spec, main, Addition32Full.circuit,
  Addition32Full.Assumptions, Addition32Full.Spec, Assumptions]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ henv  ⟨ x, y, carry_in ⟩ h_inputs as
  simp_all [circuit_norm, main, Addition32Full.circuit, Addition32Full.elaborated,
  Addition32Full.Assumptions, Addition32Full.Spec, Assumptions, IsBool]

def circuit : FormalCircuit (F p) Inputs U32 where
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Addition32
lemma UInt32.ofNat.inj_on_small (a b : ℕ) (h_a : a < UInt32.size) (h_b : b < UInt32.size) :
    UInt32.ofNat a = UInt32.ofNat b →
    a = b := by
  intro h
  rw[← UInt32.toNat_ofNat_of_lt' (n := a), ← UInt32.toNat_ofNat_of_lt' (n := b), h]
  · assumption
  · assumption

lemma UInt32.ofNat.injEq_on_small (a b : ℕ) (h_a : a < UInt32.size) (h_b : b < UInt32.size) :
    UInt32.ofNat a = UInt32.ofNat b ↔
    a = b := by
  constructor
  · apply UInt32.ofNat.inj_on_small
    · assumption
    · assumption
  · intro h
    rw [h]

-- A version of Gadgets.Addition32 whose specification is written in terms of UInt32
namespace Gadgets.Addition32.UInt32
  variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

  omit [Fact (Nat.Prime p)] [Fact (p > 512)] in
  lemma U32_value_rawValueU32_bridge (a b c : U32 (F p)) (h_a : a.Normalized) :
      a.value = (b.value + c.value) % 2 ^ 32 ↔
      a.rawValueU32 = b.rawValueU32 + c.rawValueU32 := by
    simp only [U32.rawValueU32]
    constructor
    · intro h
      simp only [h]
      rw [UInt32.ofNat_mod_size]
      simp only [UInt32.ofNat_add]
    · intro h
      rw[← UInt32.toNat_ofNat_of_lt' (n := a.value), h]
      · symm
        rw[← UInt32.ofNat_eq_iff_mod_eq_toNat]
        rw[← UInt32.ofNat_add]
      · apply U32.value_lt_of_normalized; assumption

  def Spec (input: Gadgets.Addition32.Inputs (F p)) (z : U32 (F p)) :=
    let ⟨x, y⟩ := input
    z.rawValueU32 = x.rawValueU32 + y.rawValueU32 ∧ z.Normalized
  def circuit :=
    Gadgets.Addition32.circuit (p := p).weakenSpec Spec (by
      intro input output
      simp only[Gadgets.Addition32.circuit]
      simp only[Assumptions, Addition32.Spec, Spec]
      intro h_normalized h_spec
      rw [← U32_value_rawValueU32_bridge] <;> tauto
    )
  lemma circuit_Assumptions :
    circuit (p := p).Assumptions = Assumptions := by rfl
end Gadgets.Addition32.UInt32
