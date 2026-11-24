import Midnight.SHA256.Semantics.Spread
import Midnight.SHA256.Semantics.Field

/-! Integer meaning of the native limb-reconstruction gates. A limb is its
width together with its plain value, in most-significant-first order. Bounds
come from the spread lookup (or a booleanity gate for one-bit limbs). -/

namespace Midnight.SHA256.Semantics.Decomposition
open Midnight.SHA256.Semantics

abbrev Limb := Nat × Nat

def width (limbs : List Limb) : Nat := (limbs.map Prod.fst).sum
def Bounded (limbs : List Limb) : Prop := ∀ limb ∈ limbs, limb.2 < 2 ^ limb.1

def pack : List Limb → Nat
  | [] => 0
  | (_, value) :: rest => value * 2 ^ width rest + pack rest

def packSpread : List Limb → Nat
  | [] => 0
  | (_, value) :: rest => spread value * 2 ^ (2 * width rest) + packSpread rest

theorem pack_lt (limbs : List Limb) (h : Bounded limbs) : pack limbs < 2 ^ width limbs := by
  induction limbs with
  | nil => simp [pack, width]
  | cons limb rest ih =>
    have hv := h limb (by simp)
    have hr : Bounded rest := fun l hl => h l (by simp [hl])
    have hp := ih hr
    simp only [pack, width, List.map_cons, List.sum_cons, pow_add]
    change limb.2 * 2 ^ width rest + pack rest < 2 ^ limb.1 * 2 ^ width rest
    have ht : 0 < 2 ^ width rest := by positivity
    nlinarith

/-- Doubling the offsets in a reconstruction gate exactly spreads the packed word. -/
theorem spread_pack (limbs : List Limb) (h : Bounded limbs) :
    spread (pack limbs) = packSpread limbs := by
  induction limbs with
  | nil => simp [pack, packSpread]
  | cons limb rest ih =>
    have hr : Bounded rest := fun l hl => h l (by simp [hl])
    simp only [pack, packSpread]
    rw [Nat.add_comm, Nat.mul_comm limb.2, spread_concat (width rest) limb.2 (pack_lt rest hr), ih hr]
    ring

/-- The plain reconstruction field equation fixes the canonical bounded word. -/
theorem plain_gate_sound (limbs : List Limb) (bounded : Bounded limbs)
    (hwidth : width limbs ≤ 32) {word : F}
    (equation : (pack limbs : F) - word = 0) :
    word.val = pack limbs ∧ word.val < 2 ^ 32 := by
  have hp : pack limbs < 2 ^ 32 :=
    (pack_lt limbs bounded).trans_le (Nat.pow_le_pow_right (by decide) hwidth)
  have heq : word = (pack limbs : F) := (sub_eq_zero.mp equation).symm
  have hv : word.val = pack limbs := by
    rw [heq, ZMod.val_natCast_of_lt]
    exact hp.trans (by norm_num [BLS12_381.scalarFieldSize])
  exact ⟨hv, hv ▸ hp⟩

/-- The paired plain/spread reconstruction equations fix the actual spread of
the word, even for an adversarial assignment satisfying the limb lookups. -/
theorem spread_gate_sound (limbs : List Limb) (bounded : Bounded limbs)
    (hwidth : width limbs ≤ 32) {word expanded : F}
    (plainEquation : (pack limbs : F) - word = 0)
    (spreadEquation : (packSpread limbs : F) - expanded = 0) :
    word.val < 2 ^ 32 ∧ expanded.val = spread word.val := by
  obtain ⟨hw, bound⟩ := plain_gate_sound limbs bounded hwidth plainEquation
  have hs : packSpread limbs < BLS12_381.scalarFieldSize := by
    rw [← spread_pack limbs bounded, ← hw]
    exact (spread_lt bound).trans (by norm_num [BLS12_381.scalarFieldSize])
  have heq : expanded = (packSpread limbs : F) := (sub_eq_zero.mp spreadEquation).symm
  refine ⟨bound, ?_⟩
  rw [heq, ZMod.val_natCast_of_lt hs, ← spread_pack limbs bounded, hw]

def aLimbs (a b c d : Nat) : List Limb := [(10,a),(9,b),(11,c),(2,d)]
def eLimbs (a b c d e : Nat) : List Limb := [(7,a),(12,b),(2,c),(5,d),(6,e)]
def messageLimbs (a b c d e f g h : Nat) : List Limb :=
  [(12,a),(1,b),(1,c),(1,d),(7,e),(3,f),(4,g),(3,h)]
def parityLimbs (a b c : Nat) : List Limb := [(11,a),(11,b),(10,c)]

theorem pack_a (a b c d : Nat) : pack (aLimbs a b c d) =
    2 ^ 22 * a + 2 ^ 13 * b + 2 ^ 2 * c + d := by
  simp [aLimbs, pack, width]
  ring

theorem pack_e (a b c d e : Nat) : pack (eLimbs a b c d e) =
    2 ^ 25 * a + 2 ^ 13 * b + 2 ^ 11 * c + 2 ^ 6 * d + e := by
  simp [eLimbs, pack, width]
  ring

theorem pack_message (a b c d e f g h : Nat) : pack (messageLimbs a b c d e f g h) =
    2 ^ 20 * a + 2 ^ 19 * b + 2 ^ 18 * c + 2 ^ 17 * d +
      2 ^ 10 * e + 2 ^ 7 * f + 2 ^ 3 * g + h := by
  simp [messageLimbs, pack, width]
  ring

theorem pack_parity (a b c : Nat) : pack (parityLimbs a b c) =
    2 ^ 21 * a + 2 ^ 10 * b + c := by
  simp [parityLimbs, pack, width]
  ring

end Midnight.SHA256.Semantics.Decomposition
