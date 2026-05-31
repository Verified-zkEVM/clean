import Clean.Gadgets.SHA256.BitwiseOps
import Mathlib.Tactic.LinearCombination

/-!
# Carry-save primitives for SHA-256 (pure R1CS)

The full-adder identity for bits says, for `a, b, c ∈ {0, 1}`,

  `a + b + c = (a XOR b XOR c) + 2 · maj(a, b, c)`

i.e. the parity is the low bit of the 3-bit sum and the majority is the carry.  This lets us
compute a 3-input XOR (the four SHA-256 Σ/σ functions) or a majority with a *single* witnessed
carry bit per output bit, instead of the two witnessed bits a naive `xor32`/`maj32` uses.

Concretely, witness one bit `q` per position and impose the two boolean constraints

  `q · (q − 1) = 0`   and   `(a + b + c − 2·q) · (a + b + c − 2·q − 1) = 0`.

These two constraints pin `q = maj(a,b,c)` and `a + b + c − 2·q = a XOR b XOR c` uniquely
(`bool_carry_unique` below).  Dropping the carry-bool constraint is unsound: a prover could
pick `q = 1/2 ∈ F p`.  Soundness needs the field characteristic to be `∉ {2, 3}`, supplied here
by `p > 2^35` (the bound the surrounding SHA-256 stack already carries for `AddMod32`).
-/

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Gadgets.SHA256

/-- The boolean majority expression for three bits: `maj = a·b + c·(a + b − 2·a·b)`. -/
theorem maj_is_bool {α : Type*} [CommRing α] {a b c : α}
    (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    IsBool (a * b + c * (a + b - 2 * (a * b))) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    simp [ha, hb, hc] <;> norm_num <;> first | exact IsBool.zero | exact IsBool.one

/-- `a + b + c − 2·maj(a,b,c)` is the parity `a XOR b XOR c`, hence boolean. -/
theorem parity_is_bool {α : Type*} [CommRing α] {a b c : α}
    (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    IsBool (a + b + c - 2 * (a * b + c * (a + b - 2 * (a * b)))) := by
  have h : a + b + c - 2 * (a * b + c * (a + b - 2 * (a * b)))
      = (a + b - 2 * a * b) + c - 2 * (a + b - 2 * a * b) * c := by ring
  rw [h]
  exact IsBool.xor_is_bool (IsBool.xor_is_bool ha hb) hc

/-- Uniqueness of the carry: if `x` and `y` are boolean and `s − 2·x`, `s − 2·y` are both
    boolean, then `x = y`.  (Uses char `∉ {2, 3}`, from `p > 2^35`.) -/
theorem bool_carry_unique {x y s : F p}
    (hx : IsBool x) (hy : IsBool y)
    (hsx : IsBool (s - 2 * x)) (hsy : IsBool (s - 2 * y)) : x = y := by
  have hp : 2 ^ 35 < p := Fact.out
  have hval : ∀ k : ℕ, 0 < k → k < p → ((k : ℕ) : F p) ≠ 0 := by
    intro k hk hkp h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hkp, ZMod.val_zero] at this
    omega
  have h1 : (1 : F p) ≠ 0 := one_ne_zero
  have h2 : (2 : F p) ≠ 0 := by have := hval 2 (by norm_num) (by omega); simpa using this
  have h3 : (3 : F p) ≠ 0 := by have := hval 3 (by norm_num) (by omega); simpa using this
  have close : (s - 2 * (0 : F p) = 0 ∨ s - 2 * (0 : F p) = 1) →
      (s - 2 * (1 : F p) = 0 ∨ s - 2 * (1 : F p) = 1) → False := by
    intro ha hb
    have key : (2 : F p) = (s - 2 * (0 : F p)) - (s - 2 * (1 : F p)) := by ring
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at key
    · exact h2 (by linear_combination key)
    · exact h3 (by linear_combination key)
    · exact h1 (by linear_combination key)
    · exact h2 (by linear_combination key)
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · rfl
    · exact (close hsx hsy).elim
  · rcases hy with rfl | rfl
    · exact (close hsy hsx).elim
    · rfl

/-- From the two carry-save boolean constraints, the witnessed carry equals the majority. -/
theorem carry_eq_maj {a b c q : F p}
    (ha : IsBool a) (hb : IsBool b) (hc : IsBool c)
    (hq : IsBool q) (hout : IsBool (a + b + c - 2 * q)) :
    q = a * b + c * (a + b - 2 * (a * b)) :=
  bool_carry_unique hq (maj_is_bool ha hb hc) hout (parity_is_bool ha hb hc)

/-- Shared carry-save witness + constraints for three bit-vectors `a, b, c`.

    Witnesses one carry bit `q[i] = maj(a[i], b[i], c[i])` per position, and asserts both
    `q[i]` and the parity `a[i] + b[i] + c[i] − 2·q[i]` are boolean.  Returns the carry vector
    `q` (the majority); callers wanting the XOR use `a + b + c − 2·q` (a free linear
    combination, not witnessed). Cost: 32 witnesses, 64 constraints. -/
def carrySave (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let q ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      let ai := env a[i]; let bi := env b[i]; let ci := env c[i]
      ai * bi + ci * (ai + bi - 2 * (ai * bi))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (q[i] * (q[i] - 1))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero ((a[i] + b[i] + c[i] - 2 * q[i]) * (a[i] + b[i] + c[i] - 2 * q[i] - 1))
  return q

/-- 3-input XOR via carry save: `xor3 a b c = a + b + c − 2·maj(a,b,c)` (the parity). -/
def xor3raw (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let q ← carrySave a b c
  return Vector.ofFn fun (i : Fin 32) => a[i] + b[i] + c[i] - 2 * q[i]

end Gadgets.SHA256
end
