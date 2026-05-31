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

/-!
## Single-constraint 3-input XOR

The 3-input XOR (the four SHA-256 Σ/σ functions) admits a *single* R1CS constraint per output
bit — half the carry-save cost — by directly witnessing the output `o` and imposing

  `(o + 2a + 2b + 7c) · (a + b − 4c + 1) = 6a + 6b − 24c`.

This constraint is linear in `o` with multiplier `a + b − 4c + 1`, which is nonzero for every
boolean `(a, b, c)` (its values are `±1, ±2, ±3`), so `o` is *uniquely* determined; an 8-way case
analysis over `a, b, c ∈ {0, 1}` shows that unique root is exactly `a XOR b XOR c`.  (The
coefficients were found by an exhaustive search over small-integer R1CS encodings: the only
quadratic surface through the eight `(a, b, c, parity)` points whose `o`-multiplier never vanishes.
The 3-input *majority* has no such single-constraint encoding — its residual quadratic form has full
rank — so `carrySave` above is optimal for `Maj`.)  Soundness needs char `∉ {2, 3}`, supplied by
`p > 2^35`.
-/

/-- From the single XOR constraint, the witnessed output `o` equals the nested XOR
    `(a XOR b) XOR c` (in arithmetic form).  Soundness of the single-constraint encoding. -/
theorem xor3_unique {a b c o : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c)
    (h : (o + 2 * a + 2 * b + 7 * c) * (a + b - 4 * c + 1) - (6 * a + 6 * b - 24 * c) = 0) :
    o = a + b - 2 * a * b + c - 2 * (a + b - 2 * a * b) * c := by
  have ha' : a * (a - 1) = 0 := by rcases ha with h | h <;> rw [h] <;> ring
  have hb' : b * (b - 1) = 0 := by rcases hb with h | h <;> rw [h] <;> ring
  have hc' : c * (c - 1) = 0 := by rcases hc with h | h <;> rw [h] <;> ring
  -- The constraint factors as `(o − parity) · (a + b − 4c + 1)` modulo the boolean relations.
  have key : (o - (a + b - 2 * a * b + c - 2 * (a + b - 2 * a * b) * c)) * (a + b - 4 * c + 1) = 0 := by
    linear_combination h + (-4 * b * c + 2 * b + 2 * c - 3) * ha'
      + (-4 * a * c + 2 * a + 2 * c - 3) * hb' + (16 * a * b - 8 * a - 8 * b + 32) * hc'
  -- The multiplier is nonzero (its boolean values are `±1, ±2, ±3`).
  have hp : 2 ^ 35 < p := Fact.out
  have hval : ∀ k : ℕ, 0 < k → k < p → ((k : ℕ) : F p) ≠ 0 := by
    intro k hk hkp hcon
    have := congrArg ZMod.val hcon
    rw [ZMod.val_natCast_of_lt hkp, ZMod.val_zero] at this; omega
  have h2 : (2 : F p) ≠ 0 := by have := hval 2 (by norm_num) (by omega); simpa using this
  have h3 : (3 : F p) ≠ 0 := by have := hval 3 (by norm_num) (by omega); simpa using this
  have hM : (a + b - 4 * c + 1 : F p) ≠ 0 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      intro hcon <;>
      first
        | exact one_ne_zero (by linear_combination hcon)
        | exact one_ne_zero (by linear_combination -hcon)
        | exact h2 (by linear_combination hcon)
        | exact h2 (by linear_combination -hcon)
        | exact h3 (by linear_combination hcon)
        | exact h3 (by linear_combination -hcon)
  rcases mul_eq_zero.mp key with h1 | h1
  · linear_combination h1
  · exact absurd h1 hM

omit [Fact (p > 2^35)] in
/-- The nested-XOR value satisfies the single XOR constraint.  Completeness of the encoding. -/
theorem xor3_complete {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    ((a + b - 2 * a * b + c - 2 * (a + b - 2 * a * b) * c) + 2 * a + 2 * b + 7 * c)
        * (a + b - 4 * c + 1) - (6 * a + 6 * b - 24 * c) = 0 := by
  have ha' : a * (a - 1) = 0 := by rcases ha with h | h <;> rw [h] <;> ring
  have hb' : b * (b - 1) = 0 := by rcases hb with h | h <;> rw [h] <;> ring
  have hc' : c * (c - 1) = 0 := by rcases hc with h | h <;> rw [h] <;> ring
  linear_combination (4 * b * c - 2 * b - 2 * c + 3) * ha'
    + (4 * a * c - 2 * a - 2 * c + 3) * hb' + (-16 * a * b + 8 * a + 8 * b - 32) * hc'

/-- 3-input XOR via a single R1CS constraint per bit.  Witnesses the output bit `o[i]`
    (the nested XOR of the inputs) and asserts `(o + 2a + 2b + 7c)(a + b − 4c + 1) = 6a + 6b − 24c`.
    Cost: 32 witnesses, 32 constraints (half the carry-save constraint count). -/
def xor3raw (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let o ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      let ai := env a[i]; let bi := env b[i]; let ci := env c[i]
      ai + bi - 2 * ai * bi + ci - 2 * (ai + bi - 2 * ai * bi) * ci
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero ((o[i] + 2 * a[i] + 2 * b[i] + 7 * c[i]) * (a[i] + b[i] - 4 * c[i] + 1)
      - (6 * a[i] + 6 * b[i] - 24 * c[i]))
  return o

end Gadgets.SHA256
end
