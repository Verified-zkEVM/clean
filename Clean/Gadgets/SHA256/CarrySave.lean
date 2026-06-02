import Clean.Gadgets.SHA256.BitwiseOps
import Mathlib.Tactic.LinearCombination

/-!
# Single-constraint bit primitives for SHA-256 (pure R1CS)

The four SHA-256 Σ/σ functions are 3-input XORs and `Maj` is a 3-input majority.  Each output
bit is a degree-≤3 boolean function of three boolean inputs, and a *naive* arithmetization
(carry-save or two-step) spends two R1CS rows per bit (a witnessed value plus a booleanity
check).  Both functions instead admit a **single** R1CS constraint per output bit: directly
witness the output `o` and impose one quadratic constraint `L₁(o,a,b,c) · L₂(a,b,c) = L₃(a,b,c)`
that is linear in `o` with a multiplier `L₂` that never vanishes on the boolean cube, so `o` is
*uniquely* determined and an 8-way case analysis fixes its value.

* 3-input XOR (`xor3raw`): `(o + 2a + 2b + 7c)(a + b − 4c + 1) = 6a + 6b − 24c`.
* 3-input majority (`maj3raw`): `(o + a + b − 9c + 3)(a + b + 6c − 4) = −12`.

Both multipliers take only the values `±1, ±2, ±3, ±4` on the cube, so soundness needs char
`∉ {2, 3}`, supplied by `p > 2^35` (the bound the surrounding SHA-256 stack already carries for
`AddMod32`).  The majority constraint is necessarily *asymmetric* in `(a, b, c)` — an exhaustive
search shows no symmetric single-constraint encoding of `maj` exists.  Coefficients were found by
SMT search and the ideal-membership cofactors for the soundness/completeness `linear_combination`s
were computed with a Gröbner-basis lift.
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

/-!
## Single-constraint 3-input majority

The 3-input majority admits a *single* R1CS constraint per output bit — half the carry-save
cost — by directly witnessing the output `o` (the majority) and imposing

  `(o + a + b − 9c + 3) · (a + b + 6c − 4) = −12`.

This constraint is linear in `o` with multiplier `a + b + 6c − 4`, which is nonzero for every
boolean `(a, b, c)` (its values are `±2, ±3, ±4`), so `o` is *uniquely* determined; an 8-way case
analysis over `a, b, c ∈ {0, 1}` shows that unique root is exactly `maj(a, b, c)`.  Unlike the
carry-save form there is no separate booleanity row: the single constraint already pins `o` to the
(boolean) majority value.  An SMT search establishes that no *symmetric* single-constraint
encoding exists, so the asymmetric `−9c`/`6c` coefficients are unavoidable.  Soundness needs char
`∉ {2, 3}`, supplied by `p > 2^35`.
-/

/-- From the single Maj constraint, the witnessed output `o` equals the majority
    `maj(a, b, c)` (in arithmetic form).  Soundness of the single-constraint encoding. -/
theorem maj3_unique {a b c o : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c)
    (h : (o + a + b - 9 * c + 3) * (a + b + 6 * c - 4) + 12 = 0) :
    o = a * b + c * (a + b - 2 * (a * b)) := by
  have ha' : a * (a - 1) = 0 := by rcases ha with h | h <;> rw [h] <;> ring
  have hb' : b * (b - 1) = 0 := by rcases hb with h | h <;> rw [h] <;> ring
  have hc' : c * (c - 1) = 0 := by rcases hc with h | h <;> rw [h] <;> ring
  -- The constraint factors as `(o − maj) · (a + b + 6c − 4)` modulo the boolean relations.
  have key : (o - (a * b + c * (a + b - 2 * (a * b)))) * (a + b + 6 * c - 4) = 0 := by
    linear_combination h - (-2 * b * c + b + c + 1) * ha'
      - (-2 * a * c + a + c + 1) * hb' - (-12 * a * b + 6 * a + 6 * b - 54) * hc'
  -- The multiplier is nonzero (its boolean values are `±2, ±3, ±4`).
  have hp : 2 ^ 35 < p := Fact.out
  have hval : ∀ k : ℕ, 0 < k → k < p → ((k : ℕ) : F p) ≠ 0 := by
    intro k hk hkp hcon
    have := congrArg ZMod.val hcon
    rw [ZMod.val_natCast_of_lt hkp, ZMod.val_zero] at this; omega
  have h2 : (2 : F p) ≠ 0 := by have := hval 2 (by norm_num) (by omega); simpa using this
  have h3 : (3 : F p) ≠ 0 := by have := hval 3 (by norm_num) (by omega); simpa using this
  have h4 : (4 : F p) ≠ 0 := by have := hval 4 (by norm_num) (by omega); simpa using this
  have hM : (a + b + 6 * c - 4 : F p) ≠ 0 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      intro hcon <;>
      first
        | exact h2 (by linear_combination hcon)
        | exact h2 (by linear_combination -hcon)
        | exact h3 (by linear_combination hcon)
        | exact h3 (by linear_combination -hcon)
        | exact h4 (by linear_combination hcon)
        | exact h4 (by linear_combination -hcon)
  rcases mul_eq_zero.mp key with h1 | h1
  · linear_combination h1
  · exact absurd h1 hM

omit [Fact (p > 2^35)] in
/-- The majority value satisfies the single Maj constraint.  Completeness of the encoding. -/
theorem maj3_complete {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    ((a * b + c * (a + b - 2 * (a * b))) + a + b - 9 * c + 3) * (a + b + 6 * c - 4) + 12 = 0 := by
  have ha' : a * (a - 1) = 0 := by rcases ha with h | h <;> rw [h] <;> ring
  have hb' : b * (b - 1) = 0 := by rcases hb with h | h <;> rw [h] <;> ring
  have hc' : c * (c - 1) = 0 := by rcases hc with h | h <;> rw [h] <;> ring
  linear_combination (-2 * b * c + b + c + 1) * ha'
    + (-2 * a * c + a + c + 1) * hb' + (-12 * a * b + 6 * a + 6 * b - 54) * hc'

/-- 3-input majority via a single R1CS constraint per bit.  Witnesses the output bit `o[i]`
    (the majority of the inputs) and asserts `(o + a + b − 9c + 3)(a + b + 6c − 4) = −12`.
    Cost: 32 witnesses, 32 constraints (half the carry-save constraint count). -/
def maj3raw (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let o ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      let ai := env a[i]; let bi := env b[i]; let ci := env c[i]
      ai * bi + ci * (ai + bi - 2 * (ai * bi))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero ((o[i] + a[i] + b[i] - 9 * c[i] + 3) * (a[i] + b[i] + 6 * c[i] - 4) + 12)
  return o

/-!
## Single-constraint 3-input XOR

The 3-input XOR (the four SHA-256 Σ/σ functions) admits a *single* R1CS constraint per output
bit — half the carry-save cost — by directly witnessing the output `o` and imposing

  `(o + 2a + 2b + 7c) · (a + b − 4c + 1) = 6a + 6b − 24c`.

This constraint is linear in `o` with multiplier `a + b − 4c + 1`, which is nonzero for every
boolean `(a, b, c)` (its values are `±1, ±2, ±3`), so `o` is *uniquely* determined; an 8-way case
analysis over `a, b, c ∈ {0, 1}` shows that unique root is exactly `a XOR b XOR c`.  (The
coefficients were found by a search over small-integer R1CS encodings: a quadratic surface through
the eight `(a, b, c, parity)` points whose `o`-multiplier never vanishes.  The 3-input *majority*
admits the analogous single-constraint encoding `maj3raw` above.)  Soundness needs char `∉ {2, 3}`,
supplied by `p > 2^35`.
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
