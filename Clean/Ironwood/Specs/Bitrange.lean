module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Clean.Circuit.WitnessIRSugar
public import CompElliptic.Fields.Pasta

@[expose] public section

open CompElliptic.Fields.Pasta (Fp)

/-!
# Bit ranges of a natural number

`bitrange n start len` is the value of the `len`-bit field of `n` starting at bit
`start` (i.e. bits `start .. start+len-1`). It is the scalar atom underlying every
contiguous bit-slice that shows up in the canonicity proofs (and `Sinsemilla.chunksOf`
is just a list of `K`-aligned, `K`-wide `bitrange`s).
-/

namespace Zcash.Circuits.Specs

/-- The Sinsemilla / lookup-range-check word width: bits per chunk (`= 10`).
Shared by `Sinsemilla.chunksOf` and `LookupRangeCheck`. -/
def K : ℕ := 10

/-- The value of the `len`-bit field of `n` starting at bit `start`. -/
def bitrange (n start len : ℕ) : ℕ := n / 2 ^ start % 2 ^ len

@[simp] theorem bitrange_lt (n start len : ℕ) : bitrange n start len < 2 ^ len :=
  Nat.mod_lt _ (by positivity)

/-- A number that already fits in `len` bits is its own low-`len`-bit field. -/
theorem bitrange_eq_of_lt {n len : ℕ} (h : n < 2 ^ len) : bitrange n 0 len = n := by
  simp only [bitrange, pow_zero, Nat.div_one, Nat.mod_eq_of_lt h]

/-- The low-bits field starting at `0` is just `n mod 2^len`. -/
theorem bitrange_zero (n len : ℕ) : bitrange n 0 len = n % 2 ^ len := by
  simp [bitrange]

/-- When the upper tail of `n` (from bit `start` up) already fits in `len` bits, the field
is that whole tail, i.e. the `%` is a no-op. -/
theorem bitrange_eq_div_of_lt {n start len : ℕ} (h : n / 2 ^ start < 2 ^ len) :
    bitrange n start len = n / 2 ^ start :=
  Nat.mod_eq_of_lt h

/-- Slicing after a shift is slicing at the shifted offset. -/
theorem bitrange_div (n s t len : ℕ) :
    bitrange (n / 2 ^ s) t len = bitrange n (s + t) len := by
  simp only [bitrange, Nat.div_div_eq_div_mul, ← pow_add]

/-- Adjacent fields concatenate: the low `a+b` bits split into the low `a` bits plus the
next `b` bits scaled by `2^a`. -/
theorem bitrange_add (n start a b : ℕ) :
    bitrange n start (a + b) =
      bitrange n start a + 2 ^ a * bitrange n (start + a) b := by
  have hb : bitrange n (start + a) b = n / 2 ^ start / 2 ^ a % 2 ^ b := by
    simp only [bitrange, Nat.div_div_eq_div_mul, ← pow_add]
  simp only [bitrange] at *
  rw [hb]
  set m := n / 2 ^ start with hm
  have h1 : m % 2 ^ (a + b) / 2 ^ a = m / 2 ^ a % 2 ^ b := by
    rw [pow_add, Nat.mod_mul_right_div_self]
  have h2 : m % 2 ^ (a + b) % 2 ^ a = m % 2 ^ a :=
    Nat.mod_mod_of_dvd m (pow_dvd_pow 2 (Nat.le_add_right a b))
  rw [← Nat.div_add_mod (m % 2 ^ (a + b)) (2 ^ a), h1, h2]
  ring

/-- A field is unchanged by truncating the input above its top bit. -/
theorem bitrange_mod {n s len m : ℕ} (h : s + len ≤ m) :
    bitrange (n % 2 ^ m) s len = bitrange n s len := by
  have hs : s ≤ m := le_trans (Nat.le_add_right s len) h
  have hlen : len ≤ m - s := by omega
  simp only [bitrange]
  rw [show (2 : ℕ) ^ m = 2 ^ s * 2 ^ (m - s) by rw [← pow_add, Nat.add_sub_cancel' hs],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hlen)]

theorem cast_bitrange_val {start numBits : ℕ} (hNumBits : numBits ≤ 254) (value : Fp) :
    (((bitrange value.val start numBits : ℕ) : Fp)).val = bitrange value.val start numBits :=
  ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _)
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hNumBits)
      (by norm_num [Fp])))

/-! ## Bridging lemmas for `Fp`, reused across every witness-generator/proof pair that
touches `FiniteField.fromNat`/`FiniteField.val` on the concrete Orchard field.

`FiniteField.fromNat_F`/`FiniteField.val_F` (in `Clean.Utils.FiniteField`) already state
these facts, but generically over `F p` for an abstract `p` — and `Fp` (defined as
`CompElliptic.Fields.Pasta.PallasBaseField`, not literally `F p`) doesn't unify with that
pattern at `simp`'s discrimination-tree matching, even though it does via `rw`/plain term
elaboration. Restating them at the concrete type here, once, lets every downstream site
reference one named lemma instead of re-deriving a local bridging `have` each time.

Deliberately *not* tagged `@[simp, circuit_norm]`: `circuit_norm` is used pervasively
across the whole Orchard proof base, and making these fire unconditionally there shifted
intermediate goal states in unrelated, already-working proofs elsewhere (an early `simp`
closing a goal that a later tactic still expected to be open). List them explicitly at
each call site instead. -/

theorem fromNat_Fp (n : ℕ) :
    (FiniteField.fromNat n : Fp) = (n : Fp) := FiniteField.fromNat_F n

theorem val_Fp (x : Fp) :
    FiniteField.val x = ZMod.val x := FiniteField.val_F x

/-- The raw `n / 2^s % 2^l` shape (definitionally `bitrange`) folded into the named form,
for proofs that bridge a division/mod chain into `bitrange`. -/
theorem bitrange_eq (n s l : ℕ) : n / 2 ^ s % 2 ^ l = bitrange n s l := rfl

end Zcash.Circuits.Specs

/-! ## The witness-IR counterpart of `bitrange`

`Witgen.FExprOver.bitrange x start len` computes, in the field, the bit slice
`Zcash.Circuits.Specs.bitrange (val x) start len` from the bits of `x`. Generic over the
variable atom `V`, like the witness IR. -/

namespace Witgen

variable {V Env : Type}

/-- Bits `start .. start+len-1` of `val x` as a field element: `Σ bit (start + k) · 2^k`. -/
def FExprOver.bitrange (x : FExprOver Fp V) (start : ℕ) : ℕ → FExprOver Fp V
  | 0 => .const 0
  | k + 1 => .add (x.bitrange start k) (.ite (.bit x (start + k)) (.const (2 ^ k)) (.const 0))

@[simp, circuit_norm]
theorem FExprOver.eval_bitrange [WitgenEnv Fp Env V] (ctx : CtxOver Fp Env)
    (x : FExprOver Fp V) (start len : ℕ) :
    (x.bitrange start len).eval ctx
      = ((Zcash.Circuits.Specs.bitrange (x.eval ctx).val start len : ℕ) : Fp) := by
  induction len with
  | zero => simp [FExprOver.bitrange, FExprOver.eval, Zcash.Circuits.Specs.bitrange, Nat.mod_one]
  | succ k ih =>
    set y := (x.eval ctx).val / 2 ^ start
    have hbit : (FiniteField.val (x.eval ctx)).testBit (start + k)
        = decide (y / 2 ^ k % 2 = 1) := by
      rw [Zcash.Circuits.Specs.val_Fp, Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul,
        ← pow_add]
    have hsplit : y % 2 ^ (k + 1) = y % 2 ^ k + 2 ^ k * (y / 2 ^ k % 2) := by
      rw [pow_succ, Nat.mod_mul]
    simp only [FExprOver.bitrange, FExprOver.eval, BExprOver.eval, ih, hbit,
      Zcash.Circuits.Specs.bitrange]
    rw [hsplit]
    rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ k) with h | h <;> simp [h] <;> rfl

end Witgen
