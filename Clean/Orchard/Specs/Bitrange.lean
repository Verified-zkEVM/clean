import Mathlib.Tactic
import Clean.Circuit.WitnessIRSugar
import Clean.Orchard.Specs.CompElliptic.Fields.Pasta

open CompElliptic.Fields.Pasta (Fp)

/-!
# Bit ranges of a natural number

`bitrange n start len` is the value of the `len`-bit field of `n` starting at bit
`start` (i.e. bits `start .. start+len-1`). It is the scalar atom underlying every
contiguous bit-slice that shows up in the canonicity proofs (and `Sinsemilla.chunksOf`
is just a list of `K`-aligned, `K`-wide `bitrange`s).
-/

namespace Orchard.Specs

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
for the rare proof that still needs to bridge a manually-written division/mod chain into
`bitrange`, rather than going through `Witgen.NExpr.bitrange`. -/
theorem bitrange_eq (n s l : ℕ) : n / 2 ^ s % 2 ^ l = bitrange n s l := rfl

end Orchard.Specs

/-! ## The witness-IR counterpart of `bitrange`

`Witgen.NExpr.bitrange n start len` is the witness-generation-IR expression for the same
bit slice `Orchard.Specs.bitrange` computes on concrete naturals — write `n.bitrange start
len` inside a witness generator (via dot notation) instead of spelling out
`n / 2 ^ start % 2 ^ len`. It's kept as an opaque named definition (not unfolded by
`circuit_norm`) specifically so that `circuit_proof_start`'s normalization produces
`Orchard.Specs.bitrange (n.eval ctx) start len` directly, in the exact shape the rest of
the canonicity proofs already expect — no manual re-folding needed. -/

namespace Witgen

/-- The `NExpr` (witness-IR) counterpart of `Orchard.Specs.bitrange`. -/
def NExpr.bitrange {F : Type} (n : NExpr F) (start len : ℕ) : NExpr F :=
  n / (2 ^ start : ℕ) % (2 ^ len : ℕ)

variable {F : Type} [FiniteField F]

@[simp, circuit_norm] theorem NExpr.eval_bitrange (ctx : Ctx F) (n : NExpr F) (start len : ℕ) :
    (n.bitrange start len).eval ctx = Orchard.Specs.bitrange (n.eval ctx) start len := rfl

end Witgen
