import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Utils.Primes
import Clean.Utils.Bits

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# 32-bit Bitwise Operations for SHA-256

All operations work on `fields 32`, where each field element represents one bit (boolean).
Bit 0 is the least-significant bit (LSB-first convention).

No lookup tables are used; all operations are expressed as R1CS constraints.
-/

/-- State: 8 boolean 32-bit words. -/
abbrev SHA256State := ProvableVector (fields 32) 8

/-- Block: 16 boolean 32-bit words. -/
abbrev SHA256Block := ProvableVector (fields 32) 16

/-- Message schedule: 64 boolean 32-bit words. -/
abbrev SHA256Schedule := ProvableVector (fields 32) 64

/-- Interpret a bit vector as a natural number (LSB at index 0). -/
def valueBits (bits : Vector (F p) 32) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => bits[i].val * 2^i.val

/-- All bits are boolean (0 or 1). -/
def Normalized (w : Vector (F p) 32) : Prop :=
  ∀ i : Fin 32, w[i] = 0 ∨ w[i] = 1

/-- The linear combination of bits as an expression: Σ bits[i] · 2^i (LSB first) -/
abbrev fromBitsExpr (bits : Var (fields 32) (F p)) : Expression (F p) :=
  Utils.Bits.fieldFromBitsExpr bits

/-- A constant 32-bit word from a natural number (LSB-first bit decomposition). -/
def constWord32 (n : ℕ) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) => ((n / 2^i.val % 2 : ℕ) : F p)

/-!
## Pure combinators (no witnesses, no constraints)
-/

/-- Bitwise NOT: maps each bit a[i] ↦ 1 − a[i]. -/
def not32 (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  a.map fun ai => (1 : Expression (F p)) - ai

/-- Rotate right by `k` bits (mod 32): z[i] = a[(i + k) mod 32]. -/
def rotr32 (k : Fin 32) (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  a.rotate k

/-- Shift right by `k` bits: z[i] = a[i + k] if i + k < 32, else 0. -/
def shr32 (k : Fin 32) (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) =>
    if h : i.val + k.val < 32
    then a[i.val + k.val]'h
    else (0 : Expression (F p))

end Gadgets.SHA256
end
