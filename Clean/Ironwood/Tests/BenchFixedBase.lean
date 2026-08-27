import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Basic
-- Benchmark: kernel-decide cost of the FixedBase checker primitives (Pallas-size).

def P : ℕ := 28948022309329048855892746252171976963363056481941560715954676764349967630337

/-- Fuel-based binary modular pow (kernel-friendly structural recursion). -/
def powModAux (p a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % p
  | fuel + 1, e =>
    if e = 0 then 1 % p
    else
      let h := powModAux p a fuel (e / 2)
      let h2 := h * h % p
      if e % 2 = 1 then h2 * a % p else h2

def powMod (p a e : ℕ) : ℕ := powModAux p a 256 e

-- ONE Euler check (5 is a non-square in Pallas base: 5^((P-1)/2) = P - 1)
set_option maxRecDepth 4000 in
example : powMod P 5 ((P - 1) / 2) = P - 1 := by decide +kernel

/-- A mulmod chain: fold `x := x * x % p + i % p` n times — proxy for witnessed
addition-check throughput (each step ≈ 2 GMP mulmods + control). -/
def chainAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => chainAux p n ((x * x % p + x) % p)

set_option maxRecDepth 10000 in
-- 3000 steps ≈ one base's full witnessed table check volume
example : chainAux P 3000 5 % P = chainAux P 3000 5 % P := by decide +kernel

/-- Bulk Euler proxy: 40 exponentiations in one decide. -/
def eulerBulk (p : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => (powMod p (5 + n) ((p - 1) / 2) != 0) && eulerBulk p n

set_option maxRecDepth 100000 in
example : eulerBulk P 40 = true := by decide +kernel

-- rfl route: kernel Nat-literal reduction, no Decidable wrapper
set_option maxRecDepth 4000 in
example : powMod P 5 ((P - 1) / 2) = P - 1 := rfl

-- ZMod-stated variants of the SAME algorithms (powModZ / chainZ over `ZMod P` with
-- OfNat literals) were tried here and TIMED OUT (>10 min vs 3 s for the file above):
-- although `ZMod P = Fin P` bottoms out in the same GMP Nat primitives, `rfl`-reduction
-- through the numeral/instance layer (`ZMod P` unfolding per op, `OfNat`/cast towers)
-- is >200x slower in practice. Hence the checker states its equations over Nat
-- (`.val`-level) and bridges to the ZMod facts by once-proven cast lemmas.
