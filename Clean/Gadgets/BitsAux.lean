import Clean.Circuit.Loops
import Clean.Gadgets.Boolean
import Batteries.Data.Nat.Lemmas

variable {p : ℕ} [prime: Fact p.Prime]

def to_bits (n : ℕ) (x : ZMod p) : Vector Bool n :=
  .ofFn fun i => x.val.testBit i

def from_bits {n : ℕ} (x : Vector Bool n) : ZMod p :=
  Nat.ofBits fun i => x[i.val]

theorem to_bits_from_bits {n} {x : ZMod p} (hx : x.val < 2^n) :
    from_bits (to_bits n x) = x := by
  apply ZMod.val_injective
  simp only [to_bits, from_bits, Vector.getElem_ofFn, ZMod.val_natCast]

  have : .ofBits (fun (i : Fin n) => x.val.testBit i) = x.val % 2^n := by
    apply Nat.eq_of_testBit_eq
    simp [Nat.testBit_ofBits, Nat.testBit_mod_two_pow]

  rw [this, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (ZMod.val_lt x)]

theorem from_bits_to_bits {n} {x : Vector Bool n} (hp : p > 2^n) :
    to_bits n (from_bits (p:=p) x) = x := by
  apply Vector.ext
  intro j (hj : j < n)
  simp only [to_bits, from_bits, Vector.getElem_ofFn, ZMod.val_natCast]
  let x' := Nat.ofBits fun (i : Fin n) => x[i.val]
  show (x' % p).testBit j = x[j]

  have lt_pow : x' < 2^n := Nat.ofBits_lt_two_pow _
  have lt_p : x' < p := by linarith
  rw [Nat.mod_eq_of_lt lt_p, Nat.testBit_ofBits_lt _ _ hj]
