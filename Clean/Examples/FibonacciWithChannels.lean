/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table
-/
import Clean.Circuit
import Clean.Gadgets.Addition8.Theorems
open ByteUtils (mod256 floorDiv256)
open Gadgets.Addition8 (Theorems.soundness Theorems.completeness_bool Theorems.completeness_add)

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

instance BytesChannel : Channel (F p) field where
  name := "bytes"
  Guarantees mult x _ _ :=
    if mult = -1 then x.val < 256 else True
  Requirements mult x _ _ :=
    if mult = 1 then x.val < 256 else True

instance Add8Channel : Channel (F p) fieldTriple where
  name := "add8"
  Guarantees
  | mult, (x, y, z), _, _ =>
    if mult = -1 then x.val < 256 ∧ y.val < 256 ∧ z.val = (x.val + y.val) % 256
    else True
  Requirements
  | mult, (x, y, z), _, _ =>
    if mult = 1 then x.val < 256 ∧ y.val < 256 ∧ z.val = (x.val + y.val) % 256
    else True

def add8 : FormalCircuitWithInteractions (F p) fieldTriple unit where
  main | (x, y, z) => do
    -- range-check all three inputs using the bytes channel
    BytesChannel.pull x
    BytesChannel.pull y
    BytesChannel.pull z

    -- witness the output carry
    let carry ← witness fun eval => floorDiv256 (eval (x + y))
    assertBool carry

    -- assert correctness
    x + y - z - carry * 256 === 0

    -- push the interaction to the add8 channel
    Add8Channel.push (x, y, z)

  localLength _ := 1
  output _ _ := ()

  -- TODO it's wrong that we have to eval the inputs here
  localAdds
  | (x, y, z), _, eval =>
    BytesChannel.pulled (eval x) +
    BytesChannel.pulled (eval y) +
    BytesChannel.pulled (eval z) +
    Add8Channel.pushed (eval x, eval y, eval z)

  -- TODO feels weird to put the entire spec in the completeness assumptions
  -- can we get something from the channel interactions??
  Assumptions | (x, y, z), _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [BytesChannel, Add8Channel, reduceIte]
    rcases input with ⟨ x, y, z ⟩ -- TODO circuit_proof_start should have done this
    simp_all only [Prod.mk.injEq]
    set carry := env.get i₀
    obtain ⟨ hx, hy, hz, hcarry, heq ⟩ := h_holds
    have add_soundness := Theorems.soundness x y z 0 carry hx hy hz (by left; trivial) hcarry
    simp_all

  -- TODO: we didn't need to prove z < 256, but we could have
  -- for completeness, it would make sense to require proving the Guarantees as well
  -- what about the Requirements?
  completeness := by
    circuit_proof_start
    rcases input with ⟨ x, y, z ⟩ -- TODO circuit_proof_start should have done this
    simp only [Prod.mk.injEq] at h_input
    set carry := env.get i₀
    simp_all only
    rcases h_assumptions with ⟨ hx, hy, hz, heq ⟩
    have add_completeness_bool := Theorems.completeness_bool x y 0 hx hy (by simp)
    have add_completeness_add := Theorems.completeness_add x y 0 hx hy (by simp)
    simp only [add_zero] at add_completeness_bool add_completeness_add
    use add_completeness_bool
    convert add_completeness_add
    apply FieldUtils.ext
    rw [heq, mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
    linarith [‹Fact (p > 512)›.elim]
