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

-- TODO lemma that resolves (if -1 = 1 then T else E) = E

-- TODO move this stuff

-- normal form of channel interactions
def Channel.emitted {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (chan : Channel F Message) (mult : F) (msg : Message F) : InteractionDelta F :=
  .single (chan.name, mult, (toElements msg).toArray)

def Channel.pulled {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (chan : Channel F Message) (msg : Message F) : InteractionDelta F :=
  .single (chan.name, -1, (toElements msg).toArray)

@[circuit_norm]
lemma Channel.pulled_def {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (chan : Channel F Message) (msg : Message F) :
    chan.pulled msg = chan.emitted (-1) msg  := rfl

@[circuit_norm]
lemma InteractionDelta.eq_channel_emitted {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) (env : Environment F) :
    let interaction : ChannelInteraction F Message := { channel, mult, msg }
    .single (interaction.toRaw.eval env) = channel.emitted (mult.eval env) (eval env msg) := by
  simp only [Channel.emitted, AbstractInteraction.eval, InteractionDelta.single, ChannelInteraction.toRaw, eval,
    ProvableType.toElements_fromElements]
  rfl

attribute [circuit_norm]
  ConstraintsHoldWithInteractions.Soundness Operations.forAllWithInteractions
  ConstraintsHoldWithInteractions.Completeness
  ConstraintsHoldWithInteractions.Requirements

def add8 : FormalCircuitWithInteractions (F p) fieldPair field where
  main | (x, y) => do
    -- witness the result, and range-check it using the bytes channel
    let z ← witness fun eval => mod256 (eval (x + y))
    BytesChannel.pull z

    -- witness the output carry
    let carry ← witness fun eval => floorDiv256 (eval (x + y))
    assertBool carry

    -- assert correctness, return result
    x + y - z - carry * 256 === 0
    return z

  localLength _ := 2
  output _ i0 := var ⟨i0⟩
  localAdds _ i0 env := BytesChannel.pulled (env.get i0)

  Assumptions | (x, y), _ => x.val < 256 ∧ y.val < 256
  Spec
  | (x, y), z, _ =>
    x.val < 256 → y.val < 256 →
    z.val = (x.val + y.val) % 256

  soundness := by
    circuit_proof_start [BytesChannel]
    rcases input with ⟨ x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    set z := env.get i₀
    set carry := env.get (i₀ + 1)
    simp_all only [↓reduceIte, ite_self, and_true]
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hx hy
    have add_soundness := Theorems.soundness x y z 0 carry hx hy hz (by left; trivial) hcarry
    simp_all

  -- TODO: we didn't need to prove z < 256, but we could have
  -- for completeness, it would make sense to require proving the Guarantees as well
  -- what about the Requirements?
  completeness := by
    circuit_proof_start []
    rcases input with ⟨ x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    set z := env.get i₀
    set carry := env.get (i₀ + 1)
    simp_all only
    rcases h_assumptions with ⟨ hx, hy ⟩
    have add_completeness_bool := Theorems.completeness_bool x y 0 hx hy (by simp)
    have add_completeness_add := Theorems.completeness_add x y 0 hx hy (by simp)
    simp_all [floorDiv256]
