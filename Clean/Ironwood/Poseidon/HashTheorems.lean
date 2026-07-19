import Clean.Ironwood.Poseidon.SpongeTheorems

/-!
# Orchard Poseidon hash APIs

This module mirrors `halo2_gadgets/src/poseidon.rs::Hash` for the source-shaped pieces
that can be expressed once a full padded rate-2 block is available.
-/

namespace Halo2.Ironwood.Poseidon.Hash

namespace HashPaddedBlock

/-- Value-level one-block hash after the caller/domain has prepared a full padded rate-2
block.  This is the straight-line source composition `init -> add_input -> permute ->
squeeze first`. -/
def value (roundConstants : Nat → Permute.State Fp) (capacity : Fp)
    (block : Sponge.Rate2 Fp) : Fp :=
  let initial : Permute.State Fp := { x0 := 0, x1 := 0, x2 := capacity }
  let absorbed := Sponge.AddInput.value { initialState := initial, input := block }
  let permuted := Permute.value roundConstants absorbed
  (Sponge.GetOutput.value permuted).x0

def Spec (roundConstants : Nat → Permute.State Fp) (capacity : Fp)
    (block : Sponge.Rate2 Fp) (output : Fp) : Prop :=
  output = value roundConstants capacity block

/-- Concrete one-padded-block P128 hash value using ported round constants. -/
def concreteValue (capacity : Fp) (block : Sponge.Rate2 Fp) : Fp :=
  value Permute.P128Pow5T3.roundConstants capacity block

end HashPaddedBlock

namespace ConstantLength

/-- Number of rate-2 blocks after padding a constant-length message of length `L` with
zeroes to a multiple of the rate.  This is `(L + RATE - 1) / RATE` for `RATE = 2`. -/
def blockCount (L : Nat) : Nat :=
  (L + 1) / 2

instance {L : ℕ} [NeZero L] : NeZero (blockCount L) := .mk (by
  have : L > 0 := NeZero.pos L
  simp only [blockCount]
  grind)

/-- Capacity element for `halo2_poseidon::ConstantLength<L>` with output length one:
`L * 2^64`. -/
def capacity (L : Nat) : Fp :=
  (L * 2 ^ 64 : Nat)

/-- Value-level padded word at a flattened padded index. -/
def paddedWord {L : Nat} (message : Vector Fp L) (idx : Nat) : Fp :=
  if h : idx < L then message[idx] else 0

/-- Circuit-level padded word at a flattened padded index. -/
def paddedVar {L : Nat} (message : Vector (Expression Fp) L) (idx : Nat) :
    Expression Fp :=
  if h : idx < L then message[idx] else 0

/-- Value-level padded rate-2 block. -/
def blockValue {L : Nat} (message : Vector Fp L) (i : Nat) : Sponge.Rate2 Fp :=
  { x0 := paddedWord message (2 * i), x1 := paddedWord message (2 * i + 1) }

/-- Circuit-level padded rate-2 block. -/
def blockVar {L : Nat} (message : Vector (Expression Fp) L) (i : Nat) :
    Var Sponge.Rate2 Fp :=
  { x0 := paddedVar message (2 * i), x1 := paddedVar message (2 * i + 1) }

/-- Value-level state after absorbing and permuting one padded block. -/
def absorbPermuteValue (input : Sponge.AddInputInput Fp) : Permute.State Fp :=
  Permute.concreteValue (Sponge.AddInput.value input)

namespace AbsorbPermute

def Spec (input : Sponge.AddInputInput Fp) (output : Permute.State Fp) : Prop :=
  output = absorbPermuteValue input

end AbsorbPermute

/-- Value-level body of one `ConstantLength<L>` absorb/permute step. The loop
length `m` is explicit so the scheduler proof can induct on it. -/
def stepValueAt {L m : Nat} (message : Vector Fp L) (state : Permute.State Fp)
    (i : Fin m) : Permute.State Fp :=
  absorbPermuteValue { initialState := state, input := blockValue message i.val }

/-- Value-level `Hash::hash` for `ConstantLength<L>`. -/
def value {L : Nat} (message : Vector Fp L) : Fp :=
  let initial : Permute.State Fp := { x0 := 0, x1 := 0, x2 := capacity L }
  let finalState := Fin.foldl (blockCount L) (stepValueAt message) initial
  (Sponge.GetOutput.value finalState).x0

/-- Spec for `Hash::hash` over `ConstantLength<L>`. -/
def Spec {L : Nat} (message : Vector Fp L) (output : Fp) : Prop :=
  output = value message

def evalState (env : Environment Fp) (state : Var Permute.State Fp) :
    Permute.State Fp :=
  { x0 := Expression.eval env state.x0, x1 := Expression.eval env state.x1,
    x2 := Expression.eval env state.x2 }

def evalBlock (env : Environment Fp) (block : Var Sponge.Rate2 Fp) :
    Sponge.Rate2 Fp :=
  { x0 := Expression.eval env block.x0, x1 := Expression.eval env block.x1 }

lemma evalBlock_blockVar {L : Nat} {env : Environment Fp}
    {messageVar : Vector (Expression Fp) L} {message : Vector Fp L}
    (h_input : Vector.map (Expression.eval env) messageVar = message) (i : Nat) :
    { x0 := Expression.eval env (blockVar messageVar i).x0,
      x1 := Expression.eval env (blockVar messageVar i).x1 } = blockValue message i := by
  simp only [blockValue, blockVar, circuit_norm, explicit_provable_type]
  suffices ∀ i, Expression.eval env (paddedVar messageVar i) = paddedWord message i by
    grind
  subst message
  intro i
  simp [paddedVar, paddedWord]
  by_cases h : i < L <;> simp [circuit_norm, h]

end ConstantLength

end Halo2.Ironwood.Poseidon.Hash
