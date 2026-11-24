import Clean.Orchard.Poseidon.Sponge

open Clean

/-!
# Orchard Poseidon hash APIs

This module mirrors `halo2_gadgets/src/poseidon.rs::Hash` for the source-shaped pieces
that can be expressed once a full padded rate-2 block is available.
-/

namespace Orchard.Poseidon.Hash

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

/-- `Hash::hash` for one already-padded rate-2 block. -/
def main (roundConstants : Nat → Permute.State Fp) (capacity : Fp)
    (block : Var Sponge.Rate2 Fp) : Circuit Fp (Expression Fp) := do
  let initial ← Sponge.InitialState.circuit capacity ()
  let absorbed ← Sponge.AddInput.circuit { initialState := initial, input := block }
  let permuted ← Permute.mainP128Circuit roundConstants absorbed
  let output ← Sponge.GetOutput.circuit permuted
  return output.x0

def Spec (roundConstants : Nat → Permute.State Fp) (capacity : Fp)
    (block : Sponge.Rate2 Fp) (output : Fp) : Prop :=
  output = value roundConstants capacity block

/-- Packaged one-padded-block `Hash::hash` composition. -/
def circuit (roundConstants : Nat → Permute.State Fp) (capacity : Fp) :
    FormalCircuit Fp Sponge.Rate2 field where
  name := "Hash::hash[padded_block]"
  main := main roundConstants capacity
  Spec := Spec roundConstants capacity
  soundness := by
    circuit_proof_start [main, value, Sponge.InitialState.circuit,
      Sponge.AddInput.circuit, Permute.mainP128Circuit, Sponge.GetOutput.circuit,
      Sponge.InitialState.Spec, Sponge.AddInput.Spec, Sponge.GetOutput.Spec]
    rcases h_holds with ⟨hinit, habsorb, hpermute, houtput⟩
    rw [hinit] at habsorb
    rw [habsorb] at hpermute
    rw [hpermute] at houtput
    simpa [Sponge.GetOutput.value] using congrArg Sponge.Rate2.x0 houtput
  completeness := by
    circuit_proof_start [main, value, Sponge.InitialState.circuit,
      Sponge.AddInput.circuit, Permute.mainP128Circuit, Sponge.GetOutput.circuit,
      Sponge.InitialState.Spec, Sponge.AddInput.Spec, Sponge.GetOutput.Spec]

/-- Concrete one-padded-block P128 hash value using ported round constants. -/
def concreteValue (capacity : Fp) (block : Sponge.Rate2 Fp) : Fp :=
  value Permute.P128Pow5T3.roundConstants capacity block

/-- Concrete one-padded-block P128 hash circuit using ported round constants. -/
def concreteCircuit (capacity : Fp) : FormalCircuit Fp Sponge.Rate2 field :=
  circuit Permute.P128Pow5T3.roundConstants capacity

end HashPaddedBlock

namespace ConstantLength

/-- Keep the loop argument abstract so its proof never expands the permutation. -/
private theorem fold_chain {α : Type} (step : Nat → α → α)
    (initial : α) (state : Nat → α) (n : Nat)
    (first : step 0 initial = state 0)
    (next : ∀ i, i < n → step (i + 1) (state i) = state (i + 1)) :
    Fin.foldl (n + 1) (fun a i => step i.val a) initial = state n := by
  induction n with
  | zero => simpa only [Fin.foldl_succ, Fin.foldl_zero, Fin.val_zero] using first
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    have previous : Fin.foldl (n + 1) (fun a i => step i.castSucc.val a) initial = state n :=
      ih (fun i hi => next i (Nat.lt_succ_of_lt hi))
    simpa only [previous, Fin.val_last] using next n (Nat.lt_succ_self n)

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

/-- Source-shaped one-block sponge step: `add_input -> permute`. -/
def main (input : Var Sponge.AddInputInput Fp) : Circuit Fp (Var Permute.State Fp) := do
  let absorbed ← Sponge.AddInput.circuit input
  Permute.mainP128ConcreteCircuit absorbed

def Spec (input : Sponge.AddInputInput Fp) (output : Permute.State Fp) : Prop :=
  output = absorbPermuteValue input

/-- Packaged one-block sponge step used by the `ConstantLength<L>` scheduler. -/
def circuit : FormalCircuit Fp Sponge.AddInputInput Permute.State where
  name := "Hash::hash[ConstantLength]/absorb_permute_block"
  main
  Spec
  soundness := by
    circuit_proof_start [main, Spec, absorbPermuteValue, Sponge.AddInput.circuit,
      Permute.mainP128ConcreteCircuit]
    have outputEta :
        let output := (Permute.mainP128Circuit Permute.P128Pow5T3.roundConstants).output
          {x0 := var ⟨i₀ + 5⟩, x1 := var ⟨i₀ + 6⟩, x2 := var ⟨i₀ + 7⟩} (i₀ + 8)
        output = { x0 := output.x0, x1 := output.x1, x2 := output.x2 } := rfl
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.add_assoc, Nat.reduceAdd] at h_holds ⊢
    rw [outputEta] at h_holds
    dsimp only [FormalCircuitBase.output] at outputEta
    rw [outputEta]
    simp only [circuit_norm, explicit_provable_type] at *
    rcases h_holds with ⟨habsorb, hpermute⟩
    rw [habsorb] at hpermute
    constructor
    · have hp := hpermute trivial
      change _ = Permute.value Permute.P128Pow5T3.roundConstants _ at hp
      simpa only [absorbPermuteValue, Permute.concreteValue, FormalCircuitBase.output] using hp
    · simp [Permute.mainP128Circuit]
  completeness := by
    circuit_proof_start [main, Spec, absorbPermuteValue, Sponge.AddInput.circuit,
      Permute.mainP128ConcreteCircuit]
    trivial

end AbsorbPermute

/-- Value-level body of one `ConstantLength<L>` absorb/permute step. The loop
length `m` is explicit so the scheduler proof can induct on it. -/
def stepValueAt {L m : Nat} (message : Vector Fp L) (state : Permute.State Fp)
    (i : Fin m) : Permute.State Fp :=
  absorbPermuteValue { initialState := state, input := blockValue message i.val }

/-- Circuit-level body of one `ConstantLength<L>` absorb/permute step. The loop length
`m` is explicit so the scheduler proof can induct on it. -/
def stepCircuitAt {L m : Nat} (message : Vector (Expression Fp) L)
    (state : Var Permute.State Fp) (i : Fin m) :
    Circuit Fp (Var Permute.State Fp) :=
  AbsorbPermute.circuit { initialState := state, input := blockVar message i.val }

/-- Value-level `Hash::hash` for `ConstantLength<L>`. -/
def value {L : Nat} (message : Vector Fp L) : Fp :=
  let initial : Permute.State Fp := { x0 := 0, x1 := 0, x2 := capacity L }
  let finalState := Fin.foldl (blockCount L) (stepValueAt message) initial
  (Sponge.GetOutput.value finalState).x0

/-- Source-shaped `Hash::hash` for `ConstantLength<L>`, specialized to P128Pow5T3. -/
def main {L : ℕ} [NeZero L] (message : Vector (Expression Fp) L) :
    Circuit Fp (Expression Fp) := do
  let initial ← Sponge.InitialState.circuit (capacity L) ()
  let finalState ← Circuit.foldl (.finRange (blockCount L)) initial (stepCircuitAt message)
    (by simp only [stepCircuitAt, AbsorbPermute.circuit, circuit_norm])
    (by simp only [stepCircuitAt]; infer_constant_length)
  let output ← Sponge.GetOutput.circuit finalState
  return output.x0

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

def circuit (L : ℕ) [NeZero L] : FormalCircuit Fp (fields L) field where
  name := "Hash::hash[ConstantLength]"
  main
  Spec
  soundness := by
    circuit_proof_start [Sponge.InitialState.circuit, stepCircuitAt,
      Permute.mainP128Circuit, AbsorbPermute.circuit, Sponge.GetOutput.circuit,
      Sponge.InitialState.Spec, AbsorbPermute.Spec, Sponge.GetOutput.Spec,
      Permute.State.mk.injEq, value
    ]
    simp only [Nat.isValue, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd,
      Nat.reduceMul] at h_holds ⊢
    obtain ⟨ initial_state, ⟨h_init, h_fold⟩, h_final ⟩ := h_holds
    simp only [initial_state] at h_init
    have bc_pos : blockCount L > 0 := NeZero.pos (blockCount L)
    simp [bc_pos, circuit_norm]
    replace h_final := congrArg (fun s => (s : Sponge.Rate2 Fp).x0) h_final
    simp only at h_final
    rw [h_final]; clear h_final
    congr 2
    have h_blocks (i : Nat) : eval env (blockVar input_var i) = blockValue input i := by
      simpa only [blockVar, circuit_norm, explicit_provable_type] using
        (evalBlock_blockVar h_input i)
    simp only [circuit_norm, explicit_provable_type] at h_blocks
    simp only [h_blocks] at h_init h_fold
    clear h_blocks
    replace h_input := evalBlock_blockVar h_input
    simp only [blockVar, circuit_norm, explicit_provable_type] at h_init h_fold h_input
    simp_all only; clear h_input
    set init : Permute.State Fp := ⟨ 0, 0, capacity L ⟩
    let state (i : ℕ) : Permute.State Fp := {
      x0 := env.get (i₀ + 3 + i * 144 + 8 + 12 + 112 + 9),
      x1 := env.get (i₀ + 3 + i * 144 + 8 + 12 + 112 + 9 + 1),
      x2 := env.get (i₀ + 3 + i * 144 + 8 + 12 + 112 + 9 + 1 + 1) }
    change state 0 = absorbPermuteValue _ at h_init
    change ∀ i, i + 1 < blockCount L →
      state (i + 1) = absorbPermuteValue ⟨ state i, _ ⟩ at h_fold
    suffices (Fin.foldl (blockCount L) (stepValueAt input) init) = state (blockCount L - 1) by
      simpa only [state, Nat.add_assoc, Nat.reduceAdd] using this.symm
    obtain ⟨ n, hn ⟩ : ∃ n, blockCount L = n + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bc_pos)
    rw [hn, Nat.add_sub_cancel]
    change Fin.foldl (n + 1)
      (fun s i => absorbPermuteValue ⟨s, blockValue input i.val⟩) init = state n
    exact
      (fold_chain (fun i s => absorbPermuteValue ⟨s, blockValue input i⟩)
        init state n h_init.symm (fun i hi =>
          (h_fold i (by rw [hn]; exact Nat.succ_lt_succ hi)).symm))
  completeness := by
    circuit_proof_start [Sponge.InitialState.circuit, stepCircuitAt,
      Permute.mainP128Circuit, AbsorbPermute.circuit, Sponge.GetOutput.circuit
    ]

end ConstantLength

end Orchard.Poseidon.Hash
