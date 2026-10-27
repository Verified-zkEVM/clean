module

public import Clean.Circuit
public import Clean.Gadgets.Equality
public import Clean.Gadgets.Boolean
public import Clean.Utils.Bits
public import Clean.Utils.Tactics

@[expose] public section

namespace Gadgets.PackBits
open Utils.Bits
variable {p : ℕ} [Fact p.Prime]

/-- Bits and the field element they are asserted to pack into. -/
structure Input (n : ℕ) (F : Type) where
  bits : fields n F
  value : F
deriving ProvableStruct

/-- Assert that `value` is the field element with the given bits, lowest first, computed by
Horner's rule from the top bit. -/
def main {n : ℕ} (input : Var (Input n) (F p)) : Circuit (F p) Unit :=
  assertZero (fieldFromBitsExpr input.bits - input.value)

@[reducible]
instance elaborated (n : ℕ) : ElaboratedCircuit (F p) (Input n) unit main := by
  elaborate_circuit

def circuit (n : ℕ) : FormalAssertion (F p) (Input n) where
  name := "packBits"
  main
  elaborated := elaborated n
  Spec input := input.value = fieldFromBits input.bits
  soundness := by
    circuit_proof_start
    rw [fieldFromBits_eval, sub_eq_zero,
      h_input.left] at h_holds
    exact h_holds.symm
  completeness := by
    circuit_proof_start
    rw [fieldFromBits_eval, sub_eq_zero, h_spec, h_input.left]

@[circuit_norm]
lemma localLength_eq (n : ℕ) (input : Var (Input n) (F p)) :
    (circuit n).localLength input = 0 := rfl

lemma interactions_eq (n : ℕ) (input : Var (Input n) (F p)) (offset : ℕ) :
    (((circuit n).main input).operations offset).interactions = [] := by
  simp [circuit, main, circuit_norm]

end Gadgets.PackBits

namespace Gadgets.PackLimbs
open Utils.Bits
variable {p : ℕ} [Fact p.Prime]

/-- Assert that each of `k` limbs packs its `w` bits. -/
def main {k w : ℕ} [NeZero k] (limbs : Var (ProvableVector (PackBits.Input w) k) (F p)) :
    Circuit (F p) Unit :=
  Circuit.forEach limbs (PackBits.circuit w)

@[reducible]
instance elaborated (k w : ℕ) [NeZero k] :
    ElaboratedCircuit (F p) (ProvableVector (PackBits.Input w) k) unit main := by
  elaborate_circuit

def circuit (k w : ℕ) [NeZero k] : FormalAssertion (F p) (ProvableVector (PackBits.Input w) k) where
  name := "packLimbs"
  main
  elaborated := elaborated k w
  Spec limbs := ∀ l : Fin k, limbs[l].value = fieldFromBits limbs[l].bits
  soundness := by
    circuit_proof_start [PackBits.circuit]
    intro l
    rw [← h_input]
    simpa [circuit_norm, eval_vector] using h_holds l
  completeness := by
    circuit_proof_start [PackBits.circuit]
    intro l
    have := h_spec l
    rw [← h_input] at this
    simpa [circuit_norm, eval_vector] using this

@[circuit_norm]
lemma localLength_eq (k w : ℕ) [NeZero k]
    (input : Var (ProvableVector (PackBits.Input w) k) (F p)) :
    (circuit k w).localLength input = 0 := by
  simp only [circuit, FormalCircuitBase.localLength, elaborated]
  rfl

lemma interactions_eq (k w : ℕ) [NeZero k] (input : Var (ProvableVector (PackBits.Input w) k) (F p))
    (offset : ℕ) : (((circuit k w).main input).operations offset).interactions = [] := by
  simp [circuit, main, circuit_norm, FormalAssertion.toSubcircuit_interactions,
    PackBits.interactions_eq]

end Gadgets.PackLimbs

namespace Gadgets.ToBits
open Utils.Bits
variable {p : ℕ} [prime: Fact p.Prime] [p_large_enough: Fact (p > 2)]

def main (n : ℕ) (x : Expression (F p)) : Circuit (F p) (Vector (Expression (F p)) n) := do
  -- witness the bits of `x`
  let bits ← witnessVector n (x.bits n)

  -- add boolean constraints on all bits
  Circuit.forEach bits assertBool

  -- check that the bits correctly sum to `x`
  PackBits.circuit n ⟨bits, x⟩
  return bits

-- formal circuit that implements `toBits` like a function, assuming `x.val < 2^n`

def toBits (n : ℕ) (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n) where
  main := main n

  ProverAssumptions (x : F p) _ _ := x.val < 2^n

  Spec (x : F p) (bits : Vector (F p) n) _ :=
    x.val < 2^n ∧ bits = fieldToBits n x

  soundness := by
    circuit_proof_start [PackBits.circuit]
    obtain ⟨ h_bits, h_eq ⟩ := h_holds

    let bits : Vector (F p) n := (Vector.mapRange n (var ⟨i₀ + ·⟩)).map (Expression.eval env)

    replace h_bits (i : ℕ) (hi : i < n) : IsBool bits[i] := by
      simp only [circuit_norm, bits]
      exact h_bits ⟨ i, hi ⟩

    rw [h_eq, fieldToBits_fieldFromBits hn bits h_bits]
    use fieldFromBits_lt _ h_bits

  completeness := by
    circuit_proof_start [PackBits.circuit]

    constructor
    · intro i
      rw [h_env i]
      rcases Nat.mod_two_eq_zero_or_one (input.val >>> i.val) with h | h <;> simp [h, IsBool]

    have h_bits_eq : (Vector.mapRange n (var ⟨i₀ + ·⟩)).map (Expression.eval env.toEnvironment) =
        fieldToBits n input := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm]
      rw [h_env ⟨ i, hi ⟩, getElem_fieldToBits]

    rw [h_bits_eq, fieldFromBits_fieldToBits h_assumptions]

-- formal assertion that uses the same circuit to implement a range check. without input assumption

def rangeCheck (n : ℕ) (hn : 2^n < p) : FormalAssertion (F p) field where
  main x := do
    -- we wrap the toBits circuit but ignore the output
    let _ ← toBits n hn x

  Spec (x : F p) := x.val < 2^n

  soundness := by circuit_proof_all [toBits]
  completeness := by circuit_proof_all [toBits]

end ToBits
export ToBits (toBits)
end Gadgets
