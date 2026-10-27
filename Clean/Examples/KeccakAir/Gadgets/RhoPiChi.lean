/-
ρ, π and χ in a row of the Keccak-f AIR, as Plonky3's `eval` checks them. ρ and π only rotate and
move the bits of θ's output `A'`, so they are a reading of its cells, `B`; χ's output
`A''[x, y] = B[x, y] ^ (~B[x + 1, y] & B[x + 2, y])` is checked against its limbs, which also range
checks them.
-/
module

public import Clean.Examples.KeccakAir.Lanes

@[expose] public section

namespace KeccakAir.RhoPiChi
open Specs.Keccak256 Gadgets Utils.Bits

variable {p : ℕ} [Fact p.Prime]

/-- The bits of `A''[x, y] = B[x, y] ^ (~B[x + 1, y] & B[x + 2, y])`. -/
def chiBits {α : Type} [Add α] [Sub α] [Mul α] [OfNat α 1] [OfNat α 2] (row : Row α)
    (x y : Fin 5) : Vector α 64 :=
  .ofFn fun z => bitXor (bitAndNot (row.b (x + 1) y z) (row.b (x + 2) y z)) (row.b x y z)

def main (row : Var Row (F p)) : Circuit (F p) Unit :=
  Circuit.forEach (Vector.finRange 5) fun y =>
    Circuit.forEach (Vector.finRange 5) fun x =>
      PackLimbs.circuit 4 16 (packLane (chiBits row x y) (row.aPrimePrimeLane y x))

/-- θ's output cells hold the bits of some lanes. -/
def Assumptions (row : Row (F p)) : Prop :=
  ∃ lanes : Lanes, ∀ y x, row.aPrimeLane y x = bitsOfLane (lanes x y)

/-- If θ's output cells hold the bits of some lanes, χ's output cells hold the limbs of χ, ρ and π
of them. -/
def Spec (row : Row (F p)) : Prop :=
  ∀ lanes : Lanes, (∀ y x, row.aPrimeLane y x = bitsOfLane (lanes x y)) →
    ∀ y x, row.aPrimePrimeLane y x = limbsOfLane (Lanes.chi (Lanes.rhoPi lanes) x y)

/-- The constraints of ρ, π and χ, on values. -/
def Holds (row : Row (F p)) : Prop :=
  ∀ y x (l : Fin 4), (packLane (chiBits row x y) (row.aPrimePrimeLane y x))[l].value =
    fieldFromBits (packLane (chiBits row x y) (row.aPrimePrimeLane y x))[l].bits

section Values

lemma chiBits_map_eval (env : Environment (F p)) (row : Row (Expression (F p))) (x y : Fin 5) :
    chiBits (row.map (Expression.eval env)) x y = (chiBits row x y).map (Expression.eval env) := by
  ext z hz
  simp [chiBits, circuit_norm]

/-- The cells of θ's output that hold the bits of some lanes hold the bits of `χ ∘ ρ ∘ π`'s
input `B`, and the χ bits are those of `χ ∘ ρ ∘ π` of them. -/
lemma chiBits_eq {row : Row (F p)} {lanes : Lanes}
    (h : ∀ y x, row.aPrimeLane y x = bitsOfLane (lanes x y)) (x y : Fin 5) :
    chiBits row x y = bitsOfLane (Lanes.chi (Lanes.rhoPi lanes) x y) := by
  have hbit (x y : Fin 5) (z : Fin 64) :
      row.b x y z = ofBool ((Lanes.rhoPi lanes x y).getLsbD z) := by
    have := congrArg (·[((z - rotationOffsets[x + 3 * y][x] : Fin 64) : ℕ)]) (h x (x + 3 * y))
    simp only [Row.getElem_aPrimeLane _ _ _ _ (Fin.isLt _), getElem_bitsOfLane _ _ (Fin.isLt _),
      Fin.eta] at this
    rw [Row.b, this, Lanes.rhoPi, getLsbD_rotateLeft]
  ext z hz
  simp only [chiBits, Vector.getElem_ofFn, getElem_bitsOfLane _ _ hz]
  rw [hbit, hbit, hbit, bitAndNot_ofBool, bitXor_ofBool]
  simp only [Lanes.chi, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hz,
    decide_true, Bool.true_and]
  rw [Bool.xor_comm]

end Values

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Row unit main := by
  elaborate_circuit

def circuit : FormalAssertion (F p) Row where
  name := "rhoPiChi"
  main
  elaborated
  Assumptions
  Spec
  soundness := by
    intro offset env row_var row h_input _ h_holds
    rw [← h_input, eval_row]
    refine ⟨fun lanes h_lanes y x => ?_, by simp [main, circuit_norm, PackLimbs.circuit]⟩
    simp only [main, circuit_norm, PackLimbs.circuit, Fin.eta] at h_holds
    have h : Holds (row_var.map (Expression.eval env)) := fun y x l => by
      simpa [eval_packLane, chiBits_map_eval] using h_holds y x l
    have := h y x
    rw [chiBits_eq h_lanes] at this
    exact (packed_iff _ _).mp this
  completeness := by
    intro offset env row_var _ row h_input h_assumptions h_spec
    rw [← h_input, CircuitType.eval_var_prover_to_verifier, eval_row] at h_assumptions h_spec
    obtain ⟨lanes, h_lanes⟩ := h_assumptions
    have h : Holds (row_var.map (Expression.eval env.toEnvironment)) := fun y x => by
      rw [chiBits_eq h_lanes]
      exact (packed_iff _ _).mpr (h_spec lanes h_lanes y x)
    simp only [main, circuit_norm, PackLimbs.circuit, Fin.eta]
    intro y x l
    simpa [eval_packLane, chiBits_map_eval] using h y x l

lemma interactions_eq (row : Var Row (F p)) (offset : ℕ) :
    ((circuit.main row).operations offset).interactions = [] := by
  simp [circuit, main, circuit_norm, FormalAssertion.toSubcircuit_interactions,
    PackLimbs.interactions_eq]

end KeccakAir.RhoPiChi
