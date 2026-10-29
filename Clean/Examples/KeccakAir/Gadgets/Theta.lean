/-
θ in a row of the Keccak-f AIR, as Plonky3's `eval` checks it: the bits of the column parities `C`
and of `C'[x] = C[x] ^ C[x - 1] ^ rot(C[x + 1], 1)`, the bits of θ's output `A'` against the limbs
of the round's input `A = A' ^ C ^ C'`, and the parities `C'[x]` of the columns of `A'`. Together
they make `C` the column parities of `A`, and `A'` θ's output.
-/
module

public import Clean.Examples.KeccakAir.Lanes
public import Clean.Gadgets.Bits

@[expose] public section

namespace KeccakAir.Theta
open Specs.Keccak256 Gadgets Utils.Bits

variable {p : ℕ} [Fact p.Prime]

/-- The bits of `A[x, y] = A'[x, y] ^ C[x] ^ C'[x]`, which the limbs of `A` pack. -/
def inputBits {α : Type} [Add α] [Sub α] [Mul α] [OfNat α 2] (row : Row α) (y x : Fin 5) :
    Vector α 64 :=
  .ofFn fun z => bitXor (row.aPrimeBit y x z) (bitXor (row.cBit x z) (row.cPrimeBit x z))

def main (row : Var Row (F p)) : Circuit (F p) Unit := do
  Circuit.forEach (Vector.finRange 5) fun x => do
    Circuit.forEach (row.cLane x) assertBool
    Circuit.forEach (Vector.finRange 64) fun z =>
      assertZero (row.cPrimeBit x z -
        bitXor (bitXor (row.cBit x z) (row.cBit (x + 4) z)) (row.cBit (x + 1) (z - 1)))
  Circuit.forEach (Vector.finRange 5) fun x =>
    Circuit.forEach (Vector.finRange 5) fun y => do
      Circuit.forEach (row.aPrimeLane y x) assertBool
      PackLimbs.circuit 4 16 (packLane (inputBits row y x) (row.aLane y x))
  Circuit.forEach (Vector.finRange 5) fun x =>
    Circuit.forEach (Vector.finRange 64) fun z =>
      assertZero (parityCheck (row.aPrimeBit 0 x z) (row.aPrimeBit 1 x z) (row.aPrimeBit 2 x z)
        (row.aPrimeBit 3 x z) (row.aPrimeBit 4 x z) (row.cPrimeBit x z))

/-- `C'[x] = C[x] ^ C[x - 1] ^ rot(C[x + 1], 1)` for the column parities `C` of a state. -/
def cPrime (state : Lanes) (x : Fin 5) : BitVec 64 :=
  Lanes.columnParity state x ^^^ Lanes.columnParity state (x + 4) ^^^
    (Lanes.columnParity state (x + 1)).rotateLeft 1

/-- The row's cells of θ hold the column parities of its input `A`, `C'` and θ's output, and the
limbs of `A` are 16-bit. -/
def Spec (row : Row (F p)) : Prop :=
  let state := lanesOf row.aLane
  (∀ y x, row.aLane y x = limbsOfLane (state x y)) ∧
  (∀ x, row.cLane x = bitsOfLane (Lanes.columnParity state x)) ∧
  (∀ x, row.cPrimeLane x = bitsOfLane (cPrime state x)) ∧
  (∀ y x, row.aPrimeLane y x = bitsOfLane (Lanes.theta state x y))

/-- The constraints of θ, on values. -/
structure Holds (row : Row (F p)) : Prop where
  c : ∀ x z, IsBool (row.cBit x z)
  cPrime : ∀ x z, row.cPrimeBit x z -
    bitXor (bitXor (row.cBit x z) (row.cBit (x + 4) z)) (row.cBit (x + 1) (z - 1)) = 0
  aPrime : ∀ y x z, IsBool (row.aPrimeBit y x z)
  a : ∀ y x (l : Fin 4), (packLane (inputBits row y x) (row.aLane y x))[l].value =
    fieldFromBits (packLane (inputBits row y x) (row.aLane y x))[l].bits
  parity : ∀ x z, parityCheck (row.aPrimeBit 0 x z) (row.aPrimeBit 1 x z) (row.aPrimeBit 2 x z)
    (row.aPrimeBit 3 x z) (row.aPrimeBit 4 x z) (row.cPrimeBit x z) = 0

section Values

lemma inputBits_map_eval (env : Environment (F p)) (row : Row (Expression (F p))) (y x : Fin 5) :
    inputBits (row.map (Expression.eval env)) y x =
      (inputBits row y x).map (Expression.eval env) := by
  ext z hz
  simp [inputBits, circuit_norm]

/-- Boolean cells of a lane are the bits of the lane they spell. -/
lemma bit_eq_of_isBool {lane : Vector (F p) 64} {bit : Fin 64 → F p}
    (hlane : ∀ z : ℕ, (hz : z < 64) → lane[z] = bit ⟨z, hz⟩) (hbit : ∀ z, IsBool (bit z))
    (z : Fin 64) : bit z = ofBool ((laneOfBits lane).getLsbD z) := by
  have h := bitsOfLane_laneOfBits (bits := lane) fun z => by
    rw [Fin.getElem_fin, hlane z.val z.isLt]
    exact hbit z
  have := congrArg (·[z.val]) h
  simp only [getElem_bitsOfLane _ _ z.isLt, hlane z.val z.isLt] at this
  exact this.symm

lemma theta_bool (a c c4 r : Bool) : ((a ^^ (c ^^ (c ^^ c4 ^^ r))) ^^ (c4 ^^ r)) = a := by
  revert a c c4 r
  decide

lemma columnParity_bool (a0 a1 a2 a3 a4 c c' : Bool)
    (hparity : c' = (a0 ^^ a1 ^^ a2 ^^ a3 ^^ a4)) :
    ((a0 ^^ (c ^^ c')) ^^ (a1 ^^ (c ^^ c')) ^^ (a2 ^^ (c ^^ c')) ^^ (a3 ^^ (c ^^ c')) ^^
      (a4 ^^ (c ^^ c'))) = c := by
  subst hparity
  revert a0 a1 a2 a3 a4 c
  decide

lemma getLsbD_rotateLeft_one (lane : BitVec 64) (z : Fin 64) :
    (lane.rotateLeft 1).getLsbD z = lane.getLsbD ((z - 1 : Fin 64) : ℕ) :=
  getLsbD_rotateLeft lane 1 z

/-- θ's constraints make the cells of θ hold the column parities, `C'` and θ's output. -/
theorem spec_of_holds (hp : 2 ^ 16 < p) {row : Row (F p)} (h : Holds row) : Spec row := by
  -- the lanes of the bit cells
  set C : Fin 5 → BitVec 64 := fun x => laneOfBits (row.cLane x) with hC
  set aPrime : Fin 5 → Fin 5 → BitVec 64 := fun y x => laneOfBits (row.aPrimeLane y x)
    with haPrime
  set C' : Fin 5 → BitVec 64 := fun x => C x ^^^ C (x + 4) ^^^ (C (x + 1)).rotateLeft 1 with hC'
  have hcBit (x : Fin 5) (z : Fin 64) : row.cBit x z = ofBool ((C x).getLsbD z) :=
    bit_eq_of_isBool (Row.getElem_cLane row x) (h.c x) z
  have haPrimeBit (y x : Fin 5) (z : Fin 64) :
      row.aPrimeBit y x z = ofBool ((aPrime y x).getLsbD z) :=
    bit_eq_of_isBool (Row.getElem_aPrimeLane row y x) (h.aPrime y x) z
  have hcPrimeBit (x : Fin 5) (z : Fin 64) : row.cPrimeBit x z = ofBool ((C' x).getLsbD z) := by
    rw [sub_eq_zero.mp (h.cPrime x z), hcBit, hcBit, hcBit, bitXor_ofBool, bitXor_ofBool]
    simp only [hC', BitVec.getLsbD_xor, getLsbD_rotateLeft_one]
  -- the limbs of `A`
  have hinput (y x : Fin 5) : inputBits row y x = bitsOfLane (aPrime y x ^^^ (C x ^^^ C' x)) := by
    ext z hz
    simp only [inputBits, Vector.getElem_ofFn, getElem_bitsOfLane _ _ hz, haPrimeBit, hcBit,
      hcPrimeBit, bitXor_ofBool, BitVec.getLsbD_xor]
  have hA (y x : Fin 5) : row.aLane y x = limbsOfLane (aPrime y x ^^^ (C x ^^^ C' x)) := by
    rw [← packed_iff, ← hinput]
    exact h.a y x
  set state := lanesOf row.aLane with hstate
  have hS (x y : Fin 5) : state x y = aPrime y x ^^^ (C x ^^^ C' x) := by
    simp only [hstate, lanesOf, hA, laneOf_limbsOfLane hp]
  -- `C'` is the parity of the columns of `A'`, so `C` is the parity of the columns of `A`
  have hparity (x : Fin 5) (z : Fin 64) : (C' x).getLsbD z = ((aPrime 0 x).getLsbD z ^^
      (aPrime 1 x).getLsbD z ^^ (aPrime 2 x).getLsbD z ^^ (aPrime 3 x).getLsbD z ^^
      (aPrime 4 x).getLsbD z) := by
    have := h.parity x z
    rw [haPrimeBit, haPrimeBit, haPrimeBit, haPrimeBit, haPrimeBit, hcPrimeBit,
      parity_iff (by omega)] at this
    exact this
  have hcolumn (x : Fin 5) : Lanes.columnParity state x = C x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Lanes.columnParity, BitVec.getLsbD_xor, hS]
    exact columnParity_bool _ _ _ _ _ _ _ (hparity x ⟨i, hi⟩)
  refine ⟨fun y x => (show row.aLane y x = limbsOfLane (state x y) by rw [hS, hA]),
    fun x => ?_, fun x => ?_, fun y x => ?_⟩
  · rw [hcolumn]
    ext z hz
    rw [Row.getElem_cLane _ _ _ hz, hcBit, getElem_bitsOfLane _ _ hz]
  · ext z hz
    rw [Row.getElem_cPrimeLane _ _ _ hz, hcPrimeBit, getElem_bitsOfLane _ _ hz, cPrime, hcolumn,
      hcolumn, hcolumn]
  · have htheta : Lanes.theta state x y = aPrime y x := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [Lanes.theta, hcolumn, hS, hC', BitVec.getLsbD_xor]
      exact theta_bool _ _ _ _
    ext z hz
    rw [htheta, Row.getElem_aPrimeLane _ _ _ _ hz, haPrimeBit, getElem_bitsOfLane _ _ hz]

lemma input_bool (s cp4 r cp : Bool) :
    ((s ^^ (cp4 ^^ r)) ^^ (cp ^^ (cp ^^ cp4 ^^ r))) = s := by
  revert s cp4 r cp
  decide

lemma parity_bool (s0 s1 s2 s3 s4 c4 r : Bool) :
    ((s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) ^^ c4 ^^ r) = ((s0 ^^ (c4 ^^ r)) ^^ (s1 ^^ (c4 ^^ r)) ^^
      (s2 ^^ (c4 ^^ r)) ^^ (s3 ^^ (c4 ^^ r)) ^^ (s4 ^^ (c4 ^^ r))) := by
  revert s0 s1 s2 s3 s4 c4 r
  decide

/-- The cells of θ that hold the column parities, `C'` and θ's output satisfy θ's constraints. -/
theorem holds_of_spec (hp : 2 ^ 16 < p) {row : Row (F p)} (h : Spec row) : Holds row := by
  obtain ⟨hA, hc, hcPrime, haPrime⟩ := h
  set state := lanesOf row.aLane with hstate
  have hcBit (x : Fin 5) (z : Fin 64) :
      row.cBit x z = ofBool ((Lanes.columnParity state x).getLsbD z) := by
    have := congrArg (·[z.val]) (hc x)
    simpa only [Row.getElem_cLane _ _ _ z.isLt, getElem_bitsOfLane _ _ z.isLt] using this
  have hcPrimeBit (x : Fin 5) (z : Fin 64) :
      row.cPrimeBit x z = ofBool ((cPrime state x).getLsbD z) := by
    have := congrArg (·[z.val]) (hcPrime x)
    simpa only [Row.getElem_cPrimeLane _ _ _ z.isLt, getElem_bitsOfLane _ _ z.isLt] using this
  have haPrimeBit (y x : Fin 5) (z : Fin 64) :
      row.aPrimeBit y x z = ofBool ((Lanes.theta state x y).getLsbD z) := by
    have := congrArg (·[z.val]) (haPrime y x)
    simpa only [Row.getElem_aPrimeLane _ _ _ _ z.isLt, getElem_bitsOfLane _ _ z.isLt] using this
  refine ⟨fun x z => ?_, fun x z => ?_, fun y x z => ?_, fun y x => ?_, fun x z => ?_⟩
  · rw [hcBit]
    exact isBool_ofBool _
  · rw [hcPrimeBit, hcBit, hcBit, hcBit, bitXor_ofBool, bitXor_ofBool, sub_eq_zero]
    simp only [cPrime, BitVec.getLsbD_xor, getLsbD_rotateLeft_one]
  · rw [haPrimeBit]
    exact isBool_ofBool _
  · have hinput : inputBits row y x = bitsOfLane (state x y) := by
      ext z hz
      simp only [inputBits, Vector.getElem_ofFn, getElem_bitsOfLane _ _ hz]
      rw [haPrimeBit, hcBit, hcPrimeBit, bitXor_ofBool, bitXor_ofBool]
      simp only [Lanes.theta, cPrime, BitVec.getLsbD_xor]
      rw [input_bool]
    rw [hinput]
    exact (packed_iff _ _).mpr (hA y x)
  · rw [haPrimeBit, haPrimeBit, haPrimeBit, haPrimeBit, haPrimeBit, hcPrimeBit,
      parity_iff (by omega)]
    have hcolumn : (Lanes.columnParity state x).getLsbD z = ((state x 0).getLsbD z ^^
        (state x 1).getLsbD z ^^ (state x 2).getLsbD z ^^ (state x 3).getLsbD z ^^
        (state x 4).getLsbD z) := by
      simp only [Lanes.columnParity, BitVec.getLsbD_xor]
    simp only [Lanes.theta, cPrime, BitVec.getLsbD_xor]
    rw [hcolumn]
    exact parity_bool _ _ _ _ _ _ _

end Values

variable [large : Fact (2 ^ 16 < p)]

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Row unit main := by
  elaborate_circuit

def circuit : FormalAssertion (F p) Row where
  name := "theta"
  main
  elaborated
  Spec
  soundness := by
    intro offset env row_var row h_input _ h_holds
    rw [← h_input, eval_row]
    refine ⟨spec_of_holds large.elim ?_, by simp [main, circuit_norm, PackLimbs.circuit]⟩
    simp only [main, circuit_norm, PackLimbs.circuit, Fin.eta] at h_holds
    obtain ⟨h_column, h_lane, h_parity⟩ := h_holds
    exact {
      c := fun x z => by simpa [Row.getElem_cLane] using (h_column x).1 z
      cPrime := fun x z => by simpa using (h_column x).2 z
      aPrime := fun y x z => by simpa [Row.getElem_aPrimeLane] using (h_lane x y).1 z
      a := fun y x l => by
        simpa [eval_packLane, inputBits_map_eval] using (h_lane x y).2 l
      parity := fun x z => by simpa using h_parity x z }
  completeness := by
    intro offset env row_var _ row h_input _ h_spec
    rw [← h_input, CircuitType.eval_var_prover_to_verifier, eval_row] at h_spec
    have h := holds_of_spec large.elim h_spec
    simp only [main, circuit_norm, PackLimbs.circuit, Fin.eta]
    refine ⟨fun x => ⟨fun z => ?_, fun z => ?_⟩, fun x y => ⟨fun z => ?_, fun l => ?_⟩,
      fun x z => ?_⟩
    · simpa [Row.getElem_cLane] using h.c x z
    · simpa using h.cPrime x z
    · simpa [Row.getElem_aPrimeLane] using h.aPrime y x z
    · simpa [eval_packLane, inputBits_map_eval] using h.a y x l
    · simpa using h.parity x z

lemma interactions_eq (row : Var Row (F p)) (offset : ℕ) :
    ((circuit.main row).operations offset).interactions = [] := by
  simp [circuit, main, circuit_norm, FormalAssertion.toSubcircuit_interactions, assertBool,
    PackLimbs.interactions_eq]

end KeccakAir.Theta
