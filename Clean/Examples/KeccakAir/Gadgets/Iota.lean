/-
ι in a row of the Keccak-f AIR, and the link to the next row, the last part of Plonky3's `eval`:
the bits of `A''[0, 0]` against its limbs, ι's output `A'''[0, 0] = A''[0, 0] ^ RC` against its
limbs, and, within a permutation, the round's output `A'''` as the next round's input.
-/
module

public import Clean.Examples.KeccakAir.Lanes
public import Clean.Gadgets.ConditionalEquality

@[expose] public section

namespace KeccakAir.Iota
open Air.Flat Specs.Keccak256 Gadgets Utils.Bits

variable {p : ℕ} [Fact p.Prime]

/-- The bits of ι's output `A'''[0, 0]`. -/
def iotaBits {α : Type} [Add α] [Sub α] [Mul α] [OfNat α 2] (row : Row α) : Vector α 64 :=
  .ofFn fun z => iotaBit row.stepFlags row.aPrimePrime00Bits[z] z

def main (window : Var (Window Row) (F p)) : Circuit (F p) Unit := do
  let current := window.current
  Circuit.forEach current.aPrimePrime00Bits assertBool
  PackLimbs.circuit 4 16 (packLane current.aPrimePrime00Bits (current.aPrimePrimeLane 0 0))
  PackLimbs.circuit 4 16 (packLane (iotaBits current) current.aPrimePrimePrime00Limbs)
  -- within a permutation, the round's output is the next round's input
  Circuit.forEach (Vector.finRange 5) fun x =>
    Circuit.forEach (Vector.finRange 5) fun y =>
      ConditionalEquality.circuit (fields 4)
        ⟨transitionInPermutation window, current.aPrimePrimePrimeLane y x, window.next.aLane y x⟩

/-- The row's step flags are those of a round. -/
def Assumptions (window : Window Row (F p)) : Prop :=
  ∃ r : Fin 24, window.current.stepFlags = oneHot r

/-- In round `r`, the cells of `A''[0, 0]` hold the bits and limbs of a lane, and the cells of
`A'''[0, 0]` the limbs of the lane xor the round constant. Within a permutation, the next row's
input is the round's output. -/
def Spec (window : Window Row (F p)) : Prop :=
  let current := window.current
  (∀ r : Fin 24, current.stepFlags = oneHot r → ∃ lane : BitVec 64,
    current.aPrimePrime00Bits = bitsOfLane lane ∧ current.aPrimePrimeLane 0 0 = limbsOfLane lane ∧
    current.aPrimePrimePrime00Limbs = limbsOfLane (lane ^^^ roundConstants[r].toBitVec)) ∧
  (transitionInPermutation window ≠ 0 →
    ∀ x y, current.aPrimePrimePrimeLane y x = window.next.aLane y x)

/-- The constraints of ι and the link, on values. -/
structure Holds (window : Window Row (F p)) : Prop where
  bits : ∀ z : Fin 64, IsBool window.current.aPrimePrime00Bits[z]
  limbs : ∀ l : Fin 4,
    (packLane window.current.aPrimePrime00Bits (window.current.aPrimePrimeLane 0 0))[l].value =
      fieldFromBits
        (packLane window.current.aPrimePrime00Bits (window.current.aPrimePrimeLane 0 0))[l].bits
  iota : ∀ l : Fin 4,
    (packLane (iotaBits window.current) window.current.aPrimePrimePrime00Limbs)[l].value =
      fieldFromBits
        (packLane (iotaBits window.current) window.current.aPrimePrimePrime00Limbs)[l].bits
  next : transitionInPermutation window ≠ 0 →
    ∀ x y, window.current.aPrimePrimePrimeLane y x = window.next.aLane y x

section Values

lemma eval_iotaBit (env : Environment (F p)) (flags : Vector (Expression (F p)) 24)
    (bit : Expression (F p)) (z : Fin 64) :
    Expression.eval env (iotaBit flags bit z) =
      iotaBit (flags.map (Expression.eval env)) (Expression.eval env bit) z := by
  have hfold (rounds : List (Fin 24)) (sum : Expression (F p)) :
      Expression.eval env (rounds.foldl (fun sum (r : Fin 24) => sum + flags[r.val]) sum) =
        rounds.foldl (fun sum (r : Fin 24) => sum + Expression.eval env flags[r.val])
          (Expression.eval env sum) := by
    induction rounds generalizing sum with
    | nil => rfl
    | cons r rounds ih =>
      rw [List.foldl_cons, ih, List.foldl_cons]
      rfl
  unfold iotaBit
  split
  · rfl
  · simp only [Expression.eval_bitXor, Fin.getElem_fin, Vector.getElem_map]
    rw [hfold]

lemma iotaBits_map_eval (env : Environment (F p)) (row : Row (Expression (F p))) :
    iotaBits (row.map (Expression.eval env)) = (iotaBits row).map (Expression.eval env) := by
  ext z hz
  simp [iotaBits, eval_iotaBit]

/-- With the step flags of round `r`, ι's bits are those of the lane xor the round constant. -/
lemma iotaBits_eq {row : Row (F p)} {r : Fin 24} (hflags : row.stepFlags = oneHot r)
    {lane : BitVec 64} (hbits : row.aPrimePrime00Bits = bitsOfLane lane) :
    iotaBits row = bitsOfLane (lane ^^^ roundConstants[r].toBitVec) := by
  ext z hz
  simp only [iotaBits, Vector.getElem_ofFn, hflags, hbits, Fin.getElem_fin,
    getElem_bitsOfLane _ _ hz, iotaBit_oneHot, BitVec.getLsbD_xor]
  rw [Bool.xor_comm]
  rfl

/-- ι's constraints make its cells hold the lane of `A''[0, 0]` and the lane xor the round
constant. -/
theorem spec_of_holds {window : Window Row (F p)} (h : Holds window) : Spec window := by
  refine ⟨fun r hr => ?_, h.next⟩
  have hbits : window.current.aPrimePrime00Bits =
      bitsOfLane (laneOfBits window.current.aPrimePrime00Bits) :=
    (bitsOfLane_laneOfBits h.bits).symm
  refine ⟨_, hbits, ?_, ?_⟩
  · rw [← packed_iff, ← hbits]
    exact h.limbs
  · rw [← packed_iff, ← iotaBits_eq hr hbits]
    exact h.iota

/-- In a round, cells that hold the lane of `A''[0, 0]` and the lane xor the round constant satisfy
ι's constraints. -/
theorem holds_of_spec {window : Window Row (F p)} (h_assumptions : Assumptions window)
    (h : Spec window) : Holds window := by
  obtain ⟨r, hr⟩ := h_assumptions
  obtain ⟨lane, hbits, h00, hout⟩ := h.1 r hr
  refine ⟨fun z => ?_, ?_, ?_, h.2⟩
  · rw [hbits, Fin.getElem_fin, getElem_bitsOfLane _ _ z.isLt]
    exact isBool_ofBool _
  · rw [hbits]
    exact (packed_iff _ _).mpr h00
  · rw [iotaBits_eq hr hbits]
    exact (packed_iff _ _).mpr hout

end Values

@[reducible]
instance elaborated : ElaboratedCircuit (F p) (Window Row) unit main := by
  elaborate_circuit

def circuit : FormalAssertion (F p) (Window Row) where
  name := "iota"
  main
  elaborated
  Assumptions
  Spec
  soundness := by
    intro offset env window_var window h_input _ h_holds
    rw [← h_input, eval_window]
    refine ⟨?_, by simp [main, circuit_norm, PackLimbs.circuit, ConditionalEquality.circuit]⟩
    simp only [main, circuit_norm, PackLimbs.circuit, ConditionalEquality.circuit, Fin.eta]
      at h_holds
    obtain ⟨h_bits, h_limbs, h_iota, h_next⟩ := h_holds
    apply spec_of_holds
    refine ⟨fun z => ?_, fun l => ?_, fun l => ?_, fun h x y => ?_⟩
    · simpa only [provableStructEval_row, mapWindow_current, Row.map_aPrimePrime00Bits,
        Fin.getElem_fin] using h_bits z
    · have := h_limbs l
      rw [eval_packLane] at this
      simpa only [Fin.getElem_fin, mapWindow_current, Row.map_aPrimePrime00Bits,
        Row.map_aPrimePrimeLane] using this
    · have := h_iota l
      rw [eval_packLane, ← iotaBits_map_eval] at this
      simpa only [Fin.getElem_fin, mapWindow_current, Row.map_aPrimePrimePrime00Limbs] using this
    · rw [transitionInPermutation_eval] at h
      simp only [mapWindow_current, mapWindow_next, Row.map_aPrimePrimePrimeLane, Row.map_aLane]
      exact h_next x y h
  completeness := by
    intro offset env window_var _ window h_input h_assumptions h_spec
    rw [← h_input, CircuitType.eval_var_prover_to_verifier, eval_window] at h_assumptions h_spec
    have h := holds_of_spec h_assumptions h_spec
    simp only [main, circuit_norm, PackLimbs.circuit, ConditionalEquality.circuit, Fin.eta]
    refine ⟨fun z => ?_, fun l => ?_, fun l => ?_, fun x y h_gate => ?_⟩
    · simpa only [provableStructEval_row, mapWindow_current, Row.map_aPrimePrime00Bits,
        Fin.getElem_fin] using h.bits z
    · simp only [eval_packLane]
      simpa only [Fin.getElem_fin, mapWindow_current, Row.map_aPrimePrime00Bits,
        Row.map_aPrimePrimeLane] using h.limbs l
    · simp only [eval_packLane, ← iotaBits_map_eval]
      simpa only [Fin.getElem_fin, mapWindow_current, Row.map_aPrimePrimePrime00Limbs] using
        h.iota l
    · have := h.next (by rw [transitionInPermutation_eval]; exact h_gate) x y
      simpa only [mapWindow_current, mapWindow_next, Row.map_aPrimePrimePrimeLane,
        Row.map_aLane] using this

lemma interactions_eq (window : Var (Window Row) (F p)) (offset : ℕ) :
    ((circuit.main window).operations offset).interactions = [] := by
  simp [circuit, main, circuit_norm, FormalAssertion.toSubcircuit_interactions, assertBool,
    PackLimbs.interactions_eq, ConditionalEquality.interactions_eq]

end KeccakAir.Iota
