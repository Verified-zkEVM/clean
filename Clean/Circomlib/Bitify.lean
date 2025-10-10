import Clean.Circuit
import Clean.Utils.Bits
import Clean.Gadgets.Bits

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/bitify.circom

Note: `Num2Bits_strict`, `Bits2Num_strict` and `Num2BitsNeg` are in `Bitify2.lean`,
because having them here would have caused cyclic import dependencies,
which Lean does not allow.
-/

namespace Num2Bits
/-
template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    var e2=1;
    for (var i = 0; i < n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === in;
}
-/
def main (n : ℕ) (inp : Expression (F p)) := do
  let out ← witnessVector n fun env => fieldToBits n (inp.eval env)

  let (lc1, _) ← Circuit.foldlRange n (0, 1) fun (lc1, e2) i => do
    out[i] * (out[i] - 1) === 0
    let lc1 := lc1 + out[i] * e2
    return (lc1, e2 + e2)

  lc1 === inp
  return out

-- helper for proofs below: the linear combination is equivalent to `fieldFromBits`
omit [Fact (p > 2)] in
lemma lc_eq {i0} {env} {n : ℕ} :
  (Expression.eval env <| Prod.fst <|
    Fin.foldl n (fun (lc1, e2) i => (lc1 + (var (F:=F p) ⟨ i0 + ↑i ⟩) * e2, e2 + e2)) (0, 1))
    = fieldFromBits (Vector.mapRange n fun i => env.get (i0 + i)) := by
  suffices (eval (α:=fieldPair) env <|
    Fin.foldl n (fun (lc1, e2) i => (lc1 + (var (F:=F p) ⟨ i0 + ↑i ⟩) * e2, e2 + e2)) (0, 1))
    = (fieldFromBits (Vector.mapRange n fun i => env.get (i0 + i)), 2^n) by
    simp_all [circuit_norm]
  simp only [fieldFromBits, fromBits, Vector.getElem_map]
  induction n with
  | zero => simp [circuit_norm]
  | succ n ih =>
    simp_all only [circuit_norm, Prod.mk.injEq, Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last,
      Expression.eval, Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, Nat.cast_pow, Nat.cast_ofNat,
      pow_succ', two_mul, add_right_inj, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq, and_true]
    left
    rw [ZMod.cast_id]

def arbitraryBitLengthCircuit (n : ℕ) : GeneralFormalCircuit (F p) field (fields n) where
  main := main n
  localLength _ := n
  localLength_eq := by simp +arith [circuit_norm, main]
  yields_eq := by intros; simp [circuit_norm, main]
  output _ i := varFromOffset (fields n) i

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input _ := input.val < 2^n

  /- without further assumptions on n, this circuit just tells us that the output bits represent
    _some_ number congruent to the input modulo p -/
  Spec input _ bits _ :=
    input.val < 2^n
    ∧ (∀ i (_ : i < n), bits[i] = 0 ∨ bits[i] = 1)
    ∧ fieldFromBits bits = input

  soundness := by
    circuit_proof_start
    simp only [lc_eq] at h_holds
    rw [← h_holds.right]
    and_intros
    · apply fieldFromBits_lt
      intro i hi
      simp only [circuit_norm]
      simpa [add_neg_eq_zero] using h_holds.left ⟨i, hi⟩
    · intro i hi
      simpa [add_neg_eq_zero] using h_holds.left ⟨i, hi⟩
    · congr 1
      rw [Vector.ext_iff]
      simp [circuit_norm]

  completeness := by
    circuit_proof_start
    simp only [lc_eq, Fin.forall_iff, id_eq, mul_eq_zero, add_neg_eq_zero] at h_env ⊢
    let bits := Vector.mapRange n fun i => env.get (i₀ + i)
    constructor
    · intro i hi; simp [h_env i hi, fieldToBits, toBits, Vector.getElem_mapRange]
    show fieldFromBits bits = input
    have : bits = fieldToBits n input := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [← h_env i hi, bits, Vector.getElem_mapRange]
    rw [this, fieldFromBits_fieldToBits h_assumptions]

-- the main circuit implementation makes a stronger statement assuming 2^n < p
def circuit (n : ℕ) (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n) where
  main input := arbitraryBitLengthCircuit n input
  localLength _ := n
  output _ i := varFromOffset (fields n) i
  yields_eq := by intros; simp only [circuit_norm, arbitraryBitLengthCircuit, Set.empty_union]

  Assumptions input _ := input.val < 2^n

  Spec input _ output _ :=
    input.val < 2^n ∧ output = fieldToBits n input

  soundness := by
    circuit_proof_start [arbitraryBitLengthCircuit]
    simp_all only [true_and]
    rcases h_holds with ⟨ _, h_bits, h_holds ⟩
    rw [← h_holds, fieldToBits_fieldFromBits hn]
    simpa [circuit_norm] using h_bits

  completeness := by
    circuit_proof_all [arbitraryBitLengthCircuit]

end Num2Bits

namespace Bits2Num
/-
template Bits2Num(n) {
    signal input in[n];
    signal output out;
    var lc1=0;

    var e2 = 1;
    for (var i = 0; i < n; i++) {
        lc1 += in[i] * e2;
        e2 = e2 + e2;
    }

    lc1 ==> out;
}
-/
def main (n : ℕ) (input : Vector (Expression (F p)) n) := do
  let (lc1, _) := Fin.foldl n (fun (lc1, e2) i =>
    let lc1 := lc1 + input[i] * e2
    let e2 := e2 + e2
    (lc1, e2)) (0, 1)

  let out <== lc1
  return out

omit [Fact (p > 2)] in
lemma lc_eq {env} {n : ℕ} {v : Vector (Expression (F p)) n} :
  (Expression.eval env <| Prod.fst <|
    Fin.foldl n (fun ((lc1, e2) : Expression (F p) × Expression (F p)) i =>
      (lc1 + v[↑i] * e2, e2 + e2)) (0, 1))
    = fieldFromBits (Vector.mapFinRange n fun i => v[↑i].eval env) := by
  suffices (eval (α:=fieldPair) env <|
    Fin.foldl n (fun (lc1, e2) i => (lc1 + v[↑i] * e2, e2 + e2)) (0, 1))
    = (fieldFromBits (Vector.mapFinRange n fun i => v[↑i].eval env), 2^n) by
    simp_all [circuit_norm]
  simp only [fieldFromBits, fromBits, Vector.getElem_map, Vector.getElem_mapFinRange]
  induction n with
  | zero => simp [circuit_norm]
  | succ n ih =>
    specialize ih (v := v.pop)
    simp only [Fin.getElem_fin, Vector.getElem_pop', Fin.eta] at ih
    simp_all only [circuit_norm, Fin.foldl_succ_last, Prod.mk.injEq, pow_succ', two_mul,
      Fin.coe_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_mul, ZMod.natCast_val,
      Nat.cast_pow, Nat.cast_ofNat, Prod.mk.injEq]
    rw [ZMod.cast_id]

def circuit (n : ℕ) : FormalCircuit (F p) (fields n) field where
  main := main n
  localLength _  := 1
  localLength_eq := by simp [circuit_norm, main]
  yields _ _ _ := ∅
  yields_eq := by intros; simp only [circuit_norm, main, Set.empty_union]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input _ :=
    ∀ i (_ : i < n), input[i] = 0 ∨ input[i] = 1

  Spec input output _ :=
    output = fieldFromBits input
    ∧ output.val < 2^n

  soundness := by
    circuit_proof_start
    set output : (F p) := (env.get i₀)

    change output = Expression.eval env (Fin.foldl n
      (fun (lc1, e2) i => (lc1 + input_var[↑i] * e2, e2 + e2)) (0, 1)).1
    at h_holds
    rw [lc_eq] at h_holds

    have h1 : Vector.mapFinRange n (fun i ↦ input_var[i].eval env) = input := by
      rw [← h_input]
      ext i hi
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, Fin.getElem_fin]

    rw [h1] at h_holds
    simp only [h_holds, true_and]
    apply fieldFromBits_lt _ h_assumptions

  completeness := by circuit_proof_all
end Bits2Num

end Circomlib
