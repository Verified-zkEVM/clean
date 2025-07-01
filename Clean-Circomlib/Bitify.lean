import Clean.Circuit
import Clean.Utils.Bits
import Clean.Gadgets.Bits

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Note: `Num2Bits_strict` and `Bits2Num_strict` are moved to `AliasCheck.lean` because
having them here would have caused a cyclic import dependency, which Lean does not allow.
-/

namespace Num2Bits
/-
template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    var e2=1;
    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === in;
}
-/
def main (n: ℕ) (inp : Expression (F p)) := do
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

def circuit (n : ℕ) (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n) where
  main := main n
  localLength _ := n
  localLength_eq := by simp +arith [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := input.val < 2^n
  Spec input output :=
    input.val < 2^n ∧ output = fieldToBits n input

  soundness := by
    intro i0 env input_var input h_input h_holds
    apply (Gadgets.toBits n hn).soundness i0 env input_var input h_input
    simp_all only [circuit_norm, main, Gadgets.toBits, Gadgets.ToBits.main]
    constructor
    · intro i
      simp only [circuit_norm, subcircuit_norm, Boolean.circuit]
      simpa [add_neg_eq_zero] using h_holds.left i
    rw [←h_holds.right, lc_eq]; clear h_holds
    show _ = env (fieldFromBitsExpr _)
    rw [fieldFromBits_eval]
    congr
    rw [Vector.ext_iff]
    simp [circuit_norm]

  completeness := by
    intro i0 env input_var h_env input h_input h_holds
    simp only [circuit_norm, main] at *
    simp only [lc_eq, h_input, id_eq, mul_eq_zero, add_neg_eq_zero, Fin.forall_iff] at h_env ⊢
    let bits := Vector.mapRange n fun i => env.get (i0 + i)
    constructor
    · intro i hi; simp [h_env i hi, fieldToBits, toBits, Vector.getElem_mapRange]
    show fieldFromBits bits = input
    suffices bits = fieldToBits n input by
      rw [this, fieldFromBits_fieldToBits hn h_holds]
    rw [Vector.ext_iff]
    intro i hi
    simp only [← h_env i hi, bits, Vector.getElem_mapRange]
end Num2Bits

namespace Bits2Num
/-
template Bits2Num(n) {
    signal input in[n];
    signal output out;
    var lc1=0;

    var e2 = 1;
    for (var i = 0; i<n; i++) {
        lc1 += in[i] * e2;
        e2 = e2 + e2;
    }

    lc1 ==> out;
}
-/
def main (n: ℕ) (input : Vector (Expression (F p)) n) := do
  let (lc1, _) := Fin.foldl n (fun (lc1, e2) i =>
    let lc1 := lc1 + input[i] * e2
    let e2 := e2 + e2
    (lc1, e2)) (0, 1)

  let out ← witnessField fun env => lc1.eval env
  out === lc1
  return out

def circuit (n : ℕ) (hn : 2^n < p) : GeneralFormalCircuit (F p) (fields n) field where
  main := main n
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end Bits2Num

end Circomlib
