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

-- helper for proofs below: the linear combination is equivalent `fieldFromBits`
lemma lc_eq {env} {n : ℕ} (bits : Vector (Expression (F p)) n) :
  (eval (α:=fieldPair) env <|
    Fin.foldl n (fun (lc1, e2) i => (lc1 + bits[i] * e2, e2 + e2)) (0, 1))
    = (fieldFromBits (bits.map env), 2^n) := by
  simp only [fieldFromBits, fromBits, Vector.getElem_map]
  induction n with
  | zero => simp [circuit_norm]
  | succ n ih =>
    simp_all only [circuit_norm, Fin.foldl_succ_last, Prod.mk.injEq]
    specialize ih bits.pop
    simp only [Vector.getElem_pop'] at ih
    simp only [Fin.coe_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_mul, ZMod.natCast_val,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [ih.left, ih.right]; clear ih
    simp_all [circuit_norm, Fin.foldl_succ_last, pow_succ', two_mul]
    sorry

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
    simp_all only [circuit_norm, main, Gadgets.toBits, Gadgets.ToBits.main, fieldFromBitsExpr]
    constructor
    · intro i
      simp only [circuit_norm, subcircuit_norm, Boolean.circuit]
      simpa [add_neg_eq_zero] using h_holds.left i
    rw [←h_holds.right]; clear h_holds
    -- we have to strengthen the goal for the induction
    suffices (eval (α:=fieldPair) env <| Fin.foldl n (fun ((lc1, e2) :  Expression (F p) × Expression (F p)) j =>
      (lc1 + (var ⟨i0 + j.val⟩) * e2, e2 + e2)) (0, 1))
        = (Expression.eval env <| Fin.foldl n (fun acc j => acc + var ⟨i0 + j.val⟩ * Expression.const (2^j.val)) 0, 2^n) by
      simp only [circuit_norm, Prod.mk.injEq, Fin.foldl_eq_foldl_finRange] at this ⊢
      exact this.left
    induction n with
    | zero => simp [circuit_norm]
    | succ n ih =>
      have : 2^n < 2^(n+1) := by gcongr; repeat simp
      specialize ih (by linarith)
      simp_all [circuit_norm, Fin.foldl_succ_last, pow_succ', two_mul]

  completeness := by
    intro i0 env input_var h_env input h_input h_holds
    simp only [circuit_norm, main, fieldToBits, toBits] at *
    simp only [h_input, Nat.and_one_is_mod, Vector.getElem_ofFn,
      id_eq, mul_eq_zero, add_neg_eq_zero, fieldToBits] at h_env ⊢
    clear h_input
    constructor
    · intro i
      simp_all only
      set k := (input.val >>> i.val) % 2 with hk
      have lt_2 : k < 2 := Nat.mod_lt (input.val >>> i.val) (by linarith)
      match k with
      | 0 | 1 => simp [fieldToBits, toBits, Vector.getElem_mapRange]
      | k + 2 => nomatch lt_2
    -- move the .1 outside to we can use `List.foldl_hom`
    suffices (eval (α:=fieldPair) env (List.foldl (fun ((lc1, e2) :  Expression (F p) × Expression (F p)) i =>
        (lc1 + (var ⟨i0 + i.val⟩) * e2, e2 + e2)) (0, 1) (List.finRange n))).1 = input by
      stop
      simpa [circuit_norm]
    rw [←List.foldl_hom (eval env) (g₂ := fun (lc1, e2) i => (lc1 + env.get (i0 + i.val) * e2, e2 + e2))]
    rotate_left
    · simp only [circuit_norm]
    simp only [h_env]; clear h_env
    sorry
end Num2Bits

#check List.foldl_hom

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
