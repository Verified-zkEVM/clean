import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/compconstant.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]

namespace CompConstant
/-
template CompConstant(ct) {
    signal input in[254];
    signal output out;

    signal parts[127];
    signal sout;

    var clsb;
    var cmsb;
    var slsb;
    var smsb;

    var sum=0;

    var b = (1 << 128) -1;
    var a = 1;
    var e = 1;
    var i;

    for (i=0;i<127; i++) {
        clsb = (ct >> (i*2)) & 1;
        cmsb = (ct >> (i*2+1)) & 1;
        slsb = in[i*2];
        smsb = in[i*2+1];

        if ((cmsb==0)&&(clsb==0)) {
            parts[i] <== -b*smsb*slsb + b*smsb + b*slsb;
        } else if ((cmsb==0)&&(clsb==1)) {
            parts[i] <== a*smsb*slsb - a*slsb + b*smsb - a*smsb + a;
        } else if ((cmsb==1)&&(clsb==0)) {
            parts[i] <== b*smsb*slsb - a*smsb + a;
        } else {
            parts[i] <== -a*smsb*slsb + a;
        }

        sum = sum + parts[i];

        b = b -e;
        a = a +e;
        e = e*2;
    }

    sout <== sum;

    component num2bits = Num2Bits(135);

    num2bits.in <== sout;

    out <== num2bits.out[127];
}
-/
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (ct : ℕ) (input : Vector (Expression (F p)) 254) : Circuit sentences (Expression (F p)) := do
  let parts : fields 127 (Expression (F p)) <==[order] Vector.ofFn fun i =>
    let clsb := (ct >>> (i.val * 2)) &&& 1
    let cmsb := (ct >>> (i.val * 2 + 1)) &&& 1
    let slsb := input[i.val * 2]
    let smsb := input[i.val * 2 + 1]

    -- Compute b, a values for this iteration
    let b_val : ℤ := 2^128 - 2^i.val
    let a_val : ℤ := 2^i.val

    if cmsb == 0 && clsb == 0 then
      -(b_val : F p) * smsb * slsb + (b_val : F p) * smsb + (b_val : F p) * slsb
    else if cmsb == 0 && clsb == 1 then
      (a_val : F p) * smsb * slsb - (a_val : F p) * slsb + (b_val : F p) * smsb - (a_val : F p) * smsb + (a_val : F p)
    else if cmsb == 1 && clsb == 0 then
      (b_val : F p) * smsb * slsb - (a_val : F p) * smsb + (a_val : F p)
    else
      -(a_val : F p) * smsb * slsb + (a_val : F p)

  -- Compute sum
  let sout <==[order] parts.sum

  -- Convert sum to bits
  have hp : p > 2^135 := by linarith [‹Fact (p > 2^253)›.elim]
  let bits ← Num2Bits.circuit order 135 hp sout

  let out <==[order] bits[127]
  return out

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : fields 254 (F p)) :=
  ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (c : ℕ) : FormalCircuit order (fields 254) field where
  main := main order c
  localLength _ := 127 + 1 + 135 + 1  -- parts witness + sout witness + Num2Bits + out witness
  localLength_eq := by simp only [circuit_norm, main, Num2Bits.circuit]
  subcircuitsConsistent input n := by
    simp only [circuit_norm, main, Num2Bits.circuit]
    and_intros <;> ac_rfl

  Assumptions input :=
    ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1

  CompletenessAssumptions := CompletenessAssumptions

  completenessAssumptions_implies_assumptions _ _ h := h

  Spec _ bits output :=
    output = if fromBits (bits.map ZMod.val) > c then 1 else 0

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main, Num2Bits.circuit, CompletenessAssumptions]
    sorry
end CompConstant

end Circomlib
