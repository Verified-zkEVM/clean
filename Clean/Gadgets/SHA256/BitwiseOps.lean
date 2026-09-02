import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Utils.Primes
import Clean.Utils.Bits

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# 32-bit Bitwise Operations for SHA-256

All operations work on `fields 32`, where each field element represents one bit (boolean).
Bit 0 is the least-significant bit (LSB-first convention).

No lookup tables are used; all operations are expressed as R1CS constraints.
-/

/-- State: 8 boolean 32-bit words. -/
abbrev SHA256State := ProvableVector (fields 32) 8

/-- Block: 16 boolean 32-bit words. -/
abbrev SHA256Block := ProvableVector (fields 32) 16

/-- Message schedule: 64 boolean 32-bit words. -/
abbrev SHA256Schedule := ProvableVector (fields 32) 64

/-- Interpret a bit vector as a natural number (LSB at index 0). -/
def valueBits (bits : Vector (F p) 32) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => bits[i].val * 2^i.val

/-- All bits are boolean (0 or 1). -/
def Normalized (w : Vector (F p) 32) : Prop :=
  ∀ i : Fin 32, w[i] = 0 ∨ w[i] = 1

/-- The linear combination of bits as an expression: Σ bits[i] · 2^i (LSB first) -/
abbrev fromBitsExpr (bits : Var (fields 32) (F p)) : Expression (F p) :=
  Utils.Bits.fieldFromBitsExpr bits

/-- A constant 32-bit word from a natural number (LSB-first bit decomposition). -/
def constWord32 (n : ℕ) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) => ((n / 2^i.val % 2 : ℕ) : F p)

/-!
## Pure combinators (no witnesses, no constraints)
-/

/-- Bitwise NOT: maps each bit a[i] ↦ 1 − a[i]. -/
def not32 (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  a.map fun ai => (1 : Expression (F p)) - ai

/-- Rotate right by `k` bits (mod 32): z[i] = a[(i + k) mod 32]. -/
def rotr32 (k : Fin 32) (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  a.rotate k

/-- Shift right by `k` bits: z[i] = a[i + k] if i + k < 32, else 0. -/
def shr32 (k : Fin 32) (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) =>
    if h : i.val + k.val < 32
    then a[i.val + k.val]'h
    else (0 : Expression (F p))

omit [Fact (p > 2)] in
/-- `fields`-valued outputs are decomposed to `Vector.map` by `circuit_norm`, which splits
the composite-eval atom that `FormalCircuit.output_of_input_eq` is keyed on; this restates
output congruence under env agreement in the map spelling. -/
theorem output_map_eval_congr {Input : TypeMap} [ProvableType Input] {sz : ℕ}
    (circuit : FormalCircuit (F p) Input (fields sz))
    {input_var : Var Input (F p)} {env env' : ProverEnvironment (F p)} {n m : ℕ}
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var)
    (h_agrees : env.AgreesBelow m env')
    (hm : n + circuit.localLength input_var ≤ m) :
    Vector.map (Expression.eval env.toEnvironment) (circuit.output input_var n) =
      Vector.map (Expression.eval env'.toEnvironment) (circuit.output input_var n) := by
  have h := FormalCircuit.output_of_input_eq circuit input_eq
    (ProverEnvironment.agreesBelow_of_le h_agrees hm)
  simp only [circuit_norm, ProvableType.eval_fields] at h
  exact h

grind_pattern output_map_eval_congr =>
  Vector.map (Expression.eval env.toEnvironment) (circuit.output input_var n),
  ProverEnvironment.AgreesBelow m env env'

omit [Fact (p > 2)] in
/-- Elementwise (map-spelled) consequence of a composite schedule eval equality. -/
theorem map_eval_getElem_congr {env env' : ProverEnvironment (F p)} {m : ℕ}
    {xs : Vector (fields 32 (Expression (F p))) m}
    (hxs : (eval env.toEnvironment xs : Vector (fields 32 (F p)) m) = eval env'.toEnvironment xs)
    (i : ℕ) (hi : i < m) :
    Vector.map (Expression.eval env.toEnvironment) xs[i] =
      Vector.map (Expression.eval env'.toEnvironment) xs[i] := by
  simp only [eval_vector] at hxs
  have h := congrArg (fun v => v[i]'hi) hxs
  simp only [Vector.getElem_map] at h
  simp only [ProvableType.eval_fields] at h
  exact h

end Gadgets.SHA256
end
