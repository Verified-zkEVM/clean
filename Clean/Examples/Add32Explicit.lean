import Clean.Utils.Primes
import Clean.Circuit.Explicit
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Examples.AddOperations

open Gadgets.Addition8FullCarry (add8_full_carry)
open Gadgets.Addition32Full (add32_full Inputs)

-- `infer_explicit_circuit(s)` seem to work for all circuits
instance explicit : ExplicitCircuits (add32_full (p:=p)) := by
  infer_explicit_circuits

@[reducible] def circuit32 input := add32_full (p:=p) input

example : ExplicitCircuit.local_length (circuit32 default) 0 = 8 := by
  -- rfl -- also works
  dsimp only [explicit_circuit_norm, explicit, Boolean.circuit]

example : ExplicitCircuit.output (circuit32 default) 0
    = { z := ⟨ var ⟨0⟩, var ⟨2⟩, var ⟨4⟩, var ⟨6⟩ ⟩, carry_out := var ⟨7⟩ } := by
  -- rfl -- also works
  dsimp only [explicit_circuit_norm, explicit, Boolean.circuit]

example : ((circuit32 default).operations 0).SubcircuitsConsistent 0 :=
  ExplicitCircuits.subcircuits_consistent ..

example (x0 x1 x2 x3 y0 y1 y2 y3 carry_in : Var field (F p)) env (i0 : ℕ) :
  Circuit.constraints_hold.soundness env ((circuit32 ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩, carry_in ⟩).operations i0)
  ↔
  (ZMod.val (env.get i0) < 256 ∧ (env.get (i0 + 1) = 0 ∨ env.get (i0 + 1) = 1) ∧
    Expression.eval env x0 + Expression.eval env y0 + Expression.eval env carry_in + -env.get i0 + -(env.get (i0 + 1) * 256) = 0) ∧
  (ZMod.val (env.get (i0 + 2)) < 256 ∧ (env.get (i0 + 3) = 0 ∨ env.get (i0 + 3) = 1) ∧
    Expression.eval env x1 + Expression.eval env y1 + env.get (i0 + 1) + -env.get (i0 + 2) + -(env.get (i0 + 3) * 256) = 0) ∧
  (ZMod.val (env.get (i0 + 4)) < 256 ∧ (env.get (i0 + 5) = 0 ∨ env.get (i0 + 5) = 1) ∧
    Expression.eval env x2 + Expression.eval env y2 + env.get (i0 + 3) + -env.get (i0 + 4) + -(env.get (i0 + 5) * 256) = 0) ∧
  (ZMod.val (env.get (i0 + 6)) < 256 ∧ (env.get (i0 + 7) = 0 ∨ env.get (i0 + 7) = 1) ∧
    Expression.eval env x3 + Expression.eval env y3 + env.get (i0 + 5) + -env.get (i0 + 6) + -(env.get (i0 + 7) * 256) = 0) := by

  -- these are equivalent ways of rewriting the constraints
  -- the second one relies on prior inference of a `ExplicitCircuit` instance
  -- note that the second one only uses a handful of theorems (much fewer than `circuit_norm` + `subcircuit_norm`)
  -- for 90% of the unfolding; and doesn't even need to unfold names like `add32_full` and `add8_full_carry`

  -- TODO on the whole, which is better?

  -- first version: using `circuit_norm`
  -- dsimp only [circuit_norm, circuit32, add32_full, add8_full_carry, Boolean.circuit, Gadgets.ByteLookup]
  -- simp only [subcircuit_norm, circuit_norm, Nat.reduceAdd, and_assoc]
  -- simp only [Gadgets.ByteTable]

  -- second version: using `ExplicitCircuit`
  -- resolve explicit circuit operations
  rw [ExplicitCircuit.operations_eq]
  dsimp only [explicit_circuit_norm, explicit, Boolean.circuit]
  -- simp `constraints_hold` expression
  simp only [Circuit.constraints_hold.append_soundness, Circuit.constraints_hold.soundness, Gadgets.ByteTable]
  -- simp boolean subcircuit soundness and logical/arithmetic/vector expressions
  simp only [subcircuit_norm, circuit_norm, Nat.reduceAdd]
