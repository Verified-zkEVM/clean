import Clean.Utils.Primes
import Clean.Circuit.Explicit
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Examples.AddOperations
import Clean.Gadgets.Boolean

open Gadgets.Addition32Full (Inputs)

-- `infer_explicit_circuit(s)` seem to work for all circuits
instance explicit : ExplicitCircuits (Gadgets.Addition32Full.main (p :=pBabybear)) := by
  infer_explicit_circuits

@[reducible] def circuit32 input := Gadgets.Addition32Full.main (p :=pBabybear) input

example : ExplicitCircuit.localLength (circuit32 default) 0 = 8 := by
  -- rfl -- also works
  dsimp only [explicit_circuit_norm, explicit, assertBool]

example : ExplicitCircuit.output (circuit32 default) 0
    = { z := ⟨ var ⟨0⟩, var ⟨2⟩, var ⟨4⟩, var ⟨6⟩ ⟩, carryOut := var ⟨7⟩ } := by
  -- rfl -- also works
  dsimp only [explicit_circuit_norm, explicit, ProvableType.varFromOffset_field, assertBool]

example : ((circuit32 default).operations 0).SubcircuitsConsistent 0 :=
  ExplicitCircuits.subcircuitsConsistent ..

example (x0 x1 x2 x3 y0 y1 y2 y3 carryIn : Var field (F pBabybear)) env (i0 : ℕ) :
  Circuit.ConstraintsHold.Soundness env ((circuit32 ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩, carryIn ⟩).operations i0)
  ↔
  (ZMod.val (env.get i0) < 256 ∧ IsBool (env.get (i0 + 1)) ∧
    Expression.eval env x0 + Expression.eval env y0 + Expression.eval env carryIn + -env.get i0 + -(env.get (i0 + 1) * 256) = 0) ∧
  (ZMod.val (env.get (i0 + 2)) < 256 ∧ IsBool (env.get (i0 + 3)) ∧
    Expression.eval env x1 + Expression.eval env y1 + env.get (i0 + 1) + -env.get (i0 + 2) + -(env.get (i0 + 3) * 256) = 0) ∧
  (ZMod.val (env.get (i0 + 4)) < 256 ∧ IsBool (env.get (i0 + 5)) ∧
    Expression.eval env x2 + Expression.eval env y2 + env.get (i0 + 3) + -env.get (i0 + 4) + -(env.get (i0 + 5) * 256) = 0) ∧
  (ZMod.val (env.get (i0 + 6)) < 256 ∧ IsBool (env.get (i0 + 7)) ∧
    Expression.eval env x3 + Expression.eval env y3 + env.get (i0 + 5) + -env.get (i0 + 6) + -(env.get (i0 + 7) * 256) = 0) := by

  -- these are equivalent ways of rewriting the constraints
  -- the second one relies on prior inference of a `ExplicitCircuit` instance
  -- note that the second one only uses a handful of theorems (much fewer than `circuit_norm`)
  -- for 90% of the unfolding; and doesn't even need to unfold names like `Addition32Full.main` and `Addition8FullCarry.main`

  -- TODO on the whole, which is better?

  -- first version: using `circuit_norm`
  -- dsimp only [circuit_norm, circuit32, Addition32Full.main, Addition8FullCarry.main, Gadgets.ByteTable]
  -- simp only [circuit_norm, Nat.reduceAdd, and_assoc]
  -- simp only [Gadgets.ByteTable]

  -- second version: using `ExplicitCircuit`
  -- resolve explicit circuit operations
  rw [ExplicitCircuit.operations_eq]
  dsimp only [explicit_circuit_norm, explicit, assertBool]
  -- simp `ConstraintsHold` expression
  simp only [Circuit.ConstraintsHold.append_soundness, Circuit.ConstraintsHold.Soundness, Gadgets.ByteTable]
  -- simp boolean subcircuit soundness and logical/arithmetic/vector expressions
  simp only [circuit_norm, Nat.reduceAdd]
