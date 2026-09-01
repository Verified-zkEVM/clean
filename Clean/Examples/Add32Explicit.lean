import Clean.Utils.Primes
import Clean.Circuit.Explicit
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Examples.AddOperations
import Clean.Gadgets.Boolean

open Gadgets.Addition32Full (Inputs Outputs)

@[implicit_reducible]
def circuit32 input := Gadgets.Addition32Full.main (p:=pBabybear) input

-- `infer_explicit_circuit(s)` seem to work for all circuits
@[reducible]
instance explicit : ExplicitCircuits circuit32 := by
  infer_explicit_circuits

@[reducible]
instance elaborated : ElaboratedCircuit (F pBabybear) Inputs Outputs circuit32 := by
  elaborate_circuit_naive

@[implicit_reducible]
def circuit32Reduced input := Gadgets.Addition32Full.main (p:=pBabybear) input

@[reducible]
instance reducedElaborated : ElaboratedCircuit (F pBabybear) Inputs Outputs circuit32Reduced := by
  elaborate_circuit

-- These only unfold the generated elaborated instance. They do not unfold or simplify the explicit
-- circuit derivation, so they check that the reduced tactic stores the nice metadata directly.
example : ElaboratedCircuit.localLength (F:=F pBabybear) (Input:=Inputs) (Output:=Outputs) circuit32Reduced default = 8 := by
  dsimp +instances only [reducedElaborated, explicit_circuit_norm, circuit32Reduced,
    Gadgets.Addition32Full.main, Gadgets.Addition8FullCarry.circuit, assertBool]

example : ElaboratedCircuit.output (F:=F pBabybear) (Input:=Inputs) (Output:=Outputs) circuit32Reduced default 0 =
  { z := ⟨ varFromOffset field 0, varFromOffset field 2, varFromOffset field 4, varFromOffset field 6 ⟩,
    carryOut := varFromOffset field 7 } := by
  dsimp +instances only [reducedElaborated, explicit_circuit_norm, circuit32Reduced,
    Gadgets.Addition32Full.main, Gadgets.Addition8FullCarry.circuit, assertBool]

-- #whnf elaborated.localLength default
-- #whnf elaborated.output default 0
-- #whnf explicit.operations default default

example : ExplicitCircuit.localLength (circuit32 default) 0 = 8 := rfl
example : ExplicitCircuit.localLength (circuit32 default) 0 = 8 := by
  dsimp +instances only [explicit_circuit_norm, explicit, circuit32,
    Gadgets.Addition32Full.main, Gadgets.Addition8FullCarry.circuit, assertBool]

example : ExplicitCircuit.output (circuit32 default) 0 =
  { z := ⟨ varFromOffset field 0, varFromOffset field 2, varFromOffset field 4, varFromOffset field 6 ⟩,
    carryOut := varFromOffset field 7 } := rfl
example : ExplicitCircuit.output (circuit32 default) 0 =
  { z := ⟨ varFromOffset field 0, varFromOffset field 2, varFromOffset field 4, varFromOffset field 6 ⟩,
    carryOut := varFromOffset field 7 } := by
  dsimp +instances only [explicit_circuit_norm, explicit, circuit32,
    Gadgets.Addition32Full.main, Gadgets.Addition8FullCarry.circuit, assertBool]

example : ExplicitCircuit.channelsWithGuarantees (circuit32 default) 0 = [] := rfl
example : ExplicitCircuit.channelsWithGuarantees (circuit32 default) 0 = [] := by
  dsimp +instances only [explicit_circuit_norm, explicit, circuit32,
    Gadgets.Addition32Full.main, Gadgets.Addition8FullCarry.circuit, assertBool]

example : ((circuit32 default).operations 0).SubcircuitsConsistent 0 :=
  ExplicitCircuits.subcircuitsConsistent ..

example (x0 x1 x2 x3 y0 y1 y2 y3 carryIn : Expression (F pBabybear)) env (i0 : ℕ) :
  ConstraintsHold.Soundness env ((circuit32 ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩, carryIn ⟩).operations i0)
  ↔
  let limbHolds (offset : ℕ) (x y carryIn : F pBabybear) :=
    Gadgets.Addition8FullCarry.Assumptions { x, y, carryIn } →
      Gadgets.Addition8FullCarry.Spec { x, y, carryIn }
        { z := env.get offset, carryOut := env.get (offset + 1) }
  limbHolds i0 (Expression.eval env x0) (Expression.eval env y0) (Expression.eval env carryIn) ∧
  limbHolds (i0 + 2) (Expression.eval env x1) (Expression.eval env y1) (env.get (i0 + 1)) ∧
  limbHolds (i0 + 4) (Expression.eval env x2) (Expression.eval env y2) (env.get (i0 + 3)) ∧
  limbHolds (i0 + 6) (Expression.eval env x3) (Expression.eval env y3) (env.get (i0 + 5)) := by

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
  rw [ExplicitCircuits.operations_eq (circuit := circuit32)]
  dsimp +instances only [explicit_circuit_norm, explicit, circuit32,
    Gadgets.Addition32Full.main, Gadgets.Addition8FullCarry.circuit, assertBool]
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset, circuit_norm]
