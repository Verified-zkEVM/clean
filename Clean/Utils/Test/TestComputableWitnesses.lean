module

public import Clean.Gadgets.BLAKE3.Compress
public import Clean.Gadgets.Keccak.ThetaD
public import Clean.Gadgets.Keccak.RhoPi
public import Clean.Gadgets.Rotation32.Rotation32
public import Clean.Gadgets.Rotation64.Rotation64
public import Clean.Gadgets.Addition32.Addition32Full
public import Clean.Gadgets.SHA256.Xor32
public import Clean.Gadgets.IsZero
public import Clean.Circomlib.Mux1

@[expose] public section

/-!
Regression suite for `computable_witnesses`: representative obligations the tactic must keep
closing without hints, stated as examples so that a tactic change is validated against the whole
spectrum in one fast check instead of a full library build.
-/

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 2^16 + 2^8)]

-- two-node FormalCircuit chain with a struct input (child output feeding a struct field)
example : FormalCircuitBase.ComputableWitnesses (F := F p) Gadgets.BLAKE3.Compress.main := by
  computable_witnesses

-- ten-node Rotation64/Xor64 chain
example : FormalCircuitBase.ComputableWitnesses (F := F p) Gadgets.Keccak256.ThetaD.main := by
  computable_witnesses

-- mapIdx over child-output windows
example : FormalCircuitBase.ComputableWitnesses (F := F p) Gadgets.Keccak256.RhoPi.main := by
  computable_witnesses

-- Fin-parametrized two-node chains
example (off : Fin 32) :
    FormalCircuitBase.ComputableWitnesses (F := F p) (Gadgets.Rotation32.main off) := by
  computable_witnesses

example (off : Fin 64) :
    FormalCircuitBase.ComputableWitnesses (F := F p) (Gadgets.Rotation64.main off) := by
  computable_witnesses

-- byte-decomposed witness computations
example : FormalCircuitBase.ComputableWitnesses (F := F p) Gadgets.Addition32Full.main := by
  computable_witnesses

-- per-limb map circuit
example : FormalCircuitBase.ComputableWitnesses (F := F p) Gadgets.SHA256.Xor32.main := by
  computable_witnesses

-- vector `<==` over a mapped input
example (n : ℕ) : FormalCircuitBase.ComputableWitnesses (F := F p)
    (Input := Circomlib.MultiMux1.Inputs n) (Output := fields n) (Circomlib.MultiMux1.main n) := by
  computable_witnesses

end

section
variable {F : Type} [FiniteField F] [DecidableEq F] {M : TypeMap} [ProvableType M]

-- generic-typemap gadget with symbolic sizes
example [DecidableEq (M F)] :
    FormalCircuitBase.ComputableWitnesses (Gadgets.IsZero.main (F := F) (M := M)) := by
  computable_witnesses

end
