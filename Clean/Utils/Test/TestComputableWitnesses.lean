import Clean.Gadgets.BLAKE3.Compress
import Clean.Gadgets.Keccak.ThetaD
import Clean.Gadgets.Keccak.RhoPi
import Clean.Gadgets.Rotation32.Rotation32
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Gadgets.SHA256.Xor32
import Clean.Gadgets.IsZero
import Clean.Circomlib.Mux1

/-!
Regression suite for `computable_witnesses`: the representative obligations the tactic
must keep closing, stated as examples so any tactic change is validated against the
whole spectrum in one fast check instead of a full library build. Hints mirror the
corresponding circuit fields, plus the `main` of each gadget (outside its namespace,
`unfold main` cannot resolve it).
-/

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 2^16 + 2^8)]

-- two-node FormalCircuit chain with a struct input (child output feeding a struct field)
open Gadgets.BLAKE3.Compress in
example : FormalCircuitBase.ComputableWitnesses (F := F p) main := by
  computable_witnesses [Gadgets.BLAKE3.Compress.main]

-- ten-node Rotation64/Xor64 chain
open Gadgets.Keccak256.ThetaD in
example : FormalCircuitBase.ComputableWitnesses (F := F p) main := by
  computable_witnesses [Gadgets.Keccak256.ThetaD.main]

-- mapIdx over child-output windows
open Gadgets.Keccak256.RhoPi in
example : FormalCircuitBase.ComputableWitnesses (F := F p) main := by
  computable_witnesses [Gadgets.Keccak256.RhoPi.main, Gadgets.Rotation64.output,
    Vector.getElem_mapIdx]

-- Fin-parametrized two-node chain with metadata output defs
open Gadgets.Rotation32 in
example (off : Fin 32) : FormalCircuitBase.ComputableWitnesses (F := F p) (main off) := by
  computable_witnesses [Gadgets.Rotation32.main, Gadgets.Rotation32.output,
    Gadgets.Rotation32Bits.output, U32.ByteVector.eval_fromLimbs, Vector.getElem_ofFn]

open Gadgets.Rotation64 in
example (off : Fin 64) : FormalCircuitBase.ComputableWitnesses (F := F p) (main off) := by
  computable_witnesses [Gadgets.Rotation64.main, Gadgets.Rotation64.output,
    Gadgets.Rotation64Bits.output, Vector.getElem_ofFn]

-- byte-decomposed witness computations
open Gadgets.Addition32Full in
example : FormalCircuitBase.ComputableWitnesses (F := F p) main := by
  computable_witnesses [Gadgets.Addition32Full.main]

-- per-limb map circuit
open Gadgets.SHA256.Xor32 in
example : FormalCircuitBase.ComputableWitnesses (F := F p) main := by
  computable_witnesses [Gadgets.SHA256.Xor32.main, Gadgets.SHA256.xor32]

end

section
variable {F : Type} [FiniteField F] [DecidableEq F] {M : TypeMap} [ProvableType M]

-- generic-typemap gadget with symbolic sizes
open Gadgets.IsZero in
example [DecidableEq (M F)] : FormalCircuitBase.ComputableWitnesses (Gadgets.IsZero.main (F := F) (M := M)) := by
  computable_witnesses [Gadgets.IsZero.main, Gadgets.IsZeroField.circuit,
    Gadgets.IsZero.eval_fin_foldl_mul]

end

/- The Circomlib mux family is not stated here: their `ElaboratedCircuit` instances are
inline in the bundles, so the obligation cannot be restated externally. Their coverage
is the fields themselves; see the TODO COMPWIT notes in Mux2. -/
