import Clean.Orchard.Specs.Pallas

/-!
# Orchard protocol types

Plain data shapes used by Orchard-facing specs. These are intentionally not semantic
wrappers: field-like protocol objects remain `Fp`, group-like objects remain `Point Fp`,
and partial protocol operations use `Option`.
-/

namespace Orchard.Specs

/-- Orchard Merkle tree depth. -/
def merkleDepth : ℕ := 32

/-- A Merkle authentication path, represented by sibling labels and position bits. -/
structure MerklePath (F : Type) (B : Type) where
  siblings : Vector F merkleDepth
  pos : Vector B merkleDepth

/-- Orchard note data needed by the protocol-level specs. -/
structure Note where
  d : Fp
  pkD : Point Fp
  value : UInt64
  rho : Fp
  rseed : Fp

/-- Top-level Orchard action data, before distinguishing spend/output validity modes. -/
structure ActionPublic where
  rt : Fp
  cv_net : Point Fp
  nf_old : Fp
  rk : Point Fp
  cm_x : Fp
  enableSpends : Bool
  enableOutputs : Bool

/-- Prover-known auxiliary input for an Orchard action statement. -/
structure ActionAux where
  path : MerklePath Fp Bool
  g_d_old : Point Fp
  pk_d_old : Point Fp
  v_old : UInt64
  ρ_old : Fp
  ψ_old : Fp
  rcm_old : Fq
  cm_old : Point Fp
  α : Fq
  ak : Point Fp
  nk : Fp
  rivk : Fq
  g_d_new : Point Fp
  pk_d_new : Point Fp
  v_new : UInt64
  ψ_new : Fp
  rcm_new : Fq
  rcv : Fq

/-- Circuit-compatible version of ActionPublic -/
structure ActionPublic.Circuit (F : Type) where
  rt : F
  cv_net : Point F
  nf_old : F
  rk : Point F
  cm_x : F
  enableSpends : F
  enableOutputs : F

/-- Project public action data to circuit version -/
def ActionPublic.toCircuit (pub : ActionPublic) : ActionPublic.Circuit Fp where
  rt := pub.rt
  cv_net := pub.cv_net
  nf_old := pub.nf_old
  rk := pub.rk
  cm_x := pub.cm_x
  enableSpends := if pub.enableSpends then 1 else 0
  enableOutputs := if pub.enableOutputs then 1 else 0

/-- Circuit-compatible version of ActionAux -/
structure ActionAux.Circuit (F : Type) where
  path : MerklePath F F
  g_d_old : Point F
  pk_d_old : Point F
  v_old : F
  ρ_old : F
  ψ_old : F
  rcm_old : F
  cm_old : Point F
  α : F
  ak : Point F
  nk : F
  rivk : F
  g_d_new : Point F
  pk_d_new : Point F
  v_new : F
  ψ_new : F
  rcm_new : F
  rcv : F

end Orchard.Specs
