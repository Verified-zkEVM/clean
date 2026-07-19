import Clean.Orchard.Ecc.MulFixed.Certs.NullifierK
import Clean.Orchard.Ecc.MulFixed.Certs.ValueCommitR
import Clean.Orchard.Ecc.MulFixed.Certs.SpendAuthG
import Clean.Orchard.Ecc.MulFixed.Certs.CommitIvkR
import Clean.Orchard.Ecc.MulFixed.Certs.NoteCommitR
import Clean.Orchard.Ecc.MulFixed.Certs.ValueCommitV
import Clean.Orchard.Specs.SinsemillaGenerators
import Clean.Ironwood.Action.Bundle

/-!
# The real Orchard `Bases`

The concrete, fully proof-carrying instantiation of the Action circuit's fixed bases
and Sinsemilla domain points: the six certified bases (`Orchard.Ecc.MulFixed.Certs`)
and the three domain `Q` points (orchard `constants/sinsemilla.rs`, on-curve by
`decide`). With this, `Action.Circuit.synthesize`/the Action bundle are statements
about the actual deployed constants — no hypothetical bases anywhere.
-/

namespace Halo2.Ironwood.Action

/-- `Q_MERKLE_CRH` (orchard `constants/sinsemilla.rs:56`). -/
def merkleQ : Orchard.Point Halo2.Ironwood.Fp :=
  { x := (9991206725476878888751475603038274618448000607209514551456795194094072219296 :
      Halo2.Ironwood.Fp),
    y := (24209798415301550423396126020228723009317736024280831393239261884225294625378 :
      Halo2.Ironwood.Fp) }

theorem merkleQ_onCurve : merkleQ.OnCurve := by
  show merkleQ.y ^ 2 = merkleQ.x ^ 3 + Orchard.pallasB
  decide

/-- `Q_COMMIT_IVK_M_GENERATOR` (orchard `constants/sinsemilla.rs:44`). -/
def ivkQ : Orchard.Point Halo2.Ironwood.Fp :=
  { x := (2593820817260930114322133467408868473290945477826616247349533151445648376562 :
      Halo2.Ironwood.Fp),
    y := (12214744946019415453501880094709511126888074367290315326445800415816181472958 :
      Halo2.Ironwood.Fp) }

theorem ivkQ_onCurve : ivkQ.OnCurve := by
  show ivkQ.y ^ 2 = ivkQ.x ^ 3 + Orchard.pallasB
  decide

/-- `Q_NOTE_COMMITMENT_M_GENERATOR` (orchard `constants/sinsemilla.rs:32`). -/
def noteQ : Orchard.Point Halo2.Ironwood.Fp :=
  { x := (10629404576683096409262958701336170057000067777256141967953463442979689100381 :
      Halo2.Ironwood.Fp),
    y := (22898949290933268079297281211505753011910178734473470279111609228438645877859 :
      Halo2.Ironwood.Fp) }

theorem noteQ_onCurve : noteQ.OnCurve := by
  show noteQ.y ^ 2 = noteQ.x ^ 3 + Orchard.pallasB
  decide

/-- The REAL Orchard `Bases`: the six certified fixed bases and the three domain
points of the deployed circuit. -/
def orchardBases : Circuit.Bases where
  nullifierK := Orchard.Ecc.MulFixed.Certs.nullifierK
  valueCommitV := Orchard.Ecc.MulFixed.Certs.valueCommitV
  valueCommitR := Orchard.Ecc.MulFixed.Certs.valueCommitR
  spendAuthG := Orchard.Ecc.MulFixed.Certs.spendAuthG
  commitIvkR := Orchard.Ecc.MulFixed.Certs.commitIvkR
  noteCommitR := Orchard.Ecc.MulFixed.Certs.noteCommitR
  merkleQ := merkleQ
  merkleQ_onCurve := merkleQ_onCurve
  ivkQ := ivkQ
  ivkQ_onCurve := ivkQ_onCurve
  noteQ := noteQ
  noteQ_onCurve := noteQ_onCurve

/-- The PROVEN end-to-end Action circuit (soundness + completeness, the Bundle arc)
instantiated at the real deployed constants — the certified fixed bases, the `Q`
points, and the kernel-verified Sinsemilla generator table. Only the witness programs
(the prover's private data) remain a parameter. -/
def orchardActionCircuit (W : Circuit.Witnesses) :
    FormalCircuit Halo2.Ironwood.Fp Unit Circuit.Config unit unit :=
  Circuit.circuit Orchard.Specs.Sinsemilla.orchardGenerators orchardBases W

end Halo2.Ironwood.Action
