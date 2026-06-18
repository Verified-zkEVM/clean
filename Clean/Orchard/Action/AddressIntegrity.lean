import Clean.Gadgets.Equality
import Clean.Orchard.Action.CommitIvk
import Clean.Orchard.Ecc.ScalarMul.Mul.Assign

/-!
# Orchard diversified address integrity

Reference: `orchard@0.14.0/src/circuit.rs`, the `Diversified address integrity` block in
`Circuit::synthesize`.

The source computes

* `ivk = CommitIvk(ak, nk, rivk)`,
* coerces that base-field cell into the variable-base scalar wrapper,
* computes `[ivk] g_d_old`, and
* constrains the result equal to the separately witnessed `pk_d_old`.

This module packages that block as a reusable mid-level circuit for the final action
synthesis circuit.
-/

namespace Orchard.Action.AddressIntegrity

open CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open Ecc Ecc.ScalarMul
open Orchard.Specs.Sinsemilla (Generators commitIvkChunks hashToPoint)

/-- Inputs of the diversified-address integrity block. `ak`, `nk`, and `rivk` feed
`CommitIvk`; `gDOld` is the old diversified base point, and `pkDOld` is the explicit
witness constrained equal to `[ivk] gDOld`. -/
structure Input (F : Type) where
  ak : F
  nk : F
  rivk : Unconstrained Fq F
  gDOld : Point F
  pkDOld : Point F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ ak := default, nk := default, rivk := fun _ => default,
     gDOld := { x := default, y := default },
     pkDOld := { x := default, y := default } }⟩

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Fp) : Circuit Fp (Var Point Fp) := do
  let ivk ← CommitIvk.circuit G Q hQ R
    { ak := input.ak, nk := input.nk, rivk := input.rivk }
  let derived ← Mul.circuit { alpha := ivk, base := input.gDOld }
  derived === input.pkDOld
  return input.pkDOld

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp Input Point (main G Q hQ R) := by
  elaborate_circuit

/-- `g_d_old` is witnessed by `NonIdentityPoint::new` before this block in the source. -/
def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  Pallas.OnCurve input.gDOld.coords

/-- Diversified-address integrity:
the output point is `[ivk] g_d_old`, where `ivk` is committed to `(ak, nk, rivk)`. -/
def AddressIntegrityRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : Value Input Fp) (output : Point Fp) : Prop :=
  ∃ ivk : Fp,
    CommitIvk.CommitIvkRelation G Q R
      ({ ak := input.ak, nk := input.nk, rivk := input.rivk } : Value CommitIvk.Input Fp)
      ivk ∧
    ∀ B : SWPoint Pallas.curve, B ≠ 0 → input.gDOld.coords = (B.x, B.y) →
      output.coords = ((ivk.val • B).x, (ivk.val • B).y)

/-- Honest-prover diversified-address integrity for the concrete `rivk`. -/
def ProverAddressIntegrityRelation (G : Generators) (Q : SWPoint Pallas.curve)
    (R : MulFixed.FixedBase) (input : ProverValue Input Fp) (output : Point Fp) : Prop :=
  ∃ ivk : Fp,
    CommitIvk.ProverCommitIvkRelation G Q R
      ({ ak := input.ak, nk := input.nk, rivk := input.rivk } : ProverValue CommitIvk.Input Fp)
      ivk ∧
    ∀ B : SWPoint Pallas.curve, B ≠ 0 → input.gDOld.coords = (B.x, B.y) →
      output.coords = ((ivk.val • B).x, (ivk.val • B).y)

/-- The block returns the witnessed `pk_d_old`, constrained to equal `[ivk] g_d_old` where
`ivk` is the committed incoming viewing key. -/
def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (output : Point Fp) (_data : ProverData Fp) : Prop :=
  AddressIntegrityRelation G Q R input output

/-- Honest proving requires the explicit `pk_d_old` witness to be the derived address for
the committed `ivk`; otherwise the source equality constraint is unsatisfiable. -/
def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (_data : ProverData Fp) (_hint : ProverHint Fp) : Prop :=
  let ak : Fp := input.ak
  let nk : Fp := input.nk
  (∃ H : SWPoint Pallas.curve,
    hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some H) ∧
  Pallas.OnCurve input.gDOld.coords ∧
    ∀ ivk : Fp,
      CommitIvk.ProverCommitIvkRelation G Q R
        ({ ak := input.ak, nk := input.nk, rivk := input.rivk } :
          ProverValue CommitIvk.Input Fp)
        ivk →
      ∀ B : SWPoint Pallas.curve, B ≠ 0 → input.gDOld.coords = (B.x, B.y) →
        input.pkDOld.coords = ((ivk.val • B).x, (ivk.val • B).y)

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (output : Point Fp) (_hint : ProverHint Fp) : Prop :=
  ProverAddressIntegrityRelation G Q R input output

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) Assumptions
      (Spec G Q R) := by
  circuit_proof_start [CommitIvk.circuit, Mul.circuit]
  obtain ⟨h_ivk, h_mul, h_eq⟩ := h_holds
  let ivkOut : Var field Fp := (CommitIvk.circuit G Q hQ R).output
    ({ ak := input_var.ak, nk := input_var.nk, rivk := input_var.rivk } : Var CommitIvk.Input Fp) i₀
  have h_ivk_child : CommitIvk.CommitIvkRelation G Q R
      ({ ak := input_ak, nk := input_nk, rivk := input_rivk } : Value CommitIvk.Input Fp)
        (eval env ivkOut) := by
    simpa [ivkOut, CommitIvk.Spec, circuit_norm] using h_ivk
  refine ⟨eval env ivkOut, h_ivk_child, ?_⟩
  intro B hB hcoords
  rw [← h_eq]
  simpa [ivkOut, circuit_norm] using h_mul h_assumptions B hB hcoords

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q R) (ProverSpec G Q R) := by
  circuit_proof_start [CommitIvk.circuit, Mul.circuit]
  obtain ⟨h_hash_exists, h_gd, h_pkd⟩ := h_assumptions
  have h_commit_assumptions :
      CommitIvk.ProverAssumptions G Q R { ak := input_ak, nk := input_nk, rivk := input_rivk }
        env.data env.hint := by
    simpa [CommitIvk.ProverAssumptions] using h_hash_exists
  let ivkOut : Var field Fp := (CommitIvk.circuit G Q hQ R).output
    ({ ak := input_var.ak, nk := input_var.nk, rivk := input_var.rivk } : Var CommitIvk.Input Fp) i₀
  have h_ivk_child_prover : CommitIvk.ProverCommitIvkRelation G Q R
      ({ ak := input_ak, nk := input_nk, rivk := input_rivk } : ProverValue CommitIvk.Input Fp)
        (Expression.eval env.toEnvironment ivkOut) := by
    simpa [ivkOut, CommitIvk.ProverSpec, circuit_norm]
      using (h_env.1 h_commit_assumptions).2
  have h_mul_spec := h_env.2 h_gd
  obtain ⟨B, hB, hBx, hBy⟩ : ∃ B : SWPoint Pallas.curve, B ≠ 0 ∧
      B.x = input_gDOld.x ∧ B.y = input_gDOld.y := by
    refine ⟨⟨input_gDOld.x, input_gDOld.y, Or.inl h_gd⟩, ?_, rfl, rfl⟩
    intro h0
    have hx : input_gDOld.x = (0 : Fp) := congrArg SWPoint.x h0
    have hy : input_gDOld.y = (0 : Fp) := congrArg SWPoint.y h0
    rw [Point.coords, hx, hy] at h_gd
    exact Pallas.not_onCurve_zero h_gd
  have hbase : input_gDOld.coords = (B.x, B.y) := by rw [Point.coords, hBx, hBy]
  have hderived := h_mul_spec B hB hbase
  have hpkd := h_pkd (Expression.eval env.toEnvironment ivkOut) h_ivk_child_prover B hB hbase
  refine ⟨⟨h_commit_assumptions, h_gd, ?_⟩, ?_⟩
  · apply Point.ext_coords
    trans ((ZMod.val (Expression.eval env.toEnvironment ivkOut) • B).x,
      (ZMod.val (Expression.eval env.toEnvironment ivkOut) • B).y)
    · simpa [ivkOut, circuit_norm] using hderived
    · exact hpkd.symm
  refine ⟨(Expression.eval env.toEnvironment ivkOut : Fp), h_ivk_child_prover, ?_⟩
  intro B hB hcoords
  exact h_pkd (Expression.eval env.toEnvironment ivkOut) h_ivk_child_prover B hB hcoords

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Point where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Assumptions
  Spec := Spec G Q R
  ProverAssumptions := ProverAssumptions G Q R
  ProverSpec := ProverSpec G Q R
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end Orchard.Action.AddressIntegrity
