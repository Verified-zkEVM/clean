import Clean.Gadgets.Equality
import Clean.Orchard.Action.CommitIvk
import Clean.Orchard.Ecc.Mul.Assign

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
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)
open Ecc
open Orchard.Specs.Sinsemilla (Generators commitIvkChunks hashToPoint)

/-- Inputs of the diversified-address integrity block. `ak`, `nk`, and `rivk` feed
`CommitIvk`; `gDOld` is the old diversified base point, and `pkDOld` is the explicit
witness constrained equal to `[ivk] gDOld`. -/
structure Input (F : Type) where
  ak : F
  nk : F
  rivk : UnconstrainedNat F
  gDOld : Point F
  pkDOld : Point F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ ak := default, nk := default, rivk := default,
     gDOld := { x := default, y := default },
     pkDOld := { x := default, y := default } }⟩

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (input : Var Input Fp) : Circuit Fp (Var Point Fp) := do
  let ivk ← CommitIvk.circuit G Q hQ R
    { ak := input.ak, nk := input.nk, rivk := input.rivk }
  let derived ← Mul.circuit { alpha := ivk, base := input.gDOld }
  derived === input.pkDOld
  return input.pkDOld

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) : ElaboratedCircuit Fp Input Point (main G Q hQ R) := by
  elaborate_circuit

/-- `g_d_old` is witnessed by `NonIdentityPoint::new` before this block in the source. -/
def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  input.gDOld.OnCurve

/-- The block returns the witnessed `pk_d_old`, constrained to equal `[ivk] g_d_old` where
`ivk` is the committed incoming viewing key. -/
def Spec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (ak nk : Fp) (gDOld output : Point Fp) : Prop :=
  ∃ ivk : Fp,
    (∃ rivk : Fq, ∀ B : Point Fp,
      hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B →
        ivk = (B + rivk • R).x) ∧
    output = ivk.val • gDOld

/-- Honest-prover diversified-address integrity for the concrete `rivk`. -/
def ProverSpec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (ak nk : Fp) (rivk : Fq) (gDOld output : Point Fp) : Prop :=
  ∃ ivk : Fp,
    (∀ B : Point Fp,
      hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B →
        ivk = (B + rivk • R).x) ∧
    output = ivk.val • gDOld

/-- Honest proving requires the explicit `pk_d_old` witness to be the derived address for
the committed `ivk`; otherwise the source equality constraint is unsatisfiable. -/
def ProverAssumptions (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (_data : ProverData Fp) (_hint : ProverHint Fp) : Prop :=
  let ak : Fp := input.ak
  let nk : Fp := input.nk
  let gDOld : Point Fp := input.gDOld
  let pkDOld : Point Fp := input.pkDOld
  (∃ B, hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B) ∧
  -- the blinding-scalar hint is the canonical natural representative of `rivk : Fq`
  (show ℕ from input.rivk) < PALLAS_SCALAR_CARD ∧
  gDOld.OnCurve ∧
    ∀ ivk : Fp,
      (∀ B : Point Fp,
        hashToPoint G.S Q (commitIvkChunks ak.val nk.val) = some B →
          ivk = (B + ((show ℕ from input.rivk : ℕ) : Fq) • R).x) →
      pkDOld = ivk.val • gDOld

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R) Assumptions
      (fun input output _ => Spec G Q R input.ak input.nk input.gDOld output) := by
  circuit_proof_start [CommitIvk.circuit, Mul.circuit]
  obtain ⟨h_ivk, h_mul, h_eq⟩ := h_holds
  let ivkOut : Var field Fp := (CommitIvk.circuit G Q hQ R).output
    { ak := input_var.ak, nk := input_var.nk, rivk := input_var.rivk } i₀
  have h_ivk_child : CommitIvk.Spec G Q R input_ak input_nk (eval env ivkOut) := by
    simpa [ivkOut, CommitIvk.Spec, circuit_norm] using h_ivk
  refine ⟨eval env ivkOut, h_ivk_child, ?_⟩
  have hmul := h_mul h_assumptions
  exact h_eq.symm.trans (by simpa [ivkOut, circuit_norm] using hmul)

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R)
      (ProverAssumptions G Q R)
      (fun input output _ =>
        ProverSpec G Q R input.ak input.nk ((show ℕ from input.rivk : ℕ) : Fq)
          input.gDOld output) := by
  circuit_proof_start [CommitIvk.circuit, Mul.circuit]
  obtain ⟨h_hash_exists, h_rivk, h_gd, h_pkd⟩ := h_assumptions
  have h_commit_assumptions :
      (CommitIvk.circuit G Q hQ R).ProverAssumptions
        { ak := input_ak, nk := input_nk, rivk := input_rivk }
        env.data env.hint := by
    exact ⟨by simpa [CommitIvk.circuit, CommitIvk.ProverAssumptions] using h_hash_exists,
      h_rivk⟩
  let ivkOut : Var field Fp := (CommitIvk.circuit G Q hQ R).output
    { ak := input_var.ak, nk := input_var.nk, rivk := input_var.rivk } i₀
  have h_ivk_child_prover :
      CommitIvk.ProverSpec G Q R input_ak input_nk ((show ℕ from input_rivk : ℕ) : Fq)
        (Expression.eval env.toEnvironment ivkOut) := by
    simpa [ivkOut, CommitIvk.ProverSpec, circuit_norm]
      using (h_env.1 h_commit_assumptions).2
  have h_mul_spec := h_env.2 h_gd
  have hderived := h_mul_spec
  have hpkd := h_pkd (Expression.eval env.toEnvironment ivkOut) h_ivk_child_prover
  refine ⟨⟨h_commit_assumptions, h_gd, ?_⟩, ?_⟩
  · rw [hpkd]
    simpa [ivkOut, circuit_norm] using hderived
  refine ⟨(Expression.eval env.toEnvironment ivkOut : Fp), h_ivk_child_prover, ?_⟩
  exact hpkd

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Point where
  main := main G Q hQ R
  elaborated := elaborated G Q hQ R
  Assumptions
  Spec := fun input output _ => Spec G Q R input.ak input.nk input.gDOld output
  ProverAssumptions := ProverAssumptions G Q R
  ProverSpec := fun input output _ =>
    ProverSpec G Q R input.ak input.nk ((show ℕ from input.rivk : ℕ) : Fq)
      input.gDOld output
  soundness := soundness G Q hQ R
  completeness := completeness G Q hQ R

end Orchard.Action.AddressIntegrity
