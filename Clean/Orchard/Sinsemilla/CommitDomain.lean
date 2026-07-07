import Clean.Orchard.Sinsemilla.HashToPoint
import Clean.Orchard.Ecc.MulFixed.FullWidth
import Clean.Orchard.Ecc.Add

/-!
# Sinsemilla commit domain

Reference: `halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla.rs`.

- `CommitDomain::commit`: `M.hash_to_point(msg) + [r] R`, with the blinding term a
  full-width fixed-base multiplication and the sum a complete addition. The output keeps
  the per-piece running sums `zs` (halo2's `commit` returns `(Point, Vec<RunningSum>)`),
  read by `NoteCommit`/`CommitIvk` for their canonicity gates.
- `CommitDomain::blinding_factor` is the bare `[r] R`, i.e. exactly
  `MulFixed.FullWidth.circuit R`.

`HashDomain::hash` and `CommitDomain::short_commit` (both `hash_to_point`/`commit`
followed by `x`-extraction) are realized inline where Orchard needs them — `MerkleCRH`
extracts `x` in `Merkle.HashLayer`, and `commit_ivk` extracts `x` after `commit` — so
they have no standalone gadget here.

The domain constants (`Q`, the generator table, the blinding base `R`) are abstract
parameters with the properties the proofs need (`Q.OnCurve`, `Generators.S_ne_zero`,
`FixedBase`).
-/

namespace Orchard.Sinsemilla

open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)
open Specs.Sinsemilla (Generators)
open Ecc

/-! ### `CommitDomain::commit` -/

namespace CommitDomain

/-- Inputs of `commit`: the message pieces and the prover-side full-width blinding
scalar behind the `ScalarFixed` value `r` (the canonical natural representative of the
`Fq` scalar). -/
structure Input (k : ℕ) (F : Type) where
  pieces : Vector F k
  r : UnconstrainedNat F
deriving CircuitType

instance (k : ℕ) : Inhabited (Var (Input k) Fp) :=
  ⟨{ pieces := default, r := default }⟩

/-- Outputs of `commit`: the commitment point and the hash running sums, mirroring
halo2's `commit` returning `(CommitmentPoint, Vec<RunningSum>)`. `NoteCommit`/`CommitIvk`
read individual `zs[i][j]` cells for their canonicity gates. -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  zs : HVec (Chain.zLengths ns) F
deriving ProvableStruct

theorem eval_zs {F : Type} [FiniteField F] (env : Environment F) (ns : List ℕ) (out : Var (Output ns) F) :
    (eval env out).zs = eval env out.zs := by
  simp only [circuit_norm]

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ)
    (input : Var (Input (ns.length + 1)) Fp) :
    Circuit Fp (Var (Output (n₀ :: ns)) Fp) := do
  -- blind = [r] R
  let blind ← MulFixed.FullWidth.circuit R input.r
  -- p = M.hash_to_point(msg)
  let p ← HashToPoint.circuit G Q hQ n₀ ns input.pieces
  -- commitment = p + blind
  let commitment ← Ecc.Add.circuit { p := p.point, q := blind }
  return { point := commitment, zs := p.zs }

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    ElaboratedCircuit Fp (Input (ns.length + 1)) (Output (n₀ :: ns))
      (main G Q hQ R n₀ ns) := by
  elaborate_circuit

def Spec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : Value (Input (ns.length + 1)) Fp)
    (output : Value (Output (n₀ :: ns)) Fp) (_ : ProverData Fp) : Prop :=
  ∃ (chunks : List ℕ) (r : Fq),
    Chain.PieceChunks (n₀ :: ns) input.pieces chunks ∧
    Chain.ZsFacts (n₀ :: ns) chunks output.zs ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output.point = B + r • R

def ProverAssumptions (G : Generators) (Q : Point Fp) (n₀ : ℕ)
    (ns : List ℕ) (input : ProverValue (Input (ns.length + 1)) Fp)
    (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  Chain.PieceBounds (n₀ :: ns) input.pieces ∧
  (∃ B, Specs.Sinsemilla.hashToPoint G.S Q
    (Chain.honestChunks (n₀ :: ns) input.pieces) = some B) ∧
  (show ℕ from input.r) < PALLAS_SCALAR_CARD

def ProverSpec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : ProverValue (Input (ns.length + 1)) Fp)
    (output : ProverValue (Output (n₀ :: ns)) Fp) (_ : ProverHint Fp) : Prop :=
  Chain.ZsHonest (n₀ :: ns) input.pieces output.zs ∧
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q
      (Chain.honestChunks (n₀ :: ns) input.pieces) = some B →
    output.point = B + ((show ℕ from input.r : ℕ) : Fq) • R

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ R n₀ ns)
      (fun _ _ => True) (Spec G Q R n₀ ns) := by
  circuit_proof_start [HashToPoint.circuit, HashToPoint.Spec,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.Spec,
    Ecc.Add.circuit, Ecc.Add.Spec, Ecc.Add.Assumptions]
  obtain ⟨h_fw, h_entry, h_add⟩ := h_holds
  obtain ⟨s, hblind⟩ := h_fw
  obtain ⟨chunks, hPC, hZs, hfun⟩ := h_entry
  refine ⟨chunks, s, hPC, ?_, ?_⟩
  · convert hZs using 2
  · intro B hB
    have hp := hfun B hB
    have hBvalid : B.Valid :=
      Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ) (Chain.pieceChunks_bound hPC) hB
    have h_final := h_add ⟨by
        rw [hp]
        exact hBvalid,
      by
        rw [hblind]
        exact R.smul_valid s⟩
    rw [hp, hblind] at h_final
    simpa using h_final.2

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ R n₀ ns)
      (ProverAssumptions G Q n₀ ns) (ProverSpec G Q R n₀ ns) := by
  circuit_proof_start [HashToPoint.circuit, HashToPoint.ProverAssumptions, HashToPoint.ProverSpec,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.ProverAssumptions,
    MulFixed.FullWidth.ProverSpec,
    Ecc.Add.circuit, Ecc.Add.Spec, Ecc.Add.Assumptions]
  obtain ⟨h_fw_env, h_entry_env, h_add_env⟩ := h_env
  obtain ⟨hbounds, ⟨B, hchain⟩, hr⟩ := h_assumptions
  obtain ⟨-, hblind⟩ := h_fw_env hr
  obtain ⟨hZsH, hp0⟩ := (h_entry_env ⟨hbounds, B, hchain⟩).2
  have hp := hp0 B hchain
  have hPC := Chain.pieceChunks_honestChunks (n₀ :: ns) input.pieces hbounds
  have hBvalid : B.Valid :=
    Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ) (Chain.pieceChunks_bound hPC) hchain
  have h_final := h_add_env ⟨by
      rw [hp]
      exact hBvalid,
    by
      rw [hblind]
      exact R.smul_valid _⟩
  refine ⟨⟨hr, ⟨hbounds, B, hchain⟩, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp]
    exact hBvalid
  · rw [hblind]
    exact R.smul_valid _
  · convert hZsH using 2
  · intro B' hB'
    rw [hchain] at hB'
    obtain rfl : B = B' := Option.some.inj hB'
    rw [hp, hblind] at h_final
    simpa using h_final.2

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint Fp (Input (ns.length + 1)) (Output (n₀ :: ns)) where
  main := main G Q hQ R n₀ ns
  elaborated := elaborated G Q hQ R n₀ ns
  Spec := Spec G Q R n₀ ns
  ProverAssumptions := ProverAssumptions G Q n₀ ns
  ProverSpec := ProverSpec G Q R n₀ ns
  soundness := soundness G Q hQ R n₀ ns
  completeness := completeness G Q hQ R n₀ ns

/-- `CommitDomain::blinding_factor` is the bare `[r] R`. -/
def blindingFactor (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint Fp UnconstrainedNat Point :=
  MulFixed.FullWidth.circuit R

end CommitDomain

end Orchard.Sinsemilla
