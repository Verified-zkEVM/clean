import Clean.Orchard.Sinsemilla.HashToPoint
import Clean.Orchard.Ecc.ScalarMul.MulFixed.FullWidth
import Clean.Orchard.Ecc.Add

/-!
# Sinsemilla hash and commit domains

Reference: `halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla.rs`.

- `HashDomain::hash`: `hash_to_point` followed by `x`-extraction (`Extract⊥`).
- `CommitDomain::commit`: `M.hash_to_point(msg) + [r] R`, with the blinding term a
  full-width fixed-base multiplication and the sum a complete addition.
- `CommitDomain::short_commit`: `commit` followed by `x`-extraction.
- `CommitDomain::blinding_factor` is the bare `[r] R`, i.e. exactly
  `MulFixed.FullWidth.circuit R`.

The domain constants (`Q`, the generator table, the blinding base `R`) are abstract
parameters with the properties the proofs need (`Q ≠ 0`, `Generators.S_ne_zero`,
`FixedBase`).
-/

namespace Orchard.Sinsemilla

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Ecc (Point)
open Orchard.Ecc.ScalarMul

/-! ### `HashDomain::hash` -/

namespace HashDomain

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (n₀ : ℕ)
    (ns : List ℕ) (pieces : Var (fields (ns.length + 1)) Ecc.Fp) :
    Circuit Ecc.Fp (Expression Ecc.Fp) := do
  let p ← Entry.circuit G Q hQ n₀ ns pieces
  return p.x

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (n₀ : ℕ) (ns : List ℕ) :
    ElaboratedCircuit Ecc.Fp (fields (ns.length + 1)) field (main G Q hQ n₀ ns) := by
  elaborate_circuit

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (n₀ : ℕ) (ns : List ℕ)
    (pieces : Value (fields (ns.length + 1)) Ecc.Fp) (output : Value field Ecc.Fp)
    (_ : ProverData Ecc.Fp) : Prop :=
  ∃ chunks : List ℕ, Chain.PieceChunks (n₀ :: ns) pieces chunks ∧
    ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q chunks = some B → output = B.x

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve) (n₀ : ℕ)
    (ns : List ℕ) (pieces : ProverValue (fields (ns.length + 1)) Ecc.Fp)
    (_ : ProverData Ecc.Fp) (_ : ProverHint Ecc.Fp) : Prop :=
  Chain.PieceBounds (n₀ :: ns) pieces ∧
  ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
    (Chain.honestChunks (n₀ :: ns) pieces) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (n₀ : ℕ) (ns : List ℕ)
    (pieces : ProverValue (fields (ns.length + 1)) Ecc.Fp)
    (output : ProverValue field Ecc.Fp) (_ : ProverHint Ecc.Fp) : Prop :=
  ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
      (Chain.honestChunks (n₀ :: ns) pieces) = some B →
    output = B.x

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Ecc.Fp (main G Q hQ n₀ ns)
      (fun _ _ => True) (Spec G Q n₀ ns) := by
  circuit_proof_start [main, Spec, Entry.circuit, Entry.Spec]
  obtain ⟨chunks, hPC, hfun⟩ := h_holds
  refine ⟨chunks, hPC, ?_⟩
  intro B hB
  exact congrArg Ecc.Point.x (hfun B hB)

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Ecc.Fp (main G Q hQ n₀ ns)
      (ProverAssumptions G Q n₀ ns) (ProverSpec G Q n₀ ns) := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions, Entry.circuit,
    Entry.ProverAssumptions, Entry.ProverSpec]
  refine ⟨h_assumptions, ?_⟩
  intro B hB
  exact congrArg Ecc.Point.x ((h_env h_assumptions).2 B hB)

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint Ecc.Fp (fields (ns.length + 1)) field where
  main := main G Q hQ n₀ ns
  Spec := Spec G Q n₀ ns
  ProverAssumptions := ProverAssumptions G Q n₀ ns
  ProverSpec := ProverSpec G Q n₀ ns
  soundness := soundness G Q hQ n₀ ns
  completeness := completeness G Q hQ n₀ ns

end HashDomain

/-! ### `CommitDomain::commit` and `CommitDomain::short_commit` -/

namespace CommitDomain

/-- Inputs of `commit`: the message pieces and the prover-side full-width blinding
scalar behind the `ScalarFixed` value `r`. -/
structure Input (k : ℕ) (F : Type) where
  pieces : Vector F k
  r : Unconstrained Fq F
deriving CircuitType

instance (k : ℕ) : Inhabited (Var (Input k) Ecc.Fp) :=
  ⟨{ pieces := .replicate k default, r := fun _ => default }⟩

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ)
    (input : Var (Input (ns.length + 1)) Ecc.Fp) :
    Circuit Ecc.Fp (Var Point Ecc.Fp) := do
  -- blind = [r] R
  let blind ← MulFixed.FullWidth.circuit R input.r
  -- p = M.hash_to_point(msg)
  let p ← Entry.circuit G Q hQ n₀ ns input.pieces
  -- commitment = p + blind
  Ecc.Add.circuit { p := p, q := blind }

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    ElaboratedCircuit Ecc.Fp (Input (ns.length + 1)) Point
      (main G Q hQ R n₀ ns) := by
  elaborate_circuit

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : Value (Input (ns.length + 1)) Ecc.Fp)
    (output : Point Ecc.Fp) (_ : ProverData Ecc.Fp) : Prop :=
  ∃ (chunks : List ℕ) (r : Fq),
    Chain.PieceChunks (n₀ :: ns) input.pieces chunks ∧
    ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output.coords = Pallas.add (B.x, B.y) (R.mulValue r).coords

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve) (n₀ : ℕ)
    (ns : List ℕ) (input : ProverValue (Input (ns.length + 1)) Ecc.Fp)
    (_ : ProverData Ecc.Fp) (_ : ProverHint Ecc.Fp) : Prop :=
  Chain.PieceBounds (n₀ :: ns) input.pieces ∧
  ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
    (Chain.honestChunks (n₀ :: ns) input.pieces) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : ProverValue (Input (ns.length + 1)) Ecc.Fp)
    (output : Point Ecc.Fp) (_ : ProverHint Ecc.Fp) : Prop :=
  ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
      (Chain.honestChunks (n₀ :: ns) input.pieces) = some B →
    output.coords = Pallas.add (B.x, B.y) (R.mulValue input.r).coords

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Ecc.Fp (main G Q hQ R n₀ ns)
      (fun _ _ => True) (Spec G Q R n₀ ns) := by
  circuit_proof_start [main, Spec, Entry.circuit, Entry.Spec,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.Spec,
    Ecc.Add.circuit, Ecc.Add.Spec, Ecc.Add.Assumptions]
  obtain ⟨h_fw, h_entry, h_add⟩ := h_holds
  obtain ⟨s, hblind⟩ := h_fw
  obtain ⟨chunks, hPC, hfun⟩ := h_entry
  refine ⟨chunks, s, hPC, ?_⟩
  intro B hB
  have hp := hfun B hB
  have h_final := h_add ⟨by
      rw [hp]
      exact Or.inl (SWPoint.onCurve_of_ne_zero
        (Orchard.Specs.Sinsemilla.hashToPoint_ne_zero hQ hB)),
    by
      rw [hblind]
      exact R.mulValue_valid s⟩
  rw [h_final.2, hp, hblind]
  rfl

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Ecc.Fp (main G Q hQ R n₀ ns)
      (ProverAssumptions G Q n₀ ns) (ProverSpec G Q R n₀ ns) := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions,
    Entry.circuit, Entry.ProverAssumptions, Entry.ProverSpec,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.ProverSpec,
    Ecc.Add.circuit, Ecc.Add.Spec, Ecc.Add.Assumptions]
  obtain ⟨h_fw_env, h_entry_env, h_add_env⟩ := h_env
  obtain ⟨hbounds, B, hchain⟩ := h_assumptions
  obtain ⟨-, hblind⟩ := h_fw_env
  have hp := (h_entry_env ⟨hbounds, B, hchain⟩).2 B hchain
  have h_final := h_add_env ⟨by
      rw [hp]
      exact Or.inl (SWPoint.onCurve_of_ne_zero
        (Orchard.Specs.Sinsemilla.hashToPoint_ne_zero hQ hchain)),
    by
      rw [hblind]
      exact R.mulValue_valid _⟩
  refine ⟨⟨⟨hbounds, B, hchain⟩, ?_, ?_⟩, ?_⟩
  · rw [hp]
    exact Or.inl (SWPoint.onCurve_of_ne_zero
      (Orchard.Specs.Sinsemilla.hashToPoint_ne_zero hQ hchain))
  · rw [hblind]
    exact R.mulValue_valid _
  · intro B' hB'
    rw [hchain] at hB'
    obtain rfl : B = B' := Option.some.inj hB'
    rw [h_final.2, hp, hblind]
    rfl

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint Ecc.Fp (Input (ns.length + 1)) Point where
  main := main G Q hQ R n₀ ns
  Spec := Spec G Q R n₀ ns
  ProverAssumptions := ProverAssumptions G Q n₀ ns
  ProverSpec := ProverSpec G Q R n₀ ns
  soundness := soundness G Q hQ R n₀ ns
  completeness := completeness G Q hQ R n₀ ns

/-! #### `short_commit` -/

namespace Short

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ)
    (input : Var (Input (ns.length + 1)) Ecc.Fp) :
    Circuit Ecc.Fp (Expression Ecc.Fp) := do
  let p ← CommitDomain.circuit G Q hQ R n₀ ns input
  return p.x

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    ElaboratedCircuit Ecc.Fp (Input (ns.length + 1)) field
      (main G Q hQ R n₀ ns) := by
  elaborate_circuit

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : Value (Input (ns.length + 1)) Ecc.Fp)
    (output : Value field Ecc.Fp) (_ : ProverData Ecc.Fp) : Prop :=
  ∃ (chunks : List ℕ) (r : Fq),
    Chain.PieceChunks (n₀ :: ns) input.pieces chunks ∧
    ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output = (Pallas.add (B.x, B.y) (R.mulValue r).coords).1

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : ProverValue (Input (ns.length + 1)) Ecc.Fp)
    (output : ProverValue field Ecc.Fp) (_ : ProverHint Ecc.Fp) : Prop :=
  ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
      (Chain.honestChunks (n₀ :: ns) input.pieces) = some B →
    output = (Pallas.add (B.x, B.y) (R.mulValue input.r).coords).1

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Ecc.Fp (main G Q hQ R n₀ ns)
      (fun _ _ => True) (Spec G Q R n₀ ns) := by
  circuit_proof_start [main, Spec, CommitDomain.circuit, CommitDomain.Spec]
  obtain ⟨chunks, r, hPC, hfun⟩ := h_holds
  refine ⟨chunks, r, hPC, ?_⟩
  intro B hB
  exact congrArg Prod.fst (hfun B hB)

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Ecc.Fp (main G Q hQ R n₀ ns)
      (ProverAssumptions G Q n₀ ns) (ProverSpec G Q R n₀ ns) := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions,
    CommitDomain.circuit, CommitDomain.ProverAssumptions, CommitDomain.ProverSpec]
  refine ⟨h_assumptions, ?_⟩
  intro B hB
  exact congrArg Prod.fst ((h_env h_assumptions).2 B hB)

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint Ecc.Fp (Input (ns.length + 1)) field where
  main := main G Q hQ R n₀ ns
  Spec := Spec G Q R n₀ ns
  ProverAssumptions := ProverAssumptions G Q n₀ ns
  ProverSpec := ProverSpec G Q R n₀ ns
  soundness := soundness G Q hQ R n₀ ns
  completeness := completeness G Q hQ R n₀ ns

end Short

/-- `CommitDomain::blinding_factor` is the bare `[r] R`. -/
def blindingFactor (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint Ecc.Fp (Unconstrained Fq) Point :=
  MulFixed.FullWidth.circuit R

end CommitDomain

end Orchard.Sinsemilla
