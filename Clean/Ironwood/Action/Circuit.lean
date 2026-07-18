import Clean.Ironwood.Ecc.Chip
import Clean.Ironwood.Poseidon.Hash
import Clean.Ironwood.Utilities.AddChip
import Clean.Ironwood.Sinsemilla.Merkle
import Clean.Ironwood.CommitIvk.Gadget
import Clean.Ironwood.NoteCommit.Main

/-!
# The Orchard Action circuit (Ironwood): configure

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit.rs`, `impl plonk::Circuit for Circuit` —
`fn configure` (lines 271-459), VK-exact in registration order:
the ten advices, the `q_orchard` gate, the add chip, the three lookup table columns,
the `primary` instance column, equality on all advices, the eight Lagrange fixed
columns (+ constants on the first), the range check, the ECC chip, Poseidon, the two
Sinsemilla/Merkle pairs, CommitIvk, and the two NoteCommit chips.

The synthesize assembly follows in a later slice (it additionally needs the
`assign_advice_from_instance` region operation for the final `"Orchard circuit
checks"` region).
-/

namespace Halo2.Ironwood.Action.Circuit

open Halo2.Ironwood (Fp)
open Orchard.Specs.Sinsemilla (Generators)

/-- Rust `Config` (`circuit.rs:120-137`): everything `synthesize` consumes. The shared
lookup config (`range_check`) is carried explicitly (Rust reaches it through the chips). -/
structure Config where
  primary : Column .instance
  qOrchard : Selector
  advices : Fin 10 → Column .advice
  addChipConfig : AddChip.Config
  eccConfig : Ecc.EccConfig
  poseidonConfig : Poseidon.Config
  sinsemilla1 : Sinsemilla.HashPiece.Config
  merkle1 : Sinsemilla.Merkle.Config
  sinsemilla2 : Sinsemilla.HashPiece.Config
  merkle2 : Sinsemilla.Merkle.Config
  commitIvkConfig : CommitIvk.Config
  noteCommitOld : NoteCommit.Config
  noteCommitNew : NoteCommit.Config
  lookupConfig : LookupRangeCheck.Config 10

/-- The `"Orchard circuit checks"` gate (`circuit.rs:290-329`): the four top-level value
checks over `advices[0..8]` at the current row, in the source's constraint order. -/
def orchardGate (qOrchard : Selector) (advices : Fin 10 → Column .advice) : Gate Fp where
  name := "Orchard circuit checks"
  selector := qOrchard
  constraints :=
    let vOld : Expression Fp Query := queryAdvice (advices 0) 0
    let vNew : Expression Fp Query := queryAdvice (advices 1) 0
    let magnitude : Expression Fp Query := queryAdvice (advices 2) 0
    let sign : Expression Fp Query := queryAdvice (advices 3) 0
    let root : Expression Fp Query := queryAdvice (advices 4) 0
    let anchor : Expression Fp Query := queryAdvice (advices 5) 0
    let enableSpends : Expression Fp Query := queryAdvice (advices 6) 0
    let enableOutputs : Expression Fp Query := queryAdvice (advices 7) 0
    Constraints.withSelector qOrchard
      [ ("v_old - v_new = magnitude * sign", vOld - vNew - magnitude * sign),
        ("Either v_old = 0, or root = anchor", vOld * (root - anchor)),
        ("v_old = 0 or enable_spends = 1", vOld * ((1 : Fp) - enableSpends)),
        ("v_new = 0 or enable_outputs = 1", vNew * ((1 : Fp) - enableOutputs)) ]

/-- Rust `Circuit::configure` (`circuit.rs:271-459`), VK-exact registration order. -/
def configure (G : Generators) : Configure Fp Config := do
  -- circuit.rs:273-284 — the ten advice columns
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
  let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
  let a9 ← adviceColumn
  let advices : Fin 10 → Column .advice := ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  -- circuit.rs:290-329 — `q_orchard` + the top-level checks gate
  let qOrchard ← selector
  createGate (orchardGate qOrchard advices)
  -- circuit.rs:332 — the add chip (advices 7, 8 → 6)
  let addChipConfig ← AddChip.configure a7 a8 a6
  -- circuit.rs:335-340 — the Sinsemilla generator table columns
  let tableIdx ← lookupTableColumn
  let tableX ← lookupTableColumn
  let tableY ← lookupTableColumn
  let genTable : Sinsemilla.GeneratorTableConfig := { tableIdx, tableX, tableY }
  -- circuit.rs:343-344 — the public-input instance column
  let primary ← instanceColumn
  enableEquality primary
  -- circuit.rs:347-349 — equality on all advices
  enableEquality a0; enableEquality a1; enableEquality a2; enableEquality a3
  enableEquality a4; enableEquality a5; enableEquality a6; enableEquality a7
  enableEquality a8; enableEquality a9
  -- circuit.rs:356-365 — the eight Lagrange-coefficient fixed columns
  let l0 ← fixedColumn; let l1 ← fixedColumn; let l2 ← fixedColumn
  let l3 ← fixedColumn; let l4 ← fixedColumn; let l5 ← fixedColumn
  let l6 ← fixedColumn; let l7 ← fixedColumn
  let lagrangeCoeffs : Fin 8 → Column .fixed := ![l0, l1, l2, l3, l4, l5, l6, l7]
  -- circuit.rs:371 — constants on the first Lagrange column
  enableConstant l0
  -- circuit.rs:375 — the shared 10-bit range check on `advices[9]`
  let lookupConfig ← LookupRangeCheck.configure 10 a9 tableIdx
  -- circuit.rs:379-380 — the ECC chip
  let eccConfig ← Ecc.configure advices lagrangeCoeffs lookupConfig
  -- circuit.rs:383-391 — Poseidon (state `advices[6..9]`, sbox `advices[5]`,
  -- `rc_a = lagrange[2..5]`, `rc_b = lagrange[5..8]`)
  let poseidonConfig ← Poseidon.configure ![a6, a7, a8] a5 ![l2, l3, l4] ![l5, l6, l7]
  -- circuit.rs:397-410 — Sinsemilla 1 (advices[0..5], pieces `advices[6]`,
  -- `y_Q` fixed `lagrange[0]`) + Merkle 1
  let sinsemilla1 ← Sinsemilla.HashPiece.configure G a0 a1 a2 a3 a4 a6 l0 genTable
  let merkle1 ← Sinsemilla.Merkle.configure sinsemilla1
  -- circuit.rs:416-429 — Sinsemilla 2 (advices[5..], pieces `advices[7]`,
  -- `y_Q` fixed `lagrange[1]`) + Merkle 2
  let sinsemilla2 ← Sinsemilla.HashPiece.configure G a5 a6 a7 a8 a9 a7 l1 genTable
  let merkle2 ← Sinsemilla.Merkle.configure sinsemilla2
  -- circuit.rs:433 — CommitIvk
  let commitIvkConfig ← CommitIvk.configure advices
  -- circuit.rs:437-443 — the two NoteCommit chips
  let noteCommitOld ← NoteCommit.configure advices
  let noteCommitNew ← NoteCommit.configure advices
  return { primary, qOrchard, advices, addChipConfig, eccConfig, poseidonConfig,
           sinsemilla1, merkle1, sinsemilla2, merkle2, commitIvkConfig,
           noteCommitOld, noteCommitNew, lookupConfig }

end Halo2.Ironwood.Action.Circuit
