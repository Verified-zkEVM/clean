import Clean.Ironwood.CommitIvk.Composite
import Clean.Ironwood.Sinsemilla.CommitDomain
import Clean.Ironwood.NoteCommit.Main

/-!
# CommitIvk gadget (Ironwood) — STRUCTURE-ONLY STUB

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/commit_ivk.rs::gadgets::commit_ivk` (lines 260-420), in
exact region-creation order (VK layout is order-sensitive):

1. witness pieces `a`, `b`, `c`, `d` interleaved with the sub-piece short checks
   (`b_0` 4 bits, `b_2` 5 bits, `d_0` 9 bits) — 7 regions;
2. `CommitDomain::short_commit` = `commit` + `extract_p` (the `[rivk]R` blind, the
   `hash_to_point`, the final addition) — 4 regions;
3. the canonicity flow (`ak_canonicity` 13-word witness check, `nk_canonicity` 14-word
   witness check, the `"Assign cells used in canonicity gate"` region) — the proven
   `Canonicity.circuit` composite, 3 regions.

**No proofs here yet, deliberately**: the semantic contract depends on how the
Sinsemilla `⊥` case is specced, which is being settled together with the NoteCommit /
CommitIvk proof arc (the `Canonicity` composite and all children are already proven;
only this assembly's bundle + contract are pending). This file pins the VK-relevant
structure (region order, gate configure) so the action-circuit assembly and its VK
fixtures can proceed.
-/

namespace Halo2.Ironwood.CommitIvk.Gadget

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Sinsemilla.HashToPoint (witnessMessagePiece)
open Halo2.Ironwood.NoteCommit.Main (brWit currentRegion)
open Orchard (Point)
open Orchard.Ecc.MulFixed (FixedBase)
open Orchard.Specs (bitrange)
open Orchard.Specs.Sinsemilla (Generators)

/-- The CommitIvk message piece lengths in `K = 10`-bit words:
`a(250) ‖ b(10) ‖ c(240) ‖ d(10)` — the chain convention counts words − 1 per piece. -/
def ns : List ℕ := [24, 0, 23, 0]

theorem ns_ne_nil : ns ≠ [] := by simp [ns]

/-- The gadget inputs: the `ak`/`nk` field-element cells. The blinding scalar `rivk`
enters through the fixed-base mul's window programs (a parameter, like the child
bundle). -/
structure Inputs (F : Type) where
  ak : F
  nk : F
deriving ProvableStruct

/-- The chip configs the gadget consumes (mirrors `NoteCommit.Main.Config`). -/
structure Config where
  gateConfig : CommitIvk.Config
  hashConfig : Sinsemilla.HashPiece.Config
  lookupConfig : LookupRangeCheck.Config 10
  mulConfig : Ecc.MulFixed.FullWidth.Config
  addConfig : Ecc.Add.Config

/-- The `b = b_0 ‖ b_1 ‖ b_2` piece program:
`(bits 250..254 of ak) + (bit 254 of ak)·2⁴ + (bits 0..5 of nk)·2⁵`. -/
def bWit (ak nk : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env ak).val 250 4 : ℕ) : Fp)
      + ((bitrange (readCell env ak).val 254 1 : ℕ) : Fp) * (2 ^ 4 : Fp)
      + ((bitrange (readCell env nk).val 0 5 : ℕ) : Fp) * (2 ^ 5 : Fp)]

/-- The `d = d_0 ‖ d_1` piece program:
`(bits 245..254 of nk) + (bit 254 of nk)·2⁹`. -/
def dWit (nk : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env nk).val 245 9 : ℕ) : Fp)
      + ((bitrange (readCell env nk).val 254 1 : ℕ) : Fp) * (2 ^ 9 : Fp)]

/-- The hash running-sum cell `zs[i][j]`: row `prefixRows ns i + j` of the `bits`
column inside the `hash_to_point` region. -/
def zCell (hcfg : Sinsemilla.HashPiece.Config) (iHash : RegionIndex) (i j : ℕ) :
    AssignedCell Fp :=
  .of iHash (Sinsemilla.Chain.prefixRows ns i + j) hcfg.bits

/-- Rust `gadgets::commit_ivk` (`commit_ivk.rs:260-420`), in exact region order (14
regions). Returns the `ivk` cell — `short_commit`'s `extract_p`, the commitment's
x-coordinate. Parameterized (like the fixed-base mul bundle) by the `rivk` window
programs. -/
def synth (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Inputs (AssignedCell Fp)) : Circuit Fp (Var field Fp) := do
  let i₀ ← currentRegion
  -- the `hash_to_point` region of the `CommitDomain::commit` (region 10 of the flow:
  -- 7 piece/short regions, the 2-region blind)
  let iHash := i₀ + 9
  -- `a` = bits 0..=249 of `ak`
  let a ← witnessMessagePiece cfg.hashConfig (brWit input.ak 0 250)
  -- `b = b_0 ‖ b_1 ‖ b_2`; `b_0` (4 bits) and `b_2` (5 bits) short-checked
  let b0 ← LookupRangeCheck.witnessShortCheck 10 4 cfg.lookupConfig
    (brWit input.ak 250 4)
  let b2 ← LookupRangeCheck.witnessShortCheck 10 5 cfg.lookupConfig
    (brWit input.nk 0 5)
  let b ← witnessMessagePiece cfg.hashConfig (bWit input.ak input.nk)
  -- `c` = bits 5..=244 of `nk`
  let c ← witnessMessagePiece cfg.hashConfig (brWit input.nk 5 240)
  -- `d = d_0 ‖ d_1`; `d_0` (9 bits) short-checked
  let d0 ← LookupRangeCheck.witnessShortCheck 10 9 cfg.lookupConfig
    (brWit input.nk 245 9)
  let d ← witnessMessagePiece cfg.hashConfig (dWit input.nk)
  -- `ivk = Commit^ivk_rivk(…)` — `CommitDomain::short_commit` (`Hash ak||nk`)
  let cm ← (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil).call
    (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[a, b, c, d] }
  -- `ak`/`nk` canonicity + the gate region (the proven `Canonicity` composite);
  -- `z13_a = zs[0][13]`, `z13_c = zs[2][13]` are the hash running-sum cells
  let _ ← (Canonicity.circuit (brWit input.ak 254 1) (brWit input.nk 254 1)).call
    (cfg.gateConfig, cfg.lookupConfig)
    { ak := input.ak, a := a, bWhole := b, b0 := b0, b2 := b2,
      z13A := zCell cfg.hashConfig iHash 0 13,
      nk := input.nk, c := c, dWhole := d, d0 := d0,
      z13C := zCell cfg.hashConfig iHash 2 13 }
  -- `short_commit` returns `extract_p` — the commitment's x-coordinate
  pure cm.x

end Halo2.Ironwood.CommitIvk.Gadget
