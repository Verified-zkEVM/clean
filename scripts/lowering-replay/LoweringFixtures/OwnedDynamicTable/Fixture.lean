import LoweringFixtures.Common
import Midnight.Chips.CertifiedCircuit

/-! `lookup_any(Some(q))` of `x` in the advice column `b`, which no operation assigns: Rust's table
is 0 at every usable row, so `x` must be 0. An advice table is not `owned` (Clean's `env` is
unpinned at unassigned cells), so the lookup is `RowLookupsHold` on Rust's columns and
`exact_meaning` derives `x = 0` from `Satisfied`. -/
namespace LoweringFixtures.OwnedDynamicTable
open Halo2 Midnight Midnight.Keygen Midnight.Chips.CertifiedCircuit LoweringFixtures

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let q ← selector false
  lookupAny "dynamic" q do
    let tb ← advice b
    let x ← advice a
    return #[(x, tb)]

def source : CS := (configure.run {}).2
def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩
/-- `lk.handles`' only entry, spelled out so the kernel need not run `eraseDups`. -/
def handle : Gate F :=
  ({ name := lk.name, selector := ⟨0, false⟩, queries := #[], constraints := #[], rows := true } : GateSpec).toCleanRows rfl

def ops : Operations F :=
  [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableGate handle 0]]

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := ops

#guard source.validate.isOk && !lk.owned && !lk.stated ops
#guard Midnight.Chips.Layout.Planner.simple.starts source.constantColumn ops == [0]

/-- The region's start, 0 (the kernel cannot run the planner's hash map). -/
abbrev start : Nat := Halo2.Layout.place (Midnight.Chips.Layout.Planner.simple.starts source.constantColumn ops) 0

/-- `Satisfied` forces `x = 0` at the region's start, as Rust's all-zero table column does. -/
theorem exact_meaning (env : Environment F) (h : Satisfied source ops 4 (fun _ => 0) env)
    (usable : start < (layoutConfig source 4).usableRows) :
    env.get (Column.toAny (⟨0⟩ : Column .advice)) (start : ℤ) = 0 := by
  have hmem : lk ∈ source.lookups.toList := by
    have h0 : 0 < source.lookups.size := by decide +kernel
    simp only [lk, Array.getElem?_eq_getElem h0, Option.getD_some]
    exact Array.getElem_mem_toList h0
  have hs : lk.stated ops = false := by decide +kernel
  have hsel : lk.selector = .var (.selector ⟨0, false⟩) := by decide +kernel
  have hin : lk.inputs.toList = [#[.var (.advice ⟨0⟩ 0)]] := by decide +kernel
  have htb : lk.table.toList = [.var (.advice ⟨1⟩ 0)] := by decide +kernel
  have hreg : (indexedRegions ops 0).1 = [(0, [.assignAdvice ⟨0⟩ 0 witness, .enableGate handle 0])] := rfl
  have hact : Midnight.Chips.Layout.sourceActivations ops source.constantColumn = [(0, start + 0)] := by
    unfold Midnight.Chips.Layout.sourceActivations
    rw [hreg]
    rfl
  have hcells : adviceCells (Midnight.Chips.Layout.Planner.simple.starts source.constantColumn ops) ops =
      [(0, start + 0)] := by
    unfold adviceCells
    rw [hreg]
    rfl
  have h16 : (layoutConfig source 4).usableRows ≤ 16 := by decide +kernel
  have hmod : ((start : ℤ) % 16).toNat = start := by omega
  have hmax : max ((start : ℤ) % 16) 0 = start := by omega
  have hrow := (List.forall_iff_forall_mem.mp h.2.2) lk hmem hs (fun _ _ => 0) start usable (by
    rw [hsel]
    simp [Expression.eval, rowValuation, hact])
  rw [hin, List.forall_cons] at hrow
  obtain ⟨tr, -, heq⟩ := hrow.1
  rw [htb] at heq
  have hnot : ¬ (layoutConfig source 4).usableRows ≤ start := by omega
  simpa [Expression.eval, rowValuation, hcells, hmod, hnot, Environment.advice, hmax] using heq

end LoweringFixtures.OwnedDynamicTable
