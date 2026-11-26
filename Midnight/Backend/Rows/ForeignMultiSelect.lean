import Midnight.Frontend.Configure
import Midnight.Keygen.Configure
import Clean.Halo2.ConfigurationHolds

/-! Foreign ECC's `multi_select` lookup (circuits/src/ecc/foreign/common.rs:189-256) as a
`RowsCircuit`. `lookup_any(None)` of `(v, (1 - q) * v)` over the index, x and y limbs and the
fixed tag has no shadow, so its meaning is `ConfigurationHolds`. At the row where synthesis
enables `q`, the tag is 7, so the matching table row has `q` off: there the table side is the
row's own cells, and the lookup row's limbs are some such row's. -/

namespace Midnight.Backend.Rows.ForeignMultiSelect
open Halo2 (Column ConfigureExtension LookupExtension Environment Operations RegionOperations
  RegionIndex Gate WitgenIR ConfigurationHolds ConfigurationHoldsAt RowsCircuit Expression)
open Midnight.Keygen (E)

def configure : Frontend.Configure Unit := do
  let x0 ← Frontend.adviceColumn
  let x1 ← Frontend.adviceColumn
  let y0 ← Frontend.adviceColumn
  let y1 ← Frontend.adviceColumn
  let idx ← Frontend.adviceColumn
  for c in [x0, x1, y0, y1] do Frontend.enableEquality c
  let q ← Frontend.complexSelector
  Frontend.enableEquality idx
  let tag ← Frontend.fixedColumn
  Frontend.lookupAny "multi_select lookup" none do
    let sel ← Frontend.querySelector q
    let notSel := Keygen.Rust.sub (.const 1) sel
    let mut identities : Array (E × E) := #[]
    for c in [idx, x0, x1, y0, y1] do
      let v ← Frontend.advice c
      identities := identities.push (v, Keygen.Rust.mul notSel v)
    let t ← Frontend.fixed tag
    return identities.push (t, Keygen.Rust.mul notSel t)

def sel : E := .var (.selector ⟨0, false⟩)
def notSel : E := .add (.const 1) (Keygen.Rust.neg sel)
def adv (c : ℕ) : E := .var (.advice ⟨c⟩ 0)
def tagCell : E := .var (.fixed ⟨0⟩ 0)

def entry : LookupExtension F where
  name := "multi_select lookup"
  any := true
  selector := none
  queriedCells := [sel, adv 4, adv 0, adv 1, adv 2, adv 3, tagCell]
  columns := ([4, 0, 1, 2, 3].map fun c => ([adv c], Keygen.Rust.mul notSel (adv c))) ++
    [([tagCell], Keygen.Rust.mul notSel tagCell)]

deriving instance DecidableEq for Halo2.GateExtension
deriving instance DecidableEq for Halo2.LookupExtension
deriving instance DecidableEq for Halo2.ConfigureExtension

/-- The program records the batch and one handle on `q`. -/
theorem extensions_eq :
    (configure.run {}).2.extensions = [.lookup entry, .gate { mode := .handle }] := by
  decide +kernel

theorem tuples_eq : entry.tuples = [[adv 4, adv 0, adv 1, adv 2, adv 3, tagCell]] := by
  decide +kernel

theorem tables_eq : entry.tables = ([4, 0, 1, 2, 3].map fun c => Keygen.Rust.mul notSel (adv c)) ++
    [Keygen.Rust.mul notSel tagCell] := by
  decide +kernel

/-- Keygen never reads advice values. -/
def witness : WitgenIR F 1 := .native fun _ => #v[0]

/-- The handle synthesis enables `q` with. -/
def handle : Gate F := Gate.handle "multi_select lookup" ⟨0, false⟩ [] trivial

def limbs : RegionOperations F := [4, 0, 1, 2, 3].map fun c => .assignAdvice ⟨c⟩ 0 witness

/-- `fill_dynamic_lookup_row`: the lookup row enables `q`; table rows do not. Copies are left
out, since the statement below does not use them. -/
def operations : Operations F :=
  [.region "multi_select lookup" (.assignFixed ⟨0⟩ 0 7 :: .enableGate handle 0 :: limbs),
    .region "multi_select table" (.assignFixed ⟨0⟩ 0 7 :: limbs),
    .region "multi_select table" (.assignFixed ⟨0⟩ 0 7 :: limbs)]

/-- The lookup row's index and limbs are those of a usable row where `q` is off. -/
def Spec (n : ℕ) (place : RegionIndex → ℕ) (env : Environment F) : Prop :=
  place 0 < env.usableRows → env.usableRows ≤ n →
    ∃ t < env.usableRows, (0, t) ∉ operations.enabledSelectors place 0 ∧
      ∀ c ∈ [4, 0, 1, 2, 3], env.advice ⟨c⟩ (place 0) = env.advice ⟨c⟩ t

private theorem wrap_of_lt {row n : ℕ} (h : row < n) : ((row : ℤ) + 0) % (n : ℤ) = row := by
  rw [add_zero]
  exact Int.emod_eq_of_lt (by omega) (by omega)

private theorem seven_ne_zero : (7 : F) ≠ 0 := by
  decide

private theorem table_value (s x : F) :
    (1 : F) * (1 + -1 * s) * (1 * x) = (1 - s) * x := by
  ring

theorem soundness (n : ℕ) (place : RegionIndex → ℕ) (env : Environment F)
    (constraints : Halo2.Constraints place env operations 0)
    (holds : ConfigurationHolds (configure.run {}).2 n operations place env) :
    Spec n place env := by
  intro hrow hn
  have htag : env.fixed ⟨0⟩ (place 0) = 7 := constraints.1.1
  unfold ConfigurationHolds ConfigurationHoldsAt at holds
  rw [extensions_eq] at holds
  obtain ⟨hlookup, -⟩ := holds
  have hm := hlookup rfl (place 0) hrow (by show (1 : F) ≠ 0; exact one_ne_zero)
  rw [tuples_eq] at hm
  obtain ⟨t, ht, heq⟩ := hm
  rw [tables_eq] at heq
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq,
    and_true, adv, tagCell, notSel, sel, Keygen.Rust.mul, Keygen.Rust.neg, Expression.eval,
    Halo2.wrappedRowValue, table_value, wrap_of_lt (hrow.trans_le hn),
    wrap_of_lt (ht.trans_le hn)] at heq
  obtain ⟨h4, h0, h1, h2, h3, htg⟩ := heq
  refine ⟨t, ht, fun hs => ?_, ?_⟩
  · rw [ite_eq_left hs, sub_self, zero_mul, htag] at htg
    exact seven_ne_zero htg
  · have hs : (0, t) ∉ operations.enabledSelectors place 0 := by
      intro hs
      rw [ite_eq_left hs, sub_self, zero_mul, htag] at htg
      exact seven_ne_zero htg
    rw [ite_eq_right hs, sub_zero, one_mul] at h4 h0 h1 h2 h3
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact h4
    · exact h0
    · exact h1
    · exact h2
    · exact h3

/-- `Constraints ∧ ConfigurationHolds` gives the lookup's meaning. -/
def circuit : RowsCircuit F Unit where
  configure := configure
  synthesize _ := operations
  Spec _ := Spec
  soundness := soundness

end Midnight.Backend.Rows.ForeignMultiSelect
