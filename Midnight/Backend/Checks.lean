import Midnight.SHA256.Configure
import Midnight.Poseidon.Configure
import Midnight.Backend.Fixtures

/-! Regressions for the Midnight backend: the SHA-256, Poseidon and native configure programs
compile to the frozen fixtures, and each branch no port covers compiles as the same program
written in `ConfigM`. `SHA256.configured` is the compiled SHA-256 program, so
`SHA256.KeyCheck.rust_key` derives Rust's key from the compiled source. -/

deriving instance DecidableEq for Midnight.LookupBatch
deriving instance DecidableEq for Midnight.Keygen.GateSpec
-- `rejectedLookups`' element type exceeds the default instance size.
set_option synthInstance.maxSize 1024 in
deriving instance DecidableEq for Midnight.Keygen.CS

namespace Midnight.Backend.Checks
open Midnight.Keygen
open Halo2 (Column)

theorem sha256_cs : compile Frontend.SHA256.configure = Fixtures.sha256 := by
  decide +kernel

theorem poseidon_cs : compile Frontend.Poseidon.configure = Fixtures.poseidon := by
  decide +kernel

/-! Branch checks. Each program ends with a gate, so `currentQueries` is that gate's closure in
both the compiled program and its reference. -/

private def endGate (a : Column .advice) : Frontend.Configure Unit := do
  let q ← Frontend.selector
  Frontend.gate "end" q do return #[("", ← Frontend.advice a)]

private def endGateM (a : Nat) : ConfigM Unit := do
  let q ← Keygen.selector
  Keygen.gate "end" q do return #[("", ← Keygen.advice a)]

/-- `without_selector` owned by one selector. -/
private def ownedGate : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let q ← Frontend.selector
  Frontend.gateWithoutSelector "owned" do
    let x ← Frontend.advice a
    return #[("", Halo2.querySelector q * x)]
  endGate a

private def ownedGateM : ConfigM Unit := do
  let a ← Keygen.adviceColumn
  let q ← Keygen.selector
  Keygen.gateWithoutSelector "owned" do
    let x ← Keygen.advice a
    return #[("", Halo2.querySelector q * x)]
  endGateM a

theorem owned_gate_cs : compile ownedGate = (ownedGateM.run {}).2 := by
  native_decide

/-- `enable_constant`, `set_minimum_degree` and equality. -/
private def constantsProgram : Frontend.Configure Unit := do
  let c ← Frontend.fixedColumn
  Frontend.enableConstant c
  Frontend.setMinimumDegree 7
  let a ← Frontend.adviceColumn
  Frontend.enableEquality a
  Frontend.enableConstant c
  endGate a

private def constantsProgramM : ConfigM Unit := do
  let c ← Keygen.fixedColumn
  Keygen.enableConstant c
  Keygen.setMinimumDegree 7
  let a ← Keygen.adviceColumn
  Keygen.enableEquality ⟨.advice, a⟩
  Keygen.enableConstant c
  endGateM a

theorem constants_cs : compile constantsProgram = (constantsProgramM.run {}).2 := by
  native_decide

/-- Clean's own `lookup`, unmarked: a batch of one tuple, unnamed. -/
private def cleanLookup : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let q ← Frontend.complexSelector
  let t ← Frontend.lookupTableColumn
  Halo2.lookup [Halo2.queryAdvice a 0] q [(Halo2.queryAdvice a 0, t)]
    (_hnoSimpleSelectors := by simp [Halo2.Expression.noSimpleSelectors_queryAdvice])
  endGate a

private def cleanLookupM : ConfigM Unit := do
  let a ← Keygen.adviceColumn
  let q ← Keygen.selector false
  let t ← Keygen.fixedColumn
  Keygen.batchedLookup "" (some q) do
    let x ← Keygen.advice a
    return #[(#[x], t)]
  endGateM a

theorem clean_lookup_cs : compile cleanLookup = (cleanLookupM.run {}).2 := by
  native_decide

/-- The native and pow2range chips as `ZkStdLib::configure` shares them. -/
private def native : Frontend.Configure Unit := do
  let advice ← (Array.range 5).mapM fun _ => Frontend.adviceColumn
  let fixed ← (Array.range 9).mapM fun _ => Frontend.fixedColumn
  let committed ← Frontend.instanceColumn
  let inst ← Frontend.instanceColumn
  Frontend.nativeConfigure advice fixed #[committed, inst]
  Frontend.rangeConfigure (advice.extract 1 2)
  endGate advice[0]!

theorem native_cs : compile native = Fixtures.native := by
  decide +kernel

/-- A range over two columns: the closure queries `tag` once and reuses it, so the backend must
replay the recorded closure, not the shadows' atoms. -/
private def rangeTwo : Frontend.Configure Unit := do
  let values ← (Array.range 2).mapM fun _ => Frontend.adviceColumn
  Frontend.rangeConfigure values
  endGate values[0]!

theorem range_cs : compile rangeTwo = Fixtures.rangeTwo := by
  decide +kernel

/-- A body the closure layer refuses is an error, as in `ConfigM`. -/
private def emptyBody : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let q ← Frontend.selector
  Frontend.gate "empty" q (pure #[])
  endGate a

theorem empty_errors :
    (compile emptyBody).errors = #["gate empty: expected a nonempty constraint body"] := by
  native_decide

/-- Unblinded advice is an error, not ordinary advice. -/
private def unblinded : Frontend.Configure Unit := do
  let a ← Frontend.unblindedAdviceColumn
  endGate a

theorem unblinded_errors : (compile unblinded).errors = #["unblinded advice: unsupported"] := by
  native_decide

/-- A multi-selector `without_selector` body is a rows gate. -/
private def rowsBody : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let q ← Frontend.selector
  let r ← Frontend.selector
  Frontend.gateWithoutSelector "rows" do
    let x ← Frontend.advice a
    return #[("", Halo2.querySelector q * Halo2.querySelector r * x)]
  endGate a

private def rowsBodyM : ConfigM Unit := do
  let a ← Keygen.adviceColumn
  let q ← Keygen.selector
  let r ← Keygen.selector
  Keygen.gateWithoutSelector "rows" do
    let x ← Keygen.advice a
    return #[("", Halo2.querySelector q * Halo2.querySelector r * x)]
  endGateM a

theorem rows_cs : compile rowsBody = (rowsBodyM.run {}).2 := by
  native_decide

/-- SHA-256 records only stated entries, so its `ConfigurationHolds` is `True`. -/
theorem sha256_stated :
    (Frontend.SHA256.configure.run {}).2.extensions.all (·.stated) = true := by
  native_decide

/-- An entry that does not describe its shadows is an error, not a silent batch. -/
private def misMarked : Halo2.ConstraintSystem F :=
  { (cleanLookup.run {}).2 with
    extensions := [.lookup
      { name := "bad", selector := some ⟨0⟩, queriedCells := [], columns := [], shadows := 2 }] }

theorem mis_marked_errors : ((replay misMarked).run {}).2.errors.size ≠ 0 := by
  native_decide

/-- An entry whose columns hold different numbers of inputs is an error, not a padded batch. -/
private def ragged : Halo2.ConstraintSystem F :=
  { (cleanLookup.run {}).2 with
    extensions := [.lookup
      { name := "ragged", any := true, selector := none, queriedCells := [.var (.advice ⟨0⟩ 0)],
        columns := [([.var (.advice ⟨0⟩ 0), .var (.advice ⟨0⟩ 0)], .var (.advice ⟨0⟩ 0)),
          ([.var (.advice ⟨0⟩ 0)], .var (.advice ⟨0⟩ 0))] }] }

theorem ragged_errors : ((replay ragged).run {}).2.errors.contains
    "lookup ragged: columns with different numbers of inputs" = true := by
  native_decide

/-- A simple selector in a `lookup_any` expression is an error, as in Rust. -/
private def simpleLookup : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let q ← Frontend.selector
  Frontend.lookupAny "simple" none do
    let s ← Frontend.querySelector q
    let x ← Frontend.advice a
    return #[(x, s)]
  endGate a

theorem simple_lookup_errors :
    (compile simpleLookup).errors =
      #["lookup simple: a simple selector in a lookup expression"] := by
  native_decide

/-- A `without_selector` closure keeps its `query_selector` calls in order with repeats, as Rust's
`queried_selectors`: here `r, q, r` on a rows gate over two complex selectors, since Rust refuses
a product of simple ones (circuit.rs:1271). -/
private def selectorCalls : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let q ← Frontend.complexSelector
  let r ← Frontend.complexSelector
  Frontend.gateWithoutSelector "calls" do
    let sr ← Frontend.querySelector r.toSelector
    let sq ← Frontend.querySelector q.toSelector
    let _ ← Frontend.querySelector r.toSelector
    let x ← Frontend.advice a
    return #[("", sq * sr * x)]

theorem selector_calls :
    ((selectorCalls.run {}).2.extensions.filterMap fun
      | .gate e => if e.mode = .rows then some (e.queriedSelectors.map (·.index)) else none
      | _ => none) = [[1, 0, 1]] := by
  native_decide

theorem selector_calls_compiled :
    ((compile selectorCalls).queriedSelectors 0).toList.map (·.index) = [1, 0, 1] := by
  native_decide

/-- An owned gate that queries and discards `q` twice and returns `r * x` gets `q, q, r`: the
calls, then the selector the polynomial walk meets. -/
private def ownedCalls : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let q ← Frontend.selector
  let r ← Frontend.selector
  Frontend.gateWithoutSelector "owned calls" do
    let _ ← Frontend.querySelector q
    let _ ← Frontend.querySelector q
    let x ← Frontend.advice a
    return #[("", Halo2.querySelector r * x)]

theorem owned_calls_compiled :
    (compile ownedCalls).gates.size = 1 ∧
      ((compile ownedCalls).queriedSelectors 0).toList.map (·.index) = [0, 0, 1] := by
  native_decide

end Midnight.Backend.Checks
