module

public import Clean.Backends.Plonky3.Print
public import Clean.Utils.Primes

@[expose] public section

/-!
# Differential reference for the witness IR Rust renderer

Generated Rust evaluates witness IR in witness generation, in prover row initialization, and in
fixed columns, where it defines verifier-known values and is therefore trusted for soundness. This
executable renders witness programs covering every witness IR constructor, including
wrapping, out-of-range, and division-by-zero edge cases, together with their values under the Lean
semantics. `backends/plonky3/tests/witness_ir_reference_tests.rs` checks that the generated Rust
reproduces every value.
-/

namespace Backends.Plonky3.Reference

open Witgen

abbrev Fb := F pBabybear

structure Case where
  width : ℕ
  steps : List (Step Fb)
  output : VExpr Fb width

def input : Array Fb := #[0, 1, -1, 2^30, 12345, 7, 255, -2]

def hintRows : List (List Fb) := [[3], [-1], [0], [42]]

def hint : ProverHint Fb := fun key n =>
  if key = "hint" ∧ n = 1 then
    (hintRows.map fun row => Vector.ofFn fun i : Fin n => row[i.val]?.getD 0).toArray
  else #[]

def memoryRows : List (List Fb) := [[5, 15], [7, 17]]

/-- Like data derived from committed rows, `memory` only has rows at its input width 2. -/
def data : ProverData Fb := fun key n =>
  if key = "memory" ∧ n = 2 then
    (memoryRows.map fun row => Vector.ofFn fun i : Fin n => row[i.val]?.getD 0).toArray
  else #[]

def rowIndices : List ℕ := [0, 1, 2, 3, 4, 63, 64, 65, 255, 256, 1000, pBabybear + 3, 2^32 + 5]

def cell (index : ℕ) : FExpr Fb := .expr (.var ⟨index⟩)

/-- The row index, or the loop index inside `mapRange`, as a field element. -/
def idx : FExpr Fb := .ofU64 .idx

def u (value : UInt64) : U64Expr Fb := .const value

def bool (condition : BExpr Fb) : FExpr Fb := .ite condition (.const 1) (.const 0)

def cases : List Case := [
  -- field operations, field constants, inverse of zero, reduction of u64 values and indices
  { width := 9, steps := [], output := .lit #v[
      .expr (.add (.var ⟨0⟩) (.mul (.var ⟨2⟩) (.var ⟨3⟩))),
      .const (-1), idx,
      .add (cell 2) (cell 1), .mul (cell 2) (cell 7),
      .inv (cell 0), .inv (cell 3),
      .ofU64 (u 0xFFFFFFFFFFFFFFFF), .ofU64 .idx] },
  -- u64 operations, including wrapping, division by zero, and shift amounts of 64 and more
  { width := 20, steps := [], output := .lit #v[
      .ofU64 (.val (cell 2)), .ofU64 (.val (cell 7)),
      .ofU64 (.add (u 0xFFFFFFFFFFFFFFFF) (u 2)),
      .ofU64 (.mul (u 0x8000000000000001) (u 6)),
      .ofU64 (.div (u 100) (u 7)), .ofU64 (.div (u 100) (u 0)),
      .ofU64 (.mod (u 100) (u 7)), .ofU64 (.mod (u 100) (u 0)),
      .ofU64 (.land (u 0xF0F0) (.val (cell 6))), .ofU64 (.lor (u 0xF000) (.val (cell 5))),
      .ofU64 (.lxor (u 0xFFFF) (.val (cell 4))),
      .ofU64 (.shiftL (u 3) (u 63)), .ofU64 (.shiftL (u 3) (u 64)),
      .ofU64 (.shiftL (u 3) (u 65)), .ofU64 (.shiftR (u 0xFFFFFFFFFFFFFFFF) (u 70)),
      .ofU64 (.shiftR .idx (u 1)), .ofU64 (.mod .idx (u 3)),
      .ofU64 (.ite (.lt .idx (u 64)) (u 1) (u 2)),
      .ofU64 (.mul .idx .idx), .ofU64 (.add (.val idx) (u 1))] },
  -- conditions
  { width := 16, steps := [], output := .lit #v[
      bool .true, bool .false,
      bool (.feq (cell 2) (.const (-1))), bool (.feq idx (.const 3)),
      bool (.neq .idx (u 64)), bool (.lt (.val (cell 2)) (u 5)),
      bool (.flt (cell 1) (cell 2)), bool (.flt (cell 2) (cell 1)),
      bool (.bit (cell 2) 0), bool (.bit (cell 3) 30), bool (.bit (cell 2) 63),
      bool (.bit (cell 2) 64), bool (.bit (cell 2) 200), bool (.bit idx 1),
      bool (.not (.lt .idx (u 2))), bool (.and (.lt .idx (u 100)) (.lt (u 2) .idx))] },
  -- list reads at computed and row indices, in and out of range
  { width := 7, steps := [], output := .lit #v[
      .listGet [.const 10, .const 11, .const 12] .idx,
      .listGet [.const 10, .const 11, .const 12] (u 0xFFFFFFFFFFFFFFFF),
      .listGet [cell 4, .add (cell 5) idx, .inv (cell 2)] (.mod .idx (u 4)),
      .listGet [] (u 0),
      .listGet [.const 20, .const 21, .const 22, .const 23] .idx,
      .listGet [cell 6, .mul idx idx, .const 9] .idx,
      .listGet [] .idx] },
  -- vector formers
  { width := 82, steps := [], output :=
      .append (.mapRange 5 (.add idx (.listGet [.const 100, .const 200] .idx)))
        (.append (.envRange (n := 4) 6)
          (.append (.bitsOf (n := 70) (cell 2))
            (.append (.bitsOf (n := 3) idx) (.lit #v[])))) },
  -- `let` steps of both sorts, referenced from later steps and from the output
  { width := 5,
    steps := [
      .letF (.add (cell 3) idx),
      .letU (.add (.val (.localVar 0)) .idx),
      .letF (.mul (.localVar 0) (.ofU64 (.localVar 1))),
      .letU (.ite (.lt (.localVar 1) (u 1000)) (.localVar 1) (u 7))],
    output := .lit #v[.localVar 0, .ofU64 (.localVar 1), .localVar 2, .ofU64 (.localVar 3),
      .listGet [.localVar 0, .localVar 2] (.mod (.localVar 3) (u 2))] },
  -- runtime prover input and committed prover data, in and out of range
  { width := 9, steps := [], output := .lit #v[
      .hintGet "hint" 1 (u 0) 0, .hintGet "hint" 1 (u 1) 0, .hintGet "hint" 1 (.mod .idx (u 4)) 0,
      .hintGet "hint" 1 (u 0xFFFFFFFFFFFFFFFF) 0, .hintGet "hint" 2 (u 0) 0,
      .dataGet "memory" 2 (u 0) 0, .dataGet "memory" 2 (.mod .idx (u 3)) 1,
      .dataGet "memory" 3 (u 0) 0, .dataGet "missing" 2 (u 0) 0] }
]

def Case.eval (c : Case) (row : ℕ) : Vector Fb c.width :=
  let env : ProverEnvironment Fb := {
    get index := input[index]?.getD 0
    data
    hint
  }
  c.output.eval {
    env
    locals := evalSteps env c.steps #[] row
    idx := row
  }

def u64List (values : List ℕ) : String :=
  s!"&[{Print.commaSep (values.map fun value => s!"{value}u64")}]"

def Case.toRust (c : Case) (index : ℕ) : Except String String := do
  let body ← Print.outputToRust c.steps c.output "input" "row"
  return s!"pub fn case_{index}<F: WitnessField>(input: &[F], row: u64, _hint: &WitnessData<F>, _data: &WitnessData<F>) -> Vec<F> \{\n{body}\n    output\n}"

def render : Except String String := do
  let functions ← cases.zipIdx.mapM fun (c, index) => c.toRust index
  let dispatch := Print.commaSep <| cases.zipIdx.map fun (_, index) => s!"{index} => case_{index}(input, row, hint, data)"
  let expected := Print.commaSep <| cases.map fun c =>
    s!"&[{Print.commaSep (rowIndices.map fun row => u64List ((c.eval row).toList.map (·.val)))}]"
  let memory := Print.commaSep (memoryRows.map fun row => u64List (row.map (·.val)))
  return s!"// Generated by Clean from `Clean/Backends/Plonky3/Reference.lean`. Do not edit.
use clean_backend::witness_generation::\{WitnessData, WitnessField};
use alloc::vec::Vec;

{Print.u64Helpers}
pub const FIELD_ORDER: u64 = {Print.fieldOrder (F := Fb)};
pub const INPUT: &[u64] = {u64List (input.toList.map (·.val))};
pub const HINT: &[&[u64]] = &[{Print.commaSep (hintRows.map fun row => u64List (row.map (·.val)))}];
pub const MEMORY: &[&[u64]] = &[{memory}];
pub const ROW_INDICES: &[u64] = {u64List rowIndices};
#[rustfmt::skip]
pub const EXPECTED: &[&[&[u64]]] = &[{expected}];

{String.intercalate "\n\n" functions}

pub fn eval_case<F: WitnessField>(case: usize, input: &[F], row: u64, hint: &WitnessData<F>, data: &WitnessData<F>) -> Vec<F> \{
    match case \{ {dispatch}, _ => unreachable!(\"invalid reference case\") }
}
"

end Backends.Plonky3.Reference

def main : IO Unit := do
  match Backends.Plonky3.Reference.render with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
