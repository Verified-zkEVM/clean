module

public import Clean.Backends.Plonky3.Print
public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Examples.FemtoCairo.FlatAirTestData
public import Clean.Examples.OpcodeVm.Ensemble
public import Clean.Utils.Primes

@[expose] public section

/-!
# Differential reference for the printed AIRs

The printed constraints, interactions and fixed columns are the AIR that the Rust verifier checks,
and the printed witness generator builds its traces. This executable evaluates the example ensembles
under the Lean semantics: the constraints and interactions of every component on pseudo-random rows,
the fixed columns of every preallocated row, the verifier's interactions on pseudo-random public
inputs, and the generated traces. `backends/plonky3/tests/differential_tests.rs` checks that the
printed Rust reproduces every value.
-/

namespace Backends.Plonky3.Differential

open Air.Flat Air.Flat.WitnessGeneration

abbrev Fb := F pBabybear

/-- Pseudo-random field elements, from a linear congruential generator seeded with `seed`. -/
def randomRow (seed width : ℕ) : Array Fb :=
  let next (state : ℕ) := (state * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  ((List.range width).foldl (fun (state, row) _ => (next state, row.push (state : Fb)))
    (next (seed + 1), #[])).2

def noData : ProverData Fb := fun _ _ => #[]

def u64List (values : List Fb) : String :=
  s!"&[{Print.commaSep (values.map fun value => s!"{value.val}")}]"

def interactionsToRust (interactions : List (Interaction Fb)) : String :=
  s!"&[{Print.commaSep (interactions.map fun interaction =>
    s!"ExpectedInteraction \{ channel: {Print.quoted interaction.channel.name}, \
      direction: {Print.directionToRust interaction.direction}, \
      multiplicity: {interaction.mult.val}, message: {u64List interaction.msg.toList} }")}]"

/-- The values of the fixed cells of a preallocated or standalone row, in column order. -/
def fixedRow (component : Component Fb) (row : ℕ) : List Fb :=
  let (cells, steps) := component.generation.cells
  let ctx := inputContext steps (rowEnvironment (.empty Fb)) row
  cells.toList.filterMap fun
    | .fixed value => some (value.eval ctx)
    | _ => none

def componentToRust (component : Component Fb) (index : ℕ) : String :=
  let rows := (List.range 3).map fun k => randomRow (31 * index + k) component.width
  let environments := rows.map (Environment.fromArray · noData)
  let fixedRows := match component.generation with
    | .preallocated { height, .. } | .standalone { height, .. } =>
        (List.range height.toNat).map (fixedRow component)
    | .demand _ | .segments _ => []
  s!"ExpectedComponent \{
        rows: &[{Print.commaSep (rows.map (u64List ·.toList))}],
        constraints: &[{Print.commaSep (environments.map fun env =>
          u64List (component.operations.constraints.map (·.eval env)))}],
        interactions: &[{Print.commaSep (environments.map fun env =>
          interactionsToRust (component.operations.interactionValues env))}],
        fixed_rows: &[{Print.commaSep (fixedRows.map u64List)}],
    }"

/-- The expected values of an ensemble, and the traces generated for one public and private input.
-/
def ensembleToRust {PublicIO : TypeMap} [ProvableType PublicIO] (name : String)
    (ens : Ensemble Fb PublicIO) (publicInput : PublicIO Fb) (proverInput : ens.ProverInput Fb)
    (witness : Except GenerationError (EnsembleWitness ens)) : Except String String :=
  match witness with
  | .error error => .error (toString error)
  | .ok witness =>
  let publicRows := (List.range 3).map fun k => randomRow (1000 + k) (size PublicIO)
  let tables := witness.tables.map fun table => s!"&[{Print.commaSep
    (table.table.map (u64List ·.toList))}]"
  .ok s!"pub const {name}: ExpectedEnsemble = ExpectedEnsemble \{
    components: &[{Print.commaSep (ens.tables.zipIdx.map fun (component, index) =>
      componentToRust component index)}],
    public_rows: &[{Print.commaSep (publicRows.map (u64List ·.toList))}],
    verifier_interactions: &[{Print.commaSep (publicRows.map fun row =>
      interactionsToRust (ens.verifierOperations.interactionValues
        (Environment.fromArray row noData)))}],
    public_input: {u64List (toElements publicInput).toList},
    prover_input: {u64List (toElements proverInput).toList},
    tables: &[{Print.commaSep tables}],
};"

def fibonacciCase : Except String String :=
  let state := fibonacci 32
  let publicInput : fieldTriple Fb := (32, state.1, state.2)
  ensembleToRust "FIBONACCI" fibonacciEnsemble.ensemble publicInput ()
    (fibonacciGenerate publicInput 1000)

open Examples.FemtoCairo FlatAirTestData in
def femtoCairoCase : Except String String :=
  let ens := FlatAir.formalEnsemble testProgram testProgram_valid memorySize_lt initialState
  let memory : fields 8 Fb := #v[0, 5, 3, 7, 2, 10, 0, 0]
  ensembleToRust "FEMTOCAIRO" ens.ensemble (0, 0) memory
    (FlatAir.femtoCairoGenerate testProgram testProgram_valid memorySize_lt memory initialState
      (0, 0) 1000)

def opcodeVmCase : Except String String :=
  let ens := (OpcodeVm.formalEnsemble OpcodeVm.exampleProgram OpcodeVm.exampleProgram_length
    (2 : Fb)).ensemble
  let final := OpcodeVm.run OpcodeVm.exampleProgram (2 : Fb)
  ensembleToRust "OPCODE_VM" ens final () (generate ens 1000 final ())

def prelude : String := "// Generated by Clean from the example ensembles. Do not edit.

use clean_backend::witness_generation::Direction;

pub struct ExpectedInteraction {
    pub channel: &'static str,
    pub direction: Direction,
    pub multiplicity: u64,
    pub message: &'static [u64],
}

pub struct ExpectedComponent {
    pub rows: &'static [&'static [u64]],
    pub constraints: &'static [&'static [u64]],
    pub interactions: &'static [&'static [ExpectedInteraction]],
    pub fixed_rows: &'static [&'static [u64]],
}

pub struct ExpectedEnsemble {
    pub components: &'static [ExpectedComponent],
    pub public_rows: &'static [&'static [u64]],
    pub verifier_interactions: &'static [&'static [ExpectedInteraction]],
    pub public_input: &'static [u64],
    pub prover_input: &'static [u64],
    pub tables: &'static [&'static [&'static [u64]]],
}
"

def run : IO Unit := do
  match do return [← fibonacciCase, ← femtoCairoCase, ← opcodeVmCase] with
  | .ok ensembles => IO.print (Print.lines (prelude :: ensembles) ++ "\n")
  | .error error => throw (IO.userError error)

end Backends.Plonky3.Differential

def main : IO Unit := Backends.Plonky3.Differential.run
