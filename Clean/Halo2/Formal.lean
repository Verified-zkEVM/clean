import Clean.Halo2.Basic

/-!
# Halo2 formal circuits — DESIGN SKETCH

Port of `Clean/Circuit/Formal.lean`, the proof-boundary packages that turn a circuit
into a subcircuit with a semantic contract. Deliberately simplified from main Clean per
design discussion:

- **One structure, `FormalCircuit`** — the hint-aware `GeneralFormalCircuit.WithHint`
  under the shorter name. No separate `FormalCircuit`/`FormalAssertion`/
  `GeneralFormalCircuit` variants (they were a UX nicety; `WithHint` was already
  pervasive in the phase-one Orchard port). Input/Output are general `CircuitType`s;
  the cost is that identities like `Value M F = M F` hold only up to defeq (not
  reducibly), making inputs slightly less ergonomic — tolerated.
- **No channels / `ProverData`**: halo2 has no interaction argument, and lookup tables
  are fixed columns (`Environment` carries no `data`). The `FormalCircuitBase` channel
  machinery is gone; the base collapses into `FormalCircuit` directly.
- **`Witness` slot + constructive extractor** for knowledge soundness (see the
  requirements doc): `Spec` receives a high-level witness computed by `extract` from the
  low-level witness (placement + environment). Extractors compose through the subcircuit
  tree. `Witness` defaults to `unit` (ordinary input/output soundness).
- **Region-relative**: soundness/completeness quantify over the starting region index
  `i₀` and the placement `place` (the analogues of main Clean's `offset`).

This file sketches the **layouter-level** `FormalCircuit` (over `Circuit`). A
region-level `FormalRegionCircuit` (over `RegionCircuit`, for `assign_region` fragments
composed inside a parent region like `add_incomplete` inside variable-base mul) mirrors
it and is added with the first region-level consumer.

The forward lemmas and the hypothesis-rewriting tactic (`circuit_proof_start` analogue)
live in a companion tactic file; here we provide the data + statements they consume.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {Input Output Witness : TypeMap}

/-- Verifier-view evaluation of a halo2 circuit variable, given a placement + env. -/
abbrev evalCells [CircuitType Input] (pe : Placed Environment F) (v : Var Input F) : Value Input F :=
  CircuitTypeOver.evalVerifier pe v

/-- Prover-view evaluation (hints visible). -/
abbrev evalCellsProver [CircuitType Input] (pe : Placed ProverEnvironment F) (v : Var Input F) :
    ProverValue Input F :=
  CircuitTypeOver.evalProver pe v

/-- Bundles the circuit metadata exposed in reduced form (main Clean's
`ElaboratedCircuit`): the output cells and the number of region indices consumed, as
functions of the input variable and starting region index, so parent circuits simplify
without unfolding `main`. -/
class ElaboratedCircuit (F : Type) [FiniteField F] (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output] (main : Var Input F → Circuit F (Var Output F)) where
  output : Var Input F → RegionIndex → Var Output F
  regionCount : Var Input F → ℕ
  output_eq : ∀ input i, output input i = (main input).output i := by intro _ _; rfl
  regionCount_eq : ∀ input i,
    regionCount input = Operations.regionCount ((main input).operations i) := by intro _ _; rfl

section Statements
variable [CircuitType Input] [CircuitType Output]

/-- Soundness (verifier view — hints erased). If the constraints of `main` hold at
placement `place` from region index `i₀`, then `Spec` holds on the input, the extracted
high-level witness, and the output. -/
def FormalCircuit.Soundness
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Witness F → Value Output F → Prop) : Prop :=
  ∀ (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment F)
    (input_var : Var Input F) (input : Value Input F),
  evalCells ⟨place, env⟩ input_var = input →
  Assumptions input →
  Constraints place env ((main input_var).operations i₀) i₀ →
  Spec input (extract input_var i₀ ⟨place, env⟩)
    (evalCells ⟨place, env⟩ (ElaboratedCircuit.output main input_var i₀))

/-- Completeness (prover view — hints visible). Under the honest prover's witness
generators, `ProverAssumptions` imply the constraints and the `ProverSpec`. -/
def FormalCircuit.Completeness
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (ProverAssumptions : ProverValue Input F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop) : Prop :=
  ∀ (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment F)
    (input_var : Var Input F),
  ExtendsWitnesses place env ((main input_var).operations i₀) i₀ →
  ∀ (input : ProverValue Input F),
  evalCellsProver ⟨place, env⟩ input_var = input →
  ProverAssumptions input env.hint →
  Constraints place env.toEnvironment ((main input_var).operations i₀) i₀ ∧
  ProverSpec input
    (evalCellsProver ⟨place, env⟩ (ElaboratedCircuit.output main input_var i₀)) env.hint

end Statements

/--
A formal circuit: a layouter-level circuit packaged with its contract. Single
structure (the hint-aware variant), general `CircuitType` I/O, constructive high-level
`Witness` extractor. The proof boundary — parents consume `Spec` opaquely.

Circuits with a trivial witness leave `Witness := unit` (default) and set
`extract := fun _ _ _ => ()`.
-/
structure FormalCircuit (F : Type) [FiniteField F] (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output] where
  name : String := "anonymous"
  main : Var Input F → Circuit F (Var Output F)
  elaborated : ElaboratedCircuit F Input Output main := by
    first | infer_instance | (constructor <;> intro _ _ <;> rfl)

  /-- The high-level witness type (default `unit`: ordinary I/O soundness). -/
  Witness : TypeMap := unit
  /-- Constructive extractor: the high-level witness from the low-level one
  (placement + environment), given the input variable and starting region index. -/
  extract : Var Input F → RegionIndex → Placed Environment F → Witness F

  /-- Verifier-view precondition (hints erased). -/
  Assumptions : Value Input F → Prop := fun _ => True
  /-- Verifier-view postcondition: relates input, extracted witness, and output. -/
  Spec : Value Input F → Witness F → Value Output F → Prop

  /-- Prover-view precondition (hints visible). -/
  ProverAssumptions : ProverValue Input F → ProverHint F → Prop := fun _ _ => True
  /-- Prover-view postcondition, proved alongside the constraints. -/
  ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop := fun _ _ _ => True

  soundness : FormalCircuit.Soundness main extract Assumptions Spec
  completeness : FormalCircuit.Completeness main ProverAssumptions ProverSpec

namespace FormalCircuit
variable [CircuitType Input] [CircuitType Output]

/-- The output variable of the circuit (via the elaborated metadata). -/
def output (self : FormalCircuit F Input Output) (input : Var Input F) (i₀ : RegionIndex) :
    Var Output F :=
  self.elaborated.output input i₀

/-- Number of region indices the circuit consumes. -/
def regionCount (self : FormalCircuit F Input Output) (input : Var Input F) : ℕ :=
  self.elaborated.regionCount input

/-- Call this circuit as a subcircuit from a parent layouter circuit: emit a single
`.subcircuit` operation carrying the child's operations, return the child's output,
advance the region counter by `regionCount`. Rust: calling a chip method. -/
def call (self : FormalCircuit F Input Output) (input : Var Input F) :
    Circuit F (Var Output F) :=
  fun i =>
    (self.output input i, [.subcircuit ((self.main input).operations i)], i + self.regionCount input)

/-!
TODO (with the first slice consumer — `witness_point` → `add_incomplete`):

- **Forward lemmas**, the #358 mechanism. From `self.soundness`, derive
  `Constraints place env [.subcircuit ((main input).operations i₀)] i₀ →
    (Assumptions (evalCells ⟨place,env⟩ input) →
      Spec (evalCells ⟨place,env⟩ input) (extract …) (evalCells ⟨place,env⟩ (output input i₀)))`,
  i.e. the single-subcircuit constraint chunk unfolds (a `Constraints` computation lemma)
  and `soundness` applies. The completeness direction is dual. A per-circuit `@[grind]`/
  simp-lemma-shaped statement the tactic can fire.
- **`circuit_proof_start` analogue**: sets up the soundness/completeness goal, runs the
  deliberate `circuit_norm` simp set (`Lemmas.lean`) to expose the operation list, then
  applies each child's forward lemma to rewrite subcircuit chunks to their `Spec` — the
  forward reasoning simp cannot do.
- **Extractor composition**: a parent whose `Witness` includes a child's builds `extract`
  by calling the child's `extract` on the child's region range — knowledge soundness
  composes through the subcircuit tree by construction.
- **`SubcircuitsConsistent`**: the wellformedness that subcircuit cells reference the
  ambient region range `[i₀, i₀ + regionCount)`, discharged by the monad's structure.
-/

end FormalCircuit

end Halo2
