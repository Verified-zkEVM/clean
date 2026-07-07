import Clean.Circuit.Provable
import Clean.Halo2.Expression

/-!
# Provable types over halo2 cells

Halo2 counterpart of the evaluation layer of `Clean/Circuit/Provable.lean`.

The `ProvableType` class itself — `size`/`toElements`/`fromElements`, all its instances
(`field`, `fields n`, `ProvablePair`, `ProvableVector`, …) and the `ProvableStruct`
deriving machinery — is fully generic over the element type and is **shared** with main
Clean, not ported. This file only supplies what is element-specific:

- `Var M F` is `M (AssignedCell F)` (main Clean: `M (Expression F)`): structured circuit
  values are structs of cell references, halo2's composition currency (Rust gadgets do
  the same: `EccPoint` is a struct of `AssignedCell`s).
- `eval place env` evaluates them to values `M F`, given the region placement.

Deliberately absent, with no halo2 analogue:

- `const : M F → M (Expression F)` — there are no constant-valued variables; constants
  enter circuits through `assignAdviceFromConstant`/`constrainConstant`, i.e. as real
  cells copy-constrained to fixed cells.
- `varFromOffset` — cells are not allocated in blocks from a linear tape; each cell is
  created by an assignment operation at a specific (region, column, row offset).

Not yet decided: sharing of the `CircuitType` (`Var`/`Value`/`ProverValue`) machinery and
the `Unconstrained*` hint types. Those bake in main Clean's `Environment` types; making
them environment-generic is a candidate core reorganization, to be decided when the
halo2 formal-circuit layer is ported. Until then, halo2 uses plain functions.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]

/-- Structured circuit variables: a `M F`-shaped collection of cell references.
Halo2 counterpart of main Clean's `Var M F = M (Expression F)`. -/
abbrev Var (M : TypeMap) (F : Type) := M (AssignedCell F)

instance : Inhabited Cell where
  default := ⟨0, 0, ⟨.advice, 0⟩⟩

instance : Inhabited (AssignedCell F) where
  default := ⟨default⟩

instance (priority := low) : Inhabited (Var M F) where
  default := (fromElements default : M (AssignedCell F))

namespace ProvableType

/--
Evaluate a structured variable in the given environment: every cell reference is read
from its column at its region's placement plus its row offset.

`place` is the region-placement parameter of the semantics (the analogue of main Clean's
`offset`); proofs are generic over it, the top level instantiates the floor planner's
output.

Note: like main Clean's `ProvableType.eval`, this is not tagged with `circuit_norm`, to
enable higher-level `ProvableStruct` decompositions.
-/
@[explicit_provable_type]
def eval (place : RegionIndex → ℕ) (env : Environment F) (x : M (AssignedCell F)) : M F :=
  let cells := toElements x
  let values := cells.map (AssignedCell.eval place env)
  fromElements values

/-- Evaluating a single-cell variable reads that cell. -/
@[circuit_norm]
lemma eval_field (place : RegionIndex → ℕ) (env : Environment F) (x : AssignedCell F) :
    eval (M := field) place env x = AssignedCell.eval place env x := by
  with_unfolding_all rfl

end ProvableType

end Halo2
