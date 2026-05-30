import Clean.Circuit

/-!
# R1CS cost meter

A small utility to measure the arithmetization cost of a circuit under an R1CS
cost model:

* `witnesses`   — length of the witness vector (number of allocated cells),
* `constraints` — number of R1CS rows (one per `assert`), and
* `lookups`     — number of lookup arguments (should be `0` for a pure-R1CS circuit).

In R1CS, *linear combinations are free*: building up an additive/scalar
combination of variables inside a constraint costs nothing, only the
multiplicative `assert` row and the witness allocation are charged. The number
of `assert` operations therefore equals the R1CS constraint count, and the
witness count equals `localLength`. Both recurse through subcircuits via the
existing `Operations` API (`localLength`, `constraints`, `lookups`).
-/

namespace Clean.CostR1CS

variable {F : Type} [Field F]

/-- R1CS cost summary of a circuit. -/
structure Cost where
  witnesses : ℕ
  constraints : ℕ
  lookups : ℕ
deriving Repr, DecidableEq

instance : Add Cost where
  add a b := ⟨a.witnesses + b.witnesses, a.constraints + b.constraints, a.lookups + b.lookups⟩

/-- Cost of a flat list of operations. -/
def operationsCost (ops : Operations F) : Cost where
  witnesses := Operations.localLength ops
  constraints := (Operations.constraints ops).length
  lookups := (Operations.lookups ops).length

/-- Cost of running a circuit at offset `n` (default `0`; counts are
offset-independent). -/
def circuitCost {α : Type} (c : Circuit F α) (n : ℕ := 0) : Cost :=
  operationsCost (Circuit.operations c n)

end Clean.CostR1CS
