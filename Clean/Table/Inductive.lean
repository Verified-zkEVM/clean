/-
"Inductive" table constraints are specified by a circuit on a `k`-row window of cells, which
take the first `k-1` rows as input variables and return the `k`-th row as output.

Assignment of cells is handled in the background, which simplifies reasoning about the table.

The common `k=2` case gets its own special definition.
-/
import Clean.Table.Basic

/--
In the case of two-row windows, an `InductiveTable` is basically a `FormalCircuit` but
- with the same input and output types
- with an extra input to both the spec and the circuit: the current (input) row number
- with assumptions replaced by the spec on the previous row
- with input offset hard-coded to zero
-/
structure InductiveTable (F : Type) [Field F] (Row : Type → Type) [ProvableType Row] where
  main : ℕ → Var Row F → Circuit F (Var Row F)
  spec : ℕ → Row F → Prop

  soundness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ input_var : Var Row F, ∀ input : Row F, eval env input_var = input →
    -- if the constraints hold
    Circuit.constraints_hold.soundness env (main row_index input_var |>.operations) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- we can conclude the spec on the output row
    spec (row_index + 1) (eval env (main row_index input_var |>.output))

  completeness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ input_var : Var Row F, ∀ input : Row F, eval env input_var = input →
    -- when using honest-prover witnesses
    env.uses_local_witnesses_completeness 0 (main row_index input_var |>.operations) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- the constraints hold
    Circuit.constraints_hold.completeness env (main row_index input_var |>.operations)

  subcircuits_consistent : ∀ row_index var, ((main row_index var).operations).subcircuits_consistent 0
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )
