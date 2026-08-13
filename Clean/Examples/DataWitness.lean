/-
Example: a witness generator that reads committed prover data.

`Witgen.FExpr.dataGet` is the witness IR's escape hatch for reading `ProverEnvironment.data`
(`Examples.FemtoCairo` uses it for memory). This file is the smallest circuit that uses it, and
records both directions of what `ProverEnvironment.AgreesBelow` has to say about such a circuit.

`readMemory_computableWitnesses` proves the `ComputableWitnesses` obligation — the precondition of
`Circuit.witgen_usesLocalWitnesses`, i.e. that an honest prover can actually run the circuit's
witness generators. It closes by rewriting with `AgreesBelow.data_eq`, which is exactly the
component that carries it.

`not_computable_from_cells_alone` shows the converse: agreement on environment *cells* alone does
not suffice. The obligation would not merely be hard to prove, it would be false. That is why
`AgreesBelow` constrains all three channels of a `ProverEnvironment` and not just `get`.
-/
import Clean.Circuit

namespace Examples.DataWitness
variable {p : ℕ} [Fact p.Prime]

structure Entry (F : Type) where
  address : F
  value : F
deriving ProvableStruct

/-- A read-only memory table, as in `Examples.FemtoCairo`. -/
def MemoryTable : Table (F p) Entry where
  name := "memory"
  Contains table entry := ∃ (_ : entry.address.val < table.size),
    entry.address = table[entry.address.val].address ∧
    entry.value = table[entry.address.val].value

/--
Witness the memory value committed at `address`, and constrain the resulting pair to be in the
table. The witness generator reads `env.data`; the constraint system does not.
-/
def readMemory (address : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let value ← witness (MemoryTable.dataGet address.val).value
  lookup MemoryTable ⟨address, value⟩
  return value

/--
`readMemory` has computable witnesses whenever its input expression only reads cells below the
current offset — the standard side condition, supplied by `compose_computableWitnesses` when the
circuit is used as a subcircuit.

The two rewrites are the whole proof, and they are one per environment channel the witness
generator reads: `AgreesBelow.data_eq` for the committed table, and the input hypothesis for the
address expression.
-/
theorem readMemory_computableWitnesses (n : ℕ) (address : Expression (F p))
    (h_input : ProverEnvironment.OnlyAccessedBelow n (F := F p) (eval · address)) :
    (readMemory address).ComputableWitnesses n := by
  intro env env'
  simp only [readMemory, circuit_norm, Operations.ComputableWitnesses, Operations.forAllFlat]
  intro h_agree
  have h_address := h_input env env' h_agree
  simp only [circuit_norm, explicit_provable_type] at h_address
  rw [h_agree.data_eq, h_address]

/-! ## Why `AgreesBelow` has to constrain `data`

The proof above rests on `ProverEnvironment.AgreesBelow` supplying `env.data = env'.data`. The
following shows the alternative is not an option: agreement on cells alone makes the obligation
false. Both environments below agree on every cell (they are constantly zero) yet commit
different memory, so the witness generator returns different values. -/

private def emptyEnv : ProverEnvironment (F p) :=
  ⟨⟨fun _ => 0, fun _ _ => #[]⟩, ProverHint.empty _⟩

private def onesEnv : ProverEnvironment (F p) :=
  ⟨⟨fun _ => 0, fun _ k => #[Vector.replicate k 1]⟩, ProverHint.empty _⟩

theorem not_computable_from_cells_alone :
    ¬ ∀ (n : ℕ) (compute : Witgen.WitgenIR (F p) 1) (env env' : ProverEnvironment (F p)),
        (∀ i < n, env.get i = env'.get i) → compute.eval env = compute.eval env' := by
  intro h
  -- a one-node witness program reading row 0 of the committed `memory` table
  have := h 0 (.ofFExpr (.dataGet "memory" 1 (.const 0) 0)) emptyEnv onesEnv (by omega)
  simp [Witgen.WitgenIR.ofFExpr, Witgen.WitgenIR.eval, Witgen.VExpr.eval, Witgen.evalSteps,
    Witgen.FExpr.eval, Witgen.U64Expr.eval, emptyEnv, onesEnv] at this
  -- the empty table reads as the default row, the ones table as `1`
  exact zero_ne_one (show (0 : F p) = 1 from this)

end Examples.DataWitness
