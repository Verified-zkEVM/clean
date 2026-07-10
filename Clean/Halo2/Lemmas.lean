import Clean.Halo2.Basic

/-!
# Composition lemmas: the deliberate simp set — DESIGN SKETCH

Unlike main Clean, where nearly every circuit definition carries `@[circuit_norm]` and
proofs unfold to low-level normal forms, the halo2 framework chooses its normal forms
deliberately:

- **Normal forms** (never unfolded): monadic composition (`>>=`/`do`), the DSL atoms
  (`assignAdvice`, `copyAdvice`, `Gate.enable`, `assignRegion`, …), and the circuit
  accessors `operations`/`output`/`nextRegionIndex`.
- **The simp set** (this file) consists of *composition lemmas*: how the accessors
  distribute over monadic composition and the DSL atoms, and how the `Constraints`
  predicates decompose over the resulting operation lists. Goals stay at the abstraction
  level of the circuit source.

SKETCH: this file grows with the vertical slice — lemmas are added when a proof needs
them, never speculatively. Next known additions: `Constraints.Soundness` over `++`
(with `Operation.regionCount` bookkeeping), per-atom `Constraints` characterizations,
`RegionCircuit` variants.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {α β : Type}

/-! ## Accessor algebra over the `Circuit` monad -/

@[circuit_norm]
theorem Circuit.operations_bind (x : Circuit F α) (f : α → Circuit F β) (i : RegionIndex) :
    (x >>= f).operations i
      = x.operations i ++ (f (x.output i)).operations (x.nextRegionIndex i) := rfl

@[circuit_norm]
theorem Circuit.output_bind (x : Circuit F α) (f : α → Circuit F β) (i : RegionIndex) :
    (x >>= f).output i = (f (x.output i)).output (x.nextRegionIndex i) := rfl

@[circuit_norm]
theorem Circuit.nextRegionIndex_bind (x : Circuit F α) (f : α → Circuit F β) (i : RegionIndex) :
    (x >>= f).nextRegionIndex i = (f (x.output i)).nextRegionIndex (x.nextRegionIndex i) := rfl

@[circuit_norm]
theorem Circuit.operations_pure (a : α) (i : RegionIndex) :
    (pure a : Circuit F α).operations i = [] := rfl

@[circuit_norm]
theorem Circuit.output_pure (a : α) (i : RegionIndex) :
    (pure a : Circuit F α).output i = a := rfl

@[circuit_norm]
theorem Circuit.nextRegionIndex_pure (a : α) (i : RegionIndex) :
    (pure a : Circuit F α).nextRegionIndex i = i := rfl

/-! ## Accessor algebra over the `RegionCircuit` monad -/

@[circuit_norm]
theorem RegionCircuit.operations_bind (x : RegionCircuit F α) (f : α → RegionCircuit F β)
    (self : RegionIndex) :
    (x >>= f).operations self = x.operations self ++ (f (x.output self)).operations self := rfl

@[circuit_norm]
theorem RegionCircuit.output_bind (x : RegionCircuit F α) (f : α → RegionCircuit F β)
    (self : RegionIndex) :
    (x >>= f).output self = (f (x.output self)).output self := rfl

@[circuit_norm]
theorem RegionCircuit.operations_pure (a : α) (self : RegionIndex) :
    (pure a : RegionCircuit F α).operations self = [] := rfl

@[circuit_norm]
theorem RegionCircuit.output_pure (a : α) (self : RegionIndex) :
    (pure a : RegionCircuit F α).output self = a := rfl

/-! ## Accessors of the DSL atoms -/

@[circuit_norm]
theorem operations_assignRegion (name : String) (body : RegionCircuit F α) (i : RegionIndex) :
    (assignRegion name body).operations i = [.region name (body.operations i)] := rfl

@[circuit_norm]
theorem output_assignRegion (name : String) (body : RegionCircuit F α) (i : RegionIndex) :
    (assignRegion name body).output i = body.output i := rfl

@[circuit_norm]
theorem nextRegionIndex_assignRegion (name : String) (body : RegionCircuit F α)
    (i : RegionIndex) :
    (assignRegion name body).nextRegionIndex i = i + 1 := rfl

@[circuit_norm]
theorem operations_assignAdvice (col : Column .advice) (row : ℕ)
    (compute : WitgenIR F 1) (self : RegionIndex) :
    (assignAdvice col row compute).operations self = [.assignAdvice col row compute] := rfl

@[circuit_norm]
theorem output_assignAdvice (col : Column .advice) (row : ℕ)
    (compute : WitgenIR F 1) (self : RegionIndex) :
    (assignAdvice col row compute).output self = ⟨⟨self, row, col.toAny⟩⟩ := rfl

@[circuit_norm]
theorem operations_copyAdvice (src : AssignedCell F) (col : Column .advice) (row : ℕ)
    (self : RegionIndex) :
    (copyAdvice src col row).operations self
      = [.assignAdvice col row (.ofFExpr (.expr src)),
         .constrainEqual ⟨self, row, col.toAny⟩ src.cell] := rfl

@[circuit_norm]
theorem output_copyAdvice (src : AssignedCell F) (col : Column .advice) (row : ℕ)
    (self : RegionIndex) :
    (copyAdvice src col row).output self = ⟨⟨self, row, col.toAny⟩⟩ := rfl

@[circuit_norm]
theorem operations_enable (gate : Gate F) (row : ℕ) (self : RegionIndex) :
    (gate.enable row).operations self = [.enableGate gate row] := rfl

@[circuit_norm]
theorem operations_constrainEqual (a b : AssignedCell F) (self : RegionIndex) :
    (constrainEqual a b).operations self = [.constrainEqual a.cell b.cell] := rfl

@[circuit_norm]
theorem operations_constrainInstance (cell : AssignedCell F) (col : Column .instance)
    (row : ℕ) (i : RegionIndex) :
    (constrainInstance cell col row).operations i = [.constrainInstance cell.cell col row] := rfl

/-! ## Constraints of region-operation lists

Decomposition lemmas so `circuit_norm` reduces a `RegionOperations.Constraints` over a
concrete operation list into a conjunction of per-operation facts (issue-#358 style:
subcircuits stay folded as one `RegionOperations.Constraints` chunk over the child's
named ops). -/

section Constraints

@[circuit_norm]
theorem RegionOperations.constraints_nil (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) :
    RegionOperations.Constraints place self env ([] : RegionOperations F) = True := rfl

@[circuit_norm]
theorem RegionOperations.constraints_cons (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) (op : RegionOperation F) (ops : RegionOperations F) :
    RegionOperations.Constraints place self env (op :: ops)
      = (op.Constraints place self env ∧ RegionOperations.Constraints place self env ops) := rfl

@[circuit_norm]
theorem RegionOperation.constraints_assignAdvice (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) (col : Column .advice) (row : ℕ) (w : WitgenIR F 1) :
    (RegionOperation.assignAdvice col row w).Constraints place self env = True := rfl

@[circuit_norm]
theorem RegionOperation.constraints_enableGate (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) (gate : Gate F) (row : ℕ) :
    (RegionOperation.enableGate gate row).Constraints place self env
      = gate.constraints.Forall fun c =>
          c.poly.eval (Query.eval env (fun i => if i = gate.selector.index then 1 else 0)
            (place self + row : ℕ)) = 0 := rfl

@[circuit_norm]
theorem RegionOperation.constraints_constrainEqual (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) (a b : Cell) :
    (RegionOperation.constrainEqual a b).Constraints place self env
      = (a.eval place env = b.eval place env) := rfl

@[circuit_norm]
theorem RegionOperation.constraints_subcircuit (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) (ops : RegionOperations F) :
    (RegionOperation.subcircuit ops).Constraints place self env
      = RegionOperations.Constraints place self env ops := rfl

-- `List.Forall` over a concrete list decomposes into a conjunction; `add_zero` clears
-- rotation-0 query offsets so cell reads share the row form `↑(place self + row)`.
attribute [circuit_norm] List.forall_cons add_zero

/-- Row-index normal form for `Rotation::next()` queries. A gate reads a next-row cell as
`Query.eval … (↑(place self + row) : ℤ) + 1` (the rotation `+1` lands *outside* the
`ℕ`-cast), while the assignment producing that cell reads it as
`↑(place self + (row + 1))` (`assignAdvice … (row + 1)`, cast *after* the sum). This
lemma makes both meet on the assignment's spelling, so next-row gate polynomials line up
with their assigned cells without a per-gadget cast bridge — the rotation-1 companion of
`add_zero`'s rotation-0 normalization. -/
@[circuit_norm]
theorem cast_row_succ (a b : ℕ) : ((a + b : ℕ) : ℤ) + 1 = ((a + (b + 1) : ℕ) : ℤ) := by
  push_cast; ring

@[circuit_norm]
theorem RegionOperations.extendsWitnesses_nil (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env ([] : RegionOperations F) = True := rfl

@[circuit_norm]
theorem RegionOperations.extendsWitnesses_cons (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) (op : RegionOperation F) (ops : RegionOperations F) :
    RegionOperations.ExtendsWitnesses place self env (op :: ops)
      = (op.ExtendsWitness place self env ∧ RegionOperations.ExtendsWitnesses place self env ops) := rfl

@[circuit_norm]
theorem RegionOperation.extendsWitness_assignAdvice (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) (col : Column .advice) (row : ℕ) (w : WitgenIR F 1) :
    (RegionOperation.assignAdvice col row w).ExtendsWitness place self env
      = (env.get col (place self + row : ℕ) = (w.eval ⟨place, env⟩)[0]) := rfl

@[circuit_norm]
theorem RegionOperation.extendsWitness_enableGate (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) (gate : Gate F) (row : ℕ) :
    (RegionOperation.enableGate gate row).ExtendsWitness place self env = True := rfl

end Constraints

end Halo2
