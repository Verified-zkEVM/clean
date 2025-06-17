import Clean.Circuit.SubCircuit
import Clean.Circuit.Foundations
variable {F : Type} [Field F] {α β : TypeMap} [ProvableType α] [ProvableType β]

structure TypedLawfulTable (F : Type) (Row: TypeMap) [ProvableType Row] extends TypedTable F Row where
  map : (row: Row F) → valid row → Row F
  mapContains : ∀ (row: Row F) (h_valid: valid row), contains (map row h_valid)

def TypedLawfulTable.toUntyped (table : TypedLawfulTable F α) : LawfulTable F := {
  TypedTable.toUntyped table.toTypedTable with

  map row h_valid := to_elements (table.map (from_elements row) h_valid)

  mapContains row h_valid := by
    simp only [TypedTable.toUntyped, ProvableType.from_elements_to_elements]
    apply table.mapContains
}

def FormalCircuit.toTable (circuit : FormalCircuit F α β) (name : String) : TypedTable F (ProvablePair α β) where
  name
  valid x := circuit.assumptions x.1
  contains x := circuit.spec x.1 x.2

def FormalCircuit.toLawfulTable (circuit : FormalCircuit F α β) (name : String)
  (henv : (input: α F) → (env : Environment F) ×' env.uses_local_witnesses 0 (circuit.main (const input) |>.operations 0)) :
    TypedLawfulTable F (ProvablePair α β) := {
  circuit.toTable name with

  map x _ :=
    let (input, _) := x
    let env := henv input
    let output_var := circuit.output (const input) 0
    let output : β F := eval env.1 output_var
    ⟨input, output⟩

  mapContains x hx := by
    let (input, _) := x
    simp only
    set env := (henv input).1 with env_def
    apply circuit.original_soundness 0 env (const input) input (ProvableType.eval_const ..) hx
    apply circuit.original_completeness 0 env (const input) input (ProvableType.eval_const ..) hx
    exact (henv input).2

}
