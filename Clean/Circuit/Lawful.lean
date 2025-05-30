-- import Clean.Circuit.Append
import Clean.Circuit.SubCircuit
variable {n m o : ℕ} {F : Type} [Field F] {α β : Type}

-- a constant circuit is one where the local length is constant for all inputs
class ConstantCircuit (circuit : Circuit F α) where
  local_length : ℕ
  local_length_eq : ∀ n : ℕ, circuit.local_length n = local_length := by intro _; rfl

-- even stronger (and still the typical case): an indexed family of lawful circuits that all share the same local length
class ConstantCircuits (circuit : α → Circuit F β) where
  local_length : ℕ
  local_length_eq : ∀ (a : α) (n : ℕ), (circuit a).local_length n = local_length := by intro _ _; rfl

-- `pure` is a constant circuit
instance LawfulCircuit.from_pure {a : α} : ConstantCircuit (pure a : Circuit F α) where
  local_length := 0

instance ConstantLawfulCircuits.from_pure {f : α → β} : ConstantCircuits (fun a => pure (f a) : α → Circuit F β) where
  local_length := 0

-- basic operations are constant circuits

instance : ConstantCircuits (F:=F) witness_var where
  local_length := 1

instance {k : ℕ} {c : Environment F → Vector F k} : ConstantCircuit (witness_vars k c) where
  local_length := k

instance {α: TypeMap} [ProvableType α] : ConstantCircuits (ProvableType.witness (α:=α) (F:=F)) where
  local_length := size α

instance : ConstantCircuits (F:=F) assert_zero where
  local_length := 0

instance : ConstantCircuits (F:=F) lookup where
  local_length := 0

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ConstantCircuit (subcircuit circuit input) where
  local_length := circuit.local_length input

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ConstantCircuit (assertion circuit input) where
  local_length := circuit.local_length input

-- lower `ConstantCircuits` to `ConstantCircuit`
instance ConstantCircuits.to_single (circuit : α → Circuit F β) (a : α) [lawful : ConstantCircuits circuit] :
    ConstantCircuit (circuit a) where
  local_length := local_length circuit
  local_length_eq n := local_length_eq a n

instance ConstantCircuit.from_constants {circuit : α → Circuit F β} (lawful : ConstantCircuits circuit) (a : α) :
  ConstantCircuit (circuit a) := ConstantCircuits.to_single circuit a

-- `ConstantCircuit(s)` can be proved from `Circuit` by adding the requirement that the local length is constant.
-- the latter can usually be proved by rfl!
def ConstantCircuit.from_constant_length {circuit : Circuit F α}
    (h_length : ∀ n, circuit.local_length n = circuit.local_length 0) : ConstantCircuit circuit where
  local_length := circuit.local_length 0
  local_length_eq := h_length

def ConstantCircuits.from_constant_length {circuit : α → Circuit F β} [Inhabited α]
    (h_length : ∀ a n, (circuit a).local_length n = (circuit default).local_length 0) : ConstantCircuits circuit where
  local_length := (circuit default).local_length 0
  local_length_eq a n := by rw [h_length]

syntax "infer_constant_circuits" : tactic

macro_rules
  | `(tactic|infer_constant_circuits) => `(tactic|(
    apply ConstantCircuits.from_constant_length
    try intros
    try ac_rfl))

section
example : ConstantCircuits (witness (F:=F))
  := by infer_constant_circuits

example :
  let add (x : Expression F) := do
    let y ← witness (fun _ => (1 : F))
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ConstantCircuits add := by infer_constant_circuits
end

def Circuit.constant_output (circuit : α → Circuit F β) [Inhabited α] :=
  ∀ (x : α) (n : ℕ), (circuit x).output n = (circuit default).output n

-- characterize various properties of (lawful) circuits

namespace Circuit
variable {n : ℕ} {prop : Operations.Condition F}

theorem constraints_hold.soundness_iff_forAll' {env : Environment F} {circuit : Circuit F α} {n : ℕ} :
  constraints_hold.soundness env (circuit.operations n) ↔ circuit.forAll {
    assert _ e := env e = 0,
    lookup _ l := l.table.contains (l.entry.map env),
    subcircuit _ _ s := s.soundness env
  } n := by
  rw [forAll_def, constraints_hold.soundness_iff_forAll _ _ n]

theorem constraints_hold.completeness_iff_forAll' {env : Environment F} {circuit : Circuit F α} {n : ℕ} :
  constraints_hold.completeness env (circuit.operations n) ↔ circuit.forAll {
    assert _ e := env e = 0,
    lookup _ l := l.table.contains (l.entry.map env),
    subcircuit _ _ s := s.completeness env
  } n := by
  rw [forAll_def, constraints_hold.completeness_iff_forAll _ _ n]

end Circuit
