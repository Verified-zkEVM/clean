import Clean.Circuit.Subcircuit
variable {n : ℕ} {F : Type} [Field F] {α β : Type}

/--
A constant circuit is one where the local length is constant for all inputs.
This is true for all circuits in practice, but unfortunately this can't be encoded in the monad definition.

Note also that this is a subset of the `ElaboratedCircuit` definition.
-/
class ConstantCircuit (circuit : Circuit F α) where
  localLength : ℕ
  localLength_eq : ∀ n : ℕ, circuit.localLength n = localLength := by intro _; rfl

/--
Stronger variant of `ConstantCircuit` (and still the typical case):
an indexed family of circuits that all share the same local length.
-/
class ConstantCircuits (circuit : α → Circuit F β) where
  localLength : ℕ
  localLength_eq : ∀ (a : α) (n : ℕ), (circuit a).localLength n = localLength := by intro _ _; rfl

-- circuit with _output_ not depending on the input.
@[circuit_norm]
def Circuit.constant_output (circuit : α → Circuit F β) [Inhabited α] :=
  ∀ (x : α) (n : ℕ), (circuit x).output n = (circuit default).output n

-- `pure` is a constant circuit
instance ConstantCircuit.from_pure {a : α} : ConstantCircuit (pure a : Circuit F α) where
  localLength := 0

instance Constantircuits.from_pure {f : α → β} : ConstantCircuits (fun a => pure (f a) : α → Circuit F β) where
  localLength := 0

-- basic operations are constant circuits

instance : ConstantCircuits (F:=F) witnessVar where
  localLength := 1

instance {k : ℕ} {c : Environment F → Vector F k} : ConstantCircuit (witnessVars k c) where
  localLength := k

instance {α: TypeMap} [ProvableType α] : ConstantCircuits (witness (α:=α) (F:=F)) where
  localLength := size α

instance : ConstantCircuits (F:=F) assertZero where
  localLength := 0

instance {α: TypeMap} [ProvableType α] {table : Table F α} : ConstantCircuits (F:=F) (lookup table) where
  localLength := 0

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ConstantCircuit (subcircuit circuit input) where
  localLength := circuit.localLength input

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ConstantCircuit (assertion circuit input) where
  localLength := circuit.localLength input

-- lower `ConstantCircuits` to `ConstantCircuit`
instance ConstantCircuits.to_single (circuit : α → Circuit F β) (a : α) [ConstantCircuits circuit] :
    ConstantCircuit (circuit a) where
  localLength := localLength circuit
  localLength_eq n := localLength_eq a n

instance ConstantCircuit.from_constants {circuit : α → Circuit F β} (_ : ConstantCircuits circuit) (a : α) :
  ConstantCircuit (circuit a) := ConstantCircuits.to_single circuit a

-- `ConstantCircuit(s)` can be proved from `Circuit` by adding the requirement that the local length is constant.
-- the latter can usually be proved by rfl!
def ConstantCircuit.from_constant_length {circuit : Circuit F α}
    (h_length : ∀ n, circuit.localLength n = circuit.localLength 0) : ConstantCircuit circuit where
  localLength := circuit.localLength 0
  localLength_eq := h_length

def ConstantCircuits.from_constant_length {circuit : α → Circuit F β} [Inhabited α]
    (h_length : ∀ a n, (circuit a).localLength n = (circuit default).localLength 0) : ConstantCircuits circuit where
  localLength := (circuit default).localLength 0
  localLength_eq a n := by rw [h_length]

syntax "infer_constant_circuits" : tactic

macro_rules
  | `(tactic|infer_constant_circuits) => `(tactic|(
    apply ConstantCircuits.from_constant_length
    try intros
    try simp only [circuit_norm]
    try ac_rfl))

section
example : ConstantCircuits (witnessField (F:=F))
  := by infer_constant_circuits

example :
  let add (x : Expression F) := do
    let y : fieldVar F ← witness fun _ => 1
    let z : fieldVar F ← witness fun eval => eval (x + y)
    assertZero (x + y - z)
    pure z

  ConstantCircuits add := by infer_constant_circuits
end
