-- import Clean.Circuit.Append
import Clean.Circuit.SubCircuit
variable {n m o : ℕ} {F : Type} [Field F] {α β : Type}

-- there are two different definitions of the offset resulting from running a `Circuit`:
-- 1. the output of the state monad
-- 2. the offset computed from the operations list: initial_offset + local_length
-- a lawful circuit is one where these two definitions agree.

class LawfulCircuit (circuit : Circuit F α) where
  /-- the offset derived from operations is the same as the state offset -/
  offset_consistent : ∀ n : ℕ, circuit.final_offset n = n + circuit.local_length n := by intro _; rfl

-- a constant circuit is one where the local length is constant for all inputs
class ConstantCircuit (circuit : Circuit F α) where
  local_length : ℕ
  local_length_eq : ∀ n : ℕ, circuit.local_length n = local_length := by intro _; rfl

-- combination
class ConstantLawfulCircuit (circuit : Circuit F α)
  extends LawfulCircuit circuit, ConstantCircuit circuit

-- even stronger (and still the typical case): an indexed family of lawful circuits that all share the same local length
class ConstantLawfulCircuits (circuit : α → Circuit F β) where
  local_length : ℕ
  offset_consistent : ∀ (a : α) (n: ℕ), (circuit a).final_offset n = n + local_length := by intro _ _; rfl
  local_length_eq : ∀ (a : α) (n : ℕ), (circuit a).local_length n = local_length := by intro _ _; rfl

-- `pure` is a (constant) lawful circuit
instance LawfulCircuit.from_pure {a : α} : ConstantLawfulCircuit (pure a : Circuit F α) where
  local_length := 0

instance ConstantLawfulCircuits.from_pure {f : α → β} : ConstantLawfulCircuits (fun a => pure (f a) : α → Circuit F β) where
  local_length := 0

-- `bind` and `map` of two lawful circuits yields a lawful circuit

instance LawfulCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    (f_lawful : LawfulCircuit f) (g_lawful : ∀ a : α, LawfulCircuit (g a)) : LawfulCircuit (f >>= g) where
  offset_consistent n := by
    show (g _).final_offset (f.final_offset _) = n + (f >>= g).local_length n
    rw [Circuit.bind_local_length, offset_consistent, offset_consistent, add_assoc]

instance LawfulCircuit.from_map {f : α → β} {g : Circuit F α}
    (g_lawful : LawfulCircuit g) : LawfulCircuit (f <$> g) where
  offset_consistent n := by
    show g.final_offset n = n + g.local_length n
    rw [offset_consistent]

-- basic operations are (constant) lawful circuits

instance : ConstantLawfulCircuits (F:=F) witness_var where
  local_length := 1

instance {k : ℕ} {c : Environment F → Vector F k} : ConstantLawfulCircuit (witness_vars k c) where
  local_length := k

instance {α: TypeMap} [ProvableType α] : ConstantLawfulCircuits (ProvableType.witness (α:=α) (F:=F)) where
  local_length := size α

instance : ConstantLawfulCircuits (F:=F) assert_zero where
  local_length := 0

instance : ConstantLawfulCircuits (F:=F) lookup where
  local_length := 0

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ConstantLawfulCircuit (subcircuit circuit input) where
  local_length := circuit.local_length input

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ConstantLawfulCircuit (assertion circuit input) where
  local_length := circuit.local_length input

-- lower `ConstantLawfulCircuits` to `ConstantLawfulCircuit`
instance ConstantLawfulCircuits.to_single (circuit : α → Circuit F β) (a : α) [lawful : ConstantLawfulCircuits circuit] : ConstantLawfulCircuit (circuit a) where
  local_length := local_length circuit
  offset_consistent n := lawful.local_length_eq a n ▸ offset_consistent a n
  local_length_eq n := local_length_eq a n

instance LawfulCircuit.from_constants {circuit : α → Circuit F β} (lawful : ConstantLawfulCircuits circuit) (a : α) :
    LawfulCircuit (circuit a) := ConstantLawfulCircuits.to_single circuit a |>.toLawfulCircuit

syntax "infer_lawful_circuit" : tactic

macro_rules
  | `(tactic|infer_lawful_circuit) => `(tactic|(
    try intros
    try repeat infer_instance
    repeat (
      try intros
      first
        | apply LawfulCircuit.from_bind
        | apply LawfulCircuit.from_map
      repeat infer_instance
    )))

-- this tactic is pretty good at inferring lawful circuits!
section
example : LawfulCircuit (witness (fun _ => (0 : F)))
  := by infer_lawful_circuit

example :
  let add := do
    let x : Expression F ← witness (fun _ => 0)
    let y ← witness (fun _ => 1)
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  LawfulCircuit add := by infer_lawful_circuit
end

-- `ConstantLawfulCircuit(s)` can be proved from `LawfulCircuit` by adding the requirement that the local length is constant.
-- the latter can usually be proved by rfl!
def ConstantLawfulCircuit.from_constant_length {circuit : Circuit F α} (lawful : LawfulCircuit circuit)
    (h_length : ∀ n, circuit.local_length n = circuit.local_length 0) : ConstantLawfulCircuit circuit where
  local_length := circuit.local_length 0
  local_length_eq := h_length

def ConstantLawfulCircuits.from_constant_length {circuit : α → Circuit F β} [Inhabited α] (lawful : ∀ a, LawfulCircuit (circuit a))
    (h_length : ∀ a n, (circuit a).local_length n = (circuit default).local_length 0) : ConstantLawfulCircuits circuit where
  local_length := (circuit default).local_length 0
  offset_consistent a n := by rw [(lawful a).offset_consistent, h_length]
  local_length_eq a n := by rw [h_length]

syntax "infer_constant_lawful_circuits" : tactic

macro_rules
  | `(tactic|infer_constant_lawful_circuits) => `(tactic|(
    apply ConstantLawfulCircuits.from_constant_length (by infer_lawful_circuit)
    try intros
    try simp only [LawfulCircuit.final_offset]
    try ac_rfl))

section
example : ConstantLawfulCircuits (witness (F:=F))
  := by infer_constant_lawful_circuits

example :
  let add (x : Expression F) := do
    let y ← witness (fun _ => (1 : F))
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ConstantLawfulCircuits add := by infer_constant_lawful_circuits
end

def Circuit.constant_output (circuit : α → Circuit F β) [Inhabited α] :=
  ∀ (x : α) (n : ℕ), (circuit x).output n = (circuit default).output n

-- characterize various properties of (lawful) circuits

namespace Circuit
variable {env : Environment F} {n : ℕ} {prop : Operations.Condition F}

@[reducible, circuit_norm]
def forAll (circuit : Circuit F α) (prop : Operations.Condition F) (n : ℕ) :=
  (circuit.operations n).forAll n prop

theorem bind_forAll {f : Circuit F α} {g : α → Circuit F β} :
  (f >>= g).forAll prop n ↔
    f.forAll prop n ∧ ((g (f.output n)).operations (f.final_offset n)).forAll (n + f.local_length n) prop := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (f.final_offset n) := rfl
  simp only [forAll]
  rw [h_ops, Operations.forAll_append, add_comm n]

theorem bind_forAll_lawful {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) :
  (f >>= g).forAll prop n ↔ f.forAll prop n ∧ (g (f.output n)).forAll prop (n + f.local_length n) := by
  rw [bind_forAll, ←f_lawful.offset_consistent]

end Circuit
