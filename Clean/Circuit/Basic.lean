import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable

namespace Circuit
variable {F: Type}

structure Table (F : Type) where
  name: String
  length: ℕ
  arity: ℕ
  row: Fin length → Vector F arity

def Table.contains (table: Table F) row := ∃ i, row = table.row i

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity
  index: Unit → Fin table.length -- index of the entry

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

inductive RowIndex
  | Current
  | Next
deriving Repr

structure Cell (F : Type) where
  row: RowIndex
  column: ℕ -- index of the column
deriving Repr

structure Context (F : Type) where
  offset: ℕ
  locals: Array (Variable F)
deriving Repr

namespace Context
@[simp]
def empty : Context F := ⟨ 0, #[] ⟩
end Context

variable {α : Type} [Field F]

inductive PreOperation (F : Type) [Field F] where
  | Witness : (compute : Unit → F) → PreOperation F
  | Assert : Expression F → PreOperation F
  | Lookup : Lookup F → PreOperation F
  | Assign : Cell F × Variable F → PreOperation F

namespace PreOperation
def toString [Repr F] : (op : PreOperation F) → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"

def constraints_hold (env: ℕ → F) : List (PreOperation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Assert e => e.eval_env env = 0
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env))
    | _ => True
  | op :: ops => match op with
    | PreOperation.Assert e => ((e.eval_env env) = 0) ∧ constraints_hold env ops
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env)) ∧ constraints_hold env ops
    | _ => constraints_hold env ops

def constraints_hold_default : List (PreOperation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Assert e => e.eval = 0
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval))
    | _ => True
  | op :: ops => match op with
    | PreOperation.Assert e => (e.eval = 0) ∧ constraints_hold_default ops
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval)) ∧ constraints_hold_default ops
    | _ => constraints_hold_default ops
end PreOperation

-- this type models a subcircuit: a list of operations that imply a certain spec,
-- for all traces that satisfy the constraints
structure SubCircuit (F: Type) [Field F] where
  ops: List (PreOperation F)

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `soundness`
  -- and `completeness` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  soundness : (ℕ → F) → Prop
  completeness : Prop

  -- `soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env, PreOperation.constraints_hold env ops → soundness env

  -- `completeness` needs to imply the constraints using default witnesses
  implied_by_completeness : completeness → PreOperation.constraints_hold_default ops

inductive Operation (F : Type) [Field F] where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | Circuit : SubCircuit F → Operation F
namespace Operation

@[simp]
def run (ctx: Context F) : Operation F → Context F
  | Witness compute =>
    let var := ⟨ ctx.offset, compute ⟩
    let offset := ctx.offset + 1
    { ctx with offset, locals := ctx.locals.push var }
  | Assert _ => ctx
  | Lookup _ => ctx
  | Assign _ => ctx
  | Circuit { ops, .. } =>
    let offset := ctx.offset + ops.length
    { ctx with offset }

def toString [Repr F] : (op : Operation F) → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"
  | Circuit { ops, .. } => "(Circuit " ++ reprStr (ops.map PreOperation.toString) ++ ")"

instance [Repr F] : ToString (Operation F) where
  toString := toString
end Operation

@[simp]
def Stateful (F : Type) [Field F] (α : Type) :=
  Context F → (Context F × List (Operation F)) × α

instance : Monad (Stateful F) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)

@[simp]
def Stateful.run (circuit: Stateful F α) : List (Operation F) × α :=
  let ((_, ops), a) := circuit Context.empty
  (ops, a)

@[reducible]
def Stateful.operations (circuit: Stateful F α) : List (Operation F) :=
  (circuit Context.empty).1.2

@[reducible]
def output (circuit: Stateful F α) (ctx : Context F := Context.empty) : α :=
  (circuit ctx).2

@[simp]
def as_stateful (f: Context F → Operation F × α) : Stateful F α := fun ctx  =>
  let (op, a) := f ctx
  let ctx' := Operation.run ctx op
  ((ctx', [op]), a)

-- operations we can do in a circuit

-- create a new variable
@[simp]
def witness_var (compute : Unit → F) := as_stateful (fun ctx =>
  let var: Variable F := ⟨ ctx.offset, compute ⟩
  (Operation.Witness compute, var)
)

@[simp]
def witness (compute : Unit → F) := do
  let var ← witness_var compute
  return Expression.var var

-- add a constraint
@[simp]
def assert_zero (e: Expression F) := as_stateful (
  fun _ => (Operation.Assert e, ())
)

-- add a lookup
@[simp]
def lookup (l: Lookup F) := as_stateful (
  fun _ => (Operation.Lookup l, ())
)

-- assign a variable to a cell
@[simp]
def assign_cell (c: Cell F) (v: Variable F) := as_stateful (
  fun _ => (Operation.Assign (c, v), ())
)

-- TODO derived operations: assert(lhs == rhs), <== (witness + assert)

def to_var [Field F] (x: Expression F) : Stateful F (Variable F) :=
  match x with
  | Expression.var v => pure v
  | x => do
    let x' ← witness_var (fun _ => x.eval)
    assert_zero (x - (Expression.var x'))
    return x'

structure InputCell (F : Type) where
  cell: { cell: Cell F // cell.row = RowIndex.Current }
  var: Variable F

def InputCell.set_next [Field F] (c: InputCell F) (v: Expression F) := do
  let v' ← to_var v
  assign_cell { c.cell.val with row := RowIndex.Next } v'

def create_input (value: F) (column: ℕ) : Stateful F (InputCell F) := do
  let var ← witness_var (fun _ => value)
  let cell: Cell F := ⟨ RowIndex.Current, column ⟩
  assign_cell cell var
  let input: InputCell F := ⟨ ⟨ cell, rfl ⟩, var ⟩
  return input

instance : Coe (InputCell F) (Variable F) where
  coe x := x.var

-- extract information from circuits by running them
namespace Adversarial
  @[simp]
  def constraints_hold_from_list [Field F] (env: (ℕ → F)) : List (Operation F) → Prop
    | [] => True
    | op :: [] => match op with
      | Operation.Assert e => (e.eval_env env) = 0
      | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map (fun e => e.eval_env env))
      | Operation.Circuit { soundness, .. } => soundness env
      | _ => True
    | op :: ops => match op with
      | Operation.Assert e => ((e.eval_env env) = 0) ∧ constraints_hold_from_list env ops
      | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map (fun e => e.eval_env env)) ∧ constraints_hold_from_list env ops
      | Operation.Circuit { soundness, .. } => soundness env ∧ constraints_hold_from_list env ops
      | _ => constraints_hold_from_list env ops

  @[reducible, simp]
    def constraints_hold [Field F] (env: (ℕ → F)) (circuit: Stateful F α) (ctx : Context F := Context.empty) : Prop :=
    constraints_hold_from_list env (circuit ctx).1.2
end Adversarial

/--
Weaker version of `Adversarial.constraints_hold_from_list` that captures the statement that, using the default
witness generator, checking all constraints would not fail.

For subcircuits, since we proved completeness, this only means we need to satisfy the assumptions!
-/
@[simp]
def constraints_hold_from_list [Field F] : List (Operation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Operation.Assert e => e.eval = 0
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map Expression.eval)
    | Operation.Circuit { completeness, .. } => completeness
    | _ => True
  | op :: ops => match op with
    | Operation.Assert e => (e.eval = 0) ∧ constraints_hold_from_list ops
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map Expression.eval) ∧ constraints_hold_from_list ops
    | Operation.Circuit { completeness, .. } => completeness ∧ constraints_hold_from_list ops
    | _ => constraints_hold_from_list ops

@[simp]
def constraints_hold (circuit: Stateful F α) (ctx : Context F := Context.empty) : Prop :=
  constraints_hold_from_list (circuit ctx).1.2


namespace PreOperation
-- in the following, we prove equivalence between flattened and nested constraints

def to_flat_operations [Field F] (ops: List (Operation F)) : List (PreOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | Operation.Witness compute => PreOperation.Witness compute :: to_flat_operations ops
    | Operation.Assert e => PreOperation.Assert e :: to_flat_operations ops
    | Operation.Lookup l => PreOperation.Lookup l :: to_flat_operations ops
    | Operation.Assign (c, v) => PreOperation.Assign (c, v) :: to_flat_operations ops
    | Operation.Circuit circuit => circuit.ops ++ to_flat_operations ops

-- TODO super painful, mainly because `cases` doesn't allow rich patterns -- how does this work again?
theorem can_flatten_first : ∀ (env: ℕ → F) (ops: List (Operation F)),
  PreOperation.constraints_hold env (to_flat_operations ops)
  → Adversarial.constraints_hold_from_list env ops
:= by
  intro env ops
  induction ops with
  | nil => intro h; exact h
  | cons op ops ih =>
    cases ops with
    | nil =>
      simp at ih
      cases op with
      | Circuit c =>
        sorry
      | _ => simp [PreOperation.constraints_hold]
    | cons op' ops' =>
      let ops := op' :: ops'
      cases op with
      | Circuit c => sorry
      | Assert e => sorry
      | Witness c =>
        have h_ops : to_flat_operations (Operation.Witness c :: op' :: ops') = PreOperation.Witness c :: to_flat_operations (op' :: ops') := rfl
        rw [h_ops]
        intro h_pre
        have h1 : PreOperation.constraints_hold env (to_flat_operations (op' :: ops')) := by
          rw [PreOperation.constraints_hold] at h_pre
          · exact h_pre
          · sorry
          · simp
          · simp
        have ih1 := ih h1
        simp [ih1]
      | Lookup l => sorry
      | Assign a => sorry

theorem can_flatten : ∀ (ops: List (Operation F)),
  constraints_hold_from_list ops →
  PreOperation.constraints_hold_default (to_flat_operations ops)
:= by
 sorry
end PreOperation

variable {α β γ: TypePair} [ProvableType F α] [ProvableType F β] [ProvableType F γ]
namespace Provable

private def witness' := witness (F:=F)

@[simp]
def witness {F: Type} [Field F] [ProvableType F α] (compute : Unit → α.value) :=
  let n := ProvableType.size F α
  let values : Vector F n := ProvableType.to_values (compute ())
  let varsM : Vector (Stateful F (Expression F)) n := values.map (fun v => witness' (fun () => v))
  do
    let vars ← varsM.mapM
    return ProvableType.from_vars vars

@[simp]
def assert_equal {F: Type} [Field F] [ProvableType F α] (a a': α.var) : Stateful F Unit :=
  let n := ProvableType.size F α
  let vars: Vector (Expression F) n := ProvableType.to_vars a
  let vars': Vector (Expression F) n := ProvableType.to_vars a'
  let eqs := (vars.zip vars').map (fun ⟨ x, x' ⟩ => assert_zero (x - x'))
  do let _ ← eqs.mapM
end Provable

-- goal: define circuit such that we can provably use it as subcircuit
structure FormalCircuit (F: Type) (β α: TypePair)
  [Field F] [ProvableType F α] [ProvableType F β]
where
  -- β = inputs, α = outputs
  main: β.var → Stateful F α.var

  assumptions: β.value → Prop
  spec: β.value → α.value → Prop

  soundness:
    -- for all environments that determine witness generation
    ∀ ctx : Context F, ∀ env: ℕ → F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b → assumptions b →
    -- if the constraints hold
    Adversarial.constraints_hold env (main b_var) ctx →
    -- the spec holds on the input and output
    let a := Provable.eval_env env (output (main b_var) ctx)
    spec b a

  completeness:
    ∀ ctx : Context F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval F b_var = b → assumptions b →
    -- constraints hold when using the internal witness generator
    constraints_hold (main b_var) ctx

@[simp]
def subcircuit_soundness (circuit: FormalCircuit F β α) (b_var : β.var) (a_var : α.var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  let a := Provable.eval_env env a_var
  circuit.assumptions b → circuit.spec b a

@[simp]
def subcircuit_completeness (circuit: FormalCircuit F β α) (b_var : β.var) :=
  let b := Provable.eval F b_var
  circuit.assumptions b

def formal_circuit_to_subcircuit (ctx: Context F)
  (circuit: FormalCircuit F β α) (b_var : β.var) : α.var × SubCircuit F :=
  let main := circuit.main b_var
  let res := main ctx
  -- TODO: weirdly, when we destructure we can't deduce origin of the results anymore
  -- let ((_, ops), a_var) := res
  let ops := res.1.2
  let a_var := res.2

  let flat_ops := PreOperation.to_flat_operations ops
  let soundness := subcircuit_soundness circuit b_var a_var
  let completeness := subcircuit_completeness circuit b_var

  have s: SubCircuit F := by
    use flat_ops, soundness, completeness

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

    let b : β.value := Provable.eval_env env b_var
    let a : α.value := Provable.eval_env env a_var
    rintro (as : circuit.assumptions b)
    show circuit.spec b a

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: Adversarial.constraints_hold_from_list env ops by
      exact circuit.soundness ctx env b b_var rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : PreOperation.constraints_hold env (PreOperation.to_flat_operations ops)
    exact PreOperation.can_flatten_first env ops h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions are true
    intro h_completeness
    let b := Provable.eval F b_var
    have as : circuit.assumptions b := h_completeness

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds : constraints_hold_from_list ops := circuit.completeness ctx b b_var rfl as

    -- so we just need to go from constraints to flattened constraints
    exact PreOperation.can_flatten ops h_holds

  ⟨ a_var, s ⟩

-- run a sub-circuit
@[simp]
def subcircuit (circuit: FormalCircuit F β α) (b: β.var) := as_stateful (F:=F) (
  fun ctx =>
    let ⟨ a, subcircuit ⟩ := formal_circuit_to_subcircuit ctx circuit b
    (Operation.Circuit subcircuit, a)
)
end Circuit
