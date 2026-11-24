import Midnight.Math.Witness.Reads
import Mathlib.Tactic

/-! Constructive execution for ordered Halo2 scalar assignments. The executable
check rejects duplicate writes and any witness read not already available.
The resulting environment satisfies all original program equations, with hints
and the usable-row parameter preserved. Circuit adapters must additionally
account for fixed tables, public copies and the actual chosen placement. -/
namespace Midnight.Math.Witness.Execute
open Halo2

variable {F : Type} [FiniteField F]
abbrev Address := AnyColumn × Int

def address (place : RegionIndex → Nat) (cell : AssignedCell F) : Address :=
  (cell.cell.column, (place cell.cell.regionIndex + cell.cell.rowOffset : Nat))

def read (env : ProverEnvironment F) (location : Address) : F := env.get location.1 location.2

def write (env : ProverEnvironment F) (location : Address) (value : F) : ProverEnvironment F :=
  { env with get := fun column row => if (column,row) = location then value else env.get column row }

omit [FiniteField F] in
@[simp] theorem read_write_same (env : ProverEnvironment F) (location : Address) (value : F) :
    read (write env location value) location = value := by simp [read,write]

omit [FiniteField F] in
theorem read_write_other (env : ProverEnvironment F) (location other : Address) (value : F)
    (different : other ≠ location) : read (write env location value) other = read env other := by
  simp only [read, write, Prod.mk.eta, if_neg different]

structure Assignment (F : Type) where
  destination : Address
  program : WitgenIR F 1

def step (place : RegionIndex → Nat) (env : ProverEnvironment F) (assignment : Assignment F) :
    ProverEnvironment F :=
  write env assignment.destination (assignment.program.eval ⟨place,env⟩)[0]

def run (place : RegionIndex → Nat) : List (Assignment F) → ProverEnvironment F → ProverEnvironment F
  | [], env => env
  | assignment :: rest, env => run place rest (step place env assignment)

def allowed (place : RegionIndex → Nat) (known : List Address) (cell : AssignedCell F) : Bool :=
  decide (address place cell ∈ known)

def ordered (place : RegionIndex → Nat) : List Address → List (Assignment F) → Bool
  | _, [] => true
  | known, assignment :: rest =>
    decide (assignment.destination ∉ known) && Reads.program (allowed place known) assignment.program &&
      ordered place (assignment.destination :: known) rest

omit [FiniteField F] in
theorem ordered_cons (place : RegionIndex → Nat) (known : List Address)
    (assignment : Assignment F) (rest : List (Assignment F)) :
    ordered place known (assignment :: rest) = true ↔
      assignment.destination ∉ known ∧ Reads.program (allowed place known) assignment.program = true ∧
        ordered place (assignment.destination :: known) rest = true := by
  simp only [ordered, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

@[simp] theorem run_hint (place : RegionIndex → Nat) (assignments : List (Assignment F))
    (env : ProverEnvironment F) : (run place assignments env).hint = env.hint := by
  induction assignments generalizing env with
  | nil => rfl
  | cons assignment rest ih => exact ih (step place env assignment)

@[simp] theorem run_usableRows (place : RegionIndex → Nat) (assignments : List (Assignment F))
    (env : ProverEnvironment F) : (run place assignments env).usableRows = env.usableRows := by
  induction assignments generalizing env with
  | nil => rfl
  | cons assignment rest ih => exact ih (step place env assignment)

/-- Execution preserves all cells supplied before the assignment sequence. -/
theorem run_preserves (place : RegionIndex → Nat) (assignments : List (Assignment F))
    (known : List Address) (valid : ordered place known assignments = true)
    (env : ProverEnvironment F) :
    ∀ location ∈ known, read (run place assignments env) location = read env location := by
  induction assignments generalizing known env with
  | nil => intro _ _; rfl
  | cons assignment rest ih =>
    obtain ⟨fresh,_,tail⟩ := (ordered_cons place known assignment rest).mp valid
    intro location member
    have preserved := ih (assignment.destination :: known) tail (step place env assignment) location
      (List.mem_cons_of_mem _ member)
    have different : location ≠ assignment.destination := by intro same; exact fresh (same ▸ member)
    exact preserved.trans (read_write_other env assignment.destination location _ different)

/-- Cells outside the write set remain unchanged, even if they were not listed
as initially available to witness programs. -/
theorem run_preserves_unwritten (place : RegionIndex → Nat) (assignments : List (Assignment F))
    (env : ProverEnvironment F) (location : Address)
    (unwritten : ∀ assignment ∈ assignments, location ≠ assignment.destination) :
    read (run place assignments env) location = read env location := by
  induction assignments generalizing env with
  | nil => rfl
  | cons assignment rest ih =>
    have tail := ih (step place env assignment)
      (fun next member => unwritten next (List.mem_cons_of_mem _ member))
    exact tail.trans (read_write_other env assignment.destination location _
      (unwritten assignment List.mem_cons_self))

/-- Original witness equations evaluated in the final environment. -/
def Satisfies (place : RegionIndex → Nat) (env : ProverEnvironment F) (assignments : List (Assignment F)) : Prop :=
  ∀ assignment ∈ assignments,
    read env assignment.destination = (assignment.program.eval ⟨place,env⟩)[0]

/-- The ordered evaluator constructs an environment satisfying every assignment;
its premise is solely the syntactic dependency/freshness check. -/
theorem run_satisfies (place : RegionIndex → Nat) (assignments : List (Assignment F))
    (known : List Address) (valid : ordered place known assignments = true)
    (env : ProverEnvironment F) : Satisfies place (run place assignments env) assignments := by
  induction assignments generalizing known env with
  | nil => intro _ member; contradiction
  | cons assignment rest ih =>
    obtain ⟨fresh,accepted,tail⟩ := (ordered_cons place known assignment rest).mp valid
    have keep := run_preserves place rest (assignment.destination :: known) tail (step place env assignment)
    have generated := ih (assignment.destination :: known) tail (step place env assignment)
    intro current member
    rcases List.mem_cons.mp member with same | remaining
    · subst current
      have target := keep assignment.destination List.mem_cons_self
      have agree : ∀ cell : AssignedCell F, allowed place known cell = true →
          Witgen.WitgenEnv.readVar (F := F) (Placed.mk place env) cell =
            Witgen.WitgenEnv.readVar (F := F) (Placed.mk place (run place (assignment :: rest) env)) cell := by
        intro cell available
        have member : address place cell ∈ known := of_decide_eq_true available
        have preserved := run_preserves place (assignment :: rest) known valid env _ member
        exact preserved.symm
      have evaluated := Reads.program_congr (allowed place known) assignment.program accepted
        (Placed.mk place env) (Placed.mk place (run place (assignment :: rest) env)) agree
        (run_hint place (assignment :: rest) env).symm
      have value := congrArg (fun result : Vector F 1 => result[0]) evaluated
      exact target.trans ((read_write_same env assignment.destination _).trans value)
    · exact generated current remaining

end Midnight.Math.Witness.Execute
