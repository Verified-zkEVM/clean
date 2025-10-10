import Clean.Circuit.Basic
import Clean.Circuit.Loops
import Clean.Utils.Tactics

namespace Examples.YieldExample.ByteRangeYielder

variable {F : Type} [Field F]

/--
Main circuit that yields all byte values from 0 to 255
-/
def main (_ : Var unit F) : Circuit F Unit := do
  -- Yield all byte values as constants
  -- We use foldlRange to iterate and yield each byte value
  Circuit.foldlRange 256 () fun _ i => do
    yield (NamedList.mk "byte" [(i.val : F)])
    return ()

def elaborated : ElaboratedCircuit F unit unit where
  main
  localLength _ := 0
  localLength_eq := by simp [circuit_norm, main]
  yields input env offset :=
    { nl | ∃ (n : Nat) (h : n < 256), nl = NamedList.mk "byte" [↑n] }
  yields_eq := by
    intro input env offset
    simp [main, circuit_norm]
    ext nl
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      use n
      aesop
    · rintro ⟨n, hn, nl_eq⟩
      simp only [nl_eq, Set.mem_range]
      use ⟨ n, hn ⟩
      aesop
  subcircuitsConsistent := by simp [circuit_norm, main]

/--
ByteRangeYielder has no assumptions
-/
def Assumptions (_ : unit F) (_ : Set (NamedList F)) : Prop := True

/--
Spec: If a NamedList "byte" [i] is in localYields, then i represents a byte value
-/
def Spec (_ : unit F) (_ : unit F) (localYields : Set (NamedList F)) : Prop :=
  ∀ (i : F), NamedList.mk "byte" [i] ∈ localYields → ∃ (n : Nat), n < 256 ∧ i = n

theorem soundness : Soundness F elaborated Assumptions Spec := by
  circuit_proof_start
  -- After circuit_proof_start, the goal is Spec input output localYields
  -- where localYields is the yields from elaborated
  intro i hi
  -- hi says that NamedList.mk "byte" [i] is in localYields
  -- We need to show ∃ (n : Nat), n < 256 ∧ i = n
  -- localYields comes from elaborated.yields which is { nl | ∃ (n : Nat) (h : n < 256), nl = NamedList.mk "byte" [↑n] }
  simp only [Set.mem_setOf_eq] at hi
  obtain ⟨n, hn, h_eq⟩ := hi
  -- h_eq says NamedList.mk "byte" [i] = NamedList.mk "byte" [↑n]
  -- Therefore [i] = [↑n], so i = ↑n
  injection h_eq with _ h_list
  injection h_list with h_i
  use n

def circuit : FormalCircuit F unit unit where
  elaborated
  Assumptions
  Spec
  soundness
  completeness := by circuit_proof_start

end Examples.YieldExample.ByteRangeYielder
