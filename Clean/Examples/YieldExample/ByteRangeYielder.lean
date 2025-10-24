import Clean.Circuit.Basic
import Clean.Circuit.Loops
import Clean.Utils.Tactics
import Clean.Utils.Field

namespace Examples.YieldExample.ByteRangeYielder

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Main circuit that yields all byte values from 0 to 255
-/
def main (_ : Var unit (F p)) : Circuit (F p) Unit := do
  -- Yield all byte values as constants
  -- We use foldlRange to iterate and yield each byte value
  Circuit.foldlRange 256 () fun _ i => do
    yield ⟨"byte", [(i.val : F p)]⟩
    return ()

def elaborated : ElaboratedCircuit (F p) unit unit where
  main
  localLength _ := 0
  localLength_eq := by simp [circuit_norm, main]
  yields input env offset :=
    { nl | ∃ (n : F p) (h : n.val < 256), nl = ⟨"byte", [n]⟩ }
  yields_eq := by
    intro input env offset
    simp [main, circuit_norm]
    ext nl
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨⟨n, nlt⟩, hn⟩
      use n
      simp_all only [NamedList.eval, circuit_norm]
      rwa [ZMod.val_cast_of_lt]
      linarith [‹Fact (p > 512)›.elim]
    · rintro ⟨n, hn, nl_eq⟩
      use ⟨ n.val, hn ⟩
      simp_all only [NamedList.eval, circuit_norm, ZMod.natCast_val]
      congr
      rw [FieldUtils.ext_iff, ZMod.val_cast_eq_val_of_lt]
      linarith [‹Fact (p > 512)›.elim]
  subcircuitsConsistent := by simp [circuit_norm, main]

/--
ByteRangeYielder has no assumptions
-/
def Assumptions (_ : unit (F p)) (_ : Set (NamedList (F p))) : Prop := True

/--
Spec: If a NamedList "byte" [i] is in localYields, then i represents a byte value
-/
def Spec (_ : unit (F p)) (_ : unit (F p)) (localYields : Set (NamedList (F p))) : Prop :=
  ∀ (v : (F p)), ⟨"byte", [v]⟩ ∈ localYields → v.val < 256

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
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
  rw [h_i]
  exact hn

def circuit : FormalCircuit (F p) unit unit where
  elaborated
  Assumptions
  Spec
  soundness
  completeness := by circuit_proof_start

end Examples.YieldExample.ByteRangeYielder
