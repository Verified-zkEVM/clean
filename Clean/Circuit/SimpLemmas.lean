/-
This file contains lemmas to unfold the various common operations done on a circuit,
on all of the primitive circuit building blocks.

An alternative (and previously used) approach is to unfold both the common operations and building blocks
to their definitions, and let simp reason at the fully unfolded level.
-/
import Clean.Circuit.SubCircuit

variable {F : Type} [Field F] {α β : Type} {n : ℕ}

namespace Circuit

-- from elaborated

@[circuit_norm high] theorem fromElaborated_output {α: Type} (circuit: Elaborated F α) (n : ℕ) :
  (fromElaborated circuit).output n = circuit.output n := rfl

@[circuit_norm high] theorem fromElaborated_operations {α: Type} (circuit: Elaborated F α) (n : ℕ) :
  (fromElaborated circuit).operations n = circuit.operations n := rfl

@[circuit_norm high] theorem fromElaborated_local_length {α: Type} (circuit: Elaborated F α) (n : ℕ) :
    (fromElaborated circuit).local_length n = circuit.local_length n := by
  show (circuit.operations n).local_length = _
  rw [←circuit.local_length_eq n]

-- bind

@[circuit_norm low] theorem bind_output {α β} (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).output n = (g (f.output n)).output (n + f.local_length n) := rfl

@[circuit_norm low] theorem bind_operations {α β} (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.local_length n) := rfl

@[circuit_norm low] theorem bind_local_length {α β} (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
    (f >>= g).local_length n = f.local_length n + (g (f.output n)).local_length (n + f.local_length n) := by
  show (f.operations n ++ (g _).operations _).local_length = _
  rw [Operations.local_length_append]; rfl

-- bind elaborated

@[circuit_norm ↑ 1100] theorem bind_fromElaborated_output {α β} (f : Elaborated F α) (g : α → Circuit F β) (n : ℕ) :
    ((fromElaborated f >>= g).output n = (g (f.output n)).output (n + f.local_length n)) := by
  rw [bind_output, fromElaborated_output, fromElaborated_local_length]

@[circuit_norm ↑ 1100] theorem bind_fromElaborated_operations {α β} (f : Elaborated F α) (g : α → Circuit F β) (n : ℕ) :
    ((fromElaborated f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.local_length n)) := by
  rw [bind_operations, fromElaborated_output, fromElaborated_local_length, fromElaborated_operations]

@[circuit_norm ↑ 1100] theorem bind_fromElaborated_local_length {α β} (f : Elaborated F α) (g : α → Circuit F β) (n : ℕ) :
    ((fromElaborated f >>= g).local_length n = f.local_length n + (g (f.output n)).local_length (n + f.local_length n)) := by
  rw [bind_local_length, fromElaborated_output, fromElaborated_local_length]

-- pure

@[circuit_norm] theorem pure_output (a : α) (n : ℕ) :
  (pure a : Circuit F α).output n = a := rfl

@[circuit_norm] theorem pure_operations {α} (a : α) (n : ℕ) :
  (pure a : Circuit F α).operations n = [] := rfl

@[circuit_norm] theorem pure_local_length {α} (a : α) (n : ℕ) :
  (pure a : Circuit F α).local_length n = 0 := rfl

section subcircuit
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

end subcircuit
end Circuit

-- ProvableType.witness

@[circuit_norm] theorem ProvableType.witness_output {α: TypeMap} [ProvableType α] (compute : Environment F → α F) (offset : ℕ) :
  (ProvableType.witness compute).output offset = var_from_offset α offset := rfl

@[circuit_norm] theorem ProvableType.witness_operations {α: TypeMap} [ProvableType α] (compute : Environment F → α F) (offset : ℕ) :
  (ProvableType.witness compute).operations offset = [.witness (size α) (fun env => compute env |> to_elements)] := rfl

@[circuit_norm] theorem ProvableType.witness_local_length {α: TypeMap} [ProvableType α] (compute : Environment F → α F) (offset : ℕ) :
  (ProvableType.witness compute).local_length offset = size α := rfl
