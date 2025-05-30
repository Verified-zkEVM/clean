/-
This file contains lemmas to unfold the various common operations done on a circuit,
on all of the primitive circuit building blocks.

An alternative (and previously used) approach is to unfold both the common operations and building blocks
to their definitions, and let simp reason at the fully unfolded level.
-/
import Clean.Circuit.SubCircuit

variable {F : Type} [Field F] {α β : Type} {n : ℕ} {env : Environment F}

namespace Circuit

-- from elaborated

variable {output : ℕ → α} {operations : ℕ → Operations F} {local_length : ℕ → ℕ}
  {local_length_eq : ∀ n, (operations n).local_length = local_length n}

@[circuit_norm high] theorem fromElaborated_output (n : ℕ) :
  (fromElaborated {output, local_length, operations, local_length_eq}).output n = output n := rfl

@[circuit_norm high] theorem fromElaborated_operations (n : ℕ) :
  (fromElaborated {output, local_length, operations, local_length_eq}).operations n = operations n := rfl

@[circuit_norm high] theorem fromElaborated_local_length (n : ℕ) :
    (fromElaborated {output, local_length, operations, local_length_eq}).local_length n = local_length n := by
  show (operations n).local_length = _
  rw [←local_length_eq n]

-- bind

@[circuit_norm low] theorem bind_output (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).output n = (g (f.output n)).output (n + f.local_length n) := rfl

theorem bind_operations (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.local_length n) := rfl

@[circuit_norm low] theorem bind_local_length (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
    (f >>= g).local_length n = f.local_length n + (g (f.output n)).local_length (n + f.local_length n) := by
  show (f.operations n ++ (g _).operations _).local_length = _
  rw [Operations.local_length_append]; rfl

@[circuit_norm low] theorem bind_soundness {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  constraints_hold.soundness (env) ((f >>= g).operations n)
  ↔ constraints_hold.soundness (env) (f.operations n) ∧
    constraints_hold.soundness (env) ((g (f.output n)).operations (n + f.local_length n)) := by
  rw [constraints_hold.soundness_iff_forAll n, constraints_hold.soundness_iff_forAll n,
    constraints_hold.soundness_iff_forAll (n + f.local_length n), bind_forAll]

@[circuit_norm low] theorem bind_completeness {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  constraints_hold.completeness (env) ((f >>= g).operations n)
  ↔ constraints_hold.completeness (env) (f.operations n) ∧
    constraints_hold.completeness (env) ((g (f.output n)).operations (n + f.local_length n)) := by
  rw [constraints_hold.completeness_iff_forAll n, constraints_hold.completeness_iff_forAll n,
    constraints_hold.completeness_iff_forAll (n + f.local_length n), bind_forAll]

@[circuit_norm low] theorem bind_uses_local_witnesses {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  env.uses_local_witnesses_completeness n ((f >>= g).operations n)
  ↔ env.uses_local_witnesses_completeness n (f.operations n) ∧
    env.uses_local_witnesses_completeness (n + f.local_length n) ((g (f.output n)).operations (n + f.local_length n)) := by
  rw [env.uses_local_witnesses_completeness_iff_forAll, env.uses_local_witnesses_completeness_iff_forAll,
    env.uses_local_witnesses_completeness_iff_forAll, bind_forAll]

-- bind elaborated

@[circuit_norm ↑ 1100] theorem bind_fromElaborated_output (g : α → Circuit F β) (n : ℕ) :
    ((fromElaborated {output, local_length, operations, local_length_eq} >>= g).output n = (g (output n)).output (n + local_length n)) := by
  rw [bind_output, fromElaborated_output, fromElaborated_local_length]

theorem bind_fromElaborated_operations (g : α → Circuit F β) (n : ℕ) :
    ((fromElaborated {output, local_length, operations, local_length_eq} >>= g).operations n = operations n ++ (g (output n)).operations (n + local_length n)) := by
  rw [bind_operations, fromElaborated_output, fromElaborated_local_length, fromElaborated_operations]

@[circuit_norm ↑ 1100] theorem bind_fromElaborated_local_length (g : α → Circuit F β) (n : ℕ) :
    ((fromElaborated {output, local_length, operations, local_length_eq} >>= g).local_length n = local_length n + (g (output n)).local_length (n + local_length n)) := by
  rw [bind_local_length, fromElaborated_output, fromElaborated_local_length]

@[circuit_norm] theorem bind_fromElaborated_soundness {g : α → Circuit F β} (n : ℕ) :
  constraints_hold.soundness (env) ((fromElaborated {output, local_length, operations, local_length_eq} >>= g).operations n)
  ↔ constraints_hold.soundness (env) (operations n) ∧
    constraints_hold.soundness (env) ((g (output n)).operations (n + local_length n)) := by
  set f : Elaborated F α := {output, local_length, operations, local_length_eq}
  rw [show local_length n = f.local_length n from rfl, ←f.local_length_eq]
  apply bind_soundness

@[circuit_norm] theorem bind_fromElaborated_completeness {g : α → Circuit F β} (n : ℕ) :
  constraints_hold.completeness (env) ((fromElaborated {output, local_length, operations, local_length_eq} >>= g).operations n)
  ↔ constraints_hold.completeness (env) (operations n) ∧
    constraints_hold.completeness (env) ((g (output n)).operations (n + local_length n)) := by
  set f : Elaborated F α := {output, local_length, operations, local_length_eq}
  rw [show local_length n = f.local_length n from rfl, ←f.local_length_eq]
  apply bind_completeness

@[circuit_norm] theorem bind_fromElaborated_uses_local_witnesses {g : α → Circuit F β} (n : ℕ) :
  env.uses_local_witnesses_completeness n ((fromElaborated {output, local_length, operations, local_length_eq} >>= g).operations n)
  ↔ env.uses_local_witnesses_completeness n (operations n) ∧
    env.uses_local_witnesses_completeness (n + local_length n) ((g (output n)).operations (n + local_length n)) := by
  set f : Elaborated F α := {output, local_length, operations, local_length_eq}
  rw [show local_length n = f.local_length n from rfl, ←f.local_length_eq]
  apply bind_uses_local_witnesses

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
