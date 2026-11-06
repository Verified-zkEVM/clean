module

public import Clean.Circuit.ProvableOptional
import Clean.Utils.Tactics.ProvableStructDeriving

/-! Kernel-checked layout regressions for mode-specific fields, including following-field offsets.
The selector fixes a type-level layout, not a runtime tag. -/

@[expose] public section

namespace TestProvableOptional

structure Reader (enabled : Bool) (F : Type) where
  word : Vector F 4
  mode : ProvableOptional enabled field F
  next : F
deriving ProvableStruct

example : size (Reader false) = 5 := rfl
example : size (Reader true) = 6 := rfl

example : toElements (Reader.mk (F := Nat) (enabled := true) #v[1, 2, 3, 4] 5 6) =
    #v[1, 2, 3, 4, 5, 6] := by
  change ProvableStruct.structToElements _ = _
  rw [ProvableStruct.structToElements_eq]
  rfl

example : toElements (Reader.mk (F := Nat) (enabled := false) #v[1, 2, 3, 4] () 6) =
    #v[1, 2, 3, 4, 6] := by
  change ProvableStruct.structToElements _ = _
  rw [ProvableStruct.structToElements_eq]
  rfl

-- The generic instance retains Clean's exact vector isomorphism in either mode.
example {present : Bool} {M : TypeMap} [ProvableType M] {F : Type}
    (value : ProvableOptional present M F) : fromElements (toElements value) = value :=
  ProvableType.fromElements_toElements value

-- Absence does not require any instance on the unused payload.
example (M : TypeMap) : ProvableType (ProvableOptional false M) := inferInstance
example (M : TypeMap) : size (ProvableOptional false M) = 0 := rfl
example : size (ProvableOptional true (fields 0)) = 0 := rfl
example : size (ProvableVector (ProvableOptional false field) 7) = 0 := rfl
example : size (ProvableOptional true (ProvableOptional true (fields 3))) = 3 := rfl
example (present : Bool) : size (ProvableOptional present field) = if present then 1 else 0 := by
  cases present <;> rfl
example {present : Bool} {M : TypeMap} [ProvableType M] {F : Type}
    (value : Vector F (size (ProvableOptional present M))) :
    toElements (fromElements (M := ProvableOptional present M) value) = value :=
  ProvableType.toElements_fromElements value

end TestProvableOptional
