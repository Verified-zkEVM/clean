module

public import Clean.Circuit.Provable

/-! # Statically optional circuit columns

`ProvableOptional` selects a layout using a static Boolean parameter and reuses
the existing unit or payload instance,
so absence occupies zero cells and introduces neither a tag nor unused payload cells.
The selector belongs to the circuit's type; it is not a runtime `Option` or witness value.
-/

@[expose] public section

/-- A payload whose presence is fixed by the circuit's type. -/
abbrev ProvableOptional (present : Bool) (M : TypeMap) : TypeMap :=
  match present with
  | false => unit
  | true => M

instance {present : Bool} {M : TypeMap} [ProvableType M] :
    ProvableType (ProvableOptional present M) :=
  match present with
  | false => (inferInstance : ProvableType unit)
  | true => (inferInstance : ProvableType M)

/-- A statically absent payload consumes no columns. -/
@[circuit_norm] theorem ProvableOptional.size {present : Bool} {M : TypeMap} [ProvableType M] :
    size (ProvableOptional present M) = if present then size M else 0 := by
  cases present <;> rfl
