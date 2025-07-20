import Clean.Utils.Tactics
import Clean.Circuit.Provable

-- Test structure with ProvableStruct instance
structure TestInputs (F : Type) where
  x : F
  y : F
  z : F

instance : ProvableStruct TestInputs where
  components := [field, field, field]
  toComponents := fun { x, y, z } => .cons x (.cons y (.cons z .nil))
  fromComponents := fun (.cons x (.cons y (.cons z .nil))) => { x, y, z }

-- Debug test with trace
theorem test_with_trace {F : Type} [Field F]
    (h : { x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) : 
    (1 : F) = 4 := by
  trace "Before tactic: {h}"
  split_struct_eq
  trace "After tactic: {h}"
  -- Let's see if the type shows up  
  have type_of_h := inferInstanceAs (({ x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) = (h.symm.symm))
  trace "Type info: {type_of_h}"
  sorry