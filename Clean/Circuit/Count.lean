/- Counting occurrences of ProvableType values

For permutation argument, it's necessary to count the occurrences of values.

This module defines an operation for counting occurrences.
-/

import Clean.Circuit.Provable

/--
An instance of `Accouunt` associates a label to a size of the tuple to be counted.
The multiplicity counting occurs separately on each label.
-/
class Account (label : String) (arity : outParam ℕ) (F : Type)

structure Count (label : String) {arity : ℕ} (F : Type) [Account label arity F] where
  entry : Vector (Expression F) arity
  multiplicity : Expression F -- summed up on each different value of entry

instance {label : String} {arity : ℕ} {F : Type} [Repr F] [Account label arity F] : Repr (Count label F) where
  reprPrec c _ := "(Count " ++ label ++ " " ++ reprStr c.entry ++ ")"
