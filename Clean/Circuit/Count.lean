/- Counting occurrences of ProvableType values

For permutation argument, it's necessary to count the occurrences of values.

This module defines an operation for counting occurrences of field tuples.

The business of `ProvableTypes` can be encoded into field tuples.
-/

import Clean.Circuit.Provable

/--
An `Accouunt` associates a label to the size of tuples to be counted. No runtime information
is contained in an `Account`. The actual counting will happen during the witness generation time.

The multiplicity counting occurs separately on each (label, arity).
`Account`s with different arities are treated separate even if they share the same label.
-/
structure Account where
  label : String
  arity : ℕ -- exact number of field elements of tuples to be counted

structure Count (F : Type) where
  account : Account
  entry : Vector (Expression F) account.arity
  multiplicity : Expression F -- summed up on each different value of entry

instance {F : Type} [Repr F] : Repr (Count F) where
  reprPrec c _ := "(Count " ++ c.account.label ++ " " ++ reprStr c.entry ++ ")"
