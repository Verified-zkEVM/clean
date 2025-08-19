/- Counting occurrences of ProvableType values

For permutation argument, it's necessary to count the occurrences of values.

This module defines an operation for counting occurrences.
-/

import Clean.Circuit.Provable

/--
An instance of `Accouunt` associates a label to a `ProvableType` that's counted.
There can be multiple labels associated with the same `ProvableType`.
The multiplicity counting occurs separately on each label.
Don't use the same label in multiple accounts.
-/
class Account (label : String) where
  M : TypeMap
  [inst : ProvableType M]

structure Count (F : Type) where
  label : String
  [account : Account label]
  entry : Var account.M F
  multiplicity : Expression F
