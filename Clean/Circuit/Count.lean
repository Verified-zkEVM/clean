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
class Account (label : String) (M : outParam TypeMap) (F : Type) extends ProvableType M, Repr (Var M F)

structure Count (label : String) {M : TypeMap} (F : Type) [Account label M F] where
  entry : Var M F
  multiplicity : Expression F

instance {label : String} {M : TypeMap} {F : Type} [Account label M F] : Repr (Count label (M:=M) F) where
  reprPrec c _ := "(Count " ++ label ++ " " ++ reprStr c.entry ++ ")"
