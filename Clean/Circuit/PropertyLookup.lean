import Clean.Circuit.Provable
variable {F : Type}

structure Property (F : Type) where
  name : String
  arity : ℕ
  Predicate : Vector F arity → Prop

structure PropertySet (F : Type) where
  properties : Std.HashMap String (Property F)
  NameConsistency : ∀ name (p : Property F), properties[name]? = some p → p.name = name

structure Sentence (s : PropertySet F) where
  name : String
  property : Property F
  propertyFound : s.properties[name]? = some property
  entry : Vector F property.arity

/-
Ordering of sentecnes: `s ≺ t` means, for yielding `t` (and especially for proving that `t` is valid),
the knowledge gained by using `s` is available.
-/

structure SentenceOrder (F : Type) extends s : PropertySet F where
  CanDepend : Sentence s → Sentence s → Prop
  well_founded : WellFounded CanDepend

/-
The soundness proof will depend on a set of sentences whose yields have been checked valid.

If a sentence `s` is in the set, success of `use s` implies `s` is valid.

During soundness proof, when `t` is proven valid for `yield t`, the proof can use
the knowledge obtained from `use s` with `s ≺ t`. This restriction prevents
the soundness proof from seeing `use s`, gets convinced of `s` and uses that to `yield s`.

The soundness proof uses mathematical induciton on the growing set of sentences.
- If the current set contains `s`, `use s` guarantees `s` is valid.
- If the current set doesn't contain `s`, `use s` doesn't do anything.
- If the current set contains all the precedents of `s`,
  `yield s` requires proof that `s` is valid.
- If the current set doesn't contain some elements of the precendents of `s`,
  `yield s` doesn't do anything.
-/

-- The current focus is to encode the above rules.
-- Another TODO is to run the mathemtcial induction so that we get the final theorem about soundness of a circuit.

def CheckedYields {F : Type} (sentences : PropertySet F) := Set (Sentence sentences)

/-
The completeness proof is simpler. `yield s` requires `s` is valid. `use s` requires that `yield s` is done somewhere.
The completeness proof will need to keep track of the set of the yielded sentences.
-/

-- The current focus is to get the soundness proof working.
