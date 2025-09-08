import Mathlib.Algebra.Field.Basic
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
the knowledge gained by using `s` is available. `SentenceOrder` is just relevant during soundness proofs.
-/

structure SentenceOrder (s : PropertySet F) where
  CanDepend : Sentence s → Sentence s → Prop
  well_founded : WellFounded CanDepend

/-
The soundness proof will depend on a set of sentences whose yields have been checked valid.

If a sentence `s` is in the set, success of `use s` guarantees `s` holds.

During soundness proof, when `t` is proven valid for `yield t`, the proof can use
the knowledge obtained from `use s` with `s ≺ t`. This restriction prevents
the soundness proof from seeing `use s`, gets convinced of `s` and uses that to `yield s`.

The soundness proof uses mathematical induciton on the growing set of sentences.
- If the current set contains `s`, `use s` guarantees `s` holds.
- If the current set doesn't contain `s`, `use s` doesn't do anything.
- If the current set contains all the precedents of `s`,
  `yield s` requires proof that `s` holds.
- If the current set doesn't contain some elements of the precendents of `s`,
  `yield s` doesn't do anything.
-/

-- The current focus is to encode the above rules.
-- Another TODO is to run the mathemtcial induction so that we get the final theorem about soundness of a circuit.

/--
A type for keeping track of "all `yield`s of this form have been checked."

When a sentence `s` is in `CheckedYields`, if there is `yield s` anywhere, `s` is known to hold.
If nobody ever does `yield s`, `s` can be false even when `s` is in `CheckedYield`.
-/
def CheckedYields {F : Type} (sentences : PropertySet F) := Set (Sentence sentences)

instance {F : Type} {sentences : PropertySet F} : EmptyCollection (CheckedYields sentences) where
  emptyCollection := by unfold CheckedYields; exact ∅

instance {F : Type} {sentences : PropertySet F} : HasSubset (CheckedYields sentences) where
  Subset := by unfold CheckedYields; exact Set.Subset

/-
The completeness proof is simpler. `yield s` requires `s` is valid. `use s` requires that `yield s` is done somewhere.
The completeness proof will need to keep track of the set of the yielded sentences.
-/

-- The current focus is to get the soundness proof working.

/-- Empty PropertySet for use in contexts that don't need the use/yield framework (e.g., tables) -/
def emptyPropertySet (F : Type) : PropertySet F where
  properties := {}
  NameConsistency := fun _ _ h => by simp at h

/-- Trivial SentenceOrder for the empty PropertySet -/
def emptyOrder (F : Type) : SentenceOrder (emptyPropertySet F) where
  CanDepend := fun _ _ => False
  well_founded := WellFounded.intro fun s => by
    constructor
    intro t h
    exact False.elim h

/-- Empty CheckedYields for use in contexts that don't need the use/yield framework -/
def emptyChecked (F : Type) : CheckedYields (emptyPropertySet F) := ∅

/- TODO:

 * (done) Add yielded argument next to Environment
 * (done) Add CheckedYields argument to Spec's used during the soundness proof
   + In Soundness, Spec needs to take sentances and checked
 * Add `yield` operation
   + `yield` is similar to `witness` (for completeness, `yield` makes sure that the yielded tuple is in `YieldContext`.)
 * Change Soundness statement so that `yield` validity becomes a goal according to the above rule
 * Add `use` operation
   + `use` is similar to `lookup`
   + `use` constraint guarantees properties if it's in the current `CheckedYield`

-/
