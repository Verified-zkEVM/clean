import Clean.Halo2.Keygen.Pdqsort

/-!
# Staged pdqsort evaluation

This module separates pdqsort's recursive control flow from its data-dependent partition
steps. A concrete execution can supply a small recursion plan and kernel-check individual
partitions, while `quicksortPlanned_sound` reconnects those checks to the original
implementation.
-/

namespace Halo2.FloorPlanner.Pdqsort

/-- The recursive-call shape of one concrete pdqsort execution. The data-dependent
partition work remains executable; only the recursion tree is supplied. -/
inductive Plan where
  | done
  | unary (child : Plan)
  | binary (left right : Plan)
deriving DecidableEq, Repr

variable {T : Type} [Inhabited T]

instance {S : Type} [DecidableEq S] : DecidableEq (ForInStep S)
  | .done left, .done right =>
      if h : left = right then isTrue (by cases h; rfl)
      else isFalse (by intro contradiction; cases contradiction; exact h rfl)
  | .yield left, .yield right =>
      if h : left = right then isTrue (by cases h; rfl)
      else isFalse (by intro contradiction; cases contradiction; exact h rfl)
  | .done _, .yield _ | .yield _, .done _ => isFalse nofun

def runSteps {S : Type} (step : S → ForInStep S) : ℕ → S → S
  | 0, state => state
  | fuel + 1, state =>
      match step state with
      | .done result => result
      | .yield result => runSteps step fuel result

theorem forIn_ignored_eq_runSteps
    {I S : Type}
    (indices : List I) (state : S) (step : S → ForInStep S) :
    (Id.run <| forIn indices state fun _ state => pure (step state)) =
      runSteps step indices.length state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      simp only [runSteps]
      cases hstep : step state <;> simp [hstep, inductionHypothesis]

structure PartitionSetup (T : Type) where
  values : Array T
  pivot : T
  left : ℕ
  right : ℕ
deriving DecidableEq, Repr

def preparePartition (values : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool) : PartitionSetup T := Id.run do
  let values := swp values 0 pivotIndex
  let pivot := values[0]!
  let size := values.size
  let mut left := 0
  let mut right := size - 1
  for _ in [0:size] do
    if left < right && isLess values[1 + left]! pivot then
      left := left + 1
    else break
  for _ in [0:size] do
    if left < right && !isLess values[1 + (right - 1)]! pivot then
      right := right - 1
    else break
  return ⟨values, pivot, left, right⟩

def finishPartition (setup : PartitionSetup T)
    (partitioned : ℕ × Array T) : (ℕ × Bool) × Array T :=
  let values := overwrite setup.values (1 + setup.left) partitioned.2
  let middle := setup.left + partitioned.1
  let wasPartitioned := decide (setup.left ≥ setup.right)
  ((middle, wasPartitioned), swp values 0 middle)

def partitionPFactored (values : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool) : (ℕ × Bool) × Array T :=
  let setup := preparePartition values pivotIndex isLess
  finishPartition setup <| partitionInBlocks
    (setup.values.extract (1 + setup.left) (1 + setup.right))
    setup.pivot isLess

theorem partitionP_eq_partitionPFactored
    (values : Array T) (pivotIndex : ℕ) (isLess : T → T → Bool) :
    partitionP values pivotIndex isLess =
      partitionPFactored values pivotIndex isLess := by
  rfl

def initialBlockLoopState (values : Array T) : BlockLoopState T := {
  v := values
  l := 0
  r := values.size
  blockL := 128
  blockR := 128
  startL := 0
  endL := 0
  offsetsL := Array.replicate 128 0
  startR := 0
  endR := 0
  offsetsR := Array.replicate 128 0
}

def finishBlockLoop (state : BlockLoopState T) : ℕ × Array T :=
  if state.startL < state.endL then
    let result := cleanupLeft (List.range' 0 (128 + 1)) state.startL
      state.l state.offsetsL ⟨state.endL, state.r, state.v⟩
    (result.2.1, result.2.2)
  else if state.startR < state.endR then
    let result := cleanupRight (List.range' 0 (128 + 1)) state.startR
      state.r state.offsetsR ⟨state.endR, state.l, state.v⟩
    (result.2.1, result.2.2)
  else
    (state.l, state.v)

def partitionInBlocksBySteps (values : Array T) (pivot : T)
    (isLess : T → T → Bool) : ℕ × Array T :=
  finishBlockLoop <| runSteps (blockLoopStep pivot isLess)
    (values.size + 4) (initialBlockLoopState values)

theorem partitionInBlocks_eq_partitionInBlocksBySteps
    (values : Array T) (pivot : T) (isLess : T → T → Bool) :
    partitionInBlocks values pivot isLess =
      partitionInBlocksBySteps values pivot isLess := by
  unfold partitionInBlocks partitionInBlocksFactored
    partitionInBlocksBySteps
  change finishBlockLoop
      (Id.run <| forIn (List.range' 0 (values.size + 4))
        (initialBlockLoopState values) fun _ state =>
          pure (blockLoopStep pivot isLess state)) =
    finishBlockLoop
      (runSteps (blockLoopStep pivot isLess) (values.size + 4)
        (initialBlockLoopState values))
  rw [forIn_ignored_eq_runSteps]
  simp

/-- The arguments of one recursive pdqsort call. -/
structure Request (T : Type) where
  input : Array T
  predecessor : Option T
  limit : ℕ
  wasBalanced : Bool
  wasPartitioned : Bool
deriving DecidableEq, Repr

/-- The nonrecursive result of one pdqsort driver step.  A step either finishes,
requests one recursive result to append to a prefix, or requests the two sides
of a pivot partition. -/
inductive Layer (T : Type) where
  | done (output : Array T)
  | unary (head : Array T) (child : Request T)
  | binary (left : Request T) (pivot : T) (right : Request T)
deriving DecidableEq, Repr

def partitionResultLayer
    (pred : Option T) (limit len : ℕ) : ((ℕ × Bool) × Array T) → Layer T
  | ((mid, wasPartitioned), partitioned) =>
  let balanced := decide (Nat.min mid (len - mid) ≥ len / 8)
  let pivotValue := partitioned[mid]!
  let left := partitioned.extract 0 mid
  let right := partitioned.extract (mid + 1) partitioned.size
  .binary
    ⟨left, pred, limit,
      if left.size < right.size then true else balanced,
      if left.size < right.size then true else wasPartitioned⟩
    pivotValue
    ⟨right, some pivotValue, limit,
      if left.size < right.size then balanced else true,
      if left.size < right.size then wasPartitioned else true⟩

def partitionLayer
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len pivot : ℕ) : Layer T :=
  partitionResultLayer pred limit len (partitionP v pivot isLess)

theorem partitionLayer_eq_of_partitionP_eq
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len pivot : ℕ) (result : (ℕ × Bool) × Array T)
    (hresult : partitionP v pivot isLess = result) :
    partitionLayer v isLess pred limit len pivot =
      partitionResultLayer pred limit len result := by
  rw [partitionLayer, hresult]

def predecessorLayer
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (pivot : ℕ) : Layer T :=
  match pred with
  | some predecessor =>
      if !isLess predecessor (v[pivot]!) then
        let (mid, partitioned) := partitionEqual v pivot isLess
        .unary (partitioned.extract 0 mid)
          ⟨partitioned.extract mid partitioned.size, pred, limit,
            wasBalanced, wasPartitioned⟩
      else
        partitionLayer v isLess pred limit len pivot
  | none =>
      partitionLayer v isLess pred limit len pivot

def afterPivotLayer
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned likelySorted : Bool)
    (pivot : ℕ) : Layer T :=
  if wasBalanced && wasPartitioned && likelySorted then
    let (sorted, partiallySorted) := partialInsertionSort v isLess
    if sorted then .done partiallySorted
    else predecessorLayer partiallySorted isLess pred limit len
      wasBalanced wasPartitioned pivot
  else
    predecessorLayer v isLess pred limit len wasBalanced wasPartitioned pivot

def chooseLayer
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool) : Layer T :=
  let ((pivot, likelySorted), selected) := choosePivot v isLess
  afterPivotLayer selected isLess pred limit len wasBalanced wasPartitioned
    likelySorted pivot

def longLayer
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool) : Layer T :=
  if !wasBalanced then
    chooseLayer (breakPatterns v) isLess pred (limit - 1) len
      wasBalanced wasPartitioned
  else
    chooseLayer v isLess pred limit len wasBalanced wasPartitioned

/-- Evaluate exactly one pdqsort driver layer, without entering any recursive
call.  Closed equalities about this function therefore never normalize a whole
sort tree. -/
def stepLayer
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit : ℕ) (wasBalanced wasPartitioned : Bool) : Layer T :=
  let len := v.size
  if len ≤ 20 then .done (insertionSort v isLess)
  else if limit == 0 then .done (heapsort v isLess)
  else longLayer v isLess pred limit len wasBalanced wasPartitioned

theorem stepLayer_none_true_eq_partitionLayer_of_choosePivot_eq
    (v selected : Array T) (isLess : T → T → Bool)
    (limit pivot : ℕ) (wasPartitioned : Bool)
    (hshort : ¬v.size ≤ 20) (hlimit : ¬limit == 0)
    (hchoose : choosePivot v isLess = ((pivot, false), selected)) :
    stepLayer v isLess none limit true wasPartitioned =
      partitionLayer selected isLess none limit v.size pivot := by
  simp [stepLayer, hshort, hlimit, longLayer, chooseLayer, hchoose,
    afterPivotLayer, predecessorLayer]

def interpretLayer
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) : Layer T → Option (Array T)
  | .done output => some output
  | .unary head child => do
      let .unary childPlan := plan | none
      let tail ← rec childPlan child.input child.predecessor child.limit
        child.wasBalanced child.wasPartitioned
      return head ++ tail
  | .binary left pivot right => do
      let .binary leftPlan rightPlan := plan | none
      let leftOutput ← rec leftPlan left.input left.predecessor left.limit
        left.wasBalanced left.wasPartitioned
      let rightOutput ← rec rightPlan right.input right.predecessor right.limit
        right.wasBalanced right.wasPartitioned
      return leftOutput ++ #[pivot] ++ rightOutput

def recursePartitionPlanned
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len pivot : ℕ) : Option (Array T) := do
  let .binary leftPlan rightPlan := plan | none
  let ((mid, wasPartitioned), partitioned) := partitionP v pivot isLess
  let balanced := decide (Nat.min mid (len - mid) ≥ len / 8)
  let pivotValue := partitioned[mid]!
  let left := partitioned.extract 0 mid
  let right := partitioned.extract (mid + 1) partitioned.size
  let leftResult ← rec leftPlan left pred limit
    (if left.size < right.size then true else balanced)
    (if left.size < right.size then true else wasPartitioned)
  let rightResult ← rec rightPlan right (some pivotValue) limit
    (if left.size < right.size then balanced else true)
    (if left.size < right.size then wasPartitioned else true)
  return leftResult ++ #[pivotValue] ++ rightResult

def recursePredPlanned
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) (pivot : ℕ) :
    Option (Array T) :=
  match pred with
  | some predecessor =>
      if !isLess predecessor (v[pivot]!) then do
        let .unary child := plan | none
        let (mid, partitioned) := partitionEqual v pivot isLess
        let head := partitioned.extract 0 mid
        let tail ← rec child (partitioned.extract mid partitioned.size)
          pred limit wasBalanced wasPartitioned
        return head ++ tail
      else
        recursePartitionPlanned rec plan v isLess pred limit len pivot
  | none =>
      recursePartitionPlanned rec plan v isLess pred limit len pivot

def recurseAfterPivotPlanned
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned likelySorted : Bool) (pivot : ℕ) :
    Option (Array T) :=
  if wasBalanced && wasPartitioned && likelySorted then
    let (sorted, partiallySorted) := partialInsertionSort v isLess
    if sorted then some partiallySorted
    else recursePredPlanned rec plan partiallySorted isLess pred limit len
      wasBalanced wasPartitioned pivot
  else
    recursePredPlanned rec plan v isLess pred limit len
      wasBalanced wasPartitioned pivot

def recurseChoosePlanned
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) : Option (Array T) :=
  let ((pivot, likelySorted), selected) := choosePivot v isLess
  recurseAfterPivotPlanned rec plan selected isLess pred limit len
    wasBalanced wasPartitioned likelySorted pivot

def recurseLongPlanned
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) : Option (Array T) :=
  if !wasBalanced then
    recurseChoosePlanned rec plan (breakPatterns v) isLess pred
      (limit - 1) len wasBalanced wasPartitioned
  else
    recurseChoosePlanned rec plan v isLess pred limit len
      wasBalanced wasPartitioned

def recurseStepPlanned
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit : ℕ)
    (wasBalanced wasPartitioned : Bool) : Option (Array T) :=
  let len := v.size
  if len ≤ 20 then some (insertionSort v isLess)
  else if limit == 0 then some (heapsort v isLess)
  else recurseLongPlanned rec plan v isLess pred limit len
    wasBalanced wasPartitioned

theorem recursePartitionPlanned_eq_interpretLayer
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len pivot : ℕ) :
    recursePartitionPlanned rec plan v isLess pred limit len pivot =
      interpretLayer rec plan (partitionLayer v isLess pred limit len pivot) := by
  unfold recursePartitionPlanned partitionLayer
  generalize hpartition : partitionP v pivot isLess = partitioned
  rcases partitioned with ⟨⟨mid, wasPartitioned⟩, partitioned⟩
  cases plan <;> rfl

theorem recursePredPlanned_eq_interpretLayer
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) (pivot : ℕ) :
    recursePredPlanned rec plan v isLess pred limit len wasBalanced
      wasPartitioned pivot =
      interpretLayer rec plan (predecessorLayer v isLess pred limit len
        wasBalanced wasPartitioned pivot) := by
  cases pred with
  | none => exact recursePartitionPlanned_eq_interpretLayer ..
  | some predecessor =>
      simp only [recursePredPlanned, predecessorLayer]
      split
      · cases plan <;> rfl
      · exact recursePartitionPlanned_eq_interpretLayer ..

theorem recurseAfterPivotPlanned_eq_interpretLayer
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned likelySorted : Bool) (pivot : ℕ) :
    recurseAfterPivotPlanned rec plan v isLess pred limit len wasBalanced
      wasPartitioned likelySorted pivot =
      interpretLayer rec plan (afterPivotLayer v isLess pred limit len
        wasBalanced wasPartitioned likelySorted pivot) := by
  unfold recurseAfterPivotPlanned afterPivotLayer
  split
  · generalize hinsertion : partialInsertionSort v isLess = insertion
    rcases insertion with ⟨sorted, partiallySorted⟩
    cases sorted
    · exact recursePredPlanned_eq_interpretLayer ..
    · rfl
  · exact recursePredPlanned_eq_interpretLayer ..

theorem recurseChoosePlanned_eq_interpretLayer
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) :
    recurseChoosePlanned rec plan v isLess pred limit len wasBalanced
      wasPartitioned =
      interpretLayer rec plan (chooseLayer v isLess pred limit len
        wasBalanced wasPartitioned) := by
  unfold recurseChoosePlanned chooseLayer
  generalize hchoose : choosePivot v isLess = chosen
  rcases chosen with ⟨⟨pivot, likelySorted⟩, selected⟩
  exact recurseAfterPivotPlanned_eq_interpretLayer ..

theorem recurseLongPlanned_eq_interpretLayer
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) :
    recurseLongPlanned rec plan v isLess pred limit len wasBalanced
      wasPartitioned =
      interpretLayer rec plan (longLayer v isLess pred limit len
        wasBalanced wasPartitioned) := by
  unfold recurseLongPlanned longLayer
  split <;> exact recurseChoosePlanned_eq_interpretLayer ..

theorem recurseStepPlanned_eq_interpretLayer
    (rec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit : ℕ)
    (wasBalanced wasPartitioned : Bool) :
    recurseStepPlanned rec plan v isLess pred limit wasBalanced
      wasPartitioned =
      interpretLayer rec plan
        (stepLayer v isLess pred limit wasBalanced wasPartitioned) := by
  simp only [recurseStepPlanned, stepLayer]
  split
  · rfl
  split
  · rfl
  · exact recurseLongPlanned_eq_interpretLayer ..

def recursePlanned : ℕ → Plan → Array T → (T → T → Bool) →
    Option T → ℕ → Bool → Bool → Option (Array T)
  | 0, _, v, isLess, _, _, _, _ => some (heapsort v isLess)
  | fuel + 1, plan, v, isLess, pred, limit, wasBalanced,
      wasPartitioned =>
      recurseStepPlanned
        (fun child v pred limit wasBalanced wasPartitioned =>
          recursePlanned fuel child v isLess pred limit
            wasBalanced wasPartitioned)
        plan v isLess pred limit wasBalanced wasPartitioned

def quicksortPlanned (plan : Plan) (v : Array T)
    (isLess : T → T → Bool) : Option (Array T) :=
  if v.size == 0 then some v
  else recursePlanned (v.size + 1) plan v isLess none
    (Nat.log2 v.size + 1) true true

theorem recursePartitionPlanned_sound
    (plannedRec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (actualRec : Array T → Option T → ℕ → Bool → Bool →
      Array T)
    (hrec : ∀ plan v pred limit balanced partitioned result,
      plannedRec plan v pred limit balanced partitioned = some result →
        actualRec v pred limit balanced partitioned = result)
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len pivot : ℕ) (result : Array T)
    (hresult : recursePartitionPlanned plannedRec plan v isLess pred
      limit len pivot = some result) :
    recursePartition actualRec v isLess pred limit len pivot = result := by
  cases plan with
  | done => simp [recursePartitionPlanned] at hresult
  | unary child => simp [recursePartitionPlanned] at hresult
  | binary leftPlan rightPlan =>
      simp only [recursePartitionPlanned] at hresult
      generalize hpartition : partitionP v pivot isLess = partitionResult
        at hresult ⊢
      rcases partitionResult with ⟨⟨mid, wasPartitioned⟩, partitioned⟩
      simp only at hresult
      let balanced := decide (Nat.min mid (len - mid) ≥ len / 8)
      let pivotValue := partitioned[mid]!
      let left := partitioned.extract 0 mid
      let right := partitioned.extract (mid + 1) partitioned.size
      generalize hleft : plannedRec leftPlan left pred limit
          (if left.size < right.size then true else balanced)
          (if left.size < right.size then true else wasPartitioned) =
        leftResult at hresult
      cases leftResult with
      | none => simp at hresult
      | some leftResult =>
          generalize hright : plannedRec rightPlan right (some pivotValue)
              limit (if left.size < right.size then balanced else true)
              (if left.size < right.size then wasPartitioned else true) =
            rightResult at hresult
          cases rightResult with
          | none => simp at hresult
          | some rightResult =>
              simp at hresult
              subst result
              unfold recursePartition
              rw [hpartition]
              simp only
              split
              · rw [hrec leftPlan left pred limit true true leftResult
                    (by simpa only [if_pos ‹left.size < right.size›] using hleft),
                  hrec rightPlan right (some pivotValue) limit balanced
                    wasPartitioned rightResult
                    (by simpa only [if_pos ‹left.size < right.size›] using hright)]
                simp
              · rw [hrec rightPlan right (some pivotValue) limit true true
                    rightResult
                    (by simpa only [if_neg ‹¬left.size < right.size›] using hright),
                  hrec leftPlan left pred limit balanced wasPartitioned
                    leftResult
                    (by simpa only [if_neg ‹¬left.size < right.size›] using hleft)]
                simp

theorem recursePredPlanned_sound
    (plannedRec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (actualRec : Array T → Option T → ℕ → Bool → Bool →
      Array T)
    (hrec : ∀ plan v pred limit balanced partitioned result,
      plannedRec plan v pred limit balanced partitioned = some result →
        actualRec v pred limit balanced partitioned = result)
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) (pivot : ℕ) (result : Array T)
    (hresult : recursePredPlanned plannedRec plan v isLess pred limit len
      wasBalanced wasPartitioned pivot = some result) :
    recursePred actualRec v isLess pred limit len wasBalanced
      wasPartitioned pivot = result := by
  cases pred with
  | none =>
      exact recursePartitionPlanned_sound plannedRec actualRec hrec plan v
        isLess none limit len pivot result hresult
  | some predecessor =>
      simp only [recursePredPlanned] at hresult
      simp only [recursePred]
      by_cases hequal : isLess predecessor v[pivot]! = false
      · simp [hequal] at hresult ⊢
        cases plan with
        | done => simp at hresult
        | binary left right => simp at hresult
        | unary child =>
            generalize hpartition : partitionEqual v pivot isLess =
              partitionResult at hresult ⊢
            rcases partitionResult with ⟨mid, partitioned⟩
            simp only at hresult
            generalize htail : plannedRec child
                (partitioned.extract mid partitioned.size)
                (some predecessor) limit wasBalanced wasPartitioned =
              tailResult at hresult
            cases tailResult with
            | none => simp at hresult
            | some tailResult =>
                simp at hresult
                subst result
                rw [hrec child
                  (partitioned.extract mid partitioned.size)
                  (some predecessor) limit wasBalanced wasPartitioned
                  tailResult htail]
      · have htrue : isLess predecessor v[pivot]! = true := by
          exact Bool.eq_true_of_not_eq_false hequal
        simp [htrue] at hresult ⊢
        exact recursePartitionPlanned_sound plannedRec actualRec hrec plan v
          isLess (some predecessor) limit len pivot result hresult

theorem recurseAfterPivotPlanned_sound
    (plannedRec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (actualRec : Array T → Option T → ℕ → Bool → Bool →
      Array T)
    (hrec : ∀ plan v pred limit balanced partitioned result,
      plannedRec plan v pred limit balanced partitioned = some result →
        actualRec v pred limit balanced partitioned = result)
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned likelySorted : Bool) (pivot : ℕ)
    (result : Array T)
    (hresult : recurseAfterPivotPlanned plannedRec plan v isLess pred
      limit len wasBalanced wasPartitioned likelySorted pivot = some result) :
    recurseAfterPivot actualRec v isLess pred limit len wasBalanced
      wasPartitioned likelySorted pivot = result := by
  unfold recurseAfterPivotPlanned at hresult
  unfold recurseAfterPivot
  cases wasBalanced <;> cases wasPartitioned <;> cases likelySorted <;>
    simp only [Bool.false_and, Bool.true_and, if_true] at hresult ⊢
  all_goals first
  | exact recursePredPlanned_sound plannedRec actualRec hrec plan v isLess
      pred limit len _ _ pivot result hresult
  | generalize hpartial : partialInsertionSort v isLess = partialResult
      at hresult ⊢
    rcases partialResult with ⟨sorted, partiallySorted⟩
    cases sorted with
    | false =>
        exact recursePredPlanned_sound plannedRec actualRec hrec plan
          partiallySorted isLess pred limit len true true pivot result hresult
    | true => simpa using hresult

theorem recurseChoosePlanned_sound
    (plannedRec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (actualRec : Array T → Option T → ℕ → Bool → Bool →
      Array T)
    (hrec : ∀ plan v pred limit balanced partitioned result,
      plannedRec plan v pred limit balanced partitioned = some result →
        actualRec v pred limit balanced partitioned = result)
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) (result : Array T)
    (hresult : recurseChoosePlanned plannedRec plan v isLess pred limit len
      wasBalanced wasPartitioned = some result) :
    recurseChoose actualRec v isLess pred limit len wasBalanced
      wasPartitioned = result := by
  unfold recurseChoosePlanned at hresult
  unfold recurseChoose
  generalize hchoose : choosePivot v isLess = choice at hresult ⊢
  rcases choice with ⟨⟨pivot, likelySorted⟩, selected⟩
  exact recurseAfterPivotPlanned_sound plannedRec actualRec hrec plan
    selected isLess pred limit len wasBalanced wasPartitioned likelySorted
    pivot result hresult

theorem recurseLongPlanned_sound
    (plannedRec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (actualRec : Array T → Option T → ℕ → Bool → Bool →
      Array T)
    (hrec : ∀ plan v pred limit balanced partitioned result,
      plannedRec plan v pred limit balanced partitioned = some result →
        actualRec v pred limit balanced partitioned = result)
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) (result : Array T)
    (hresult : recurseLongPlanned plannedRec plan v isLess pred limit len
      wasBalanced wasPartitioned = some result) :
    recurseLong actualRec v isLess pred limit len wasBalanced
      wasPartitioned = result := by
  unfold recurseLongPlanned at hresult
  unfold recurseLong
  cases wasBalanced <;> simp only [Bool.not_false, Bool.not_true,
    if_true] at hresult ⊢
  · exact recurseChoosePlanned_sound plannedRec actualRec hrec plan
      (breakPatterns v) isLess pred (limit - 1) len false
      wasPartitioned result hresult
  · exact recurseChoosePlanned_sound plannedRec actualRec hrec plan v
      isLess pred limit len true wasPartitioned result hresult

theorem recurseStepPlanned_sound
    (plannedRec : Plan → Array T → Option T → ℕ → Bool → Bool →
      Option (Array T))
    (actualRec : Array T → Option T → ℕ → Bool → Bool →
      Array T)
    (hrec : ∀ plan v pred limit balanced partitioned result,
      plannedRec plan v pred limit balanced partitioned = some result →
        actualRec v pred limit balanced partitioned = result)
    (plan : Plan) (v : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit : ℕ)
    (wasBalanced wasPartitioned : Bool) (result : Array T)
    (hresult : recurseStepPlanned plannedRec plan v isLess pred limit
      wasBalanced wasPartitioned = some result) :
    recurseStep actualRec v isLess pred limit wasBalanced
      wasPartitioned = result := by
  unfold recurseStepPlanned at hresult
  unfold recurseStep
  by_cases hsmall : v.size ≤ 20
  · simp [hsmall] at hresult ⊢
    exact hresult
  · simp [hsmall] at hresult ⊢
    by_cases hlimit : limit = 0
    · simp [hlimit] at hresult ⊢
      exact hresult
    · simp [hlimit] at hresult ⊢
      exact recurseLongPlanned_sound plannedRec actualRec hrec plan v
        isLess pred limit v.size wasBalanced wasPartitioned result hresult

theorem recursePlanned_sound : ∀ (fuel : ℕ) (plan : Plan)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit : ℕ) (wasBalanced wasPartitioned : Bool) (result : Array T),
    recursePlanned fuel plan v isLess pred limit wasBalanced
      wasPartitioned = some result →
      recurse fuel v isLess pred limit wasBalanced wasPartitioned = result := by
  intro fuel
  induction fuel with
  | zero =>
      intro plan v isLess pred limit wasBalanced wasPartitioned result hresult
      simpa only [recursePlanned, recurse, Option.some.injEq] using hresult
  | succ fuel inductionHypothesis =>
      intro plan v isLess pred limit wasBalanced wasPartitioned result hresult
      rw [recurse.eq_2]
      apply recurseStepPlanned_sound
        (fun child v pred limit balanced partitioned =>
          recursePlanned fuel child v isLess pred limit balanced partitioned)
        (fun v pred limit balanced partitioned =>
          recurse fuel v isLess pred limit balanced partitioned)
      · intro child childInput childPred childLimit childBalanced
          childPartitioned childResult hchild
        exact inductionHypothesis child childInput isLess childPred childLimit
          childBalanced childPartitioned childResult hchild
      · exact hresult

theorem quicksortPlanned_sound (plan : Plan) (v : Array T)
    (isLess : T → T → Bool) (result : Array T)
    (hresult : quicksortPlanned plan v isLess = some result) :
    quicksort v isLess = result := by
  unfold quicksortPlanned at hresult
  unfold quicksort
  by_cases hempty : (v.size == 0) = true
  · simp [hempty] at hresult ⊢
    exact hresult
  · simp [hempty] at hresult ⊢
    exact recursePlanned_sound (v.size + 1) plan v isLess none
      (Nat.log2 v.size + 1) true true result hresult

end Halo2.FloorPlanner.Pdqsort
