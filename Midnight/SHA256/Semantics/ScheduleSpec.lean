import Midnight.SHA256.Spec
import Mathlib.Tactic

/-! Pure equivalence of the native growing-array schedule recurrence and
Clean's fixed-vector SHA specification. This module asserts no circuit theorem. -/
namespace Midnight.SHA256.Semantics.ScheduleSpec

def next (i : Nat) (words : Array Nat) : Nat :=
  (words[i-16]! + words[i-7]! + Specs.SHA256.lowerSigma0 words[i-15]! +
    Specs.SHA256.lowerSigma1 words[i-2]!) % 2 ^ 32

def step (i : Nat) (words : Array Nat) : Array Nat := words.push (next i words)

def expand (block : Array Nat) : Array Nat :=
  (List.range' 16 48).foldl (fun words i => step i words) block

theorem step_size (i : Nat) (words : Array Nat) : (step i words).size = words.size + 1 := by
  simp [step]

theorem fold_size (items : List Nat) (words : Array Nat) :
    (items.foldl (fun words i => step i words) words).size = words.size + items.length := by
  induction items generalizing words with
  | nil => simp
  | cons item items ih =>
    simp only [List.foldl_cons, ih, step_size, List.length_cons]
    omega

theorem foldl_range {α : Type} (count start : Nat) (f : Nat → α → α) (initial : α) :
    Fin.foldl count (fun state i => f (i.val + start) state) initial =
      (List.range' start count).foldl (fun state i => f i state) initial := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Fin.foldl_succ_last, List.range'_1_concat, List.foldl_append]
    simp only [Fin.val_last, Fin.val_castSucc, List.foldl_cons, List.foldl_nil]
    rw [ih, Nat.add_comm count start]

private theorem foldl_map {α β : Type} (convert : α → β) (count : Nat)
    (f : α → Fin count → α) (g : β → Fin count → β)
    (commutes : ∀ value index, convert (f value index) = g (convert value) index)
    (initial : α) :
    convert (Fin.foldl count f initial) = Fin.foldl count g (convert initial) := by
  simp only [Fin.foldl_eq_finRange_foldl]
  exact (List.foldl_hom convert (fun value index => (commutes value index).symm)).symm

private theorem add32_four (a b c d : Nat) :
    add32 (add32 d b) (add32 c a) = (a + b + c + d) % 2 ^ 32 := by
  simp only [add32, ← Nat.add_mod]
  congr 1
  omega

private def fixedStep (i : Nat) (words : Array Nat) : Array Nat :=
  words.setIfInBounds i (next i words)

private def initial (block : Vector Nat 16) : Vector Nat 64 :=
  Vector.mapFinRange 64 fun i => if h : i.val < 16 then block.get ⟨i.val, h⟩ else 0

private def referenceStep (words : Vector Nat 64) (i : Fin 48) : Vector Nat 64 :=
  let j := i.val + 16
  let value := add32 (add32 (Specs.SHA256.lowerSigma1 words[j - 2]) words[j - 7])
    (add32 (Specs.SHA256.lowerSigma0 words[j - 15]) words[j - 16])
  words.set (⟨j, by omega⟩ : Fin 64) value

private theorem referenceStep_array (words : Vector Nat 64) (i : Fin 48) :
    (referenceStep words i).toArray = fixedStep (i.val + 16) words.toArray := by
  unfold referenceStep fixedStep next
  dsimp only
  rw [add32_four]
  have h0 : i.val + 16 < words.toArray.size := by simp; omega
  have h2 : i.val + 16 - 2 < words.toArray.size := by simp; omega
  have h7 : i.val + 16 - 7 < words.toArray.size := by simp; omega
  have h15 : i.val + 16 - 15 < words.toArray.size := by simp; omega
  have h16 : i.val + 16 - 16 < words.toArray.size := by simp; omega
  simp only [Vector.toArray_set, Array.setIfInBounds, h0, ↓reduceDIte,
    getElem!_pos words.toArray (i.val + 16 - 2) h2,
    getElem!_pos words.toArray (i.val + 16 - 7) h7,
    getElem!_pos words.toArray (i.val + 16 - 15) h15,
    getElem!_pos words.toArray (i.val + 16 - 16) h16,
    Vector.getElem_toArray]

private theorem reference_array (block : Vector Nat 16) :
    (Specs.SHA256.messageSchedule block).toArray =
      (List.range' 16 48).foldl (fun words i => fixedStep i words) (initial block).toArray := by
  change (Fin.foldl 48 referenceStep (initial block)).toArray = _
  rw [foldl_map Vector.toArray 48 referenceStep
    (fun words i => fixedStep (i.val + 16) words) referenceStep_array]
  exact foldl_range 48 16 fixedStep (initial block).toArray

/-- Prefix agreement describes the actual growing array, without making any
claim about the unused suffix of the fixed reference vector. -/
private def Prefix (growing full : Array Nat) : Prop :=
  growing.size ≤ full.size ∧ ∀ i, i < growing.size → growing[i]! = full[i]!

private theorem initial_prefix (block : Vector Nat 16) : Prefix block.toArray (initial block).toArray := by
  constructor
  · simp [initial]
  intro i hi
  have h16 : i < 16 := by simpa using hi
  have h64 : i < (initial block).toArray.size := by simp; omega
  rw [getElem!_pos block.toArray i hi, getElem!_pos (initial block).toArray i h64]
  simp [initial, Vector.getElem_mapFinRange, h16]
  rfl

private theorem step_prefix {growing full : Array Nat} (same : Prefix growing full)
    (lower : 16 ≤ growing.size) (room : growing.size < full.size) :
    Prefix (step growing.size growing) (fixedStep growing.size full) := by
  have sameNext : next growing.size growing = next growing.size full := by
    unfold next
    rw [same.2 _ (by omega), same.2 _ (by omega),
      same.2 _ (by omega), same.2 _ (by omega)]
  constructor
  · simp only [step_size, fixedStep, Array.size_setIfInBounds]
    omega
  intro i hi
  have limit : i < growing.size + 1 := by simpa [step] using hi
  have hfull : i < full.size := by omega
  rw [getElem!_pos (step growing.size growing) i hi,
    getElem!_pos (fixedStep growing.size full) i (by simpa [fixedStep] using hfull)]
  by_cases old : i < growing.size
  · have notLast : growing.size ≠ i := by omega
    simp only [step, fixedStep, Array.getElem_push_lt old,
      Array.getElem_setIfInBounds_ne hfull notLast]
    have result := same.2 i old
    rw [getElem!_pos growing i old, getElem!_pos full i hfull] at result
    exact result
  · have last : i = growing.size := by omega
    subst i
    simp only [step, fixedStep, Array.getElem_push_eq,
      Array.getElem_setIfInBounds_self, sameNext]

private theorem fixed_fold_size (items : List Nat) (words : Array Nat) :
    (items.foldl (fun words i => fixedStep i words) words).size = words.size := by
  induction items generalizing words with
  | nil => rfl
  | cons item items ih => simpa [fixedStep] using ih (fixedStep item words)

private theorem fold_prefix (block : Vector Nat 16) (count : Nat) (bound : count ≤ 48) :
    Prefix ((List.range' 16 count).foldl (fun words i => step i words) block.toArray)
      ((List.range' 16 count).foldl (fun words i => fixedStep i words) (initial block).toArray) := by
  induction count with
  | zero => simpa using initial_prefix block
  | succ count ih =>
    have previous := ih (by omega)
    have size : ((List.range' 16 count).foldl (fun words i => step i words) block.toArray).size =
        16 + count := by simp [fold_size]
    have result := step_prefix previous (by omega) (by
      rw [fixed_fold_size]
      simp only [Vector.size_toArray]
      omega)
    simpa only [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      size] using result

private theorem prefix_eq {growing full : Array Nat} (same : Prefix growing full)
    (size : growing.size = full.size) : growing = full := by
  apply Array.ext size
  intro i hi hj
  have eq := same.2 i hi
  rw [getElem!_pos growing i hi, getElem!_pos full i hj] at eq
  exact eq

attribute [local irreducible] expand fixedStep initial Specs.SHA256.messageSchedule

/-- The native pushed-array recurrence is exactly Clean's SHA message schedule. -/
theorem expand_eq_messageSchedule (block : Vector Nat 16) :
    expand block.toArray = (Specs.SHA256.messageSchedule block).toArray := by
  apply Eq.trans ?_ (reference_array block).symm
  unfold expand
  apply prefix_eq (fold_prefix block 48 (by omega))
  simp only [fold_size, fixed_fold_size, List.length_range', Vector.size_toArray]

end Midnight.SHA256.Semantics.ScheduleSpec
