module

public import Clean.Utils.ResourceHistory.Ordered
public import Mathlib.Logic.Function.Basic

/-! # Replay of keyed resources

The ledger stores complete predecessor/successor records. The schedule orders only
successor versions, not predecessor links. Balance derives those links and hence
every read's current value. An absent frontier entry denotes nonparticipation;
allocation is represented by an explicit absent value inside a participating record.
-/

@[expose] public section

namespace Utils.ResourceHistory

universe u v w x y

/-- A heterogeneous resource record. Versions are proof metadata, not architectural values. -/
structure ResourceRecord (Key : Type u) (Value : Key → Type v) (Version : Type w) where
  key : Key
  version : Version
  value : Value key

/-- An access occurrence. Intent distinguishes writes (including same-value writes)
from reads; owner and position connect a multirow implementation to its semantic event. -/
structure ResourceAccess (Record : Type u) (Owner : Type v) (Intent : Type w) where
  before : Record
  after : Record
  owner : Owner
  position : ℕ
  intent : Intent
  deriving DecidableEq

abbrev ResourceFrontier (Key : Type u) (Record : Type v) := Key → Option Record

variable {Key Record Access : Type*} [DecidableEq Key]

/-- Optional boundary records contribute zero or one occurrence. -/
def optionalRecord (record : Option Record) : Multiset Record := ↑record.toList

/-- The accesses to one key, retaining their supplied semantic order. -/
def accessesAt (key : Record → Key) (edge : Access → Record × Record)
    (rows : List Access) (k : Key) : List Access :=
  rows.filter fun row => key (edge row).1 = k

/-- Exact per-key conservation; there is no predecessor-link assumption. -/
def FrontierBalance (key : Record → Key) (edge : Access → Record × Record)
    (rows : List Access) (initial final : ResourceFrontier Key Record) : Prop :=
  ∀ k, optionalRecord (initial k) + (↑(accessesAt key edge rows k) : Multiset Access).map
      (fun row => (edge row).2) =
    optionalRecord (final k) + (↑(accessesAt key edge rows k) : Multiset Access).map
      (fun row => (edge row).1)

/-- Sequential semantics: consume the current record and replace it by the successor. -/
def ResourceReplay (key : Record → Key) (edge : Access → Record × Record) :
    ResourceFrontier Key Record → List Access → ResourceFrontier Key Record → Prop
  | initial, [], final => initial = final
  | initial, row :: rest, final =>
    initial (key (edge row).1) = some (edge row).1 ∧
      ResourceReplay key edge
        (Function.update initial (key (edge row).1) (some (edge row).2)) rest final

variable [DecidableEq Access] [DecidableEq Record]

/-- The first scheduled access has an authentic current predecessor. -/
theorem current_of_balance (key : Record → Key) (edge : Access → Record × Record)
    (before : Record → Record → Prop) (irrefl : ∀ a, ¬ before a a) (trans : ∀ ⦃a b c⦄, before a b → before b c → before a c)
    (row : Access) (rest : List Access) (initial final : ResourceFrontier Key Record)
    (balanced : FrontierBalance key edge (row :: rest) initial final)
    (increases : ∀ e ∈ row :: rest, before (edge e).1 (edge e).2)
    (ordered : ∀ k, (accessesAt key edge (row :: rest) k).Pairwise
      (fun a b => before (edge a).2 (edge b).2)) :
    initial (key (edge row).1) = some (edge row).1 := by
  let k := key (edge row).1
  let rows := accessesAt key edge (row :: rest) k
  have head : rows = row :: accessesAt key edge rest k := by simp [rows, accessesAt, k]
  have strict : ∀ e ∈ (↑rows : Multiset Access), before (edge e).1 (edge e).2 := by
    intro e member
    exact increases e (List.mem_filter.mp (Multiset.mem_coe.mp member)).1
  have balance := balanced k
  change optionalRecord (initial k) + (↑rows : Multiset Access).map (fun e => (edge e).2) =
    optionalRecord (final k) + (↑rows : Multiset Access).map (fun e => (edge e).1) at balance
  cases hi : initial k with
  | none =>
    cases hf : final k with
    | none =>
      simp only [hi, hf, optionalRecord, Option.toList_none, Multiset.coe_nil, zero_add] at balance
      have empty := eq_zero_of_acyclic_balanced (↑rows) edge
        (acyclic_of_strict (↑rows) edge before irrefl trans strict) balance
      rw [head] at empty
      simp at empty
    | some finish =>
      have counts := congrArg Multiset.card balance
      simp [hi, hf, optionalRecord] at counts
  | some start =>
    cases hf : final k with
    | none =>
      have counts := congrArg Multiset.card balance
      simp [hi, hf, optionalRecord] at counts
    | some finish =>
      have endpoints : Ranked.EndpointBalanced (↑rows) edge start finish := by
        simp only [hi, hf, optionalRecord, Option.toList_some, Multiset.coe_singleton,
          Multiset.singleton_add] at balance
        exact balance
      have walk := walk_of_ordered_balance rows edge before irrefl trans start finish endpoints
        strict (ordered k)
      rw [head] at walk
      change (edge row).1 = start ∧ _ at walk
      exact congrArg some walk.1.symm

omit [DecidableEq Access] [DecidableEq Record] in
/-- Removing an established current access preserves complete resource balance. -/
theorem FrontierBalance.tail (key : Record → Key) (edge : Access → Record × Record)
    {row : Access} {rest : List Access} {initial final : ResourceFrontier Key Record}
    (balanced : FrontierBalance key edge (row :: rest) initial final)
    (current : initial (key (edge row).1) = some (edge row).1) :
    FrontierBalance key edge rest
      (Function.update initial (key (edge row).1) (some (edge row).2)) final := by
  intro k
  have h := balanced k
  by_cases same : key (edge row).1 = k
  · subst k
    simp only [accessesAt, List.filter_cons, decide_true, ↓reduceIte, ← Multiset.cons_coe,
      Multiset.map_cons, current, optionalRecord, Option.toList_some,
      Multiset.coe_nil] at h
    rw [Multiset.cons_add, zero_add, Multiset.add_cons] at h
    have canceled := (Multiset.cons_inj_right (edge row).1).mp h
    simp only [Function.update_self, optionalRecord, Option.toList_some,
      Multiset.coe_singleton, Multiset.singleton_add]
    exact canceled
  · simp only [accessesAt, List.filter_cons, same, decide_false, Bool.false_eq_true,
      ↓reduceIte] at h
    rw [Function.update_of_ne (Ne.symm same)]
    exact h

/-- The core memory theorem: ordering and balance establish sequential replay.
Resource identity preservation is a separate local constraint, checked by the caller;
the theorem works on arbitrary record types and keeps all occurrence labels. -/
theorem replay_of_balance (key : Record → Key) (edge : Access → Record × Record)
    (before : Record → Record → Prop) (irrefl : ∀ a, ¬ before a a) (trans : ∀ ⦃a b c⦄, before a b → before b c → before a c)
    (rows : List Access) (initial final : ResourceFrontier Key Record)
    (balanced : FrontierBalance key edge rows initial final)
    (increases : ∀ e ∈ rows, before (edge e).1 (edge e).2)
    (ordered : ∀ k, (accessesAt key edge rows k).Pairwise
      (fun a b => before (edge a).2 (edge b).2)) :
    ResourceReplay key edge initial rows final := by
  induction rows generalizing initial with
  | nil =>
    funext k
    have h := balanced k
    cases hi : initial k <;> cases hf : final k <;>
      simp [accessesAt, optionalRecord, hi, hf] at h ⊢
    exact h
  | cons row rest ih =>
    have current := current_of_balance key edge before irrefl trans row rest initial final
      balanced increases ordered
    refine ⟨current, ih _ (balanced.tail key edge current)
      (fun e member => increases e (List.mem_cons_of_mem _ member)) ?_⟩
    intro k
    have order := ordered k
    simp only [accessesAt, List.filter_cons] at order ⊢
    split_ifs at order
    · exact order.tail
    · exact order

omit [DecidableEq Access] [DecidableEq Record] in
/-- Untouched keys retain their full record, including absence. -/
theorem ResourceReplay.frame (key : Record → Key) (edge : Access → Record × Record)
    {initial final : ResourceFrontier Key Record} {rows : List Access}
    (replay : ResourceReplay key edge initial rows final) (k : Key)
    (untouched : ∀ row ∈ rows, key (edge row).1 ≠ k) : initial k = final k := by
  induction rows generalizing initial with
  | nil => exact congrFun replay k
  | cons row rest ih =>
    have tail := ih replay.2 (fun e member => untouched e (List.mem_cons_of_mem _ member))
    rw [Function.update_of_ne (Ne.symm (untouched row (List.mem_cons_self ..)))] at tail
    exact tail

omit [DecidableEq Access] [DecidableEq Record] in
/-- Resource replay splits and joins at the same complete frontier. -/
theorem ResourceReplay.append_iff (key : Record → Key) (edge : Access → Record × Record)
    (left right : List Access) (initial final : ResourceFrontier Key Record) :
    ResourceReplay key edge initial (left ++ right) final ↔
      ∃ middle, ResourceReplay key edge initial left middle ∧
        ResourceReplay key edge middle right final := by
  induction left generalizing initial with
  | nil => simp [ResourceReplay]
  | cons row rest ih =>
    simp only [List.cons_append, ResourceReplay, ih]
    constructor
    · rintro ⟨current, middle, firstPart, suffix⟩
      exact ⟨middle, ⟨current, firstPart⟩, suffix⟩
    · rintro ⟨middle, ⟨current, firstPart⟩, suffix⟩
      exact ⟨current, middle, firstPart, suffix⟩

omit [DecidableEq Access] [DecidableEq Record] in
/-- Replay determines the complete frontier by functional updates. The fold alone does
not check reads; `ResourceReplay` is the proof that all those checks succeed. -/
theorem ResourceReplay.final_eq_fold (key : Record → Key) (edge : Access → Record × Record)
    {initial final : ResourceFrontier Key Record} {rows : List Access}
    (replay : ResourceReplay key edge initial rows final) :
    final = rows.foldl (fun current row =>
      Function.update current (key (edge row).1) (some (edge row).2)) initial := by
  induction rows generalizing initial with
  | nil => exact replay.symm
  | cons row rest ih => exact ih replay.2

omit [DecidableEq Access] [DecidableEq Record] in
/-- Same-key local transitions preserve authentic resource identities. -/
theorem ResourceReplay.keys (key : Record → Key) (edge : Access → Record × Record)
    {initial final : ResourceFrontier Key Record} {rows : List Access}
    (replay : ResourceReplay key edge initial rows final)
    (initialKeys : ∀ k r, initial k = some r → key r = k)
    (preserves : ∀ row ∈ rows, key (edge row).2 = key (edge row).1) :
    ∀ k r, final k = some r → key r = k := by
  induction rows generalizing initial with
  | nil => exact replay ▸ initialKeys
  | cons row rest ih =>
    apply ih replay.2 _ (fun r member => preserves r (List.mem_cons_of_mem _ member))
    intro k record present
    by_cases same : k = key (edge row).1
    · subst k
      rw [Function.update_self, Option.some.injEq] at present
      rw [← present]
      exact preserves row (List.mem_cons_self ..)
    · rw [Function.update_of_ne same] at present
      exact initialKeys k record present

end Utils.ResourceHistory
