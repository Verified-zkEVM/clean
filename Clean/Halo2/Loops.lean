module

public import Clean.Halo2.Lemmas
public import Clean.Halo2.Operations.Copy
public import Clean.Halo2.Operations.FixedWrites
public import Clean.Halo2.Operations.AdviceWrites
public import Clean.Halo2.SynthesisSummary.Operations

@[expose] public section

/-!
# Native loop support for `RegionCircuit`

Region-scoped loop combinators (maintainer-approved design). Unlike main Clean's
`Clean/Circuit/Loops.lean` — which needs the `ConstantLength` machinery to know each round's
row-stride from the threaded row counter — the halo2 `RegionCircuit` model addresses cells by
**explicit absolute rows** (`assignAdvice col row …`), so a round's base row is just an argument.
That collapses the whole `ForM`/`MapM`/`FoldlM` + `ConstantLength` tower here to a thin fold over
the monad's append-bind (`RegionCircuit.operations_bind` is `++` by `rfl`).

## The combinators

- `RegionCircuit.forRange offset stride m body` — `m` independent rounds; round `i` runs
  `body i (offset + i*stride)` (its base row). Returns `Vector α m` of per-round outputs
  (the map-loop). `forRange'` is the `Unit` (`forEach`) specialization.
- `RegionCircuit.foldRange offset stride m init body` — serial accumulator-threading variant.
  Body `(i : ℕ) → ℕ → β → RegionCircuit F β`: round `i` reads the running accumulator and its ops
  MAY depend on it (MulComplete: the round's `Add.add.call`s take the previous accumulator's cells
  as inputs). **ConstantOutput analogue (maintainer rule): the accumulator VAR at round `k` is the
  closed form `foldAcc … k` (the running fold of the per-round outputs)** — true of every serial
  loop in the corpus (accumulator = cell records at round-determined rows), which keeps the split's
  per-round predicate a closed form. A genuinely output-*value*-dependent loop gets a separately
  named `foldRangeDynOutput`; this natural name is the good path.
- `RegionCircuit.forRangeVar' rows m body` / `foldRangeVar rows m init body` — the
  **variable-stride** general forms (round bases supplied as `rows : ℕ → ℕ`, e.g. partial sums of a
  per-piece width for Chain's heterogeneous widths). Constant stride is the special case
  `rows i := offset + i*stride`.

## The proof-side split lemmas (the point)

For every combinator, `@[circuit_norm ↓]` lemmas turn `RegionOperations.Constraints` /
`ExtendsWitnesses` of the loop directly into `∀ i : Fin m, <round i's predicate at its base row>`
— keyed on `(loop …).operations self`, so they fire BEFORE `operations` is unfolded (the
`..._operations` flatten lemmas are deliberately NOT in `circuit_norm`, to keep `operations` folded
until the split has matched; a generic `constraints_ofFn_flatten` covers any residual flatten
spelling). After the split, each round's `(body i base).operations self` reduces like straight-line
code under the existing `circuit_norm` blocks — deleting the hand-written `loop_operations_succ` /
`rangeCheck_loop_*` / `loop_gate_facts` recursion the gadgets used to carry.
-/

namespace Halo2
namespace RegionCircuit

variable {F : Type} [FiniteField F] {α β : Type}

/-- Mapping a vector's backing list contains the image of every vector element. -/
theorem Vector.map_getElem_mem_toList {n : ℕ} (values : Vector α n) (f : α → β)
    (i : Fin n) : f values[i] ∈ values.toList.map f := by
  apply List.mem_map.mpr
  refine ⟨values[i], ?_, rfl⟩
  have hi : i.val < values.toList.length := by
    rw [Vector.length_toList]
    exact i.isLt
  have hmem := List.getElem_mem hi
  rwa [Vector.getElem_toList hi] at hmem

/-- The bounds-checked spelling used by source loops has the same membership fact. -/
theorem Vector.map_getElem!_mem_toList {n : ℕ} [Inhabited α]
    (values : Vector α n) (f : α → β) (i : Fin n) :
    f values[i.val]! ∈ values.toList.map f := by
  rw [getElem!_pos values i.val i.isLt]
  exact Vector.map_getElem_mem_toList values f i

/-- The same in the form that the keygen sets give a membership in a map, after
`List.mem_map`: some element of the vector maps to the element at `i`'s image. -/
theorem Vector.exists_mem_toList_map_getElem! {n : ℕ} [Inhabited α]
    (values : Vector α n) (f : α → β) (i : Fin n) :
    (∃ a ∈ values.toList, f a = f values[i.val]!) ↔ True :=
  iff_true_intro (List.mem_map.mp (Vector.map_getElem!_mem_toList values f i))

/-- The same at a natural-number index with its bound as a premiss. -/
theorem Vector.exists_mem_toList_map_getElem!_of_lt {n : ℕ} [Inhabited α]
    (values : Vector α n) (f : α → β) (i : ℕ) (hi : i < n) :
    (∃ a ∈ values.toList, f a = f values[i]!) ↔ True :=
  Vector.exists_mem_toList_map_getElem! values f ⟨i, hi⟩

/-! ## Generic per-round splits on the `List.ofFn`-flatten form

The fundamental split lemmas, keyed on `(List.ofFn f).flatten` — the shape a loop's `operations`
reduces to once `circuit_norm` fires `..._operations`. They make the `Constraints`/`ExtendsWitnesses`
split robust to reduction order: whether the goal still spells `(loop …).operations self` or has
already been flattened, `circuit_norm` reaches the per-round `∀ i` form. (The combinator-specific
split lemmas below are corollaries for the unflattened spelling.) -/

@[circuit_norm ↓]
theorem constraints_ofFn_flatten {m : ℕ} (ops : Fin m → RegionOperations F)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env (List.ofFn ops).flatten
      ↔ ∀ i : Fin m, RegionOperations.Constraints place self env (ops i) := by
  induction m with
  | zero => simp [RegionOperations.Constraints]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append,
      RegionOperations.constraints_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, Fin.forall_fin_succ']

@[circuit_norm ↓]
theorem extendsWitnesses_ofFn_flatten {m : ℕ} (ops : Fin m → RegionOperations F)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env (List.ofFn ops).flatten
      ↔ ∀ i : Fin m, RegionOperations.ExtendsWitnesses place self env (ops i) := by
  induction m with
  | zero => simp [RegionOperations.ExtendsWitnesses]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append,
      RegionOperations.extendsWitnesses_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, Fin.forall_fin_succ']

/-! ## The variable-stride core

`forRangeVarAux bases body k` runs rounds `0 .. k-1` in order (structural recursion on `k`, so
`operations` of the `k+1` case is `rfl`-equal to the `k` case appended with round `k`), each round
`body ⟨i, _⟩ (bases ⟨i, _⟩)`. The public combinators fix `k := m` and derive the stride bases.
Bodies are `Unit` at this core (the map/fold value-threading is layered on top so the operations
theory stays value-free). -/

/-- Serial `Unit` loop over rounds `0 .. k-1`, round `i` at base row `rows i`. Structurally
recursive so `(loopAux rows body (k+1)).operations self` is `rfl`-equal to
`(loopAux rows body k).operations self ++ (body k).operations self`. -/
def loopAux (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit) :
    ℕ → RegionCircuit F Unit
  | 0 => pure ()
  | k + 1 => do
    loopAux rows body k
    body k (rows k)

/-- Per-round operations decomposition (holds by `rfl` via `operations_bind`). -/
theorem loopAux_operations_succ (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (k : ℕ) (self : RegionIndex) :
    (loopAux rows body (k + 1)).operations self
      = (loopAux rows body k).operations self ++ (body k (rows k)).operations self := rfl

/-- `operations` of the whole loop as a flatten-of-`ofFn` of the per-round ops — the shape the
split lemmas below (and downstream `circuit_norm`) consume. -/
theorem loopAux_operations (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (k : ℕ) (self : RegionIndex) :
    (loopAux rows body k).operations self
      = (List.ofFn fun i : Fin k => (body i.val (rows i.val)).operations self).flatten := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [loopAux_operations_succ, ih, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.val_last, Fin.val_castSucc, List.flatten_cons, List.flatten_nil,
      List.append_nil]

/--
An operation-local law holds over a loop exactly when it holds over every
round.  Unlike the constraint-specific splits below, this generic `List.Forall`
interface is also useful for static synthesis laws.
-/
theorem loopAux_forall (property : RegionOperation F → Prop)
    (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (k : ℕ) :
    ((loopAux rows body k).operations self).Forall property ↔
      ∀ i : Fin k,
        ((body i.val (rows i.val)).operations self).Forall property := by
  induction k with
  | zero =>
      change List.Forall property [] ↔
        ∀ i : Fin 0,
          ((body i.val (rows i.val)).operations self).Forall property
      simp
  | succ n ih =>
      rw [loopAux_operations_succ, List.forall_append, ih,
        Fin.forall_fin_succ']
      simp only [Fin.val_last, Fin.val_castSucc]

/-- **The `Constraints` split.** The loop's constraints hold iff each round's constraints hold at
its base row — `∀ i : Fin k, <round i's predicate>`. This is what lets each round reduce like
straight-line code after the split (the port of main Clean's `forEach.forAll`). -/
@[circuit_norm ↓]
theorem loopAux_constraints (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) (k : ℕ) :
    RegionOperations.Constraints place self env ((loopAux rows body k).operations self)
      ↔ ∀ i : Fin k,
          RegionOperations.Constraints place self env ((body i.val (rows i.val)).operations self) := by
  induction k with
  | zero => simp only [loopAux, operations_pure, RegionOperations.constraints_nil, true_iff]
            exact fun i => i.elim0
  | succ n ih =>
    rw [loopAux_operations_succ, RegionOperations.constraints_append, ih, Fin.forall_fin_succ']
    simp only [Fin.val_last, Fin.val_castSucc]

/-- **The `ExtendsWitnesses` split** (completeness counterpart). -/
@[circuit_norm ↓]
theorem loopAux_extendsWitnesses (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) (k : ℕ) :
    RegionOperations.ExtendsWitnesses place self env ((loopAux rows body k).operations self)
      ↔ ∀ i : Fin k,
          RegionOperations.ExtendsWitnesses place self env
            ((body i.val (rows i.val)).operations self) := by
  induction k with
  | zero => simp only [loopAux, operations_pure, RegionOperations.extendsWitnesses_nil, true_iff]
            exact fun i => i.elim0
  | succ n ih =>
    rw [loopAux_operations_succ, RegionOperations.extendsWitnesses_append, ih,
      Fin.forall_fin_succ']
    simp only [Fin.val_last, Fin.val_castSucc]

/-! ## The public forEach combinator (`Unit`, constant stride) -/

/-- `forRange' offset stride m body`: `m` independent `Unit` rounds, round `i` at base row
`offset + i*stride`. The forEach-shaped loop the range-check / double-and-add gadgets use. -/
def forRange' (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit) :
    RegionCircuit F Unit :=
  loopAux (fun i => offset + i * stride) body m

-- (intentionally NOT @[circuit_norm]: keeps `operations` folded so the ↓ split lemma matches;
--  fire this explicitly if you need the `List.ofFn`-flatten spelling)
theorem forRange'_operations (offset stride m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit) (self : RegionIndex) :
    (forRange' offset stride m body).operations self
      = (List.ofFn fun i : Fin m =>
          (body i.val (offset + i.val * stride)).operations self).flatten :=
  loopAux_operations _ _ _ _

/-- Exact compositional summary of a region loop, expressed only through the
already-reduced summary of each round. -/
@[synthesis_summary_norm]
theorem forRange'_regionSynthesisSummary
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((forRange' offset stride m body).operations self) =
      (List.ofFn fun i : Fin m =>
        FloorPlanner.regionSynthesisSummary
          ((body i.val (offset + i.val * stride)).operations self)).foldr
            FloorPlanner.RegionSynthesisSummary.combine {} := by
  rw [forRange'_operations, FloorPlanner.regionSynthesisSummary_flatten,
    List.map_ofFn]
  rfl

/-- Operation-local laws over `forRange'`, split by symbolic round. -/
theorem forRange'_forall (property : RegionOperation F → Prop)
    (offset stride m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    ((forRange' offset stride m body).operations self).Forall property ↔
      ∀ i : Fin m,
        ((body i.val (offset + i.val * stride)).operations self).Forall property :=
  loopAux_forall property _ _ _ _

/-- Fixed assignments from consecutive loop iterations agree when each iteration is
internally lawful and writes only at its own base row. -/
theorem forRange'_fixedAssignmentsAgree
    (offset count : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hagree : ∀ i : Fin count,
      ((body i.val (offset + i.val * 1)).operations self).FixedAssignmentsAgree)
    (hrow : ∀ (i : Fin count) column row value,
      .assignFixed column row value ∈
        (body i.val (offset + i.val * 1)).operations self →
      row = offset + i.val * 1) :
    ((forRange' offset 1 count body).operations self).FixedAssignmentsAgree := by
  unfold RegionOperations.FixedAssignmentsAgree
  intro column row left right hleft hright
  rw [forRange'_operations, List.mem_flatten] at hleft hright
  obtain ⟨leftOperations, hleftOperations, hleft⟩ := hleft
  obtain ⟨rightOperations, hrightOperations, hright⟩ := hright
  rw [List.mem_ofFn] at hleftOperations hrightOperations
  obtain ⟨i, rfl⟩ := hleftOperations
  obtain ⟨j, rfl⟩ := hrightOperations
  have hleftRow := hrow i column row left hleft
  have hrightRow := hrow j column row right hright
  have hij : i = j := Fin.ext (by omega)
  subst j
  exact hagree i column row left right hleft hright

/-- Fixed writes from a consecutive loop lie in its half-open row interval. -/
theorem forRange'_assignFixed_row_bounds
    (offset count : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hrow : ∀ (i : Fin count) column row value,
      .assignFixed column row value ∈
        (body i.val (offset + i.val * 1)).operations self →
      row = offset + i.val * 1)
    (column : Column .fixed) (row : ℕ) (value : F)
    (hassignment : .assignFixed column row value ∈
      (forRange' offset 1 count body).operations self) :
    offset ≤ row ∧ row < offset + count := by
  rw [forRange'_operations, List.mem_flatten] at hassignment
  obtain ⟨operations, hoperations, hassignment⟩ := hassignment
  rw [List.mem_ofFn] at hoperations
  obtain ⟨i, rfl⟩ := hoperations
  rw [hrow i column row value hassignment]
  omega

private theorem flatMap_flatten {α β : Type} (f : α → List β) (xss : List (List α)) :
    xss.flatten.flatMap f = (xss.map (List.flatMap f)).flatten := by
  induction xss with
  | nil => rfl
  | cons xs rest ih => simp [List.flatMap_append, ih]

/-- Advice writes from a constant-stride loop are pairwise distinct when each round is
internally distinct and distinct rounds have disjoint advice writes. -/
theorem forRange'_adviceWritesDistinct_of_disjoint
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hdistinct : ∀ i : Fin m,
      ((body i.val (offset + i.val * stride)).operations self).AdviceWritesDistinct)
    (hdisj : ∀ i j : Fin m, i < j →
      (((body i.val (offset + i.val * stride)).operations self).adviceWrites).Disjoint
        (((body j.val (offset + j.val * stride)).operations self).adviceWrites)) :
    ((forRange' offset stride m body).operations self).AdviceWritesDistinct := by
  unfold RegionOperations.AdviceWritesDistinct RegionOperations.adviceWrites
  rw [forRange'_operations, flatMap_flatten, List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨ops, hops, rfl⟩ := hl
    rw [List.mem_ofFn] at hops
    obtain ⟨i, rfl⟩ := hops
    exact hdistinct i
  · rw [List.pairwise_map, List.pairwise_ofFn]
    exact hdisj

/-- Membership in a constant-stride loop's advice writes reduces to membership in some round. -/
theorem mem_forRange'_adviceWrites_iff
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (column : Column .advice) (row : ℕ) :
    (column, row) ∈ ((forRange' offset stride m body).operations self).adviceWrites ↔
      ∃ i : Fin m,
        (column, row) ∈ ((body i.val (offset + i.val * stride)).operations self).adviceWrites := by
  unfold RegionOperations.adviceWrites
  rw [forRange'_operations, flatMap_flatten, List.mem_flatten]
  constructor
  · rintro ⟨writes, hwrites, hmem⟩
    rw [List.mem_map] at hwrites
    obtain ⟨ops, hops, rfl⟩ := hwrites
    rw [List.mem_ofFn] at hops
    obtain ⟨i, rfl⟩ := hops
    exact ⟨i, hmem⟩
  · rintro ⟨i, hi⟩
    refine ⟨((body i.val (offset + i.val * stride)).operations self).adviceWrites, ?_, hi⟩
    rw [List.mem_map]
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩

/-- Advice writes from a constant-stride loop are pairwise distinct when each round is
internally distinct and writes only in its half-open row window `[offset + i * stride,
offset + (i + 1) * stride)`. -/
theorem forRange'_adviceWritesDistinct
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hdistinct : ∀ i : Fin m,
      ((body i.val (offset + i.val * stride)).operations self).AdviceWritesDistinct)
    (hrow : ∀ (i : Fin m) column row,
      (column, row) ∈ ((body i.val (offset + i.val * stride)).operations self).adviceWrites →
      offset + i.val * stride ≤ row ∧ row < offset + (i.val + 1) * stride) :
    ((forRange' offset stride m body).operations self).AdviceWritesDistinct := by
  apply forRange'_adviceWritesDistinct_of_disjoint offset stride m body self hdistinct
  intro i j hij
  rw [List.disjoint_left]
  rintro ⟨col, row⟩ hi hj
  have hbi := hrow i col row hi
  have hbj := hrow j col row hj
  have hstep : (i.val + 1) * stride ≤ j.val * stride :=
    Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hij)
  omega

/-- Membership in a constant-stride loop's non-self-copy advice writes reduces to membership in
some round. -/
theorem mem_forRange'_nonSelfCopyAdviceWrites_iff
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (column : Column .advice) (row : ℕ) :
    (column, row) ∈
        ((forRange' offset stride m body).operations self).nonSelfCopyAdviceWrites self ↔
      ∃ i : Fin m,
        (column, row) ∈
          ((body i.val (offset + i.val * stride)).operations self).nonSelfCopyAdviceWrites self := by
  unfold RegionOperations.nonSelfCopyAdviceWrites
  rw [forRange'_operations, flatMap_flatten, List.mem_flatten]
  constructor
  · rintro ⟨writes, hwrites, hmem⟩
    rw [List.mem_map] at hwrites
    obtain ⟨ops, hops, rfl⟩ := hwrites
    rw [List.mem_ofFn] at hops
    obtain ⟨i, rfl⟩ := hops
    exact ⟨i, hmem⟩
  · rintro ⟨i, hi⟩
    refine ⟨((body i.val (offset + i.val * stride)).operations self).nonSelfCopyAdviceWrites self,
      ?_, hi⟩
    rw [List.mem_map]
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩

/-- Self-copy-consistent advice writes compose over a constant-stride loop whenever each round is
internally consistent and earlier rounds' advice writes are disjoint from later rounds'
non-self-copy advice writes. -/
theorem forRange'_adviceWritesConsistent_of_disjoint
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hcons : ∀ i : Fin m,
      ((body i.val (offset + i.val * stride)).operations self).AdviceWritesConsistent self)
    (hdisj : ∀ i j : Fin m, i < j →
      (((body i.val (offset + i.val * stride)).operations self).adviceWrites).Disjoint
        (((body j.val (offset + j.val * stride)).operations self).nonSelfCopyAdviceWrites self)) :
    ((forRange' offset stride m body).operations self).AdviceWritesConsistent self := by
  have haux : ∀ k (hk : k ≤ m),
      ((loopAux (fun i => offset + i * stride) body k).operations self).AdviceWritesConsistent
        self := by
    intro k hk
    induction k with
    | zero =>
      simp [loopAux, RegionCircuit.operations_pure, RegionOperations.adviceWritesConsistent_nil]
    | succ k ih =>
      rw [loopAux_operations_succ]
      apply RegionOperations.adviceWritesConsistent_append_of_disjoint self
        (ih (Nat.le_of_succ_le hk)) (hcons ⟨k, hk⟩)
      rw [List.disjoint_left]
      rintro ⟨col, row⟩ hprev hcur
      have hprevMem :
          (col, row) ∈ ((forRange' offset stride k body).operations self).adviceWrites :=
        hprev
      obtain ⟨i, hi⟩ :=
        (mem_forRange'_adviceWrites_iff offset stride k body self col row).mp hprevMem
      exact List.disjoint_left.mp
        (hdisj ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_succ_le hk)⟩ ⟨k, hk⟩ i.isLt) hi hcur
  exact haux m le_rfl

/-- Advice writes from a constant-stride loop lie in `[offset, offset + m * stride)`. -/
theorem forRange'_adviceWrites_row_bounds
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hrow : ∀ (i : Fin m) column row,
      (column, row) ∈ ((body i.val (offset + i.val * stride)).operations self).adviceWrites →
      offset + i.val * stride ≤ row ∧ row < offset + (i.val + 1) * stride)
    (column : Column .advice) (row : ℕ)
    (hmem : (column, row) ∈ ((forRange' offset stride m body).operations self).adviceWrites) :
    offset ≤ row ∧ row < offset + m * stride := by
  unfold RegionOperations.adviceWrites at hmem
  rw [forRange'_operations, flatMap_flatten, List.mem_flatten] at hmem
  obtain ⟨writes, hwrites, hmem⟩ := hmem
  rw [List.mem_map] at hwrites
  obtain ⟨ops, hops, rfl⟩ := hwrites
  rw [List.mem_ofFn] at hops
  obtain ⟨i, rfl⟩ := hops
  have hb := hrow i column row hmem
  have hle : (i.val + 1) * stride ≤ m * stride :=
    Nat.mul_le_mul_right stride (Nat.succ_le_of_lt i.isLt)
  omega

/-- A loop whose rounds consume nothing is lawful for every incoming cell state. -/
@[keygen_helper]
theorem forRange'_assignedFrom_of_forall_consumes_nil (consumption : Consumption F)
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell)
    (hbody : ∀ i : Fin m,
      ((body i.val (offset + i.val * stride)).operations self).Forall
        fun operation => [] ∈ consumption operation) :
    ((forRange' offset stride m body).operations self).AssignedFrom consumption
      self available := by
  apply RegionOperations.assignedFrom_of_forall_consumes_nil
  exact (forRange'_forall _ _ _ _ _ _).2 hbody

/-- A loop is lawful when each round is lawful from the caller's cells together with
everything the earlier rounds assigned. -/
theorem loopAux_assignedFrom (consumption : Consumption F)
    (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell) (k : ℕ)
    (hbody : ∀ i : Fin k,
      ((body i.val (rows i.val)).operations self).AssignedFrom consumption self
        (((loopAux rows body i.val).operations self).assignedCellsAfter self available)) :
    ((loopAux rows body k).operations self).AssignedFrom consumption self available := by
  induction k with
  | zero => exact .nil available
  | succ n inductionHypothesis =>
      rw [loopAux_operations_succ, RegionOperations.assignedFrom_append_iff]
      exact ⟨inductionHypothesis (fun i => hbody i.castSucc), hbody (Fin.last n)⟩

/-- A loop is lawful when each symbolic round is lawful from the caller's original input
cells. -/
@[keygen_helper]
theorem loopAux_assignedFrom_of_forall (consumption : Consumption F)
    (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell) (k : ℕ)
    (hbody : ∀ i : Fin k,
      ((body i.val (rows i.val)).operations self).AssignedFrom consumption
        self available) :
    ((loopAux rows body k).operations self).AssignedFrom consumption self available :=
  loopAux_assignedFrom consumption rows body self available k fun i =>
    (hbody i).mono fun cell hcell =>
      RegionOperations.mem_assignedCellsAfter_of_mem _ _ _ cell hcell

/-- Constant-stride specialization of `loopAux_assignedFrom`. -/
theorem forRange'_assignedFrom (consumption : Consumption F)
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell)
    (hbody : ∀ i : Fin m,
      ((body i.val (offset + i.val * stride)).operations self).AssignedFrom consumption self
        (RegionOperations.assignedCellsAfter self available
          ((loopAux (fun i => offset + i * stride) body i.val).operations self))) :
    ((forRange' offset stride m body).operations self).AssignedFrom consumption
      self available :=
  loopAux_assignedFrom consumption _ body self available m hbody

/-- A loop whose rounds read rows that earlier rounds wrote is lawful when its first round
is lawful from the caller's cells, and every later round is lawful from the caller's cells
together with everything the rounds before it assigned. -/
theorem loopAux_assignedFrom_of_earlier_rounds (consumption : Consumption F)
    (rows : ℕ → ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell) (m : ℕ)
    (hfirst : 0 < m →
      ((body 0 (rows 0)).operations self).AssignedFrom consumption self available)
    (hnext : ∀ i, i + 1 < m →
      ((body (i + 1) (rows (i + 1))).operations self).AssignedFrom consumption self
        (((loopAux rows body (i + 1)).operations self).assignedCellsAfter self available)) :
    ((loopAux rows body m).operations self).AssignedFrom consumption self available := by
  apply loopAux_assignedFrom consumption rows body self available m
  intro i
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero =>
      exact (hfirst hk).mono fun cell hcell =>
        RegionOperations.mem_assignedCellsAfter_of_mem _ _ _ cell hcell
  | succ k => exact hnext k hk

/-- A cell that round `k` assigns is available from round `k + 1` onward. -/
@[keygen_norm]
theorem mem_assignedCellsAfter_loopAux_succ_of_mem_round (rows : ℕ → ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit) (k : ℕ) (self : RegionIndex)
    (available : List Cell) (cell : Cell)
    (hcell : cell ∈ ((body k (rows k)).operations self).assignedCells self) :
    cell ∈ ((loopAux rows body (k + 1)).operations self).assignedCellsAfter self available := by
  rw [loopAux_operations_succ, RegionOperations.assignedCellsAfter_append,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  exact Or.inr hcell

/-- Constant-stride form of `loopAux_assignedFrom_of_earlier_rounds`. -/
@[keygen_helper]
theorem forRange'_assignedFrom_of_earlier_rounds (consumption : Consumption F)
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell)
    (hfirst : 0 < m →
      ((body 0 offset).operations self).AssignedFrom consumption self available)
    (hnext : ∀ i, i + 1 < m →
      ((body (i + 1) (offset + i * stride + stride)).operations self).AssignedFrom
        consumption self
        (((loopAux (fun i => offset + i * stride) body (i + 1)).operations self)
          |>.assignedCellsAfter self available)) :
    ((forRange' offset stride m body).operations self).AssignedFrom consumption
      self available := by
  apply loopAux_assignedFrom_of_earlier_rounds consumption _ body self available m
  · intro hm
    simpa only [Nat.zero_mul, Nat.add_zero] using hfirst hm
  · intro i hi
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hnext i hi

/-- Constant-stride specialization of `loopAux_assignedFrom_of_forall`. -/
@[keygen_norm, keygen_helper]
theorem forRange'_assignedFrom_of_forall (consumption : Consumption F)
    (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell)
    (hbody : ∀ i : Fin m,
      ((body i.val (offset + i.val * stride)).operations self)
        |>.AssignedFrom consumption self available) :
    ((forRange' offset stride m body).operations self)
      |>.AssignedFrom consumption self available :=
  loopAux_assignedFrom_of_forall consumption _ _ self available m hbody

/-- A region loop requests no deferred constant cells when every iteration requests
none. The proof composes the exact summaries without unfolding any iteration body. -/
theorem forRange'_regionSynthesisSummary_constantSiteCount_eq_zero
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hbody : ∀ i : Fin m,
      (FloorPlanner.regionSynthesisSummary
        ((body i.val (offset + i.val * stride)).operations self)).constantSiteCount = 0) :
    (FloorPlanner.regionSynthesisSummary
      ((forRange' offset stride m body).operations self)).constantSiteCount = 0 := by
  apply FloorPlanner.regionSynthesisSummary_constantSiteCount_eq_zero_of_forall
  rw [forRange'_forall]
  intro i
  apply FloorPlanner.forall_regionOperationConstantSiteCount_eq_zero_of_regionSynthesisSummary
  exact hbody i

/-- Exact columns contributed by a region loop, one summarized fragment per
iteration. -/
@[synthesis_summary_norm]
theorem forRange'_regionSynthesisSummary_columns
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((forRange' offset stride m body).operations self)).columns =
      (List.ofFn fun i : Fin m =>
        (FloorPlanner.regionSynthesisSummary
          ((body i.val (offset + i.val * stride)).operations self)).columns).foldr
            FloorPlanner.unionColumns [] := by
  rw [forRange'_operations,
    FloorPlanner.regionSynthesisSummary_flatten_columns, List.map_ofFn]
  congr 2

/-- Exact maximum row extent of a region loop. -/
@[synthesis_summary_norm]
theorem forRange'_regionSynthesisSummary_rowCount
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((forRange' offset stride m body).operations self)).rowCount =
      (List.ofFn fun i : Fin m =>
        (FloorPlanner.regionSynthesisSummary
          ((body i.val (offset + i.val * stride)).operations self)).rowCount).foldr max 0 := by
  rw [forRange'_operations,
    FloorPlanner.regionSynthesisSummary_flatten_rowCount, List.map_ofFn]
  congr 2

/-- A uniform bound on the row extent of every loop iteration bounds the whole loop.
This avoids reducing a concrete loop into one goal per iteration. -/
theorem forRange'_regionSynthesisSummary_rowCount_le
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (bound : ℕ)
    (hbody : ∀ i : Fin m,
      (FloorPlanner.regionSynthesisSummary
        ((body i.val (offset + i.val * stride)).operations self)).rowCount ≤ bound) :
    (FloorPlanner.regionSynthesisSummary
      ((forRange' offset stride m body).operations self)).rowCount ≤ bound := by
  rw [forRange'_regionSynthesisSummary_rowCount]
  apply List.max_le_of_forall_le
  intro value hvalue
  rw [List.mem_ofFn] at hvalue
  obtain ⟨i, rfl⟩ := hvalue
  exact hbody i

/-- The row extent of a selected iteration is bounded by the whole loop. -/
theorem regionSynthesisSummary_rowCount_le_forRange'
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (i : Fin m) :
    (FloorPlanner.regionSynthesisSummary
      ((body i.val (offset + i.val * stride)).operations self)).rowCount ≤
      (FloorPlanner.regionSynthesisSummary
        ((forRange' offset stride m body).operations self)).rowCount := by
  rw [forRange'_regionSynthesisSummary_rowCount]
  apply List.le_max_of_le (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact Nat.le_refl _

/-- Any column used by a selected loop iteration is used by the whole loop. -/
theorem mem_forRange'_regionSynthesisSummary_columns
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (column : FloorPlanner.RegionColumn) (i : Fin m)
    (hcolumn : column ∈
      (FloorPlanner.regionSynthesisSummary
        ((body i.val (offset + i.val * stride)).operations self)).columns) :
    column ∈ (FloorPlanner.regionSynthesisSummary
      ((forRange' offset stride m body).operations self)).columns := by
  rw [forRange'_regionSynthesisSummary_columns,
    FloorPlanner.mem_foldr_unionColumns_iff]
  exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hcolumn⟩

/-- Exact deferred-constant demand of a region loop. -/
@[synthesis_summary_norm]
theorem forRange'_regionSynthesisSummary_constantSiteCount
    (offset stride m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((forRange' offset stride m body).operations self)).constantSiteCount =
      (List.ofFn fun i : Fin m =>
        (FloorPlanner.regionSynthesisSummary
          ((body i.val (offset + i.val * stride)).operations self)).constantSiteCount).sum := by
  rw [forRange'_operations,
    FloorPlanner.regionSynthesisSummary_flatten_constantSiteCount, List.map_ofFn]
  congr 2

@[circuit_norm ↓]
theorem forRange'_constraints (offset stride m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env ((forRange' offset stride m body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.Constraints place self env
            ((body i.val (offset + i.val * stride)).operations self) :=
  loopAux_constraints _ _ _ _ _ _

@[circuit_norm ↓]
theorem forRange'_extendsWitnesses (offset stride m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env
        ((forRange' offset stride m body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.ExtendsWitnesses place self env
            ((body i.val (offset + i.val * stride)).operations self) :=
  loopAux_extendsWitnesses _ _ _ _ _ _

/-- Variable-stride forEach: round bases supplied directly (`rows i` for round `i`). Chain's
heterogeneous piece widths use this with `rows` the partial sums. -/
def forRangeVar' (rows : ℕ → ℕ) (m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit) :
    RegionCircuit F Unit :=
  loopAux rows body m

-- (intentionally NOT @[circuit_norm]: keeps `operations` folded so the ↓ split lemma matches;
--  fire this explicitly if you need the `List.ofFn`-flatten spelling)
theorem forRangeVar'_operations (rows : ℕ → ℕ) (m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit) (self : RegionIndex) :
    (forRangeVar' rows m body).operations self
      = (List.ofFn fun i : Fin m => (body i.val (rows i.val)).operations self).flatten :=
  loopAux_operations _ _ _ _

/-- Exact compositional summary of a variable-stride region loop. -/
@[synthesis_summary_norm]
theorem forRangeVar'_regionSynthesisSummary
    (rows : ℕ → ℕ) (m : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((forRangeVar' rows m body).operations self) =
      (List.ofFn fun i : Fin m =>
        FloorPlanner.regionSynthesisSummary
          ((body i.val (rows i.val)).operations self)).foldr
            FloorPlanner.RegionSynthesisSummary.combine {} := by
  rw [forRangeVar'_operations, FloorPlanner.regionSynthesisSummary_flatten,
    List.map_ofFn]
  rfl

/-- Exact columns contributed by a variable-stride region loop. -/
@[synthesis_summary_norm]
theorem forRangeVar'_regionSynthesisSummary_columns
    (rows : ℕ → ℕ) (m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((forRangeVar' rows m body).operations self)).columns =
      (List.ofFn fun i : Fin m =>
        (FloorPlanner.regionSynthesisSummary
          ((body i.val (rows i.val)).operations self)).columns).foldr
            FloorPlanner.unionColumns [] := by
  rw [forRangeVar'_operations,
    FloorPlanner.regionSynthesisSummary_flatten_columns, List.map_ofFn]
  congr 2

/-- Exact maximum row extent of a variable-stride region loop. -/
@[synthesis_summary_norm]
theorem forRangeVar'_regionSynthesisSummary_rowCount
    (rows : ℕ → ℕ) (m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((forRangeVar' rows m body).operations self)).rowCount =
      (List.ofFn fun i : Fin m =>
        (FloorPlanner.regionSynthesisSummary
          ((body i.val (rows i.val)).operations self)).rowCount).foldr max 0 := by
  rw [forRangeVar'_operations,
    FloorPlanner.regionSynthesisSummary_flatten_rowCount, List.map_ofFn]
  congr 2

/-- Exact deferred-constant demand of a variable-stride region loop. -/
@[synthesis_summary_norm]
theorem forRangeVar'_regionSynthesisSummary_constantSiteCount
    (rows : ℕ → ℕ) (m : ℕ) (body : ℕ → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((forRangeVar' rows m body).operations self)).constantSiteCount =
      (List.ofFn fun i : Fin m =>
        (FloorPlanner.regionSynthesisSummary
          ((body i.val (rows i.val)).operations self)).constantSiteCount).sum := by
  rw [forRangeVar'_operations,
    FloorPlanner.regionSynthesisSummary_flatten_constantSiteCount, List.map_ofFn]
  congr 2

/-- Operation-local laws over `forRangeVar'`, split by symbolic round. -/
theorem forRangeVar'_forall (property : RegionOperation F → Prop)
    (rows : ℕ → ℕ) (m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) :
    ((forRangeVar' rows m body).operations self).Forall property ↔
      ∀ i : Fin m,
        ((body i.val (rows i.val)).operations self).Forall property :=
  loopAux_forall property _ _ _ _

/-- Fixed assignments from a variable-stride loop agree when each iteration is
internally lawful and its writes stay in the half-open interval before the next
iteration. The interval-ordering premise is phrased separately so callers can
derive it from compact partial-sum descriptions without expanding the loop. -/
theorem forRangeVar'_fixedAssignmentsAgree
    (rows : ℕ → ℕ) (count : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hagree : ∀ i : Fin count,
      ((body i.val (rows i.val)).operations self).FixedAssignmentsAgree)
    (hrow : ∀ (i : Fin count) column row value,
      .assignFixed column row value ∈
          (body i.val (rows i.val)).operations self →
        rows i.val ≤ row ∧ row < rows (i.val + 1))
    (hordered : ∀ i j : Fin count, i.val < j.val →
      rows (i.val + 1) ≤ rows j.val) :
    ((forRangeVar' rows count body).operations self).FixedAssignmentsAgree := by
  unfold RegionOperations.FixedAssignmentsAgree
  intro column row left right hleft hright
  rw [forRangeVar'_operations, List.mem_flatten] at hleft hright
  obtain ⟨leftOperations, hleftOperations, hleft⟩ := hleft
  obtain ⟨rightOperations, hrightOperations, hright⟩ := hright
  rw [List.mem_ofFn] at hleftOperations hrightOperations
  obtain ⟨i, rfl⟩ := hleftOperations
  obtain ⟨j, rfl⟩ := hrightOperations
  rcases hrow i column row left hleft with ⟨hileft, hiright⟩
  rcases hrow j column row right hright with ⟨hjleft, hjright⟩
  have hij : i = j := by
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hij | hji
    · have := hordered i j hij
      omega
    · have := hordered j i hji
      omega
  subst j
  exact hagree i column row left right hleft hright

/-- Advice writes from a variable-stride loop are pairwise distinct when each round is
internally distinct and distinct rounds have disjoint advice-write lists. -/
theorem forRangeVar'_adviceWritesDistinct_of_disjoint
    (rows : ℕ → ℕ) (count : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hdistinct : ∀ i : Fin count,
      ((body i.val (rows i.val)).operations self).AdviceWritesDistinct)
    (hdisjoint : ∀ i j : Fin count, i.val < j.val →
      List.Disjoint ((body i.val (rows i.val)).operations self).adviceWrites
        ((body j.val (rows j.val)).operations self).adviceWrites) :
    ((forRangeVar' rows count body).operations self).AdviceWritesDistinct := by
  unfold RegionOperations.AdviceWritesDistinct RegionOperations.adviceWrites
  rw [forRangeVar'_operations, flatMap_flatten, List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨ops, hops, rfl⟩ := hl
    rw [List.mem_ofFn] at hops
    obtain ⟨i, rfl⟩ := hops
    exact hdistinct i
  · rw [List.pairwise_map, List.pairwise_ofFn]
    intro i j hij
    exact hdisjoint i j hij

/-- Membership in a variable-stride loop's advice writes reduces to membership in some round. -/
theorem mem_forRangeVar'_adviceWrites_iff
    (rows : ℕ → ℕ) (count : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (col : Column .advice) (row : ℕ) :
    (col, row) ∈ ((forRangeVar' rows count body).operations self).adviceWrites ↔
      ∃ i : Fin count,
        (col, row) ∈ ((body i.val (rows i.val)).operations self).adviceWrites := by
  unfold RegionOperations.adviceWrites
  rw [forRangeVar'_operations, flatMap_flatten, List.mem_flatten]
  constructor
  · rintro ⟨writes, hwrites, hmem⟩
    rw [List.mem_map] at hwrites
    obtain ⟨ops, hops, rfl⟩ := hwrites
    rw [List.mem_ofFn] at hops
    obtain ⟨i, rfl⟩ := hops
    exact ⟨i, hmem⟩
  · rintro ⟨i, hmem⟩
    refine ⟨((body i.val (rows i.val)).operations self).adviceWrites, ?_, hmem⟩
    rw [List.mem_map]
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩

/-- Advice writes from a variable-stride loop are pairwise distinct when each round is
internally distinct and writes only in `[rows i, rows (i + 1))` with monotone `rows`. -/
theorem forRangeVar'_adviceWritesDistinct
    (rows : ℕ → ℕ) (count : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hdistinct : ∀ i : Fin count,
      ((body i.val (rows i.val)).operations self).AdviceWritesDistinct)
    (hrow : ∀ (i : Fin count) column row,
      (column, row) ∈ ((body i.val (rows i.val)).operations self).adviceWrites →
      rows i.val ≤ row ∧ row < rows (i.val + 1))
    (hordered : ∀ i j : Fin count, i.val < j.val →
      rows (i.val + 1) ≤ rows j.val) :
    ((forRangeVar' rows count body).operations self).AdviceWritesDistinct := by
  unfold RegionOperations.AdviceWritesDistinct RegionOperations.adviceWrites
  rw [forRangeVar'_operations, flatMap_flatten, List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨ops, hops, rfl⟩ := hl
    rw [List.mem_ofFn] at hops
    obtain ⟨i, rfl⟩ := hops
    exact hdistinct i
  · rw [List.pairwise_map, List.pairwise_ofFn]
    intro i j hij
    rw [List.disjoint_left]
    rintro ⟨col, row⟩ hi hj
    have hbi := hrow i col row hi
    have hbj := hrow j col row hj
    have hstep := hordered i j hij
    omega

/-- Advice writes from a variable-stride loop lie in `[rows 0, rows count)`. -/
theorem forRangeVar'_adviceWrites_row_bounds
    (rows : ℕ → ℕ) (count : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex)
    (hrow : ∀ (i : Fin count) column row,
      (column, row) ∈ ((body i.val (rows i.val)).operations self).adviceWrites →
      rows i.val ≤ row ∧ row < rows (i.val + 1))
    (hmono : ∀ a b, a ≤ b → b ≤ count → rows a ≤ rows b)
    (column : Column .advice) (row : ℕ)
    (hmem : (column, row) ∈ ((forRangeVar' rows count body).operations self).adviceWrites) :
    rows 0 ≤ row ∧ row < rows count := by
  unfold RegionOperations.adviceWrites at hmem
  rw [forRangeVar'_operations, flatMap_flatten, List.mem_flatten] at hmem
  obtain ⟨writes, hwrites, hmem⟩ := hmem
  rw [List.mem_map] at hwrites
  obtain ⟨ops, hops, rfl⟩ := hwrites
  rw [List.mem_ofFn] at hops
  obtain ⟨i, rfl⟩ := hops
  have hb := hrow i column row hmem
  have h0 : rows 0 ≤ rows i.val := hmono 0 i.val (Nat.zero_le _) (Nat.le_of_lt i.isLt)
  have h1 : rows (i.val + 1) ≤ rows count := hmono (i.val + 1) count (Nat.succ_le_of_lt i.isLt) (Nat.le_refl _)
  omega

/-- A variable-stride loop is lawful when each round is lawful from the caller's cells
together with everything the earlier rounds assigned. -/
theorem forRangeVar'_assignedFrom (consumption : Consumption F)
    (rows : ℕ → ℕ) (m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell)
    (hbody : ∀ i : Fin m,
      ((body i.val (rows i.val)).operations self).AssignedFrom consumption self
        (((loopAux rows body i.val).operations self).assignedCellsAfter self available)) :
    ((forRangeVar' rows m body).operations self).AssignedFrom consumption self available :=
  loopAux_assignedFrom consumption rows body self available m hbody

/-- A variable-stride loop is lawful when each symbolic round is lawful from the caller's
original input cells. -/
@[keygen_norm, keygen_helper]
theorem forRangeVar'_assignedFrom_of_forall (consumption : Consumption F)
    (rows : ℕ → ℕ) (m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell)
    (hbody : ∀ i : Fin m,
      ((body i.val (rows i.val)).operations self)
        |>.AssignedFrom consumption self available) :
    ((forRangeVar' rows m body).operations self)
      |>.AssignedFrom consumption self available :=
  loopAux_assignedFrom_of_forall consumption rows body self available m hbody

/-- Variable-stride form of `loopAux_assignedFrom_of_earlier_rounds`. -/
@[keygen_helper]
theorem forRangeVar'_assignedFrom_of_earlier_rounds (consumption : Consumption F)
    (rows : ℕ → ℕ) (m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (self : RegionIndex) (available : List Cell)
    (hfirst : 0 < m →
      ((body 0 (rows 0)).operations self).AssignedFrom consumption self available)
    (hnext : ∀ i, i + 1 < m →
      ((body (i + 1) (rows (i + 1))).operations self).AssignedFrom consumption self
        (((loopAux rows body (i + 1)).operations self).assignedCellsAfter self available)) :
    ((forRangeVar' rows m body).operations self).AssignedFrom consumption self available :=
  loopAux_assignedFrom_of_earlier_rounds consumption rows body self available m hfirst hnext

@[circuit_norm ↓]
theorem forRangeVar'_constraints (rows : ℕ → ℕ) (m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env ((forRangeVar' rows m body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.Constraints place self env ((body i.val (rows i.val)).operations self) :=
  loopAux_constraints _ _ _ _ _ _

@[circuit_norm ↓]
theorem forRangeVar'_extendsWitnesses (rows : ℕ → ℕ) (m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env
        ((forRangeVar' rows m body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.ExtendsWitnesses place self env
            ((body i.val (rows i.val)).operations self) :=
  loopAux_extendsWitnesses _ _ _ _ _ _

/-! ## The map combinator (`Vector` of per-round outputs, constant stride)

Layered on the `Unit` core: the per-round output cells live at round-determined rows and are
named by `body`'s output; the loop returns `Vector.ofFn` of them directly (so its `output` is
`rfl` and indexes by `Vector.getElem_ofFn`), while its `operations` are exactly the `Unit` core's
(the outputs emit nothing). This keeps the operations theory value-free — the maintainer's
ConstantOutput analogue holds by construction. -/

/-- `forRange offset stride m body`: like `forRange'` but each round `i` also *names* an output
`out i (offset + i*stride)` (a cell reference / value at its base row, emitting no extra op), and
the loop returns the `Vector α m` of them. `body` returns the round's `Unit` ops; `out` names the
output. -/
def forRange (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (out : (i : ℕ) → ℕ → α) : RegionCircuit F (Vector α m) :=
  fun self =>
    (Vector.ofFn (fun i : Fin m => out i.val (offset + i.val * stride)),
      (forRange' offset stride m body).operations self)

@[circuit_norm]
theorem forRange_output (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (out : (i : ℕ) → ℕ → α) (self : RegionIndex) :
    (forRange offset stride m body out).output self
      = Vector.ofFn (fun i : Fin m => out i.val (offset + i.val * stride)) := rfl

-- (intentionally NOT @[circuit_norm]: keeps `operations` folded so the ↓ split lemma matches;
--  fire this explicitly if you need the `List.ofFn`-flatten spelling)
theorem forRange_operations (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (out : (i : ℕ) → ℕ → α) (self : RegionIndex) :
    (forRange offset stride m body out).operations self
      = (List.ofFn fun i : Fin m =>
          (body i.val (offset + i.val * stride)).operations self).flatten :=
  loopAux_operations _ _ _ _

@[circuit_norm ↓]
theorem forRange_constraints (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (out : (i : ℕ) → ℕ → α)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env ((forRange offset stride m body out).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.Constraints place self env
            ((body i.val (offset + i.val * stride)).operations self) :=
  loopAux_constraints _ _ _ _ _ _

@[circuit_norm ↓]
theorem forRange_extendsWitnesses (offset stride m : ℕ)
    (body : (i : ℕ) → ℕ → RegionCircuit F Unit) (out : (i : ℕ) → ℕ → α)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env
        ((forRange offset stride m body out).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.ExtendsWitnesses place self env
            ((body i.val (offset + i.val * stride)).operations self) :=
  loopAux_extendsWitnesses _ _ _ _ _ _

/-! ## The serial `foldRange` combinator (accumulator threads INTO the round body)

Serial accumulator-threading form, the general one the corpus's serial loops need (MulComplete:
each round's `Add.add.call`s take the previous round's accumulator *cells* as inputs, so the round
`operations` genuinely depend on the accumulator). The body is
`(i : ℕ) → ℕ → β → RegionCircuit F β`: round `i` at base row `offset + i*stride` reads the
accumulator `acc : β` and returns the next one.

**ConstantOutput analogue (maintainer rule): the accumulator VAR at round `k` is a closed form of
the round index** — `foldAcc … k self`, the running fold of the per-round `output`s (true of every
serial loop in the corpus: the accumulator is cell records at round-determined rows). This is what
keeps the split's per-round predicate a closed form. A genuinely output-*value*-dependent loop (one
whose op structure depends on witness values, not just cell positions) would need a separate
`foldRangeDynOutput` — this natural name is the good path.

`foldRangeVar` supplies the round bases directly (variable stride — Chain's per-piece widths). -/

/-- Serial accumulator-threading loop over rounds `0 .. k-1` at base rows `rows i`, structurally
recursive. Round `i` runs `body i (rows i) acc` on the running accumulator. -/
def foldRangeVarAux (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β) : ℕ → RegionCircuit F β
  | 0 => pure init
  | k + 1 => do
    let acc ← foldRangeVarAux rows init body k
    body k (rows k) acc

/-- The accumulator VAR at round `k` — the closed form `(foldRangeVarAux … k).output self`
(ConstantOutput analogue). The per-round split predicate is stated over it. -/
def foldAcc (rows : ℕ → ℕ) (init : β) (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (k : ℕ) (self : RegionIndex) : β :=
  (foldRangeVarAux rows init body k).output self

@[circuit_norm]
theorem foldAcc_zero (rows : ℕ → ℕ) (init : β) (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) : foldAcc rows init body 0 self = init := rfl

theorem foldAcc_succ (rows : ℕ → ℕ) (init : β) (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (k : ℕ) (self : RegionIndex) :
    foldAcc rows init body (k + 1) self
      = (body k (rows k) (foldAcc rows init body k self)).output self := rfl

/-- An invariant of the initial accumulator and every body output holds for every
closed-form accumulator in a serial fold. -/
theorem foldAcc_property (property : β → Prop)
    (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β) (self : RegionIndex)
    (hinit : property init)
    (hbody : ∀ i acc, property acc → property ((body i (rows i) acc).output self)) :
    ∀ k, property (foldAcc rows init body k self) := by
  intro k
  induction k with
  | zero => simpa only [foldAcc_zero] using hinit
  | succ k ih =>
      rw [foldAcc_succ]
      exact hbody k _ ih

/-- Per-round operations decomposition: round `k`'s ops read the accumulator at round `k`
(`foldAcc … k`), the closed form. Holds by `rfl` via `operations_bind`. -/
theorem foldRangeVarAux_operations_succ (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β) (k : ℕ) (self : RegionIndex) :
    (foldRangeVarAux rows init body (k + 1)).operations self
      = (foldRangeVarAux rows init body k).operations self
        ++ (body k (rows k) (foldAcc rows init body k self)).operations self := rfl

/-- `operations` of the fold as the flatten-of-`ofFn` of per-round ops at the closed-form
accumulators `foldAcc … i`. -/
theorem foldRangeVarAux_operations (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β) (k : ℕ) (self : RegionIndex) :
    (foldRangeVarAux rows init body k).operations self
      = (List.ofFn fun i : Fin k =>
          (body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self).flatten := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [foldRangeVarAux_operations_succ, ih, List.ofFn_succ', List.concat_eq_append,
      List.flatten_append]
    simp only [Fin.val_last, Fin.val_castSucc, List.flatten_cons, List.flatten_nil,
      List.append_nil]

/-- Provenance through a serial fold. The invariant records exactly which cells of the
running accumulator are available after the preceding rounds. -/
theorem foldRangeVarAux_assignedFrom (consumption : Consumption F)
    (invariant : List Cell → β → Prop)
    (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) (available : List Cell)
    (hinit : invariant available init)
    (hbodyAssigned : ∀ i cells acc, invariant cells acc →
      ((body i (rows i) acc).operations self).AssignedFrom consumption self cells)
    (hbodyInvariant : ∀ i cells acc, invariant cells acc →
      invariant
        ((body i (rows i) acc).operations self |>.assignedCellsAfter self cells)
        ((body i (rows i) acc).output self)) :
    ∀ k,
      ((foldRangeVarAux rows init body k).operations self
          |>.AssignedFrom consumption self available) ∧
        invariant
          ((foldRangeVarAux rows init body k).operations self
            |>.assignedCellsAfter self available)
          (foldAcc rows init body k self) := by
  intro k
  induction k with
  | zero =>
      exact ⟨.nil available, hinit⟩
  | succ k inductionHypothesis =>
      rcases inductionHypothesis with ⟨hprefixAssigned, hprefixInvariant⟩
      have hroundAssigned := hbodyAssigned k _ _ hprefixInvariant
      have hroundInvariant := hbodyInvariant k _ _ hprefixInvariant
      constructor
      · rw [foldRangeVarAux_operations_succ,
          RegionOperations.assignedFrom_append_iff]
        exact ⟨hprefixAssigned, hroundAssigned⟩
      · simpa only [foldRangeVarAux_operations_succ, foldAcc_succ,
          RegionOperations.assignedCellsAfter, List.foldl_append] using
          hroundInvariant

/-- Advice-write consistency through a serial fold when each round is internally consistent and
earlier rounds' advice writes are disjoint from later rounds' non-self-copy advice writes. -/
theorem foldRangeVarAux_adviceWritesConsistent
    (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) (m : ℕ)
    (hcons : ∀ i : Fin m,
      ((body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self)
        |>.AdviceWritesConsistent self)
    (hdisj : ∀ i j : Fin m, i < j →
      (((body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self).adviceWrites).Disjoint
        (((body j.val (rows j.val) (foldAcc rows init body j.val self)).operations self)
          |>.nonSelfCopyAdviceWrites self)) :
    ((foldRangeVarAux rows init body m).operations self).AdviceWritesConsistent self := by
  have hmemAux : ∀ k col row,
      (col, row) ∈ ((foldRangeVarAux rows init body k).operations self).adviceWrites →
      ∃ i : Fin k,
        (col, row) ∈ ((body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self).adviceWrites := by
    intro k col row hmem
    unfold RegionOperations.adviceWrites at hmem
    rw [foldRangeVarAux_operations, flatMap_flatten, List.mem_flatten] at hmem
    obtain ⟨writes, hwrites, hmem⟩ := hmem
    rw [List.mem_map] at hwrites
    obtain ⟨ops, hops, rfl⟩ := hwrites
    rw [List.mem_ofFn] at hops
    obtain ⟨i, rfl⟩ := hops
    exact ⟨i, hmem⟩
  have haux : ∀ k (hk : k ≤ m),
      ((foldRangeVarAux rows init body k).operations self).AdviceWritesConsistent self := by
    intro k hk
    induction k with
    | zero => exact RegionOperations.adviceWritesConsistent_nil self
    | succ k ih =>
      rw [foldRangeVarAux_operations_succ]
      apply RegionOperations.adviceWritesConsistent_append_of_disjoint self
        (ih (Nat.le_of_succ_le hk)) (hcons ⟨k, hk⟩)
      rw [List.disjoint_left]
      rintro ⟨col, row⟩ hprev hcur
      obtain ⟨i, hi⟩ := hmemAux k col row hprev
      exact List.disjoint_left.mp
        (hdisj ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_succ_le hk)⟩ ⟨k, hk⟩ i.isLt) hi hcur
  exact haux m le_rfl

/-- Advice-write distinctness through a serial fold with monotone row windows. -/
theorem foldRangeVarAux_adviceWritesDistinct
    (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex)
    (hdistinct : ∀ i acc,
      ((body i (rows i) acc).operations self).AdviceWritesDistinct)
    (hrow : ∀ i acc column row,
      (column, row) ∈ ((body i (rows i) acc).operations self).adviceWrites →
      rows i ≤ row ∧ row < rows (i + 1))
    (hmono : ∀ a b, a ≤ b → rows a ≤ rows b) :
    ∀ k,
      ((foldRangeVarAux rows init body k).operations self).AdviceWritesDistinct ∧
        ∀ column row,
          (column, row) ∈ ((foldRangeVarAux rows init body k).operations self).adviceWrites →
          rows 0 ≤ row ∧ row < rows k := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, fun _ _ h => ?_⟩
      · change RegionOperations.AdviceWritesDistinct []
        exact RegionOperations.adviceWritesDistinct_nil
      · change _ ∈ RegionOperations.adviceWrites [] at h
        simp [RegionOperations.adviceWrites] at h
  | succ k ih =>
      rcases ih with ⟨hprevDist, hprevBound⟩
      rw [foldRangeVarAux_operations_succ]
      refine ⟨?_, ?_⟩
      · rw [RegionOperations.adviceWritesDistinct_append_iff]
        refine ⟨hprevDist, hdistinct k _, ?_⟩
        exact RegionOperations.adviceWrites_disjoint_of_row_sep (rows k)
          (fun c r h => (hprevBound c r h).2)
          (fun c r h => (hrow k _ c r h).1)
      · intro col row hmem
        rw [RegionOperations.adviceWrites_append, List.mem_append] at hmem
        rcases hmem with hpre | hcur
        · have hb := hprevBound col row hpre
          have hle := hmono k (k + 1) (Nat.le_succ k)
          omega
        · have hb := hrow k _ col row hcur
          have h0 := hmono 0 k (Nat.zero_le k)
          omega

/-- An operation-local law over a serial fold reduces to the law for every round,
with the accumulator kept in its closed `foldAcc` form. -/
theorem foldRangeVarAux_forall (property : RegionOperation F → Prop)
    (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) (k : ℕ) :
    ((foldRangeVarAux rows init body k).operations self).Forall property ↔
      ∀ i : Fin k,
        ((body i.val (rows i.val)
          (foldAcc rows init body i.val self)).operations self).Forall property := by
  induction k with
  | zero =>
      change List.Forall property [] ↔
        ∀ i : Fin 0,
          ((body i.val (rows i.val)
            (foldAcc rows init body i.val self)).operations self).Forall property
      simp
  | succ n ih =>
      rw [foldRangeVarAux_operations_succ, List.forall_append, ih,
        Fin.forall_fin_succ']
      simp only [Fin.val_last, Fin.val_castSucc]

/-- **The `Constraints` split**, per-round at the closed-form accumulator. -/
@[circuit_norm ↓]
theorem foldRangeVarAux_constraints (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) (k : ℕ) :
    RegionOperations.Constraints place self env ((foldRangeVarAux rows init body k).operations self)
      ↔ ∀ i : Fin k,
          RegionOperations.Constraints place self env
            ((body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self) := by
  induction k with
  | zero => simp only [foldRangeVarAux, operations_pure, RegionOperations.constraints_nil, true_iff]
            exact fun i => i.elim0
  | succ n ih =>
    rw [foldRangeVarAux_operations_succ, RegionOperations.constraints_append, ih,
      Fin.forall_fin_succ']
    simp only [Fin.val_last, Fin.val_castSucc]

/-- **The `ExtendsWitnesses` split** (completeness counterpart). -/
@[circuit_norm ↓]
theorem foldRangeVarAux_extendsWitnesses (rows : ℕ → ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) (k : ℕ) :
    RegionOperations.ExtendsWitnesses place self env
        ((foldRangeVarAux rows init body k).operations self)
      ↔ ∀ i : Fin k,
          RegionOperations.ExtendsWitnesses place self env
            ((body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self) := by
  induction k with
  | zero => simp only [foldRangeVarAux, operations_pure, RegionOperations.extendsWitnesses_nil,
              true_iff]
            exact fun i => i.elim0
  | succ n ih =>
    rw [foldRangeVarAux_operations_succ, RegionOperations.extendsWitnesses_append, ih,
      Fin.forall_fin_succ']
    simp only [Fin.val_last, Fin.val_castSucc]

/-- `foldRangeVar rows m init body`: `m` serial rounds, round `i` at supplied base row `rows i`,
threading `β`. The variable-stride general form (Chain's heterogeneous piece widths: `rows i` the
partial sums). -/
def foldRangeVar (rows : ℕ → ℕ) (m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β) : RegionCircuit F β :=
  foldRangeVarAux rows init body m

theorem foldRangeVar_forall (property : RegionOperation F → Prop)
    (rows : ℕ → ℕ) (m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) :
    ((foldRangeVar rows m init body).operations self).Forall property ↔
      ∀ i : Fin m,
        ((body i.val (rows i.val)
          (foldAcc rows init body i.val self)).operations self).Forall property :=
  foldRangeVarAux_forall _ _ _ _ _ _

@[circuit_norm ↓]
theorem foldRangeVar_constraints (rows : ℕ → ℕ) (m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env ((foldRangeVar rows m init body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.Constraints place self env
            ((body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self) :=
  foldRangeVarAux_constraints _ _ _ _ _ _ _

@[circuit_norm ↓]
theorem foldRangeVar_extendsWitnesses (rows : ℕ → ℕ) (m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env
        ((foldRangeVar rows m init body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.ExtendsWitnesses place self env
            ((body i.val (rows i.val) (foldAcc rows init body i.val self)).operations self) :=
  foldRangeVarAux_extendsWitnesses _ _ _ _ _ _ _

/-- `foldRange offset stride m init body`: constant-stride serial fold (round `i` at
`offset + i*stride`) — the special case of `foldRangeVar` with `rows i := offset + i*stride`. -/
def foldRange (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β) : RegionCircuit F β :=
  foldRangeVar (fun i => offset + i * stride) m init body

/-- Constant-stride specialization of `foldRangeVarAux_assignedFrom`. -/
theorem foldRange_assignedFrom (consumption : Consumption F)
    (invariant : List Cell → β → Prop)
    (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) (available : List Cell)
    (hinit : invariant available init)
    (hbodyAssigned : ∀ i cells acc, invariant cells acc →
      ((body i (offset + i * stride) acc).operations self
        |>.AssignedFrom consumption self cells))
    (hbodyInvariant : ∀ i cells acc, invariant cells acc →
      invariant
        ((body i (offset + i * stride) acc).operations self
          |>.assignedCellsAfter self cells)
        ((body i (offset + i * stride) acc).output self)) :
    ((foldRange offset stride m init body).operations self
      |>.AssignedFrom consumption self available) :=
  (foldRangeVarAux_assignedFrom consumption invariant
    (fun i => offset + i * stride) init body self available
    hinit hbodyAssigned hbodyInvariant m).1

/-- Constant-stride specialization of `foldRangeVarAux_adviceWritesConsistent`. -/
theorem foldRange_adviceWritesConsistent
    (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex)
    (hcons : ∀ i : Fin m,
      ((body i.val (offset + i.val * stride)
          (foldAcc (fun j => offset + j * stride) init body i.val self)).operations self)
        |>.AdviceWritesConsistent self)
    (hdisj : ∀ i j : Fin m, i < j →
      (((body i.val (offset + i.val * stride)
          (foldAcc (fun k => offset + k * stride) init body i.val self)).operations self).adviceWrites).Disjoint
        (((body j.val (offset + j.val * stride)
          (foldAcc (fun k => offset + k * stride) init body j.val self)).operations self)
          |>.nonSelfCopyAdviceWrites self)) :
    ((foldRange offset stride m init body).operations self).AdviceWritesConsistent self :=
  foldRangeVarAux_adviceWritesConsistent (fun i => offset + i * stride) init body self m hcons hdisj

/-- Constant-stride specialization of `foldRangeVarAux_adviceWritesDistinct`. -/
theorem foldRange_adviceWritesDistinct
    (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex)
    (hdistinct : ∀ i acc,
      ((body i (offset + i * stride) acc).operations self).AdviceWritesDistinct)
    (hrow : ∀ i acc column row,
      (column, row) ∈ ((body i (offset + i * stride) acc).operations self).adviceWrites →
      offset + i * stride ≤ row ∧ row < offset + (i + 1) * stride) :
    ((foldRange offset stride m init body).operations self).AdviceWritesDistinct :=
  (foldRangeVarAux_adviceWritesDistinct (fun i => offset + i * stride) init body self
    hdistinct hrow (fun _ _ hab => Nat.add_le_add_left (Nat.mul_le_mul_right stride hab) offset) m).1

@[circuit_norm]
theorem foldRange_output (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β) (self : RegionIndex) :
    (foldRange offset stride m init body).output self =
      foldAcc (fun i => offset + i * stride) init body m self := rfl

/-- Exact compositional summary of a serial region fold, expressed through the
already-reduced summary of each accumulator-dependent round. -/
@[synthesis_summary_norm]
theorem foldRange_regionSynthesisSummary
    (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((foldRange offset stride m init body).operations self) =
      (List.ofFn fun i : Fin m =>
        FloorPlanner.regionSynthesisSummary
          ((body i.val (offset + i.val * stride)
            (foldAcc (fun j => offset + j * stride)
              init body i.val self)).operations self)).foldr
        FloorPlanner.RegionSynthesisSummary.combine {} := by
  unfold foldRange foldRangeVar
  rw [foldRangeVarAux_operations,
    FloorPlanner.regionSynthesisSummary_flatten, List.map_ofFn]
  rfl

theorem foldRange_forall (property : RegionOperation F → Prop)
    (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (self : RegionIndex) :
    ((foldRange offset stride m init body).operations self).Forall property ↔
      ∀ i : Fin m,
        ((body i.val (offset + i.val * stride)
          (foldAcc (fun j => offset + j * stride)
            init body i.val self)).operations self).Forall property :=
  foldRangeVarAux_forall _ _ _ _ _ _

@[circuit_norm ↓]
theorem foldRange_constraints (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env ((foldRange offset stride m init body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.Constraints place self env
            ((body i.val (offset + i.val * stride)
              (foldAcc (fun j => offset + j * stride) init body i.val self)).operations self) :=
  foldRangeVarAux_constraints _ _ _ _ _ _ _

@[circuit_norm ↓]
theorem foldRange_extendsWitnesses (offset stride m : ℕ) (init : β)
    (body : (i : ℕ) → ℕ → β → RegionCircuit F β)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env
        ((foldRange offset stride m init body).operations self)
      ↔ ∀ i : Fin m,
          RegionOperations.ExtendsWitnesses place self env
            ((body i.val (offset + i.val * stride)
              (foldAcc (fun j => offset + j * stride) init body i.val self)).operations self) :=
  foldRangeVarAux_extendsWitnesses _ _ _ _ _ _ _

/-! ## The `chunk_split` membership (see `Clean/Halo2/Attributes.lean`)

Every combinator's canonical ∀-round split pair, in the pre-order (`↓`) discipline the
`circuit_norm` tags already use: the fold head splits before simp descends into it. -/

attribute [chunk_split ↓] loopAux_constraints loopAux_extendsWitnesses
  forRange'_constraints forRange'_extendsWitnesses
  forRangeVar'_constraints forRangeVar'_extendsWitnesses
  forRange_constraints forRange_extendsWitnesses
  foldRangeVarAux_constraints foldRangeVarAux_extendsWitnesses
  foldRangeVar_constraints foldRangeVar_extendsWitnesses
  foldRange_constraints foldRange_extendsWitnesses

end RegionCircuit
end Halo2
