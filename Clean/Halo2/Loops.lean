import Clean.Halo2.Lemmas

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
