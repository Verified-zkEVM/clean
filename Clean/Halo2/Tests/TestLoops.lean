import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: `RegionCircuit` loop combinators + `∀`-bound chunk consumption

Acceptance pins for the native loop support (`Clean/Halo2/Loops.lean`):

1. **Split lemmas fire** — `circuit_norm` alone turns a `forRange'` / `foldRange`'s
   `RegionOperations.Constraints` / `ExtendsWitnesses` into the per-round
   `∀ i : Fin m, <round i's predicate at base row offset + i*stride>`, and the loop's `operations`
   into the `List.ofFn`-flatten form. This is what deletes the hand-written
   `loop_operations_succ` / `rangeCheck_loop_*` recursion.
2. **`∀`-bound bundle-chunk consumption** — the `subcircuit_rw` engine consumes a child
   `.call` chunk sitting UNDER the `∀ i : Fin m` binder the split lemma produced (the
   congruence walker traverses `∀` via `forall_mono`; the leaf matching reads the bound index
   off the base row / per-round input). This is the bodies-as-bundles path (MulComplete's shape:
   a child call per round). Raw-ops bodies (WitnessPoint-style gate/assign rounds) keep working
   as ordinary `circuit_norm` after the split — covered by the range-check / double-and-add
   migrations.
3. A **Permutation.lean-quality serial example** — a `foldRange` value-chain whose per-round
   fact is read off the split, then folded by a genuine value induction (no framework recursion).
-/

namespace Halo2.LoopsTest

open Halo2 Halo2.RegionCircuit Halo2.Ironwood.Ecc Orchard

variable {F : Type} [FiniteField F]

/-! ## 1. The split lemmas fire under `circuit_norm` alone -/

-- `forRange'` (forEach) constraints ⇒ per-round `∀ i : Fin m`, at base row `offset + i*stride`.
example (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env
        ((forRange' offset stride m body).operations self)
      ↔ ∀ i : Fin m, RegionOperations.Constraints place self env
          ((body i.val (offset + i.val * stride)).operations self) := by
  simp only [circuit_norm]

-- `forRange'` witnesses split (completeness side).
example (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place self env
        ((forRange' offset stride m body).operations self)
      ↔ ∀ i : Fin m, RegionOperations.ExtendsWitnesses place self env
          ((body i.val (offset + i.val * stride)).operations self) := by
  simp only [circuit_norm]

-- `foldRange` (serial, accumulator threads INTO the body) constraints split — per-round predicate
-- at the closed-form accumulator `foldAcc … i` (MulComplete's shape: acc-dependent round ops).
example (offset stride m : ℕ) (init : F) (body : (i : ℕ) → ℕ → F → RegionCircuit F F)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env
        ((foldRange offset stride m init body).operations self)
      ↔ ∀ i : Fin m, RegionOperations.Constraints place self env
          ((body i.val (offset + i.val * stride)
            (foldAcc (fun j => offset + j * stride) init body i.val self)).operations self) := by
  simp only [circuit_norm]

-- Variable-stride forEach: the general form, bases supplied directly (Chain's shape).
example (rows : ℕ → ℕ) (m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations.Constraints place self env
        ((forRangeVar' rows m body).operations self)
      ↔ ∀ i : Fin m, RegionOperations.Constraints place self env
          ((body i.val (rows i.val)).operations self) := by
  simp only [circuit_norm]

-- The `operations` flatten form (the `List.ofFn` shape downstream reductions consume). This lemma
-- is deliberately NOT in `circuit_norm` (so the ↓ split above matches the folded `operations`
-- spelling first); it is available by name when a proof genuinely wants the flatten form.
example (offset stride m : ℕ) (body : (i : ℕ) → ℕ → RegionCircuit F Unit) (self : RegionIndex) :
    (forRange' offset stride m body).operations self
      = (List.ofFn fun i : Fin m =>
          (body i.val (offset + i.val * stride)).operations self).flatten :=
  forRange'_operations _ _ _ _ _

/-! ## 2. `∀`-bound bundle-chunk consumption (bodies-as-bundles)

The double-and-add / range-check rounds are RAW ops; the harder shape MulComplete uses is a
child `.call` per round. Here the loop body is a `WitnessPoint.point.call` at the round's base
row, so after the split the goal / hypothesis has the child chunk UNDER `∀ i : Fin m`. The engine
must fire there — traversing the binder and reading the bound index off the base row. -/

/-- Bundle-bodied loop: round `i` calls `witness_point` at base row `offset + i*stride`, with the
per-round input `inputs i`. -/
def bundleLoop (cfg : WitnessPoint.Config) (offset stride m : ℕ)
    (inputs : ℕ → Point (FExpr Fp)) : RegionCircuit Fp Unit :=
  forRange' offset stride m fun i row => do
    let _ ← WitnessPoint.point.call cfg row (inputs i)
    pure ()

-- SOUNDNESS: the loop's constraints, split to `∀ i`, then `subcircuit_rw` under the binder
-- exposes each round's `witness_point` `Spec` (`(output i).Valid`).
example (cfg : WitnessPoint.Config) (offset stride m : ℕ) (inputs : ℕ → Point (FExpr Fp))
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (h : RegionOperations.Constraints place self env
        ((bundleLoop cfg offset stride m inputs).operations self)) :
    ∀ i : Fin m, (eval (⟨place, env⟩ : Placed Environment Fp)
        (WitnessPoint.point.output cfg (offset + i.val * stride) (inputs i.val) self)).Valid := by
  simp only [bundleLoop, circuit_norm] at h
  subcircuit_rw at h
  intro i
  exact (h i) trivial trivial

/-! ## 3. Permutation.lean-quality serial value-chain

A `foldRange` whose accumulator is a running sum threaded through the OUTPUT value (the operations
are per-round independent — a single `assignFixed` per round pinning the round's fixed cell to the
loop index). Soundness reads each round's `assignFixed` equation off the split and folds them by a
genuine value induction — the shape a serial gadget's `Spec` proof takes, with zero framework
recursion. -/

/-- One round: pin fixed column `col` at `row` to the field value `↑i`. -/
def stampRound (col : Column .fixed) (i : ℕ) (row : ℕ) : RegionCircuit Fp Unit := do
  let _ ← assignFixed col row (i : Fp)
  pure ()

/-- `stampLoop offset stride m col`: `m` rounds, round `i` pins `col` at `offset + i*stride`. -/
def stampLoop (col : Column .fixed) (offset stride m : ℕ) : RegionCircuit Fp Unit :=
  forRange' offset stride m fun i row => stampRound col i row

-- Each round's fixed-cell equation, read straight off the split (no recursion / peel lemma).
example (col : Column .fixed) (offset stride m : ℕ)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (h : RegionOperations.Constraints place self env
        ((stampLoop col offset stride m).operations self)) :
    ∀ i : Fin m, env.fixed col ((place self + (offset + i.val * stride) : ℕ) : ℤ) = (i.val : Fp) := by
  simp only [stampLoop, stampRound, circuit_norm] at h
  exact h

/-! ## 4. `foldRange` with accumulator threaded INTO the round body (MulComplete's shape)

The genuine serial case the corpus needs: each round's `operations` depend on the running
accumulator (MulComplete: the round's `Add.add.call`s take the previous round's accumulator cells
as inputs). Here the round `copyAdvice`s FROM the accumulator cell — an acc-dependent op — and
returns the freshly-written cell as the next accumulator. The `foldRange` split states each round's
`Constraints` over the closed-form accumulator `foldAcc … i` (the constancy the maintainer's
ConstantOutput analogue guarantees). -/

/-- A serial fold whose round copies FROM the running accumulator cell into `col` at the round's
base row, and hands the new cell forward — the accumulator threads into the round's `operations`
(the `copyAdvice` reads `acc`). -/
def accFoldLoop (col : Column .advice) (offset stride m : ℕ) (init : AssignedCell Fp) :
    RegionCircuit Fp (AssignedCell Fp) :=
  foldRange offset stride m init fun _i row acc => copyAdvice acc col row

-- The fold's constraints split to `∀ i` over the acc-dependent chunk; each round's `copyAdvice`
-- constraint (the copy-equality against `foldAcc … i`) is read straight off the split — no
-- loop-structure recursion, and the round op genuinely references the closed-form accumulator.
example (col : Column .advice) (offset stride m : ℕ) (init : AssignedCell Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (h : RegionOperations.Constraints place self env
        ((accFoldLoop col offset stride m init).operations self)) :
    ∀ i : Fin m,
      (Cell.of self (offset + i.val * stride) col).eval place env
        = (foldAcc (fun j => offset + j * stride) init
            (fun _i row acc => copyAdvice acc col row) i.val self).cell.eval place env := by
  simp only [accFoldLoop, circuit_norm] at h
  exact h

/-! ## 5. Branching round body: `circuit_norm` descends the `ite`

A round body that branches on the index (`double-and-add`'s anchored-first-row / last-row shape).
`circuit_norm` must push `operations`/`Constraints` through the lifted `ite` so the split hypothesis
lands as `if c then P₁ else P₂` over value-level content — both branches exposed, ready for a
`by_cases`/`split` consumer. Covers both the do-elaborator's lifted `if` and the raw bind-of-`ite`
spelling. -/

/-- Round that stamps a different constant depending on the index (lifted `if`, no trailing bind). -/
def branchStamp (col : Column .fixed) (i row : ℕ) : RegionCircuit Fp Unit := do
  if i = 0 then
    let _ ← assignFixed col row (0 : Fp)
    pure ()
  else
    let _ ← assignFixed col row (1 : Fp)
    pure ()

def branchLoop (col : Column .fixed) (offset stride m : ℕ) : RegionCircuit Fp Unit :=
  forRange' offset stride m fun i row => branchStamp col i row

-- `circuit_norm` alone exposes both branches as the per-round `if`-form.
example (col : Column .fixed) (offset stride m : ℕ)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) :
    RegionOperations.Constraints place self env ((branchLoop col offset stride m).operations self)
      ↔ ∀ i : Fin m, if (i.val : ℕ) = 0
          then env.fixed col ((place self + (offset + i.val * stride) : ℕ) : ℤ) = 0
          else env.fixed col ((place self + (offset + i.val * stride) : ℕ) : ℤ) = 1 := by
  simp only [branchLoop, branchStamp, circuit_norm]

/-- Same branch, spelled as a genuine bind-of-`ite` (`let _ ← if …; …`). -/
def branchBindStamp (col : Column .fixed) (i row : ℕ) : RegionCircuit Fp Unit := do
  let _ ← if i = 0 then assignFixed col row (0 : Fp) else assignFixed col row (1 : Fp)
  pure ()

def branchBindLoop (col : Column .fixed) (offset stride m : ℕ) : RegionCircuit Fp Unit :=
  forRange' offset stride m fun i row => branchBindStamp col i row

example (col : Column .fixed) (offset stride m : ℕ)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) :
    RegionOperations.Constraints place self env ((branchBindLoop col offset stride m).operations self)
      ↔ ∀ i : Fin m, if (i.val : ℕ) = 0
          then env.fixed col ((place self + (offset + i.val * stride) : ℕ) : ℤ) = 0
          else env.fixed col ((place self + (offset + i.val * stride) : ℕ) : ℤ) = 1 := by
  simp only [branchBindLoop, branchBindStamp, circuit_norm]

end Halo2.LoopsTest
