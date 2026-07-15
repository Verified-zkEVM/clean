import Clean.Halo2.Tactics.ProvableTypeSimp
import Clean.Ironwood.Ecc.Basic

/-!
Regression tests for `provable_type_simp` (halo2). Each asserts a shape or a consumption
pattern the confluence claims depend on. Companion to main Clean's `TestProvableStructSimp`.
-/

namespace Halo2.ProvableTypeSimp.Test
open Halo2 Halo2.Ironwood

/-- Two-level struct: a `ProvableStruct` whose components are themselves higher-level
(`Point`) — the Add32 `{x:U32,y:U32}` analogue. -/
structure TwoPoints (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

/-- Struct with a `Vector`-valued field — the `MulIncomplete.Output {xA, yA, zs}` analogue
(and the shape any vector-valued Output, e.g. Sinsemilla, will hit). Its derived
`ProvableStruct.components` spells the vector field's `M` as `fields n`, which the literal
simproc reads to decompose through the field for which a raw `Eval` synthesis has no `M`. -/
structure VecStruct (n : ℕ) (F : Type) where
  head : F
  rest : Vector F n
deriving ProvableStruct

-- 1. Plain `ProvableType` (`Point`) literal decomposition, consumed by a row fact:
-- the whole-struct eval equation splits field-wise and discharges the projected goal.
example (env : Placed Environment Fp) (a b : AssignedCell Fp) (out : Point Fp)
    (h : eval env (⟨a, b⟩ : Point (AssignedCell Fp)) = out) :
    eval env a = out.x := by
  provable_type_simp
  exact h.1

-- 2. Two-level struct decomposes along component boundaries and keeps `Point` WHOLE: the
-- literal decomposes to `⟨eval env p, eval env q⟩` with the `Point` components *un*-flattened.
-- The equality closes only because both sides carry the identical Point-level `eval env p`
-- (had the LHS flattened to field reads it would not match the RHS).
example (env : Placed Environment Fp) (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : TwoPoints (AssignedCell Fp)) = ⟨eval env p, eval env q⟩ := by
  provable_type_simp

-- 3. Plain `ProvableType` drilled into: a projection under `eval` lifts to the row level and
-- the row fact discharges it.
example (env : Placed Environment Fp) (v : Point (AssignedCell Fp)) (out : Point Fp)
    (h : eval env v = out) :
    eval env v.x = out.x := by
  provable_type_simp
  exact h.1

-- 4. Opaque `eval = eval` between two structs is a row-level fact: left folded, as `eval`
-- (NOT flattened to `ProvableType.eval`). `provable_type_simp` is intentionally a no-op here
-- — that no-op is the assertion that the opaque value keeps the `eval` normal form.
set_option linter.unusedTactic false in
example (env : Placed Environment Fp) (u v : Point (AssignedCell Fp))
    (h : eval env u = eval env v) :
    eval env u = eval env v := by
  provable_type_simp
  exact h

-- 5. Constructor-equality of values splits field-wise (verifier side).
example (a b c d : AssignedCell Fp) (env : Placed Environment Fp)
    (h : eval env (⟨a, b⟩ : Point (AssignedCell Fp)) = eval env (⟨c, d⟩ : Point (AssignedCell Fp))) :
    eval env a = eval env c := by
  provable_type_simp
  exact h.1

/-! ### Vector-valued struct fields (`Output.zs` analogue)

A `ProvableStruct` literal with a `Vector (AssignedCell F) n` field decomposes through the
vector field: the plain `Eval` synthesis cannot recover `M = fields n` from the raw `Vector`
type, so the literal simproc reads the component's `M` off the derived `components` list. Before
the fix the whole literal stayed folded as `ProvableStruct.eval …` (the `MulIncomplete`
`output_eval_fields` hand-lemma existed only to work around that). -/

-- 5a. The vector-field literal decomposes to the record of per-field evals; the vector field
-- becomes a folded per-field `Eval.eval` (`Value (fields n)`, i.e. `Vector F n`), never a bailed
-- whole-struct `ProvableStruct.eval` atom.
example (env : Placed Environment Fp) (a : AssignedCell Fp) (v : Vector (AssignedCell Fp) 3) :
    eval env (⟨a, v⟩ : VecStruct 3 (AssignedCell Fp))
      = ⟨eval env a, Eval.eval (Var := (fields 3) (AssignedCell Fp)) env v⟩ := by
  provable_type_simp

-- 5b. The decomposition makes the non-vector field consumable through the record split (both
-- sides literals so the constructor equality splits field-wise, incl. across the vector field).
example (env : Placed Environment Fp) (a a' : AssignedCell Fp) (v v' : Vector (AssignedCell Fp) 3)
    (h : eval env (⟨a, v⟩ : VecStruct 3 (AssignedCell Fp))
        = eval env (⟨a', v'⟩ : VecStruct 3 (AssignedCell Fp))) :
    eval env a = eval env a' := by
  provable_type_simp
  exact h.1

-- 5c. Prover-view (`Placed ProverEnvironment`) literal decomposes too.
example (env : Placed ProverEnvironment Fp) (a a' : AssignedCell Fp)
    (v v' : Vector (AssignedCell Fp) 3)
    (h : eval env (⟨a, v⟩ : VecStruct 3 (AssignedCell Fp))
        = eval env (⟨a', v'⟩ : VecStruct 3 (AssignedCell Fp))) :
    eval env a = eval env a' := by
  provable_type_simp
  exact h.1

-- 5d. An *opaque* struct eval (an `eval` of a variable, not a literal) with a vector field stays
-- folded — `provable_type_simp` is a no-op, the assertion that the confluence restriction
-- (literal-only decomposition) still holds through the vector-field path.
set_option linter.unusedTactic false in
example (env : Placed Environment Fp) (u w : VecStruct 3 (AssignedCell Fp))
    (h : eval env u = eval env w) :
    eval env u = eval env w := by
  provable_type_simp
  exact h

/-! ### Vector-component equation forming (the split's vector case)

When `structEqSplit` splits a provable-struct value equation, a vector (`fields n`) component
bottoms out at a whole-vector equation `Eval.eval env ⟨cells⟩ = output_vec`. `provable_type_simp`'s
vector-equation pass forms the per-index fact, in the **atom-left** orientation
`∀ i hi, <cell i> = output_vec[i]`, its per-index LHS resolved to a single cell read via the lazy
`getElem_eval_fields_cells` bridge. (The end-to-end auto-forming inside a full split is exercised by
the `MulIncomplete`/`HashPiece`/`MulComplete` bundle proofs; these pins fix the two load-bearing
pieces in isolation: the lazy getElem bridge and the atom-left orientation, both input orientations.)

The lazy `getElem` bridge: `(eval env v)[i]` on a `fields n` vector of cells reduces to the single
cell read, on demand — the vector counterpart of `evalProjectionLift`. The whole-vector map form
stays folded (never a `circuit_norm` member). -/

open Halo2.ProvableType in
-- 6a. The lazy getElem bridge fires under `circuit_norm`: `(eval env vec)[i]` resolves to one
-- `Environment.advice` cell read (verifier view). No eager whole-vector map.
example (self : RegionIndex) (env : Placed Environment Fp) (col : Column .advice) (i : ℕ) (hi : i < 3) :
    (Eval.eval (Var := (fields 3) (AssignedCell Fp)) env
        (Vector.ofFn (fun j : Fin 3 => AssignedCell.of self (7 + j.val) col)))[i]'hi
      = env.env.advice col ((env.place self + (7 + i) : ℕ) : ℤ) := by
  simp only [circuit_norm]

-- 6b. Prover view of the lazy getElem bridge, landing on the `.toEnvironment` read.
example (self : RegionIndex) (env : Placed ProverEnvironment Fp) (col : Column .advice)
    (i : ℕ) (hi : i < 3) :
    (Eval.eval (Var := (fields 3) (AssignedCell Fp)) env
        (Vector.ofFn (fun j : Fin 3 => AssignedCell.of self (7 + j.val) col)))[i]'hi
      = env.env.toEnvironment.advice col ((env.place self + (7 + i) : ℕ) : ℤ) := by
  simp only [circuit_norm]

-- 6c. Atom-left orientation of the formed fact: from a whole-vector equation `eval ⟨cells⟩ = v`
-- (either orientation), the per-index fact reads `<cell i> = v[i]` (cell atom on the LEFT), so a
-- consuming `simp only [·]` rewrites cell reads toward the value variable.
example (self : RegionIndex) (env : Placed Environment Fp) (col : Column .advice)
    (output_vec : Vector Fp 3)
    (h : Eval.eval (Var := (fields 3) (AssignedCell Fp)) env
        (Vector.ofFn (fun j : Fin 3 => AssignedCell.of self (7 + j.val) col)) = output_vec) :
    ∀ (i : ℕ) (hi : i < 3),
      env.env.advice col ((env.place self + (7 + i) : ℕ) : ℤ) = output_vec[i] := by
  intro i hi
  -- the atom-left per-index fact: `<cell i> = output_vec[i]`, LHS reduced via the lazy bridge
  have := congrArg (fun w => w[i]'hi) h
  simpa only [circuit_norm] using this

/-! ### Named-cell / typed-read normal form ("pretty cells")

The `circuit_norm` normal form for circuit-created cells and environment reads: assign/copy
outputs are the *named* `AssignedCell.of` (never an anonymous record literal), and every
typed read — gate query, assigned-cell eval, witness read — lands on the
`Environment.advice`-family accessors with the `↑(place self + row)` row form. The
`guard_hyp … :ₛ` assertions are syntactic: they fail if record literals
(`{ kind := … }`, `{ regionIndex := … }`) ever leak back into the normal form. -/

-- 6. The assign/copy output is the named cell, kept folded.
example (col : Column .advice) (self : RegionIndex) (row : ℕ) (compute : WitgenIR Fp 1) :
    (assignAdvice (F := Fp) col row compute).output self = .of self row col := by
  simp only [circuit_norm]

-- 7. An `assignAdvice` output under `eval` normalizes to a typed `env.advice` read —
-- syntactically (`guard_hyp :ₛ`): no cell/column record literals, row spelled
-- `↑(place self + row)`. (`provable_type_simp` doing nothing on top asserts the terminal
-- form is stable under it.)
set_option linter.unusedTactic false in
example (env : Placed Environment Fp) (col : Column .advice) (self : RegionIndex)
    (row : ℕ) (compute : WitgenIR Fp 1) (out : Fp)
    (h : eval env ((assignAdvice col row compute).output self) = out) :
    env.env.advice col ((env.place self + row : ℕ) : ℤ) = out := by
  simp only [circuit_norm] at h
  provable_type_simp
  guard_hyp h :ₛ env.env.advice col ((env.place self + row : ℕ) : ℤ) = out
  exact h

-- 8. The gate-query path meets the assigned-cell path on the same `env.advice` spelling:
-- after `circuit_norm` (rotation 0 cleared by `add_zero`) both sides are the SAME atom,
-- so simp closes the equality by rfl.
example (env : Environment Fp) (col : Column .advice) (sel : ℕ → Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (row : ℕ) :
    Query.eval env sel ((place self + row : ℕ) : ℤ) (.advice col 0)
      = AssignedCell.eval place env (.of self row col) := by
  simp only [circuit_norm]

-- 9. The witness-read path (witgen `readVar`) also lands on `env.advice` for named cells.
set_option linter.unusedVariables false in
example (pe : Placed ProverEnvironment Fp) (col : Column .advice) (self : RegionIndex)
    (row : ℕ) (out : Fp)
    (h : Witgen.WitgenEnv.readVar pe (AssignedCell.of self row col : AssignedCell Fp) = out) :
    True := by
  simp only [circuit_norm] at h
  guard_hyp h :ₛ pe.env.toEnvironment.advice col ((pe.place self + row : ℕ) : ℤ) = out
  trivial

/-! ### Record-eval decomposition under an opaque predicate (C2a #3 root-cause pin)

The `rw`-vs-`simp` finding (`Mul.lean` "Composition ergonomics" #2): whole-record eval bridges
(`hiInputs_eval_eq : eval env ⟨…⟩ = {…}`) fire under `rw` (defeq unification) but NOT under
`simp only [that_lemma]` on an iff-produced term, because the discr-tree key includes the
`Eval`/`CircuitType` instance, whose spelling differs between the locally-elaborated lemma LHS
and the instance threaded through `FormalRegionCircuit.Spec`. The `structEvalLiteral` simproc
sidesteps this: it keys only on the `eval` HEAD and recomputes each field's instance, validating
by `.all` defeq — so `provable_type_simp` decomposes the record-eval regardless of the instance
spelling, even when the result must feed an opaque predicate (the iff-produced consumption site).
This pin asserts the simproc fires there; it is the mechanized replacement for the hand `rw`. -/
example (env : Placed Environment Fp) (a b : AssignedCell Fp)
    (P : Value Point Fp → Prop)
    (h : P { x := eval env a, y := eval env b }) :
    P (eval env (⟨a, b⟩ : Point (AssignedCell Fp))) := by
  provable_type_simp
  exact h

end Halo2.ProvableTypeSimp.Test
