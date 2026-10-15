/-
Structural properties of circuits: measures.

A *measure* is a monoid-valued function of native operations. Its value on a circuit is the sum
over the circuit's operations, so it is additive under sequencing, and every measure obeys the
same proof rules: an `_append` lemma, a rule per loop combinator, and a call rule that replaces
a subcircuit by a closed form recorded once for its implementation (`Impl.Measured`).

Examples: the cost of an R1CS circuit (cells, constraints), the number of rows of a plonkish
circuit, the set of gate shapes it uses, a bound on the steps of witness generation. Each is one
`Backend.Measure`; a gadget states its value under a measure by an `Impl.Measured` instance, and
a parent computes its own value from those of its children without unfolding them.

This is the pattern of `Impl.advance`/`advance_eq` and `Impl.output`/`output_eq`, generalized:
a closed form of a structural quantity, with a proof that it is what the circuit does.
-/
module

public import Clean2.Core.Formal
public import Clean2.Core.Loops
public import Lean.Elab.Tactic
meta import Clean2.Core.Spatial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section

namespace Clean2

/-- A structural property of a backend: a monoid-valued measure of its native operations, and of
the rare events a circuit assumes (zero by default). The measure of a circuit is the sum of the
measures of the operations it emits. -/
structure Backend.Measure (B : Backend) (M : Type) [AddCommMonoid M] where
  op : B.Op → M
  rare : RareEvent B → M := fun _ => 0
  rareHonest : RareEvent B → M := fun _ => 0

namespace Backend.Measure
variable {B : Backend} {M : Type} [AddCommMonoid M] (μ : B.Measure M)

/-- The measure of a flat list of native operations: the real semantics. -/
def flat : List B.Op → M
  | [] => 0
  | op :: ops => μ.op op + flat ops

theorem flat_append (a b : List B.Op) : μ.flat (a ++ b) = μ.flat a + μ.flat b := by
  induction a with
  | nil => simp [flat]
  | cons op ops ih => simp [flat, ih, add_assoc]

/-- The measure of the rare events of a circuit: those assumed for soundness and those assumed
by the honest prover. -/
def rares (evs hevs : List (RareEvent B)) : M := (evs.map μ.rare).sum + (hevs.map μ.rareHonest).sum

/-- The measure of operations, with a call contributing the measure of its (flattened) body and
of its rare events: the proof-level semantics. A parent never unfolds `sc.ops`: `Impl.flat_call`
replaces it by the closed form recorded for the callee. -/
@[circuit_norm]
def ofOps : Ops B → M
  | [] => 0
  | .native op :: ops => μ.op op + ofOps ops
  | .call sc :: ops => (μ.flat sc.ops + μ.rares sc.events sc.honestEvents) + ofOps ops
  | .rare ev :: ops => μ.rare ev + ofOps ops
  | .rareHonest ev :: ops => μ.rareHonest ev + ofOps ops

/-- The two semantics agree: the native operations, and the rare events. -/
theorem flat_toFlat (ops : Ops B) :
    μ.flat ops.toFlat + μ.rares ops.events ops.honestEvents = μ.ofOps ops := by
  induction ops with
  | nil => simp [Ops.toFlat, flat, rares, Ops.events, Ops.honestEvents, ofOps]
  | cons op ops ih =>
    simp only [rares] at ih ⊢
    cases op with
    | native op =>
      simp only [Ops.toFlat, flat, ofOps, Ops.events, Ops.honestEvents]
      rw [← ih]; abel
    | call sc =>
      simp only [Ops.toFlat, flat_append, ofOps, Ops.events, Ops.honestEvents, List.map_append, List.sum_append, rares]
      rw [← ih]; abel
    | rare ev =>
      simp only [Ops.toFlat, ofOps, Ops.events, Ops.honestEvents, List.map_cons, List.sum_cons]
      rw [← ih]; abel
    | rareHonest ev =>
      simp only [Ops.toFlat, ofOps, Ops.events, Ops.honestEvents, List.map_cons, List.sum_cons]
      rw [← ih]; abel

/-- A measure that ignores rare events sees only the native operations. -/
theorem flat_toFlat_of_rare_eq_zero (h : ∀ ev, μ.rare ev = 0) (h' : ∀ ev, μ.rareHonest ev = 0) (ops : Ops B) :
    μ.flat ops.toFlat = μ.ofOps ops := by
  have h0 : ∀ l : List (RareEvent B), (l.map μ.rare).sum = 0 := by
    intro l; induction l <;> simp_all
  have h0' : ∀ l : List (RareEvent B), (l.map μ.rareHonest).sum = 0 := by
    intro l; induction l <;> simp_all
  rw [← flat_toFlat, rares, h0, h0', add_zero, add_zero]

@[circuit_norm]
theorem ofOps_append (a b : Ops B) : μ.ofOps (a ++ b) = μ.ofOps a + μ.ofOps b := by
  induction a with
  | nil => simp [ofOps]
  | cons op ops ih => cases op <;> simp [ofOps, ih, add_assoc]

end Backend.Measure

/-! ### Loop rules: one per loop combinator, for every measure -/

namespace Circuit
variable {B : Backend} {M : Type} [AddCommMonoid M] (μ : B.Measure M)

/-- The measure of a `foldr` is the sum of the measures of its iterations. -/
theorem foldr_measure {α : Type} {n : ℕ} (f : Fin n → α → Circuit B α) (z : α) (m : Fin n → M)
    (h : ∀ i acc s, μ.ofOps ((f i acc).operations s) = m i) (s : B.State) :
    μ.ofOps ((foldr n f z).operations s) = ∑ i, m i := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm, Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    simp only [circuit_norm, Fin.sum_univ_succ]
    rw [h, ih (fun i => f i.succ) z (fun i => m i.succ) (fun i => h i.succ) s, add_comm]

/-- The measure of a `mapFin` is the sum of the measures of its iterations. -/
theorem mapFin_measure {α : Type} {n : ℕ} (f : Fin n → Circuit B α) (m : Fin n → M)
    (h : ∀ i s, μ.ofOps ((f i).operations s) = m i) (s : B.State) :
    μ.ofOps ((mapFin n f).operations s) = ∑ i, m i := by
  induction n generalizing s with
  | zero => simp only [circuit_norm, Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    simp only [circuit_norm, Fin.sum_univ_castSucc]
    rw [h, ih (fun i => f i.castSucc) (fun i => m i.castSucc) (fun i => h i.castSucc) s]

/-- A loop whose every iteration has the same measure `c` has measure `n • c`. -/
theorem foldr_measure_const {α : Type} {n : ℕ} (f : Fin n → α → Circuit B α) (z : α) (c : M)
    (h : ∀ i acc s, μ.ofOps ((f i acc).operations s) = c) (s : B.State) :
    μ.ofOps ((foldr n f z).operations s) = n • c := by
  rw [foldr_measure μ f z (fun _ => c) h s, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem mapFin_measure_const {α : Type} {n : ℕ} (f : Fin n → Circuit B α) (c : M)
    (h : ∀ i s, μ.ofOps ((f i).operations s) = c) (s : B.State) :
    μ.ofOps ((mapFin n f).operations s) = n • c := by
  rw [mapFin_measure μ f (fun _ => c) h s, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Circuit

/-! ### The closed form of a measure on an implementation -/

/--
Discharge `Impl.Measured.value_eq`: destructure the input, normalize the circuit (which turns
every call into the callee's recorded value), and sum. `measure [d₁, d₂]` also unfolds the
definitions `dᵢ`, for an instance stated outside the definition of the implementation.
-/
syntax "measure" (" [" term,* "]")? : tactic

meta section
open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| measure $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let lemmas ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    evalTactic (← `(tactic| intro input s))
    destructProds
    evalTactic (← `(tactic| (
      simp only [circuit_norm, zero_add, add_zero, add_assoc, $lemmas,*]
      try simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      try omega
      try abel)))
end

namespace Impl
variable {B : Backend} {M : Type} [AddCommMonoid M]

/-- `impl` has measure `value` under `μ`: whatever the input and the state, its operations
measure `value`. This is what a caller sees of a call; the callee's operations are never
unfolded. Stated as a class so that a parent's instance is found from its children's.

The value is a constant: circuit shapes do not depend on the input variables or on the
allocation state, only on compile-time parameters, which are parameters of `impl`. -/
class Measured (μ : B.Measure M) {c : Interface B.Native} (impl : Impl B c) where
  value : M
  value_eq : ∀ (input : c.Input B.Var) (s : B.State), μ.ofOps ((impl.main input).operations s) = value := by
    measure

/-- The measure of an implementation, by its `Measured` instance. -/
@[reducible]
def _root_.Clean2.Backend.Measure.of (μ : B.Measure M) {c : Interface B.Native} (impl : Impl B c)
    [inst : Measured μ impl] : M :=
  inst.value

/-- The call rule: the body of a call measures what its implementation is recorded to measure. -/
@[circuit_norm]
theorem flat_call (μ : B.Measure M) {c : Interface B.Native} (impl : Impl B c) [Measured μ impl]
    (s : B.State) (input : c.Input B.Var) :
    μ.flat (impl.toSubcircuit s input).ops +
      μ.rares (impl.toSubcircuit s input).events (impl.toSubcircuit s input).honestEvents = μ.of impl := by
  show μ.flat ((impl.main input).operations s).toFlat +
    μ.rares ((impl.main input).operations s).events ((impl.main input).operations s).honestEvents = _
  rw [Backend.Measure.flat_toFlat, Measured.value_eq]

/-- Refinement does not change the circuit. -/
instance (μ : B.Measure M) {c : Interface B.Native} (impl : Impl B c) [inst : Measured μ impl]
    {Assumptions : c.input → Prop} {Spec : c.input → c.output → Prop}
    {ProverAssumptions : c.input → Prop} {ProverSpec : c.input → c.output → Prop}
    (h : c.Refines Assumptions Spec ProverAssumptions ProverSpec) :
    Measured μ (impl.refine h) where
  value := inst.value
  value_eq := inst.value_eq

@[simp]
theorem of_refine (μ : B.Measure M) {c : Interface B.Native} (impl : Impl B c) [Measured μ impl]
    {Assumptions : c.input → Prop} {Spec : c.input → c.output → Prop}
    {ProverAssumptions : c.input → Prop} {ProverSpec : c.input → c.output → Prop}
    (h : c.Refines Assumptions Spec ProverAssumptions ProverSpec) :
    μ.of (impl.refine h) = μ.of impl := rfl

end Impl

end Clean2
