/-
Poseidon: one circuit, two backends.

The permutation is a loop over rounds, against a `Round.interface`; a round is what a backend
chooses to make of it:
- from arithmetic (`Round.ofArith`): an S-box per lane and a linear combination per lane, so
  that on R1CS a round costs `3 t` constraints and the mixing layer is free;
- from a custom gate (`Round.ofGate`): one placement of `roundGate` per round, so that on the
  plonkish backend a round costs one row. The round constants are the gate's fixed cells, so
  every round places the *same* gate and the configuration of the whole circuit is one gate.

`Poseidon.impl` is the same code and the same proofs in both cases; only the round passed in
differs. Full rounds only.
-/
module

public import Clean2.Backends.Plonkish
public import Clean2.Backends.R1CS
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

/-! ## Two small functionalities: an S-box lane, and a linear combination -/

namespace SBox

def sbox (x : F) : F := x ^ 5

/-- `x ↦ (x + c)^5`, the constant being the parameter. -/
@[reducible]
def interface (c : F) : Interface F where
  input := F
  inputCType := .native
  output := F
  outputCType := .native
  Spec := fun x y => y = sbox (x + c)

/-- Three multiplications. -/
def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) (c : B.Native) : Impl B (interface c) where
  main x := do
    let k ← arith (.const c) ()
    let a ← arith .add (x, k)
    let a2 ← arith .mul (a, a)
    let a4 ← arith .mul (a2, a2)
    arith .mul (a4, a)
  soundness := by
    intro s env x _ h
    simp only [circuit_norm, sbox] at h ⊢
    obtain ⟨hk, ha, h2, h4, h5⟩ := h
    rw [h5, h4, h2, ha, hk]
    ring
  completeness := by
    intro s env x _ _
    simp only [circuit_norm]

end SBox

namespace Mix

/-- The coefficients of a linear combination, over `t` inputs. -/
structure Params (F : Type) where
  t : ℕ
  m : Fin t → F

/-- `x ↦ ∑ i, m i * x[i]`. -/
@[reducible]
def interface (p : Params F) : Interface F where
  input := Vector F p.t
  inputCType := .natives p.t
  output := F
  outputCType := .native
  Spec := fun x y => y = ∑ i, p.m i * x[i]

/-- The tail sums `∑_{j ≥ i}`, one step: the loop invariant of `impl`. -/
theorem sum_tail_succ {t : ℕ} (f : Fin t → F) (i : Fin t) :
    (∑ j : Fin t, if (i : ℕ) ≤ j then f j else 0) =
      f i + ∑ j : Fin t, if (i : ℕ) + 1 ≤ j then f j else 0 := by
  have : ∀ j : Fin t, (if (i : ℕ) ≤ j then f j else 0) =
      (if j = i then f j else 0) + (if (i : ℕ) + 1 ≤ j then f j else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · have : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      by_cases hle : (i : ℕ) ≤ j
      · rw [if_pos hle, if_neg hj, if_pos (by omega), zero_add]
      · rw [if_neg hle, if_neg hj, if_neg (by omega), zero_add]
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i,
    if_pos (Finset.mem_univ _)]

/-- A loop of scalings and additions: linear, so free on R1CS. -/
def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) (p : Params B.Native) : Impl B (interface p) where
  main x := do
    let zero ← arith (.const 0) ()
    Circuit.foldr p.t (fun i acc => do
      let y ← arith (.scale (p.m i)) x[i]
      arith .add (acc, y)) zero
  consistent := by
    intro x s
    simp only [circuit_norm]
    exact Circuit.foldr_consistent _ _ _ fun i acc s => by simp only [circuit_norm]
  spatial := by
    intro x s h_in
    simp only [circuit_norm] at h_in ⊢
    refine ⟨Set.empty_subset _, fun h_zero h_mono => ?_⟩
    refine Circuit.foldr_local _ _ _ _ (fun i acc s => by simp only [circuit_norm])
      (fun i acc s h_mono' h_acc => ?_) (by rw [Backend.footprintT_native]; exact h_zero)
      fun h => by rw [Backend.footprintT_native] at h; exact h
    simp only [circuit_norm, Set.union_subset_iff] at h_acc ⊢
    exact ⟨(Backend.footprint_getElem_subset h_in i i.isLt).trans (h_mono.trans h_mono'),
      fun h_y h_mono'' => ⟨⟨h_acc.trans h_mono'', h_y⟩, fun h_out _ => h_out⟩⟩
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_zero, h_loop⟩ := h
    have := Circuit.foldr_sound _ _ _ env
      (fun i acc => B.eval env acc = ∑ j : Fin p.t, if i ≤ (j : ℕ) then p.m j * B.eval env x[j] else 0)
      ?_ ?_ h_loop
    · simp only [zero_le, if_true, Vector.getElem_map, Fin.getElem_fin] at this ⊢
      exact this
    · rw [h_zero]
      exact (Finset.sum_eq_zero fun j _ => if_neg (by have := j.isLt; omega)).symm
    · intro i acc s h_inv h_step
      simp only [circuit_norm] at h_step ⊢
      obtain ⟨h_y, h_add⟩ := h_step
      rw [h_add, h_y, h_inv, sum_tail_succ, Fin.getElem_fin]
      ring
  completeness := by
    intro s env x h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.foldr_complete _ _ _ env (fun i acc s h => by simp only [circuit_norm] at h ⊢) h.2

end Mix

/-! ## Poseidon -/

namespace Poseidon

/-- The parameters: the width, the number of rounds, the round constants and the MDS matrix. -/
structure Params (F : Type) where
  t : ℕ
  rounds : ℕ
  rc : ℕ → Vector F t
  mds : Fin t → Fin t → F

variable (p : Params F)

/-- One round with round constants `k`: add the constants, S-box every lane, mix. -/
def roundWith (k x : Vector F p.t) : Vector F p.t :=
  Vector.ofFn fun j => ∑ i, p.mds j i * SBox.sbox (x[i] + k[i])

def round (r : ℕ) (x : Vector F p.t) : Vector F p.t := roundWith p (p.rc r) x

/-- Rounds `0, …, m - 1`. -/
def iterate : ℕ → Vector F p.t → Vector F p.t
  | 0, x => x
  | m + 1, x => round p m (iterate m x)

def permutation (x : Vector F p.t) : Vector F p.t := iterate p p.rounds x

/-- Round `r`. -/
@[reducible]
def Round.interface (r : ℕ) : Interface F where
  input := Vector F p.t
  inputCType := .natives p.t
  output := Vector F p.t
  outputCType := .natives p.t
  Spec := fun x y => y = round p r x

/-- The permutation. -/
@[reducible]
def interface : Interface F where
  input := Vector F p.t
  inputCType := .natives p.t
  output := Vector F p.t
  outputCType := .natives p.t
  Spec := fun x y => y = permutation p x

section
variable {B : Backend} [Field B.Native] (p : Params B.Native)

/-- The permutation is a loop over the rounds, whatever a round is. -/
def impl (round : ∀ r, Impl B (Round.interface p r)) : Impl B (interface p) where
  main x := Circuit.foldr p.rounds (fun i acc => round (p.rounds - 1 - i) acc) x
  consistent := by
    intro x s
    simp only [circuit_norm]
    exact Circuit.foldr_consistent _ _ _ fun i acc s => by simp only [circuit_norm]
  spatial := by
    intro x s h_in
    simp only [circuit_norm] at h_in ⊢
    exact Circuit.foldr_local _ _ _ _ (fun i acc s => by simp only [circuit_norm])
      (fun i acc s _ h_acc => by simp only [circuit_norm]; exact ⟨h_acc, fun h_post _ => h_post⟩) h_in id
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    have := Circuit.foldr_sound _ x s env
      (fun i acc => B.evalT env acc = iterate p (p.rounds - i) (B.evalT env x)) ?_ ?_ h
    · simp only [Nat.sub_zero, circuit_norm] at this
      exact this
    · simp only [Nat.sub_self, iterate]
    · intro i acc s h_inv h_step
      simp only [circuit_norm] at h_inv h_step ⊢
      have hi := i.isLt
      rw [h_step, h_inv, show p.rounds - i = (p.rounds - 1 - i) + 1 by omega, iterate,
        show p.rounds - (i + 1) = p.rounds - 1 - i by omega]
  completeness := by
    intro s env x h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.foldr_complete _ _ _ env (fun i acc s h => by simp only [circuit_norm] at h ⊢) h

/-- A round from an S-box and a linear combination, each applied lane by lane. -/
def Round.ofLayers (sbox : ∀ c, Impl B (SBox.interface c)) (mix : ∀ q, Impl B (Mix.interface q)) (r : ℕ) :
    Impl B (Round.interface p r) where
  main x := do
    let a ← Circuit.mapFin p.t fun i => sbox (p.rc r)[i] x[i]
    Circuit.mapFin p.t fun j => mix ⟨p.t, p.mds j⟩ a
  consistent := by
    intro x s
    simp only [circuit_norm]
    exact ⟨Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm],
      Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]⟩
  spatial := by
    intro x s h_in
    simp only [circuit_norm] at h_in ⊢
    rw [Ops.localHold_append_of_consistent]
    · refine Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
        (fun i s h_mono => ?_) fun h_a => ?_
      · simp only [circuit_norm]
        exact ⟨(Backend.footprint_getElem_subset h_in i i.isLt).trans h_mono, fun h_post _ => h_post⟩
      · exact Circuit.mapFin_local _ _ _ (fun j s => by simp only [circuit_norm])
          (fun j s h_mono => by simp only [circuit_norm]; exact ⟨h_a.trans h_mono, fun h_post _ => h_post⟩) id
    · exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h₁, h₂⟩ := h
    have ha := Circuit.mapFin_sound _ s env (fun i v => v = SBox.sbox (B.eval env x[i] + (p.rc r)[i]))
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h₁
    simp only [Fin.getElem_fin] at ha
    have hb := Circuit.mapFin_sound _ _ env
      (fun j v => v = ∑ i : Fin p.t, p.mds j i * SBox.sbox (B.eval env x[i] + (p.rc r)[i]))
      (fun j s h => by
        simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h ⊢
        rw [h]
        exact Finset.sum_congr rfl fun i _ => by rw [ha i i.isLt]) h₂
    simp only [Fin.getElem_fin] at hb
    ext j hj
    simp only [Vector.getElem_map, round, roundWith, Vector.getElem_ofFn, Fin.getElem_fin]
    exact hb j hj
  completeness := by
    intro s env x h _
    simp only [circuit_norm] at h ⊢
    exact ⟨Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h.1,
      Circuit.mapFin_complete _ _ env (fun j s h => by simp only [circuit_norm] at h ⊢) h.2⟩

/-- A round from arithmetic alone. -/
def Round.ofArith (arith : ∀ n, Impl B (Arith.interface n)) (r : ℕ) : Impl B (Round.interface p r) :=
  Round.ofLayers p (SBox.impl arith) (Mix.impl arith) r

end

/-! ### The round as a gate -/

/-- The round gate: `t` inputs, `t` fixed cells holding the round constants, `t` outputs, and
the identities `y_j = ∑ i, mds j i * (x_i + k_i)^5`. The round constants are fixed cells, not
part of the gate, so one gate serves every round. Reducible, so that its shape is visible to
proofs about its identities. -/
@[reducible]
def roundGate : Gate F where
  nIn := p.t
  nFixed := p.t
  nOut := p.t
  polys := List.ofFn fun j : Fin p.t =>
    .output j - .sum (List.ofFn fun i : Fin p.t => .const (p.mds j i) * (.input i + .fixed i) ^ 5)
  witness x k := roundWith p k x

/-- The gate's identities say exactly that the outputs are the round of the inputs. -/
theorem roundGate_constraint (x k y : Vector F p.t) :
    (roundGate p).Constraint x k y ↔ y = roundWith p k x := by
  simp only [Gate.Constraint, roundGate, List.forall_mem_ofFn_iff, GateExpr.eval_hsub,
    GateExpr.eval_sum_ofFn, GateExpr.eval_hpow, GateExpr.eval, sub_eq_zero, roundWith, SBox.sbox,
    Fin.getElem_fin]
  constructor
  · intro h
    ext j hj
    simp only [Vector.getElem_ofFn]
    exact h ⟨j, hj⟩
  · rintro rfl j
    simp only [Vector.getElem_ofFn]

/-- The round, as one placement of the round gate. The gate's contract is its identities; the
round's contract is the round function; the difference is `roundGate_constraint`. -/
def Round.ofGate (r : ℕ) : Impl (Plonkish F) (Round.interface p r) :=
  (Plonkish.gate (roundGate p) (p.rc r)).refine
    { assumptions := fun _ _ => trivial
      spec := fun x y _ h => (roundGate_constraint p x _ y).mp h
      proverAssumptions := fun x _ => (roundGate_constraint p x _ _).mpr rfl
      proverSpec := fun _ _ _ _ => trivial }

/-! ## The same circuit on both backends -/

/-- Poseidon on R1CS: `3 t` constraints per round. -/
def r1cs : Impl (R1CS F) (interface p) := impl (B := R1CS F) p (Round.ofArith (B := R1CS F) p R1CS.arith)

/-- Poseidon on the plonkish backend, with the round gate: one row per round. -/
def plonkish : Impl (Plonkish F) (interface p) := impl (B := Plonkish F) p (Round.ofGate p)

/-- Poseidon on the plonkish backend, from arithmetic gates: the arithmetic round, on the
backend where nothing is free. The same round as `r1cs`, at another `arith`. -/
def plonkishArith : Impl (Plonkish F) (interface p) :=
  impl (B := Plonkish F) p (Round.ofArith (B := Plonkish F) p Plonkish.arith)

/-! ### Costs, and the configuration -/

/-- R1CS: `3 t` cells per round, the three multiplications of each S-box. The mixing layer and
the round constants are free. -/
theorem r1cs_advance (x : Vector (LinComb F) p.t) (s : ℕ) :
    (r1cs p).advance x s = s + p.rounds * (3 * p.t) := by
  refine (Circuit.foldr_advance (B := R1CS F) _ x (fun s : ℕ => s + 3 * p.t) (fun i acc s => ?_) s).trans
    (iterate_add_const _ _ _)
  simp only [circuit_norm]
  unfold Round.ofArith Round.ofLayers
  simp only [circuit_norm]
  refine (Circuit.mapFin_advance (B := R1CS F) _ id (fun j s => ?_) _).trans ?_
  · unfold Mix.impl
    simp only [circuit_norm]
    refine (Circuit.foldr_advance (B := R1CS F) _ _ id (fun i acc s => rfl) _).trans ?_
    rw [Function.iterate_id]
    rfl
  · rw [Function.iterate_id, id]
    exact (Circuit.mapFin_advance (B := R1CS F) _ (fun s : ℕ => s + 3) (fun i s => rfl) s).trans
      (by rw [iterate_add_const, Nat.mul_comm])

/-- Plonkish, with the round gate: one row per round. -/
theorem plonkish_advance (x : Vector (ℕ × ℕ) p.t) (s : ℕ) : (plonkish p).advance x s = s + p.rounds := by
  refine (Circuit.foldr_advance (B := Plonkish F) _ x (fun s : ℕ => s + 1) (fun i acc s => rfl) s).trans ?_
  rw [iterate_add_const, Nat.mul_one]

/-- Every operation of the gated circuit places the round gate. -/
theorem plonkish_shape (x : Vector (ℕ × ℕ) p.t) (s : ℕ) :
    ∀ op ∈ (((plonkish p).main x).operations s).toFlat, op.shape = (roundGate p).toGateShape :=
  Circuit.foldr_flat (B := Plonkish F) _ _ _ (fun i acc s op h => by
    have h' : op ∈ [PlonkishOp.gate (roundGate p) acc (p.rc (p.rounds - 1 - i))] := h
    obtain rfl := List.mem_singleton.mp h'
    rfl) s

/-- The configuration of the gated circuit, read off its operations: one gate. -/
theorem plonkish_config [DecidableEq F] (h : p.rounds ≠ 0) (x : Vector (ℕ × ℕ) p.t) (s : ℕ) :
    Plonkish.config (((plonkish p).main x).operations s).toFlat = [(roundGate p).toGateShape] := by
  have h_all : ∀ sh ∈ (((plonkish p).main x).operations s).toFlat.map PlonkishOp.shape,
      sh = (roundGate p).toGateShape := by
    intro sh hsh
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hsh
    exact plonkish_shape p x s op hop
  have h_len : (((plonkish p).main x).operations s).toFlat.length = p.rounds * 1 :=
    Circuit.foldr_flat_length (B := Plonkish F) _ x 1 (fun i acc s => rfl) s
  unfold Plonkish.config
  rw [List.eq_replicate_of_mem h_all, List.replicate_dedup]
  rw [List.length_map, h_len]
  omega


/-! ### Measures: the cost of the permutation, from the cost of a round -/

section
variable {B : Backend} [Field B.Native] {M : Type} [AddCommMonoid M] (μ : B.Measure M)

instance _root_.Clean2.SBox.measured (arith : ∀ n, Impl B (Arith.interface n)) [∀ n, Impl.Measured μ (arith n)]
    (c : B.Native) : Impl.Measured μ (SBox.impl arith c) where
  value := μ.of (arith (.const c)) + μ.of (arith .add) + 3 • μ.of (arith .mul)
  value_eq := by measure [SBox.impl]

instance _root_.Clean2.Mix.measured (arith : ∀ n, Impl B (Arith.interface n)) [∀ n, Impl.Measured μ (arith n)]
    (q : Mix.Params B.Native) : Impl.Measured μ (Mix.impl arith q) where
  value := μ.of (arith (.const 0)) + ∑ i : Fin q.t, (μ.of (arith (.scale (q.m i))) + μ.of (arith .add))
  value_eq := by
    intro x s
    simp only [Mix.impl, circuit_norm]
    rw [Circuit.foldr_measure μ _ _ (fun i => μ.of (arith (.scale (q.m i))) + μ.of (arith .add))
      (fun i acc s => by simp only [circuit_norm, add_zero])]

variable (p : Params B.Native)

instance Round.measured_ofLayers (sbox : ∀ c, Impl B (SBox.interface c)) (mix : ∀ q, Impl B (Mix.interface q))
    [∀ c, Impl.Measured μ (sbox c)] [∀ q, Impl.Measured μ (mix q)] (r : ℕ) :
    Impl.Measured μ (Round.ofLayers p sbox mix r) where
  value := (∑ i : Fin p.t, μ.of (sbox (p.rc r)[i])) + ∑ j : Fin p.t, μ.of (mix ⟨p.t, p.mds j⟩)
  value_eq := by
    intro x s
    simp only [Round.ofLayers, circuit_norm]
    rw [Circuit.mapFin_measure μ _ (fun i => μ.of (sbox (p.rc r)[i])) (fun i s => by simp only [circuit_norm, add_zero]),
      Circuit.mapFin_measure μ _ (fun j => μ.of (mix ⟨p.t, p.mds j⟩)) (fun j s => by simp only [circuit_norm, add_zero])]

instance Round.measured_ofArith (arith : ∀ n, Impl B (Arith.interface n)) [∀ n, Impl.Measured μ (arith n)] (r : ℕ) :
    Impl.Measured μ (Round.ofArith p arith r) :=
  inferInstanceAs (Impl.Measured μ (Round.ofLayers p (SBox.impl arith) (Mix.impl arith) r))

/-- The permutation measures the sum of its rounds. -/
instance measured_impl (round : ∀ r, Impl B (Round.interface p r)) [∀ r, Impl.Measured μ (round r)] :
    Impl.Measured μ (impl p round) where
  value := ∑ i : Fin p.rounds, μ.of (round (p.rounds - 1 - i))
  value_eq := by
    intro x s
    simp only [impl, circuit_norm]
    exact Circuit.foldr_measure μ _ _ _ (fun i acc s => by simp only [circuit_norm, add_zero]) s

end

instance Round.measured_ofGate (r : ℕ) : Impl.Measured Plonkish.rows (Round.ofGate p r) :=
  inferInstanceAs (Impl.Measured Plonkish.rows ((Plonkish.gate (roundGate p) (p.rc r)).refine _))

instance measured_r1cs : Impl.Measured R1CS.cost (r1cs p) :=
  inferInstanceAs (Impl.Measured R1CS.cost (impl (B := R1CS F) p (Round.ofArith (B := R1CS F) p R1CS.arith)))

instance measured_plonkish : Impl.Measured Plonkish.rows (plonkish p) :=
  inferInstanceAs (Impl.Measured Plonkish.rows (impl (B := Plonkish F) p (Round.ofGate p)))

instance measured_plonkishArith : Impl.Measured Plonkish.rows (plonkishArith p) :=
  inferInstanceAs (Impl.Measured Plonkish.rows (impl (B := Plonkish F) p (Round.ofArith (B := Plonkish F) p Plonkish.arith)))

/-! The closed forms. `Backend.Measure.of` unfolds to the instance's `value`, and `simp` reduces
the class projection through the (reducible) instances down to the vocabulary's costs. -/

/-- R1CS: `3 t` cells and `3 t` constraints per round, the three multiplications of each S-box.
The mixing layer and the round constants are free. -/
theorem r1cs_cost : R1CS.cost.of (r1cs p) = (p.rounds * (3 * p.t), p.rounds * (3 * p.t)) := by
  simp only [Backend.Measure.of, Impl.Measured.value, R1CS.cost_const, R1CS.cost_add, R1CS.cost_mul, R1CS.cost_scale,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul,
    Prod.mk.injEq, add_zero, mul_zero, mul_one]
  constructor <;> ring

/-- Plonkish, with the round gate: one row per round. -/
theorem plonkish_rows : Plonkish.rows.of (plonkish p) = p.rounds := by
  simp only [Backend.Measure.of, Impl.Measured.value, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

/-- Plonkish, from arithmetic gates: `(6 + 2 t) t` rows per round, nothing being free. -/
theorem plonkishArith_rows : Plonkish.rows.of (plonkishArith p) = p.rounds * ((6 + 2 * p.t) * p.t) := by
  simp only [Backend.Measure.of, Impl.Measured.value, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

end Poseidon
end Clean2
