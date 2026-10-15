/-
Challenges in an extension field, from a basis.

When the native field `F` is small (BabyBear, Goldilocks, Mersenne-31), a challenge in `F` is not
enough: a soundness error of `deg / |F|` is useless. The challenge, and everything computed from
it, then lives in an extension `K` of `F` of degree `d`, laid out as its `d` coordinates in a
basis `b` (`basisType b`). This file implements the arithmetic of `K` that the protocols use
(`KArith.interface`) from native arithmetic alone:

- `+`, `-`, scaling by a native value, constants, embedding: coordinate by coordinate, linear;
- `*`: the `d²` products of coordinates, then `d` linear combinations with the structure
  constants of `b` (`Mix`): `d²` multiplications;
- inverse: witness the coordinates of `x⁻¹`, check `x * y - 1 = 0`;
- assert zero: every coordinate.

Nothing here knows about challenges: the protocols are written once against `KArith.interface`,
and run on `K = F` (`KArith.native`) or on an extension (`KArith.ofBasis`). The error bounds are
numbers of bad values of `K`: with `|K| = |F|^d`, the same bound is a much smaller probability.
-/
module

public import Clean2.Challenge.Field
public import Clean2.Challenge.Basic
public import Clean2.Gadgets.Mix
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public noncomputable section

namespace Clean2
open Module

namespace KArith
variable {F K : Type} [Field F] [Field K] [Algebra F K] {d : ℕ}

/-! ## The layout: coordinates in a basis -/

/-- `K`, laid out as its coordinates in the basis `b`. -/
@[reducible]
def basisType (b : Basis (Fin d) F K) : CType F K :=
  (CType.natives d).map fun v => b.equivFun.symm fun i => v[i]

instance (b : Basis (Fin d) F K) : (basisType b).Faithful where
  valid _ := trivial
  injective x y h := by
    have h' := congrFun (b.equivFun.symm.injective h)
    ext i hi
    exact h' ⟨i, hi⟩

/-! ## The algebra of coordinates -/

section Algebra
variable (b : Basis (Fin d) F K)

/-- The structure constants of `b`: the `k`-th coordinate of `b i * b j`. -/
def mulCoeff (k : Fin d) (ij : Fin (d * d)) : F :=
  b.equivFun (b (finProdFinEquiv.symm ij).1 * b (finProdFinEquiv.symm ij).2) k

/-- The coordinates of a product: bilinear in the coordinates of the factors. -/
theorem equivFun_mul (x y : Fin d → F) (k : Fin d) :
    b.equivFun (b.equivFun.symm x * b.equivFun.symm y) k =
      ∑ ij : Fin (d * d), mulCoeff b k ij *
        (x (finProdFinEquiv.symm ij).1 * y (finProdFinEquiv.symm ij).2) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [mulCoeff, Equiv.symm_apply_apply, Basis.equivFun_symm_apply, Finset.sum_mul_sum,
    smul_mul_smul_comm, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem equivFun_algebraMap (v : F) (i : Fin d) :
    b.equivFun (algebraMap F K v) i = b.equivFun 1 i * v := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end Algebra

/-! ## The arithmetic -/

section Impls
variable {B : Backend} [Field B.Native] [Algebra B.Native K] (b : Basis (Fin d) B.Native K)
  (arith : ∀ n, Impl B (Arith.interface n))

local notation "kty" => basisType b

/-- The meaning of a layout, as a function of its values. -/
theorem decode_eq (env : B.Cell → B.Native) (x : Vector B.Var d) :
    (basisType b).decode (B.evalT (M := (basisType b).Shape) env x) =
      b.equivFun.symm fun i => B.eval env x[i] := by
  simp [circuit_norm]

/-- Embed a native value: its coordinates are those of `1`, scaled. -/
def basisEmbed : Impl B (embed kty) where
  main v := Circuit.mapFin d fun i => arith (.scale (b.equivFun 1 i)) v
  consistent := by
    intro v s
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro v s h_in
    simp only [circuit_norm] at h_in ⊢
    exact Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
      (fun i s h_mono => by simp only [circuit_norm]; exact ⟨h_in.trans h_mono, fun h_post _ => h_post⟩) id
  soundness := by
    intro s env v _ h
    simp only [circuit_norm] at h ⊢
    have hz := Circuit.mapFin_sound _ s env (fun i z => z = b.equivFun 1 i * B.eval env v)
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h
    apply b.equivFun.injective
    ext i
    simp only [Function.comp_def, LinearEquiv.apply_symm_apply, equivFun_algebraMap]
    simp only [Fin.getElem_fin, Vector.getElem_map]
    exact hz i i.isLt
  completeness := by
    intro s env v h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h

/-- Read the meaning of a layout off its coordinates. -/
theorem symm_coords (z : Vector B.Native d) (f : Fin d → B.Native) (h : ∀ (i : ℕ) (hi : i < d), z[i] = f ⟨i, hi⟩) :
    (b.equivFun.symm fun i => z[i]) = b.equivFun.symm f := by
  congr 1
  funext i
  exact h i i.isLt

def basisAdd : Impl B (add kty) where
  main | (x, y) => Circuit.mapFin d fun i => arith .add (x[i], y[i])
  consistent := by
    intro (x, y) s
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro (x, y) s h_in
    simp only [circuit_norm, Set.union_subset_iff] at h_in ⊢
    exact Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
      (fun i s h_mono => by
        simp only [circuit_norm, Set.union_subset_iff]
        exact ⟨⟨(Backend.footprint_getElem_subset h_in.1 i i.isLt).trans h_mono,
          (Backend.footprint_getElem_subset h_in.2 i i.isLt).trans h_mono⟩, fun h_post _ => h_post⟩) id
  soundness := by
    intro s env (x, y) _ h
    simp only [circuit_norm] at h ⊢
    have hz := Circuit.mapFin_sound _ s env (fun i z => z = B.eval env x[i] + B.eval env y[i])
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h
    simp only [Function.comp_def, ← map_add]
    exact symm_coords b _ _ fun i hi => by simpa using hz i hi
  completeness := by
    intro s env (x, y) h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h

def basisSub : Impl B (sub kty) where
  main | (x, y) => Circuit.mapFin d fun i => arith .sub (x[i], y[i])
  consistent := by
    intro (x, y) s
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro (x, y) s h_in
    simp only [circuit_norm, Set.union_subset_iff] at h_in ⊢
    exact Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
      (fun i s h_mono => by
        simp only [circuit_norm, Set.union_subset_iff]
        exact ⟨⟨(Backend.footprint_getElem_subset h_in.1 i i.isLt).trans h_mono,
          (Backend.footprint_getElem_subset h_in.2 i i.isLt).trans h_mono⟩, fun h_post _ => h_post⟩) id
  soundness := by
    intro s env (x, y) _ h
    simp only [circuit_norm] at h ⊢
    have hz := Circuit.mapFin_sound _ s env (fun i z => z = B.eval env x[i] - B.eval env y[i])
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h
    simp only [Function.comp_def, ← map_sub]
    exact symm_coords b _ _ fun i hi => by simpa using hz i hi
  completeness := by
    intro s env (x, y) h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h

/-- Scale by a native value: every coordinate. -/
def basisSmul : Impl B (smul kty) where
  main | (v, x) => Circuit.mapFin d fun i => arith .mul (v, x[i])
  consistent := by
    intro (v, x) s
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro (v, x) s h_in
    simp only [circuit_norm, Set.union_subset_iff] at h_in ⊢
    exact Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
      (fun i s h_mono => by
        simp only [circuit_norm, Set.union_subset_iff]
        exact ⟨⟨h_in.1.trans h_mono,
          (Backend.footprint_getElem_subset h_in.2 i i.isLt).trans h_mono⟩, fun h_post _ => h_post⟩) id
  soundness := by
    intro s env (v, x) _ h
    simp only [circuit_norm] at h ⊢
    have hz := Circuit.mapFin_sound _ s env (fun i z => z = B.eval env v * B.eval env x[i])
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h
    simp only [Function.comp_def, ← Algebra.smul_def, ← map_smul]
    exact symm_coords b _ _ fun i hi => by simpa using hz i hi
  completeness := by
    intro s env (v, x) h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h

/-- A constant: its coordinates. -/
def basisConst (c : K) : Impl B (const kty c) where
  main _ := Circuit.mapFin d fun i => arith (.const (b.equivFun c i)) ()
  consistent := by
    intro _ s
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro _ s h_in
    simp only [circuit_norm] at h_in ⊢
    exact Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
      (fun i s h_mono => by simp only [circuit_norm]; exact ⟨Set.empty_subset _, fun h_post _ => h_post⟩) id
  soundness := by
    intro s env _ _ h
    simp only [circuit_norm] at h ⊢
    have hz := Circuit.mapFin_sound _ s env (fun i z => z = b.equivFun c i)
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h
    simp only [Function.comp_def]
    rw [symm_coords b _ (b.equivFun c) fun i hi => by simpa using hz i hi, LinearEquiv.symm_apply_apply]
  completeness := by
    intro s env _ h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h

/-- Multiply: the `d²` products of coordinates, then one linear combination per coordinate, with
the structure constants of `b`. -/
def basisMul : Impl B (mul kty) where
  main | (x, y) => do
    let p ← Circuit.mapFin (d * d) fun ij =>
      arith .mul (x[(finProdFinEquiv.symm ij).1], y[(finProdFinEquiv.symm ij).2])
    Circuit.mapFin d fun k => Mix.impl arith ⟨d * d, mulCoeff b k⟩ p
  consistent := by
    intro (x, y) s
    simp only [circuit_norm]
    exact ⟨Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm],
      Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]⟩
  spatial := by
    intro (x, y) s h_in
    simp only [circuit_norm, Set.union_subset_iff] at h_in ⊢
    rw [Ops.localHold_append_of_consistent]
    · refine Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
        (fun ij s h_mono => ?_) fun h_p => ?_
      · simp only [circuit_norm, Set.union_subset_iff]
        exact ⟨⟨(Backend.footprint_getElem_subset h_in.1 _ (finProdFinEquiv.symm ij).1.isLt).trans h_mono,
          (Backend.footprint_getElem_subset h_in.2 _ (finProdFinEquiv.symm ij).2.isLt).trans h_mono⟩,
          fun h_post _ => h_post⟩
      · exact Circuit.mapFin_local _ _ _ (fun k s => by simp only [circuit_norm])
          (fun k s h_mono => by simp only [circuit_norm]; exact ⟨h_p.trans h_mono, fun h_post _ => h_post⟩) id
    · exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  soundness := by
    intro s env (x, y) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h₁, h₂⟩ := h
    have hp := Circuit.mapFin_sound _ s env
      (fun ij z => z = B.eval env x[(finProdFinEquiv.symm ij).1] * B.eval env y[(finProdFinEquiv.symm ij).2])
      (fun ij s h => by simp only [circuit_norm] at h ⊢; exact h) h₁
    have hz := Circuit.mapFin_sound _ _ env
      (fun k z => z = ∑ ij : Fin (d * d), mulCoeff b k ij *
        (B.eval env x[(finProdFinEquiv.symm ij).1] * B.eval env y[(finProdFinEquiv.symm ij).2]))
      (fun k s h => by
        simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h ⊢
        rw [h]
        exact Finset.sum_congr rfl fun ij _ => congrArg _ (hp ij ij.isLt)) h₂
    simp only [Function.comp_def]
    apply b.equivFun.injective
    ext k
    rw [LinearEquiv.apply_symm_apply, equivFun_mul]
    simpa using hz k k.isLt
  completeness := by
    intro s env (x, y) h _
    simp only [circuit_norm] at h ⊢
    exact ⟨Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h.1,
      Circuit.mapFin_complete _ _ env (fun k s h => by simp only [circuit_norm] at h ⊢) h.2⟩

/-- Assert zero: every coordinate. -/
def basisAssertZero : Impl B (assertZero kty) where
  main x := Circuit.foldr (α := Unit) d (fun i _ => arith .assertZero x[i]) ()
  consistent := by
    intro x s
    exact Circuit.foldr_consistent _ _ _ fun i acc s => by simp only [circuit_norm]
  spatial := by
    intro x s h_in
    simp only [circuit_norm] at h_in ⊢
    refine Circuit.foldr_local (M := unit) _ _ _ _ (fun i acc s => by simp only [circuit_norm])
      (fun i acc s h_mono _ => ?_) (by simp only [circuit_norm]; exact Set.empty_subset _)
      fun _ => by simp only [circuit_norm]; exact Set.empty_subset _
    simp only [circuit_norm]
    exact ⟨(Backend.footprint_getElem_subset h_in i i.isLt).trans h_mono, fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    have hz := Circuit.foldr_sound _ _ s env
      (fun i _ => ∀ j : Fin d, i ≤ (j : ℕ) → B.eval env x[j] = 0)
      (fun j hj => absurd hj (by omega))
      (fun i _ s h_inv h => by
        simp only [circuit_norm] at h
        intro j hj
        rcases Nat.lt_or_eq_of_le hj with hj | hj
        · exact h_inv j hj
        · rw [show j = i from Fin.ext hj.symm]; exact h) h
    simp only [Function.comp_def]
    rw [symm_coords b _ 0 fun i hi => by simpa using hz ⟨i, hi⟩ (Nat.zero_le _), map_zero]
  completeness := by
    intro s env x h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    have h0 : ∀ i : Fin d, B.eval env x[i] = 0 := by
      have h' : (fun i : Fin d => (Vector.map (B.eval env) x)[i]) = 0 :=
        b.equivFun.symm.injective (by rw [map_zero]; simpa [Function.comp_def] using h_prover)
      intro i
      simpa using congrFun h' i
    exact Circuit.foldr_complete _ _ _ env (fun i acc s _ => by simp only [circuit_norm]; exact h0 i) h

/-- Invert: witness the coordinates of `x⁻¹`, check `x * y - 1 = 0`. -/
def basisInv : Impl B (inv kty) where
  main x := do
    let y ← Circuit.mapFin d fun i =>
      arith (.witness (natives d) fun v => b.equivFun ((basisType b).decode v)⁻¹ i) x
    let p ← basisMul b arith (x, y)
    let one ← basisConst b arith 1 ()
    let δ ← basisSub b arith (p, one)
    basisAssertZero b arith δ
    return y
  consistent := by
    intro x s
    simp only [circuit_norm]
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro x s h_in
    simp only [circuit_norm] at h_in ⊢
    rw [Ops.localHold_append_of_consistent]
    · refine Circuit.mapFin_local _ _ _ (fun i s => by simp only [circuit_norm])
        (fun i s h_mono => by simp only [circuit_norm]; exact ⟨h_in.trans h_mono, fun h_post _ => h_post⟩)
        fun h_y => ?_
      have h_mono := Ops.alloc_mono (Circuit.mapFin_consistent
        (fun i => arith (.witness (natives d) fun v => b.equivFun ((basisType b).decode v)⁻¹ i) x) s
        fun i s => by simp only [circuit_norm])
      simp only [circuit_norm, Set.union_subset_iff] at h_y h_mono ⊢
      spatial_split
    · exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨-, h_p, h_one, h_δ, h_zero⟩ := h
    rw [h_δ, h_p, h_one, sub_eq_zero] at h_zero
    exact ⟨left_ne_zero_of_mul_eq_one h_zero, (eq_inv_of_mul_eq_one_right h_zero)⟩
  completeness := by
    intro s env x h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    obtain ⟨h_y, h_p, h_one, h_δ⟩ := h
    have hy := Circuit.mapFin_honest _ s env
      (fun i z => z = b.equivFun (b.equivFun.symm fun i => (Vector.map (B.eval env) x)[i])⁻¹ i)
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h_y
    have h_inv : (b.equivFun.symm fun i => (Vector.map (B.eval env) ((Circuit.mapFin d fun i =>
        arith (.witness (natives d) fun v => b.equivFun ((basisType b).decode v)⁻¹ i) x).output s))[i]) =
        (b.equivFun.symm fun i => (Vector.map (B.eval env) x)[i])⁻¹ := by
      rw [symm_coords b _ _ fun i hi => by rw [Vector.getElem_map]; exact hy i hi, LinearEquiv.symm_apply_apply]
    simp only [Function.comp_def] at h_prover h_p h_one h_δ h_inv ⊢
    refine ⟨⟨Circuit.mapFin_complete _ _ env (fun i s h => by simp only [circuit_norm] at h ⊢) h_y, ?_⟩, h_inv⟩
    rw [h_δ, h_p, h_one, h_inv, mul_inv_cancel₀ h_prover, sub_self]

/-- The arithmetic of `K`, from a basis of `K` over the native field and native arithmetic. -/
def ofBasis : ∀ n, Impl B (interface kty n)
  | .embed => basisEmbed b arith
  | .add => basisAdd b arith
  | .sub => basisSub b arith
  | .mul => basisMul b arith
  | .smul => basisSmul b arith
  | .inv => basisInv b arith
  | .assertZero => basisAssertZero b arith
  | .const c => basisConst b arith c

section NoEvents
variable [∀ n, Impl.NoEvents (arith n)]

instance (q : Mix.Params B.Native) : Impl.NoEvents (Mix.impl arith q) := by no_events [Mix.impl]
instance : Impl.NoEvents (basisEmbed b arith) := by no_events [basisEmbed]
instance : Impl.NoEvents (basisAdd b arith) := by no_events [basisAdd]
instance : Impl.NoEvents (basisSub b arith) := by no_events [basisSub]
instance : Impl.NoEvents (basisSmul b arith) := by no_events [basisSmul]
instance : Impl.NoEvents (basisMul b arith) := by no_events [basisMul]
instance (c : K) : Impl.NoEvents (basisConst b arith c) := by no_events [basisConst]
instance : Impl.NoEvents (basisAssertZero b arith) := by no_events [basisAssertZero]
instance : Impl.NoEvents (basisInv b arith) := by no_events [basisInv]

instance (n : Name B.Native K) : Impl.NoEvents (ofBasis b arith n) := by
  cases n
  · exact inferInstanceAs (Impl.NoEvents (basisEmbed b arith))
  · exact inferInstanceAs (Impl.NoEvents (basisAdd b arith))
  · exact inferInstanceAs (Impl.NoEvents (basisSub b arith))
  · exact inferInstanceAs (Impl.NoEvents (basisMul b arith))
  · exact inferInstanceAs (Impl.NoEvents (basisSmul b arith))
  · exact inferInstanceAs (Impl.NoEvents (basisInv b arith))
  · exact inferInstanceAs (Impl.NoEvents (basisAssertZero b arith))
  · exact inferInstanceAs (Impl.NoEvents (basisConst b arith _))

end NoEvents

end Impls

end KArith
end Clean2
