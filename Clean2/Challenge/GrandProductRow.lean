/-
A grand product, row by row: the multiplicative counterpart of `LogUpRow`.

- `ProductRow`: one row multiplies the accumulator by `(α - a) / (α - v)`. A pointwise spec, no
  soundness cost; the honest prover assumes `α ≠ v` (completeness).
- `ProductLoop`: `n` rows, from `1`.
- `PermutationRow`: the product, minus one, at a boundary: `∏ (X - a i) / (X - v i) - 1 ≡ 0`, so
  `a` and `v` are the same multiset. Soundness error `n`, completeness error `n`.
-/
module

public import Clean2.Challenge.LogUpRow
public import Clean2.Challenge.Permutation

@[expose] public section

namespace Clean2
open Polynomial

namespace ProductRow
variable {F : Type} [Field F]

/-- Multiply `acc` by `(α - a) / (α - v)`. -/
@[reducible]
def interface : Interface F where
  input := ((F × F) × F) × F
  inputCType := ((.native ×ᵗ .native) ×ᵗ .native) ×ᵗ .native
  output := F
  outputCType := .native
  Spec := fun (((v, a), acc), α) out => α ≠ v ∧ out = acc * ((α - a) / (α - v))

variable {B : Backend} [Field B.Native]

/-- The honest prover divides by `α - v`: it is stuck if the challenge hits `v`. -/
def event (v α : B.Var) : RareEvent B where
  committed := #v[v]
  challenge := α
  Bad := fun c a => a = c[0]
  bound := 1
  encard_bad_le := fun c => by simp

variable (arith : ∀ n, Impl B (Arith.interface n)) (inverse : Impl B Inverse.interface)

def impl : Impl B interface where
  main | (((v, a), acc), α) => do
    let δ ← arith .sub (α, v)
    let d ← inverse δ
    let num ← arith .sub (α, a)
    let q ← arith .mul (num, d)
    Circuit.assumeRareHonest (event v α)
    arith .mul (acc, q)
  spatial := by
    intro (((v, a), acc), α) s h
    obtain ⟨⟨⟨h_v, h_m⟩, h_acc⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left fun h =>
      (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm, Set.union_subset_iff] at h_v h_m h_acc h_α ⊢
    spatial_split
  soundness := by
    intro s env (((v, a), acc), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_δ, ⟨h_ne, h_d⟩, h_num, h_q, h_out⟩ := h
    refine ⟨fun h_eq => h_ne (by rw [h_δ, h_eq, sub_self]), ?_⟩
    rw [h_out, h_q, h_num, h_d, h_δ, div_eq_mul_inv]
  completeness := by
    intro s env (((v, a), acc), α) h _
    simp only [circuit_norm, event] at h ⊢
    obtain ⟨h_δ, -, -, -, h_ev, -⟩ := h
    rw [h_δ, sub_ne_zero]
    simpa using h_ev

end ProductRow

namespace ProductLoop
variable {F : Type} [Field F]

/-- `∏ (α - a i) / (α - v i)`, and the challenge avoids every `v i`. -/
@[reducible]
def interface (n : ℕ) : Interface F where
  input := (Vector F n × Vector F n) × F
  inputCType := (.natives n ×ᵗ .natives n) ×ᵗ .native
  output := F
  outputCType := .native
  Spec := fun ((v, a), α) out => (∀ i : Fin n, α ≠ v[i]) ∧ out = ∏ i : Fin n, (α - a[i]) / (α - v[i])

variable {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n))
  (row : Impl B ProductRow.interface)

section Loop
variable (α : B.Var) (n : ℕ) (v m : Fin n → B.Var) (z : B.Var)

/-- The rows, from `z`. -/
@[reducible, circuit_norm]
def loop : Circuit B B.Var := Circuit.foldr n (fun i acc => row (((v i, m i), acc), α)) z

theorem loop_consistent (s : B.State) : ((loop row α n v m z).operations s).Consistent s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm]
    exact ih _ _ s

theorem loop_sound (s : B.State) (env : B.Cell → B.Native)
    (h : ((loop row α n v m z).operations s).SoundnessHold env s) :
    (∀ i, B.eval env α ≠ B.eval env (v i)) ∧
      B.eval env ((loop row α n v m z).output s) =
        B.eval env z * ∏ i, (B.eval env α - B.eval env (m i)) / (B.eval env α - B.eval env (v i)) := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]; simp
  | succ n ih =>
    simp only [circuit_norm] at h ih ⊢
    obtain ⟨h_loop, h_ne0, h_out⟩ := h
    obtain ⟨h_ne, h_acc⟩ := ih (fun i => v i.succ) (fun i => m i.succ) s h_loop
    refine ⟨Fin.cases h_ne0 h_ne, ?_⟩
    rw [h_out, h_acc, Fin.prod_univ_succ]
    ring

/-- What the honest prover knows: the same running product. -/
theorem loop_honest (s : B.State) (env : B.Cell → B.Native)
    (h : ((loop row α n v m z).operations s).HonestCompleteness env s) :
    (∀ i, B.eval env α ≠ B.eval env (v i)) ∧
      B.eval env ((loop row α n v m z).output s) =
        B.eval env z * ∏ i, (B.eval env α - B.eval env (m i)) / (B.eval env α - B.eval env (v i)) := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]; simp
  | succ n ih =>
    simp only [circuit_norm] at h ih ⊢
    obtain ⟨h_loop, h_ne0, h_out⟩ := h
    obtain ⟨h_ne, h_acc⟩ := ih (fun i => v i.succ) (fun i => m i.succ) s h_loop
    refine ⟨Fin.cases h_ne0 h_ne, ?_⟩
    rw [h_out, h_acc, Fin.prod_univ_succ]
    ring

theorem loop_complete (s : B.State) (env : B.Cell → B.Native) :
    ((loop row α n v m z).operations s).CompletenessHold env s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm] at ih ⊢
    exact ih _ _ s

theorem loop_local (s : B.State) (K : B.State → Prop)
    (h_α : B.footprint α ⊆ B.Alloc s) (h_v : ∀ i, B.footprint (v i) ⊆ B.Alloc s)
    (h_m : ∀ i, B.footprint (m i) ⊆ B.Alloc s) (h_z : B.footprint z ⊆ B.Alloc s)
    (h_K : B.footprint ((loop row α n v m z).output s) ⊆
        B.Alloc (((loop row α n v m z).operations s).advance s) →
      K (((loop row α n v m z).operations s).advance s)) :
    ((loop row α n v m z).operations s).LocalHold s K := by
  induction n generalizing s K with
  | zero =>
    simp only [circuit_norm] at h_K ⊢
    exact h_K h_z
  | succ n ih =>
    have h_v' : ∀ i : Fin n, B.footprint (v i.succ) ⊆ B.Alloc s := fun i => h_v i.succ
    have h_m' : ∀ i : Fin n, B.footprint (m i.succ) ⊆ B.Alloc s := fun i => h_m i.succ
    have hc := loop_consistent row α n (fun i => v i.succ) (fun i => m i.succ) z s
    have h_post := (Ops.local_of_localHold hc
      (ih (fun i => v i.succ) (fun i => m i.succ) s
        (fun s' => B.footprint ((loop row α n (fun i => v i.succ) (fun i => m i.succ) z).output s) ⊆ B.Alloc s')
        h_α h_v' h_m' h_z id)).2
    have h_mono := Ops.alloc_mono hc
    have h_v0 := h_v 0
    have h_m0 := h_m 0
    simp only [circuit_norm] at h_K hc h_post h_mono ⊢
    rw [Ops.localHold_append_of_consistent hc]
    refine ih _ _ s _ h_α h_v' h_m' h_z fun _ => ?_
    simp only [circuit_norm]
    refine ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
      ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_native_subset.mpr (h_v0.trans h_mono),
        Backend.footprintT_native_subset.mpr (h_m0.trans h_mono)⟩, Backend.footprintT_native_subset.mpr h_post⟩,
      Backend.footprintT_native_subset.mpr (h_α.trans h_mono)⟩, fun h_out _ => h_K h_out⟩

end Loop

/-- `n` rows, from `1`. Generic over the row. -/
def impl (n : ℕ) : Impl B (interface n) where
  main | ((v, m), α) => do
    let one ← arith (.const 1) ()
    loop row α n (fun i => v[i]) (fun i => m[i]) one
  consistent := by
    intro ((v, m), α) s
    simp only [circuit_norm]
    exact loop_consistent row α n _ _ _ _
  spatial := by
    intro ((v, m), α) s h
    obtain ⟨⟨h_v, h_m⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    have h_v : ∀ i : Fin n, B.footprint v[i] ⊆ B.Alloc s := fun i => Backend.footprint_getElem_subset h_v i i.isLt
    have h_m : ∀ i : Fin n, B.footprint m[i] ⊆ B.Alloc s := fun i => Backend.footprint_getElem_subset h_m i i.isLt
    simp only [circuit_norm] at h_α ⊢
    refine ⟨Set.empty_subset _, fun h_zero h_mono => ?_⟩
    exact loop_local row α n _ _ _ _ _ (h_α.trans h_mono) (fun i => (h_v i).trans h_mono)
      (fun i => (h_m i).trans h_mono) h_zero id
  soundness := by
    intro s env ((v, m), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_one, h_loop⟩ := h
    obtain ⟨h_ne, h_prod⟩ := loop_sound row α n (fun i => v[i]) (fun i => m[i]) _ _ env h_loop
    simp only [circuit_norm] at h_ne h_prod
    refine ⟨fun i => by simpa using h_ne i, ?_⟩
    rw [h_prod, h_one, one_mul]
    simp
  completeness := by
    intro s env ((v, m), α) h _
    simp only [circuit_norm] at h ⊢
    exact loop_complete row α n _ _ _ _ env

end ProductLoop


namespace PermutationRow
open Permutation
variable {F : Type} [Field F]

/-- `b` is a permutation of `a`. -/
@[reducible]
def interface (n : ℕ) : Interface F where
  input := (Vector F n × Vector F n) × F
  inputCType := (.natives n ×ᵗ .natives n) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun ((a, b), _) _ => elems a = elems b
  ProverAssumptions := fun ((a, b), _) => elems a = elems b

/-- What the final product, minus one, stands for, in the committed values `b ++ a`. -/
noncomputable def R (n : ℕ) (c : Vector F (n + n)) : RatFunc F :=
  ∏ i : Fin n, (RatFunc.X - RatFunc.C c[Fin.natAdd n i]) / (RatFunc.X - RatFunc.C c[Fin.castAdd n i]) - 1

theorem R_append {n : ℕ} (b a : Vector F n) :
    R n (b ++ a) = ∏ i : Fin n, (RatFunc.X - RatFunc.C a[i]) / (RatFunc.X - RatFunc.C b[i]) - 1 := by
  simp [R]

variable {B : Backend} [Field B.Native] {n : ℕ} (arith : ∀ n, Impl B (Arith.interface n))
  (prod : Impl B (ProductLoop.interface n)) (boundary : Impl B (AssertIdentity.interface (n + n) n (R n)))

theorem represents_prod {α p : B.Native} {a b : Vector B.Native n} (h_ne : ∀ i : Fin n, α ≠ b[i])
    (h_p : p = ∏ i : Fin n, (α - a[i]) / (α - b[i])) : p - 1 ≙[α] R n (b ++ a) := by
  rw [R_append, h_p]
  exact (Represents.prod _ fun i _ => (Represents.X.sub (Represents.const _)).div
    (Represents.X.sub (Represents.const _)) (sub_ne_zero.mpr (h_ne i))).sub (Represents.const 1) |>.congr (by simp)

theorem R_eq_zero_iff (a b : Vector B.Native n) : R n (b ++ a) = 0 ↔ elems a = elems b := by
  rw [R_append, sub_eq_zero, Finset.prod_div_distrib,
    div_eq_one_iff_eq (RatFunc.prod_X_sub_C_ne_zero fun i => b[i])]
  exact ⟨elems_eq_of_prod_eq, fun h => prod_eq_of_elems_eq h (fun x => RatFunc.X - RatFunc.C x)⟩

/-- The running product, and a boundary. -/
noncomputable def impl : Impl B (interface n) where
  main | ((a, b), α) => do
    let p ← prod ((b, a), α)
    let one ← arith (.const 1) ()
    let x ← arith .sub (p, one)
    boundary ((b ++ a, x), α)
  spatial := by
    intro ((a, b), α) s h
    obtain ⟨⟨h_a, h_b⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm] at h_α ⊢
    refine ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨h_b, h_a⟩,
      Backend.footprintT_native_subset.mpr h_α⟩, fun h_p m₁ => ⟨Set.empty_subset _, fun h_one m₂ =>
        ⟨Set.union_subset (h_p.trans m₂) h_one, fun h_x m₃ => ⟨?_, fun _ _ => Set.empty_subset _⟩⟩⟩⟩
    have m := m₁.trans (m₂.trans m₃)
    exact Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
      ⟨Backend.footprintT_append_subset (h_b.trans m) (h_a.trans m), Backend.footprintT_native_subset.mpr h_x⟩,
      Backend.footprintT_native_subset.mpr (h_α.trans m)⟩
  soundness := by
    intro s env ((a, b), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨⟨h_ne, h_p⟩, h_one, h_x, h_boundary⟩ := h
    rw [Vector.map_append] at h_boundary
    have h_R := h_boundary ⟨by rw [h_x, h_one]; exact represents_prod h_ne h_p,
      by rw [R_append]; exact NumDegLE.prod_div_sub_one _ _⟩
    exact (R_eq_zero_iff _ _).mp h_R
  completeness := by
    intro s env ((a, b), α) h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    obtain ⟨⟨h_ne, h_p⟩, h_one, h_x, -⟩ := h
    rw [Vector.map_append, h_x, h_one]
    exact ⟨represents_prod h_ne h_p, (R_eq_zero_iff _ _).mpr h_prover⟩

end PermutationRow
end Clean2
