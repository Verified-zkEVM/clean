/-
A grand product, row by row: the multiplicative counterpart of `LogUpRow`.

- `ProductRow`: one row multiplies the accumulator by `(α - a) / (α - v)`. A pointwise spec, no
  soundness cost; the honest prover assumes `α ≠ v` (completeness).
- `ProductLoop`: `n` rows, from `1`.
- `PermutationCheck`: the product, minus one, at a boundary: `∏ (X - a i) / (X - v i) - 1 ≡ 0`, so
  `a` and `v` are the same multiset. Soundness error `n`, completeness error `n`.

As for logUp, the values are native and the challenge lives in the challenge field `K`.
-/
module

public import Clean2.Challenge.LogUp

@[expose] public section

namespace Clean2
open Polynomial

namespace ProductRow
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Multiply `acc` by `(α - a) / (α - v)`. -/
@[reducible]
def interface (kty : CType F K) : Interface F where
  input := ((F × F) × K) × K
  inputCType := ((.native ×ᵗ .native) ×ᵗ kty) ×ᵗ kty
  output := K
  outputCType := kty
  Spec := fun (((v, a), acc), α) out => α ≠ algebraMap F K v ∧
    out = acc * ((α - algebraMap F K a) / (α - algebraMap F K v))

/-- `v` is committed. -/
@[reducible]
def phases (kty : CType F K) : (interface kty).Phases where
  Committed := F
  committed := fun (((v, _), _), _) => v
  Challenge := K
  challenge := fun (_, α) => α

variable {B : Backend} [Field B.Native] [Algebra B.Native K] (kty : CType B.Native K) [kty.Faithful]

/-- The honest prover divides by `α - v`: it is stuck if the challenge hits `v`. -/
def event (v : B.Var) (α : kty.Shape B.Var) : RareEvent B :=
  .ofType kty #v[v] α (fun c a => a = algebraMap B.Native K c[0]) 1 fun c => by simp

variable (karith : ∀ n, Impl B (KArith.interface kty n))

def impl : Impl B (interface kty) where
  main | (((v, a), acc), α) => do
    let vK ← karith .embed v
    let aK ← karith .embed a
    let δ ← karith .sub (α, vK)
    let d ← karith .inv δ
    let num ← karith .sub (α, aK)
    let q ← karith .mul (num, d)
    Circuit.assumeRareHonest (event kty v α)
    karith .mul (acc, q)
  spatial := by
    intro (((v, a), acc), α) s h
    obtain ⟨⟨⟨h_v, h_m⟩, h_acc⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left fun h =>
      (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm, Set.union_subset_iff] at h_v h_m h_acc h_α ⊢
    spatial_split
  soundness := by
    intro s env (((v, a), acc), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_vK, h_aK, h_δ, ⟨h_ne, h_d⟩, h_num, h_q, h_out⟩ := h
    refine ⟨fun h_eq => h_ne (by rw [h_δ, h_vK, h_eq, sub_self]), ?_⟩
    rw [h_out, h_q, h_num, h_d, h_δ, h_vK, h_aK, div_eq_mul_inv]
  completeness := by
    intro s env (((v, a), acc), α) h _
    simp only [circuit_norm, event] at h ⊢
    obtain ⟨h_vK, -, h_δ, -, -, -, h_ev, -⟩ := h
    rw [h_δ, h_vK, sub_ne_zero]
    simpa using h_ev

instance [∀ n, Impl.NoEvents (karith n)] : Impl.Phased (impl kty karith) (phases kty) := by
  phased [impl, event]

end ProductRow

namespace ProductLoop
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `∏ (α - a i) / (α - v i)`, and the challenge avoids every `v i`. -/
@[reducible]
def interface (kty : CType F K) (n : ℕ) : Interface F where
  input := (Vector F n × Vector F n) × K
  inputCType := (.natives n ×ᵗ .natives n) ×ᵗ kty
  output := K
  outputCType := kty
  Spec := fun ((v, a), α) out => (∀ i : Fin n, α ≠ algebraMap F K v[i]) ∧
    out = ∏ i : Fin n, (α - algebraMap F K a[i]) / (α - algebraMap F K v[i])

/-- The denominators `v` are committed. -/
@[reducible]
def phases (kty : CType F K) (n : ℕ) : (interface kty n).Phases where
  Committed := Vector F n
  committed := fun ((v, _), _) => v
  Challenge := K
  challenge := fun (_, α) => α

variable {B : Backend} [Field B.Native] [Algebra B.Native K] (kty : CType B.Native K) [kty.Faithful]
  (karith : ∀ n, Impl B (KArith.interface kty n)) (row : Impl B (ProductRow.interface kty))

local notation "ι" => algebraMap B.Native K

section Loop
variable (α : kty.Shape B.Var) (n : ℕ) (v m : Fin n → B.Var) (z : kty.Shape B.Var)

/-- The rows, from `z`. -/
@[reducible, circuit_norm]
def loop : Circuit B (kty.Shape B.Var) := Circuit.foldr n (fun i acc => row (((v i, m i), acc), α)) z

omit [kty.Faithful] in
theorem loop_consistent (s : B.State) : ((loop kty row α n v m z).operations s).Consistent s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm]
    exact ih _ _ s

theorem loop_sound (s : B.State) (env : B.Cell → B.Native)
    (h : ((loop kty row α n v m z).operations s).SoundnessHold env s) :
    (∀ i, kty.decode (B.evalT env α) ≠ ι (B.eval env (v i))) ∧
      kty.decode (B.evalT env ((loop kty row α n v m z).output s)) =
        kty.decode (B.evalT env z) * ∏ i, (kty.decode (B.evalT env α) - ι (B.eval env (m i))) /
          (kty.decode (B.evalT env α) - ι (B.eval env (v i))) := by
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
    ((loop kty row α n v m z).operations s).CompletenessHold env s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm] at ih ⊢
    exact ih _ _ s

omit [kty.Faithful] in
theorem loop_local (s : B.State) (K : B.State → Prop)
    (h_α : B.footprintT α ⊆ B.Alloc s) (h_v : ∀ i, B.footprint (v i) ⊆ B.Alloc s)
    (h_m : ∀ i, B.footprint (m i) ⊆ B.Alloc s) (h_z : B.footprintT z ⊆ B.Alloc s)
    (h_K : B.footprintT ((loop kty row α n v m z).output s) ⊆
        B.Alloc (((loop kty row α n v m z).operations s).advance s) →
      K (((loop kty row α n v m z).operations s).advance s)) :
    ((loop kty row α n v m z).operations s).LocalHold s K := by
  induction n generalizing s K with
  | zero =>
    simp only [circuit_norm] at h_K ⊢
    exact h_K h_z
  | succ n ih =>
    have h_v' : ∀ i : Fin n, B.footprint (v i.succ) ⊆ B.Alloc s := fun i => h_v i.succ
    have h_m' : ∀ i : Fin n, B.footprint (m i.succ) ⊆ B.Alloc s := fun i => h_m i.succ
    have hc := loop_consistent kty row α n (fun i => v i.succ) (fun i => m i.succ) z s
    have h_post := (Ops.local_of_localHold hc
      (ih (fun i => v i.succ) (fun i => m i.succ) s
        (fun s' => B.footprintT ((loop kty row α n (fun i => v i.succ) (fun i => m i.succ) z).output s) ⊆ B.Alloc s')
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
        Backend.footprintT_native_subset.mpr (h_m0.trans h_mono)⟩, h_post⟩,
      h_α.trans h_mono⟩, fun h_out _ => h_K h_out⟩

end Loop

/-- `n` rows, from `1`. Generic over the row. -/
def impl (n : ℕ) : Impl B (interface kty n) where
  main | ((v, m), α) => do
    let one ← karith (.const 1) ()
    loop kty row α n (fun i => v[i]) (fun i => m[i]) one
  consistent := by
    intro ((v, m), α) s
    simp only [circuit_norm]
    exact loop_consistent kty row α n _ _ _ _
  spatial := by
    intro ((v, m), α) s h
    obtain ⟨⟨h_v, h_m⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    have h_v : ∀ i : Fin n, B.footprint v[i] ⊆ B.Alloc s := fun i => Backend.footprint_getElem_subset h_v i i.isLt
    have h_m : ∀ i : Fin n, B.footprint m[i] ⊆ B.Alloc s := fun i => Backend.footprint_getElem_subset h_m i i.isLt
    simp only [circuit_norm]
    refine ⟨Set.empty_subset _, fun h_one h_mono => ?_⟩
    exact loop_local kty row α n _ _ _ _ _ (h_α.trans h_mono) (fun i => (h_v i).trans h_mono)
      (fun i => (h_m i).trans h_mono) h_one id
  soundness := by
    intro s env ((v, m), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_one, h_loop⟩ := h
    obtain ⟨h_ne, h_prod⟩ := loop_sound kty row α n (fun i => v[i]) (fun i => m[i]) _ _ env h_loop
    simp only [circuit_norm] at h_ne h_prod
    refine ⟨fun i => by simpa using h_ne i, ?_⟩
    rw [h_prod, h_one, one_mul]
    simp
  completeness := by
    intro s env ((v, m), α) h _
    simp only [circuit_norm] at h ⊢
    exact loop_complete kty row α n _ _ _ _ env

instance (n : ℕ) [∀ n, Impl.NoEvents (karith n)] [Impl.Phased row (ProductRow.phases kty)] :
    Impl.Phased (impl kty karith row n) (phases kty n) := by
  phased [impl]

end ProductLoop

namespace PermutationCheck
open Permutation
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `b` is a permutation of `a`. -/
@[reducible]
def contract (n : ℕ) : Interface F where
  input := Vector F n × Vector F n
  inputCType := .natives n ×ᵗ .natives n
  output := Unit
  outputCType := .unit
  Spec := fun (a, b) _ => elems a = elems b
  ProverAssumptions := fun (a, b) => elems a = elems b

/-- The check, given a challenge: both sides are committed. -/
@[reducible]
def interface (kty : CType F K) (n : ℕ) : Interface F := (contract n).withChallenge kty

@[reducible]
def phases (kty : CType F K) (n : ℕ) : (interface kty n).Phases := Interface.withChallenge.phases _ _

variable (K) in
/-- What the final product, minus one, stands for, in the committed values `b ++ a`. -/
noncomputable def R (n : ℕ) (c : Vector F (n + n)) : RatFunc K :=
  ∏ i : Fin n, (RatFunc.X - RatFunc.C (algebraMap F K c[Fin.natAdd n i])) /
    (RatFunc.X - RatFunc.C (algebraMap F K c[Fin.castAdd n i])) - 1

theorem R_append {n : ℕ} (b a : Vector F n) :
    R K n (b ++ a) = ∏ i : Fin n, (RatFunc.X - RatFunc.C (algebraMap F K a[i])) /
      (RatFunc.X - RatFunc.C (algebraMap F K b[i])) - 1 := by
  simp [R]

variable {B : Backend} [Field B.Native] [Algebra B.Native K] {kty : CType B.Native K} [kty.Faithful] {n : ℕ}
  (karith : ∀ n, Impl B (KArith.interface kty n))
  (prod : Impl B (ProductLoop.interface kty n)) (boundary : Impl B (AssertIdentity.interface kty (n + n) n (R K n)))

local notation "ι" => algebraMap B.Native K

theorem represents_prod {α p : K} {a b : Vector B.Native n} (h_ne : ∀ i : Fin n, α ≠ ι b[i])
    (h_p : p = ∏ i : Fin n, (α - ι a[i]) / (α - ι b[i])) : p - 1 ≙[α] R K n (b ++ a) := by
  rw [R_append, h_p]
  exact (Represents.prod _ fun i _ => (Represents.X.sub (Represents.const _)).div
    (Represents.X.sub (Represents.const _)) (sub_ne_zero.mpr (h_ne i))).sub (Represents.const 1) |>.congr (by simp)

theorem R_eq_zero_iff (a b : Vector B.Native n) : R K n (b ++ a) = 0 ↔ elems a = elems b := by
  rw [R_append, sub_eq_zero, Finset.prod_div_distrib,
    div_eq_one_iff_eq (RatFunc.prod_X_sub_C_ne_zero fun i => ι b[i]),
    ← elems_map_eq_iff (algebraMap B.Native K).injective]
  have ha : ∀ i : Fin n, ι a[i] = (a.map ι)[i] := fun i => by simp
  have hb : ∀ i : Fin n, ι b[i] = (b.map ι)[i] := fun i => by simp
  simp only [ha, hb]
  exact ⟨elems_eq_of_prod_eq, fun h => prod_eq_of_elems_eq h (fun x => RatFunc.X - RatFunc.C x)⟩

/-- The running product, and a boundary. -/
noncomputable def impl : Impl B (interface kty n) where
  main | ((a, b), α) => do
    let p ← prod ((b, a), α)
    let one ← karith (.const 1) ()
    let x ← karith .sub (p, one)
    boundary ((b ++ a, x), α)
  spatial := by
    intro ((a, b), α) s h
    obtain ⟨⟨h_a, h_b⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    refine ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨h_b, h_a⟩,
      h_α⟩, fun h_p m₁ => ⟨Set.empty_subset _, fun h_one m₂ =>
        ⟨Set.union_subset (h_p.trans m₂) h_one, fun h_x m₃ => ⟨?_, fun _ _ => Set.empty_subset _⟩⟩⟩⟩
    have m := m₁.trans (m₂.trans m₃)
    exact Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
      ⟨Backend.footprintT_append_subset (h_b.trans m) (h_a.trans m), h_x⟩, h_α.trans m⟩
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

instance [∀ n, Impl.NoEvents (karith n)] [Impl.Phased prod (ProductLoop.phases kty n)]
    [Impl.Phased boundary (AssertIdentity.phases _ _ _ _)] : Impl.Phased (impl karith prod boundary) (phases kty n) := by
  phased [impl]

end PermutationCheck
end Clean2
