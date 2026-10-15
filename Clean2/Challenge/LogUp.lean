/-
logUp, row by row: how a table circuit uses a challenge.

- `LogUpRow`: one row adds `m / (α - v)` to a running sum. An ordinary gadget with a pointwise spec,
  `out = acc + m / (α - v)`. Its constraint `d * (α - v) = 1` already rules out `α = v`, so it costs
  no soundness; the honest prover is stuck if `α = v`, a rare event it assumes (completeness).
- `LogUpSum`: `n` rows, from `0`: the running sum ends at `∑ m i / (α - v i)`.
- `Balance`: the running sum, and a boundary (`AssertIdentity`). The final sum stands for
  `∑ m i / (X - v i)`, which is zero at the challenge, so it is zero as a rational function:
  every value's multiplicities add up to zero. This is bus balance, as a theorem.
- `Lookup`: two running sums (the table side and the lookup side) on the same challenge, and one
  boundary for their difference.

The values `v` and `m` are native; the challenge, the running sum and the identity live in the
challenge field `K` (`Field.lean`): `F` itself, or an extension. User proofs are pointwise, plus
the symbolic step at the boundary (`Fractions.balance_iff_map`). Soundness error `n` (the
boundary), completeness error `n` (one per row), as numbers of bad values of `K`.
-/
module

public import Clean2.Challenge.AssertIdentity
public import Clean2.Challenge.Protocol
public import Clean2.Challenge.Fractions

@[expose] public section

namespace Clean2
open Polynomial

namespace LogUpRow
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Add `m / (α - v)` to `acc`. -/
@[reducible]
def interface (kty : CType F K) : Interface F where
  input := ((F × F) × K) × K
  inputCType := ((.native ×ᵗ .native) ×ᵗ kty) ×ᵗ kty
  output := K
  outputCType := kty
  Spec := fun (((v, m), acc), α) out =>
    α ≠ algebraMap F K v ∧ out = acc + algebraMap F K m / (α - algebraMap F K v)

/-- `v` is committed; `m` and `acc` need not be. -/
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
  main | (((v, m), acc), α) => do
    let vK ← karith .embed v
    let δ ← karith .sub (α, vK)
    let d ← karith .inv δ
    let md ← karith .smul (m, d)
    Circuit.assumeRareHonest (event kty v α)
    karith .add (acc, md)
  spatial := by
    intro (((v, m), acc), α) s h
    obtain ⟨⟨⟨h_v, h_m⟩, h_acc⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left fun h =>
      (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm, Set.union_subset_iff] at h_v h_m h_acc h_α ⊢
    spatial_split
  soundness := by
    intro s env (((v, m), acc), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_vK, h_δ, ⟨h_ne, h_d⟩, h_md, h_out⟩ := h
    refine ⟨fun h_eq => h_ne (by rw [h_δ, h_vK, h_eq, sub_self]), ?_⟩
    rw [h_out, h_md, h_d, h_δ, h_vK, div_eq_mul_inv]
  completeness := by
    intro s env (((v, m), acc), α) h _
    simp only [circuit_norm, event] at h ⊢
    obtain ⟨h_vK, h_δ, -, -, h_ev, -⟩ := h
    rw [h_δ, h_vK, sub_ne_zero]
    simpa using h_ev

instance [∀ n, Impl.NoEvents (karith n)] : Impl.Phased (impl kty karith) (phases kty) := by
  phased [impl, event]

end LogUpRow

namespace LogUpSum
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `∑ m i / (α - v i)`, and the challenge avoids every `v i`. -/
@[reducible]
def interface (kty : CType F K) (n : ℕ) : Interface F where
  input := (Vector F n × Vector F n) × K
  inputCType := (.natives n ×ᵗ .natives n) ×ᵗ kty
  output := K
  outputCType := kty
  Spec := fun ((v, m), α) out => (∀ i : Fin n, α ≠ algebraMap F K v[i]) ∧
    out = ∑ i : Fin n, algebraMap F K m[i] / (α - algebraMap F K v[i])

/-- The values `v` are committed; the multiplicities need not be. -/
@[reducible]
def phases (kty : CType F K) (n : ℕ) : (interface kty n).Phases where
  Committed := Vector F n
  committed := fun ((v, _), _) => v
  Challenge := K
  challenge := fun (_, α) => α

variable {B : Backend} [Field B.Native] [Algebra B.Native K] (kty : CType B.Native K) [kty.Faithful]
  (karith : ∀ n, Impl B (KArith.interface kty n)) (row : Impl B (LogUpRow.interface kty))

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
        kty.decode (B.evalT env z) +
          ∑ i, ι (B.eval env (m i)) / (kty.decode (B.evalT env α) - ι (B.eval env (v i))) := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]; simp
  | succ n ih =>
    simp only [circuit_norm] at h ih ⊢
    obtain ⟨h_loop, h_ne0, h_out⟩ := h
    obtain ⟨h_ne, h_acc⟩ := ih (fun i => v i.succ) (fun i => m i.succ) s h_loop
    refine ⟨Fin.cases h_ne0 h_ne, ?_⟩
    rw [h_out, h_acc, Fin.sum_univ_succ]
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

/-- `n` rows, from `0`. Generic over the row. -/
def impl (n : ℕ) : Impl B (interface kty n) where
  main | ((v, m), α) => do
    let zero ← karith (.const 0) ()
    loop kty row α n (fun i => v[i]) (fun i => m[i]) zero
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
    refine ⟨Set.empty_subset _, fun h_zero h_mono => ?_⟩
    exact loop_local kty row α n _ _ _ _ _ (h_α.trans h_mono) (fun i => (h_v i).trans h_mono)
      (fun i => (h_m i).trans h_mono) h_zero id
  soundness := by
    intro s env ((v, m), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_zero, h_loop⟩ := h
    obtain ⟨h_ne, h_sum⟩ := loop_sound kty row α n (fun i => v[i]) (fun i => m[i]) _ _ env h_loop
    simp only [circuit_norm] at h_ne h_sum
    refine ⟨fun i => by simpa using h_ne i, ?_⟩
    rw [h_sum, h_zero, zero_add]
    simp
  completeness := by
    intro s env ((v, m), α) h _
    simp only [circuit_norm] at h ⊢
    exact loop_complete kty row α n _ _ _ _ env

instance (n : ℕ) [∀ n, Impl.NoEvents (karith n)] [Impl.Phased row (LogUpRow.phases kty)] :
    Impl.Phased (impl kty karith row n) (phases kty n) := by
  phased [impl]

end LogUpSum

namespace Balance
open Fractions
variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- Every value's multiplicities add up to zero. -/
@[reducible]
def contract (n : ℕ) : Interface F where
  input := Vector F n × Vector F n
  inputCType := .natives n ×ᵗ .natives n
  output := Unit
  outputCType := .unit
  Spec := fun (v, m) _ => ∀ y, ∑ i ∈ Finset.univ.filter (fun i : Fin n => v[i] = y), m[i] = 0
  ProverAssumptions := fun (v, m) => ∀ y, ∑ i ∈ Finset.univ.filter (fun i : Fin n => v[i] = y), m[i] = 0

/-- The check, given a challenge: everything else is committed. -/
@[reducible]
def interface (kty : CType F K) (n : ℕ) : Interface F := (contract n).withChallenge kty

@[reducible]
def phases (kty : CType F K) (n : ℕ) : (interface kty n).Phases := Interface.withChallenge.phases _ _

omit [DecidableEq F] in
variable (K) in
/-- What the final sum stands for, in the committed values `v ++ m`: `∑ m i / (X - v i)`. -/
noncomputable def R (n : ℕ) (c : Vector F (n + n)) : RatFunc K :=
  ∑ i : Fin n, RatFunc.C (algebraMap F K c[Fin.natAdd n i]) / (RatFunc.X - RatFunc.C (algebraMap F K c[Fin.castAdd n i]))

omit [DecidableEq F] in
theorem R_append {n : ℕ} (v m : Vector F n) :
    R K n (v ++ m) = ∑ i : Fin n, RatFunc.C (algebraMap F K m[i]) / (RatFunc.X - RatFunc.C (algebraMap F K v[i])) := by
  simp [R]

variable {B : Backend} [Field B.Native] [DecidableEq B.Native] [Algebra B.Native K] {kty : CType B.Native K}
  [kty.Faithful] {n : ℕ}
  (sum : Impl B (LogUpSum.interface kty n)) (boundary : Impl B (AssertIdentity.interface kty (n + n) n (R K n)))

omit [DecidableEq B.Native] in
/-- The final sum stands for `∑ m i / (X - v i)`. -/
theorem represents_sum {α acc : K} {V M : Vector B.Native n} (h_ne : ∀ i : Fin n, α ≠ algebraMap B.Native K V[i])
    (h_acc : acc = ∑ i : Fin n, algebraMap B.Native K M[i] / (α - algebraMap B.Native K V[i])) :
    acc ≙[α] R K n (V ++ M) := by
  rw [R_append, h_acc]
  exact Represents.sum _ fun i _ =>
    (Represents.const _).div (Represents.X.sub (Represents.const _)) (sub_ne_zero.mpr (h_ne i))

/-- The running sum, and the boundary. Generic over both. -/
noncomputable def impl : Impl B (interface kty n) where
  main | ((v, m), α) => do
    let acc ← sum ((v, m), α)
    boundary ((v ++ m, acc), α)
  spatial := by
    intro ((v, m), α) s h
    obtain ⟨⟨h_v, h_m⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨h_v, h_m⟩, h_α⟩,
      fun h_acc h_mono => ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
        ⟨Backend.footprintT_append_subset (h_v.trans h_mono) (h_m.trans h_mono), h_acc⟩, h_α.trans h_mono⟩,
        fun _ _ => Set.empty_subset _⟩⟩
  soundness := by
    intro s env ((v, m), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨⟨h_ne, h_acc⟩, h_boundary⟩ := h
    rw [Vector.map_append] at h_boundary
    have h_R := h_boundary ⟨represents_sum h_ne h_acc, by rw [R_append]; exact NumDegLE.sum_div_X_sub_C _ _⟩
    rw [R_append] at h_R
    classical
    exact (balance_iff_map (fun i : Fin n => (Vector.map (B.eval env) v)[i])
      (fun i : Fin n => (Vector.map (B.eval env) m)[i])).mp h_R
  completeness := by
    intro s env ((v, m), α) h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    obtain ⟨⟨h_ne, h_acc⟩, -⟩ := h
    rw [Vector.map_append]
    refine ⟨represents_sum h_ne h_acc, ?_⟩
    rw [R_append]
    classical
    exact (balance_iff_map (fun i : Fin n => (Vector.map (B.eval env) v)[i])
      (fun i : Fin n => (Vector.map (B.eval env) m)[i])).mpr h_prover

instance [Impl.Phased sum (LogUpSum.phases kty n)] [Impl.Phased boundary (AssertIdentity.phases _ _ _ _)] :
    Impl.Phased (impl sum boundary) (phases kty n) := by
  phased [impl]

end Balance

namespace Lookup
open Fractions
variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- Every value is looked up (in `f`) as often as the table's multiplicities (`μ` on `t`) say. -/
@[reducible]
def contract (n l : ℕ) : Interface F where
  input := (Vector F n × Vector F n) × Vector F l
  inputCType := (.natives n ×ᵗ .natives n) ×ᵗ .natives l
  output := Unit
  outputCType := .unit
  Spec := fun ((t, μ), f) _ => ∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) = ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), μ[i]
  ProverAssumptions := fun ((t, μ), f) => ∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) = ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), μ[i]

/-- The check, given a challenge: the table, its multiplicities, and the looked-up values are
committed. -/
@[reducible]
def interface (kty : CType F K) (n l : ℕ) : Interface F := (contract n l).withChallenge kty

@[reducible]
def phases (kty : CType F K) (n l : ℕ) : (interface kty n l).Phases := Interface.withChallenge.phases _ _

omit [DecidableEq F] in
variable (K) in
/-- What the final sum stands for, in the committed values `t ++ (μ ++ f)`. -/
noncomputable def R (n l : ℕ) (c : Vector F (n + (n + l))) : RatFunc K :=
  ∑ i : Fin n, RatFunc.C (algebraMap F K c[Fin.natAdd n (Fin.castAdd l i)]) /
      (RatFunc.X - RatFunc.C (algebraMap F K c[Fin.castAdd (n + l) i])) -
    ∑ j : Fin l, (RatFunc.X - RatFunc.C (algebraMap F K c[Fin.natAdd n (Fin.natAdd n j)]))⁻¹

omit [DecidableEq F] in
theorem R_append {n l : ℕ} (t μ : Vector F n) (f : Vector F l) :
    R K n l (t ++ (μ ++ f)) =
      ∑ i : Fin n, RatFunc.C (algebraMap F K μ[i]) / (RatFunc.X - RatFunc.C (algebraMap F K t[i])) -
        ∑ j : Fin l, (RatFunc.X - RatFunc.C (algebraMap F K f[j]))⁻¹ := by
  simp [R]

variable {B : Backend} [Field B.Native] [DecidableEq B.Native] [Algebra B.Native K] {kty : CType B.Native K}
  [kty.Faithful] {n l : ℕ}
  (arith : ∀ n, Impl B (Arith.interface n)) (karith : ∀ n, Impl B (KArith.interface kty n))
  (sumT : Impl B (LogUpSum.interface kty n)) (sumF : Impl B (LogUpSum.interface kty l))
  (boundary : Impl B (AssertIdentity.interface kty (n + (n + l)) (n + l) (R K n l)))

local notation "ι" => algebraMap B.Native K

omit [DecidableEq B.Native] in
/-- The two running sums together stand for the logUp rational function. -/
theorem represents_sum {α s₁ s₂ : K} {t μ : Vector B.Native n} {f : Vector B.Native l}
    (h_t : ∀ i : Fin n, α ≠ ι t[i]) (h_s₁ : s₁ = ∑ i : Fin n, ι μ[i] / (α - ι t[i]))
    (h_f : ∀ j : Fin l, α ≠ ι f[j]) (h_s₂ : s₂ = ∑ j : Fin l, ι (-1) / (α - ι f[j])) :
    s₁ + s₂ ≙[α] R K n l (t ++ (μ ++ f)) := by
  rw [R_append, sub_eq_add_neg, ← Finset.sum_neg_distrib, h_s₁, h_s₂]
  refine (Represents.sum _ fun i _ =>
    (Represents.const _).div (Represents.X.sub (Represents.const _)) (sub_ne_zero.mpr (h_t i))).add ?_
  refine (Represents.sum (f := fun j : Fin l => ι (-1) / (α - ι f[j])) _ fun j _ =>
    (Represents.const (ι (-1))).div (Represents.X.sub (Represents.const _)) (sub_ne_zero.mpr (h_f j))).congr ?_
  simp [neg_div]

/-- The table's sum, the lookups' sum, and a boundary. -/
noncomputable def impl : Impl B (interface kty n l) where
  main | (((t, μ), f), α) => do
    let negOne ← arith (.const (-1)) ()
    let s₁ ← sumT ((t, μ), α)
    let s₂ ← sumF ((f, Vector.replicate l negOne), α)
    let acc ← karith .add (s₁, s₂)
    boundary ((t ++ (μ ++ f), acc), α)
  spatial := by
    intro (((t, μ), f), α) s h
    obtain ⟨⟨⟨h_t, h_μ⟩, h_f⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left fun h =>
      (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    have h_rep : ∀ {x : B.Var} {S : Set B.Cell}, B.footprint x ⊆ S →
        B.footprintT (M := natives l) (Vector.replicate l x) ⊆ S := fun h => by
      rw [Backend.footprintT_natives]
      exact Set.iUnion_subset fun i => by simpa using h
    refine ⟨Set.empty_subset _, fun h_neg m₁ => ⟨?_, fun h_s₁ m₂ => ⟨?_, fun h_s₂ m₃ =>
      ⟨Set.union_subset (h_s₁.trans m₃) h_s₂, fun h_acc m₄ => ⟨?_, fun _ _ => Set.empty_subset _⟩⟩⟩⟩⟩
    · exact Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
        ⟨h_t.trans m₁, h_μ.trans m₁⟩, h_α.trans m₁⟩
    · exact Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
        ⟨h_f.trans (m₁.trans m₂), h_rep (h_neg.trans m₂)⟩, h_α.trans (m₁.trans m₂)⟩
    · have m := m₁.trans (m₂.trans (m₃.trans m₄))
      exact Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_ctypeProd_subset.mpr
        ⟨Backend.footprintT_append_subset (h_t.trans m) (Backend.footprintT_append_subset (h_μ.trans m) (h_f.trans m)),
          h_acc⟩, h_α.trans m⟩
  soundness := by
    intro s env (((t, μ), f), α) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_neg, ⟨h_t, h_s₁⟩, ⟨h_f, h_s₂⟩, h_add, h_boundary⟩ := h
    rw [Vector.map_append, Vector.map_append] at h_boundary
    have h_R := h_boundary ⟨by rw [h_add]; exact represents_sum h_t h_s₁ h_f (by simpa [h_neg] using h_s₂),
      by rw [R_append]; exact NumDegLE.sum_sub_sum_inv _ _ _⟩
    rw [R_append, sub_eq_zero] at h_R
    classical
    exact (logUp_iff_map (fun i : Fin n => (Vector.map (B.eval env) t)[i])
      (fun i : Fin n => (Vector.map (B.eval env) μ)[i]) (fun j : Fin l => (Vector.map (B.eval env) f)[j])).mp h_R
  completeness := by
    intro s env (((t, μ), f), α) h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    obtain ⟨h_neg, ⟨h_t, h_s₁⟩, ⟨h_f, h_s₂⟩, h_add, -⟩ := h
    rw [Vector.map_append, Vector.map_append, h_add]
    refine ⟨represents_sum h_t h_s₁ h_f (by simpa [h_neg] using h_s₂), ?_⟩
    rw [R_append, sub_eq_zero]
    classical
    exact (logUp_iff_map (fun i : Fin n => (Vector.map (B.eval env) t)[i])
      (fun i : Fin n => (Vector.map (B.eval env) μ)[i]) (fun j : Fin l => (Vector.map (B.eval env) f)[j])).mpr h_prover

instance [∀ n, Impl.NoEvents (arith n)] [∀ n, Impl.NoEvents (karith n)] [Impl.Phased sumT (LogUpSum.phases kty n)]
    [Impl.Phased sumF (LogUpSum.phases kty l)] [Impl.Phased boundary (AssertIdentity.phases _ _ _ _)] :
    Impl.Phased (impl arith karith sumT sumF boundary) (phases kty n l) := by
  phased [impl]

end Lookup
end Clean2
