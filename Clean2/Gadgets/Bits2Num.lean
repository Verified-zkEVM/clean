/-
`bits2num`: the number with the given little-endian bits, for any number of bits.

A gadget with a shape parameter, written the way one writes it: `main n bits` is a loop over
`i < n` (`Circuit.foldr`: Horner's rule, `acc ↦ bits[i] + 2 * acc` from the top bit down), and
`n` is only the loop bound. It is one `Impl B Bits2Num.interface`; its proofs are one induction over the loop
each, against the interfaces of the `add`s it calls. The circuit only adds, so it is free on
both backends, whatever the width.

The input is `n` booleans, at a synthetic type `bool`; the implementation is at `bit`, where a
boolean is one native element that is `0` or `1`. The spec: the output is the number the
booleans denote (which is below `2^n`: `Nat.ofBits_lt_two_pow`).
-/
module

public import Clean2.Gadgets.Bool
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Batteries.Data.Nat.Lemmas

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

namespace Bits2Num

/-- The number with the given little-endian bits, as a sum of powers of two. -/
theorem ofBits_eq_sum : ∀ {n : ℕ} (b : Fin n → Bool), Nat.ofBits b = ∑ i : Fin n, (b i).toNat * 2 ^ (i : ℕ)
  | 0, b => by simp [Nat.ofBits_zero]
  | n + 1, b => by
    rw [Nat.ofBits_succ, ofBits_eq_sum, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Function.comp_apply, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

/-- On bits, the number they denote is the weighted sum of the field elements themselves. -/
theorem cast_ofBits [DecidableEq Native] {n : ℕ} (bits : Vector Native n) (h : ∀ i : Fin n, IsBool bits[i]) :
    ((Nat.ofBits fun i : Fin n => decide (bits[i] = 1) : ℕ) : Native) = ∑ i : Fin n, bits[i] * 2 ^ (i : ℕ) := by
  simp only [ofBits_eq_sum, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases h i with h | h <;> simp [h]

/-- `n` booleans in, laid out as `bool`; the number they denote out. -/
@[reducible]
def interface (bool : CType Native Bool) (n : ℕ) : Interface Native where
  input := Vector Bool n
  inputCType := CType.vec n bool
  output := Native
  outputCType := .native
  Spec := fun bits out => out = ((Nat.ofBits fun i : Fin n => bits[i] : ℕ) : Native)

variable {B : Backend} [Field B.Native]

/-- One step of the loop: `(b, acc) ↦ b + 2 * acc`. -/
@[circuit_norm]
def step (arith : ∀ n, Impl B (Arith.interface n)) (b acc : B.Var) : Circuit B B.Var := do
  let twice ← arith .add (acc, acc)
  arith .add (b, twice)

/-! The loop, by induction on its bound. Each lemma is the corresponding proof obligation of
`impl`, for a loop over any variables `v 0, …, v (n - 1)`, from any state, with any initial
value, and (for the spatial one) with any continuation. -/
section Loop
variable (arith : ∀ n, Impl B (Arith.interface n)) (n : ℕ) (v : Fin n → B.Var) (z : B.Var)

theorem loop_consistent (s : B.State) :
    ((Circuit.foldr n (fun i acc => step arith (v i) acc) z).operations s).Consistent s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm]
    exact ih _ s

theorem loop_sound (s : B.State) (env : B.Cell → B.Native)
    (h : ((Circuit.foldr n (fun i acc => step arith (v i) acc) z).operations s).SoundnessHold env s) :
    B.eval env ((Circuit.foldr n (fun i acc => step arith (v i) acc) z).output s) =
      ∑ i : Fin n, B.eval env (v i) * 2 ^ (i : ℕ) + 2 ^ n * B.eval env z := by
  induction n generalizing s with
  | zero => simp only [circuit_norm, Finset.univ_eq_empty, Finset.sum_empty, pow_zero, zero_add, one_mul]
  | succ n ih =>
    simp only [circuit_norm] at h ih ⊢
    obtain ⟨h_loop, h_twice, h_out⟩ := h
    have h_acc := ih (fun i => v i.succ) s h_loop
    rw [h_out, h_twice, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc, ← Finset.sum_mul] at h_acc ⊢
    linear_combination 2 * h_acc

theorem loop_complete (s : B.State) (env : B.Cell → B.Native)
    (h : ((Circuit.foldr n (fun i acc => step arith (v i) acc) z).operations s).HonestCompleteness env s) :
    ((Circuit.foldr n (fun i acc => step arith (v i) acc) z).operations s).CompletenessHold env s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm] at h ⊢
    exact ih _ s h.1

theorem loop_local (s : B.State) (K : B.State → Prop)
    (h_v : ∀ i, B.footprint (v i) ⊆ B.Alloc s) (h_z : B.footprint z ⊆ B.Alloc s)
    (h_K : B.footprint ((Circuit.foldr n (fun i acc => step arith (v i) acc) z).output s) ⊆
        B.Alloc (((Circuit.foldr n (fun i acc => step arith (v i) acc) z).operations s).advance s) →
      K (((Circuit.foldr n (fun i acc => step arith (v i) acc) z).operations s).advance s)) :
    ((Circuit.foldr n (fun i acc => step arith (v i) acc) z).operations s).LocalHold s K := by
  induction n generalizing s K with
  | zero =>
    simp only [circuit_norm] at h_K ⊢
    exact h_K h_z
  | succ n ih =>
    have h_v' : ∀ i : Fin n, B.footprint (v i.succ) ⊆ B.Alloc s := fun i => h_v i.succ
    have h_post := (Ops.local_of_localHold (loop_consistent arith n _ z s)
      (ih _ s (fun s' => B.footprint ((Circuit.foldr n (fun i acc => step arith (v i.succ) acc) z).output s) ⊆ B.Alloc s')
        h_v' h_z id)).2
    have h_mono := Ops.alloc_mono (loop_consistent arith n (fun i => v i.succ) z s)
    have hc := loop_consistent arith n (fun i => v i.succ) z s
    simp only [circuit_norm] at h_K hc ⊢
    rw [Ops.localHold_append_of_consistent hc]
    refine ih _ s _ h_v' h_z fun _ => ?_
    simp only [circuit_norm, Set.union_subset_iff]
    refine ⟨⟨h_post, h_post⟩, fun h_twice h_mono' => ⟨⟨((h_v 0).trans h_mono).trans h_mono', h_twice⟩,
      fun h_out _ => h_K h_out⟩⟩

end Loop

/-- Horner's rule over the bits. One implementation for every `n`: `n` is only the loop bound. -/
def impl [DecidableEq B.Native] (arith : ∀ n, Impl B (Arith.interface n)) (n : ℕ) : Impl B (interface (bit B.Native) n) where
  main bits := do
    let zero ← arith (.const 0) ()
    Circuit.foldr n (fun i acc => step arith bits[i] acc) zero
  consistent := by
    intro bits s
    simp only [circuit_norm]
    exact loop_consistent arith n _ _ _
  spatial := by
    intro bits s h_in
    have h_in := Backend.footprintT_ctypeVec_subset.mp h_in
    simp only [circuit_norm] at h_in ⊢
    refine ⟨Set.empty_subset _, fun h_zero h_mono => ?_⟩
    exact loop_local arith n _ _ _ _ (fun i => (h_in i).trans h_mono) h_zero id
  soundness := by
    intro s env bits h_bool h
    simp only [circuit_norm] at h_bool h ⊢
    obtain ⟨h_zero, h_loop⟩ := h
    have h_val := loop_sound arith n (fun i => bits[i]) _ _ env h_loop
    have h_cast := cast_ofBits (bits.map (B.eval env)) h_bool
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_val h_cast ⊢
    rw [h_val, h_zero, mul_zero, add_zero]
    exact h_cast.symm
  completeness := by
    intro s env bits h _
    simp only [circuit_norm] at h ⊢
    exact loop_complete arith n _ _ _ _ h.2

end Bits2Num

end Clean2
