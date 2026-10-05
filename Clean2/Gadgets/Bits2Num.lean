/-
`bits2num`: the number with the given little-endian bits, for any number of bits.

A gadget with a shape parameter, written the way one writes it: `main n bits` is a loop over
`i < n` (`Circuit.foldr`: Horner's rule, `acc ↦ bits[i] + 2 * acc` from the top bit down), and
`n` is only the loop bound. It is one `Impl B Bits2Num.interface`; its proofs are one induction over the loop
each, against the interfaces of the `add`s it calls. The circuit only adds, so it is free on
both backends, whatever the width.

The spec is Clean's: assuming the inputs are bits, the output is the number they denote, and
that number is below `2^n`. Clean states the bound as `out.val < 2^n`; the native type here is
any field, so the bound is on the number itself, which is the same thing for `ZMod p`.
-/
module

public import Clean2.Gadgets.Bool
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

namespace Bits2Num

/-- The number with the given little-endian bits: `∑ bits[i] * 2^i`, reading a field element as
the bit `1` exactly when it is `1`. -/
noncomputable def fromBits {n : ℕ} (bits : Vector Native n) : ℕ :=
  open Classical in ∑ i : Fin n, (if bits[i] = 1 then 1 else 0) * 2 ^ (i : ℕ)

/-- `n` bits are below `2^n`. -/
theorem sum_lt_pow : ∀ (n : ℕ) (b : Fin n → ℕ), (∀ i, b i ≤ 1) → ∑ i, b i * 2 ^ (i : ℕ) < 2 ^ n
  | 0, _, _ => by simp
  | n + 1, b, hb => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
    have h₁ := sum_lt_pow n (fun i => b i.castSucc) fun i => hb _
    have h₂ : b (Fin.last n) * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ (hb (Fin.last n))
    omega

theorem fromBits_lt {n : ℕ} (bits : Vector Native n) : fromBits bits < 2 ^ n :=
  sum_lt_pow n _ fun _ => by split <;> omega

/-- On bits, the number is the weighted sum of the field elements themselves. -/
theorem cast_fromBits {n : ℕ} (bits : Vector Native n) (h : ∀ i : Fin n, IsBool bits[i]) :
    (fromBits bits : Native) = ∑ i : Fin n, bits[i] * 2 ^ (i : ℕ) := by
  simp only [fromBits, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases h i with h | h <;> simp [h]

/-- `n` bits in, their value out. -/
abbrev interface (n : ℕ) : Interface Native :=
  { input := Vector Native n, inputCType := .natives n,
    output := Native, outputCType := .native
    Assumptions := fun bits => ∀ i : Fin n, IsBool bits[i]
    Spec := fun bits out => out = fromBits bits ∧ fromBits bits < 2 ^ n }

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
def impl (arith : ∀ n, Impl B (Arith.interface n)) (n : ℕ) : Impl B (interface n) where
  main bits := do
    let zero ← arith (.const 0) ()
    Circuit.foldr n (fun i acc => step arith bits[i] acc) zero
  consistent := by
    intro bits s
    simp only [circuit_norm]
    exact loop_consistent arith n _ _ _
  spatial := by
    intro bits s h_in
    simp only [circuit_norm] at h_in ⊢
    refine ⟨Set.empty_subset _, fun h_zero h_mono => ?_⟩
    exact loop_local arith n _ _ _ _ (fun i => (Backend.footprint_getElem_subset h_in i i.isLt).trans h_mono) h_zero id
  soundness := by
    intro s env bits h_bool h
    simp only [circuit_norm] at h_bool h ⊢
    obtain ⟨h_zero, h_loop⟩ := h
    have h_val := loop_sound arith n (fun i => bits[i]) _ _ env h_loop
    have h_cast := cast_fromBits (bits.map (B.eval env)) h_bool
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_val h_cast ⊢
    rw [h_val, h_zero, mul_zero, add_zero]
    exact ⟨h_cast.symm, fromBits_lt _⟩
  completeness := by
    intro s env bits h _
    simp only [circuit_norm] at h ⊢
    exact loop_complete arith n _ _ _ _ h.2

end Bits2Num

def bits2numExpr (n : ℕ) : Impl (ExprBackend Native) (Bits2Num.interface n) := Bits2Num.impl ExprBackend.arith n
def bits2numR1CS (n : ℕ) : Impl (R1CS Native) (Bits2Num.interface n) := Bits2Num.impl R1CS.arith n

/-! ### One implementation, several widths

A caller picks the width at each call site: here the two halves of a value are converted with
the same `bits2num`, at the widths of the caller's own inputs. -/

/-- `(lo, hi) ↦ (bits2num lo, bits2num hi)`, over any `bits2num`. -/
def twoWidths {B : Backend} [Field B.Native] (bits2num : ∀ n, Impl B (Bits2Num.interface n)) {m k : ℕ}
    (lo : Vector B.Var m) (hi : Vector B.Var k) : Circuit B (B.Var × B.Var) := do
  let a ← bits2num m lo
  let b ← bits2num k hi
  return (a, b)

/-- Linear, so free on both backends, at any width. -/
example (bits : Vector (Expr Native) 8) (s : ℕ) : (bits2numExpr (Native := Native) 8).advance bits s = s := rfl
example (bits : Vector (LinComb Native) 8) (s : ℕ) : (bits2numR1CS (Native := Native) 8).advance bits s = s := rfl
example (bits : Vector (LinComb Native) 8) (s : ℕ) :
    ((bits2numR1CS (Native := Native) 8).main bits |>.operations s).toFlat = [] := rfl
example (lo : Vector (LinComb Native) 8) (hi : Vector (LinComb Native) 4) (s : ℕ) :
    ((twoWidths (bits2numR1CS (Native := Native)) lo hi).operations s).toFlat = [] := rfl

end Clean2
