/-
A logUp lookup argument, as a user writes it.

A table `t` with multiplicities `m`, and lookups `f`. The identity
  `∑ m i / (X - t i) - ∑ 1 / (X - f j) = 0`
says that every value `y` is looked up as often as the table's multiplicities for `y` add up to,
in the field: `#{j | f j = y} = ∑_{t i = y} m i` (`logUp_iff`). Completeness needs the challenge
to avoid the table and the lookups, since the honest prover divides by `α - t i` and `α - f j`.

The symbolic argument is a uniqueness of partial fractions (`eq_zero_of_sum_div_eq_zero`): if
`∑_{y ∈ S} d y / (X - y) = 0` for distinct `y`, then every `d y` is zero.
-/
module

public import Clean2.Challenge.Identity
public import Clean2.Challenge.Fractions

@[expose] public section

namespace Clean2
open Polynomial

namespace LogUp
open Fractions
variable {F : Type} [Field F] [DecidableEq F]

/-- Every value is looked up as often as the table's multiplicities for it add up to. -/
@[reducible]
def interface (n l : ℕ) : Interface F where
  input := ((Vector F n × Vector F n) × Vector F l) × F
  inputCType := ((.natives n ×ᵗ .natives n) ×ᵗ .natives l) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun (((t, m), f), _) _ => ∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) = ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), m[i]
  ProverAssumptions := fun (((t, m), f), α) => (∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) = ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), m[i]) ∧
    (∀ i : Fin n, α ≠ t[i]) ∧ ∀ j : Fin l, α ≠ f[j]

/-- `∑ m i / (X - t i) - ∑ 1 / (X - f j)`, in the committed values `t ++ (m ++ f)`. -/
def expr (n l : ℕ) : RExpr F (n + (n + l)) :=
  .sum n (fun i => .leaf (Fin.natAdd n (Fin.castAdd l i)) / (.X - .leaf (Fin.castAdd (n + l) i))) -
    .sum l (fun j => .const 1 / (.X - .leaf (Fin.natAdd n (Fin.natAdd n j))))

variable {B : Backend} [Field B.Native] [DecidableEq B.Native]
  (identity : ∀ {k : ℕ} (e : RExpr B.Native k), Impl B (Identity.interface e))

def impl (n l : ℕ) : Impl B (interface n l) where
  main | (((t, m), f), α) => identity (expr n l) (t ++ (m ++ f), α)
  spatial := by
    intro (((t, m), f), α) s h
    obtain ⟨⟨⟨h_t, h_m⟩, h_f⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      fun h => (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_append_subset
      h_t (Backend.footprintT_append_subset h_m h_f), h_α⟩, fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env (((t, m), f), α) _ h
    simp only [circuit_norm] at h ⊢
    have h := h (by simp [expr])
    simp [expr, sub_eq_zero] at h
    simpa using (logUp_iff _ _ _).mp h
  completeness := by
    intro s env (((t, m), f), α) _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    obtain ⟨h_spec, h_t, h_f⟩ := h_prover
    have h := (logUp_iff (fun i => B.eval env t[i]) (fun i => B.eval env m[i]) (fun j => B.eval env f[j])).mpr
      (by simpa using h_spec)
    refine ⟨by simp [expr], by simpa [expr, sub_eq_zero] using h, ?_⟩
    simp_all [expr, sub_eq_zero]

end LogUp
end Clean2
