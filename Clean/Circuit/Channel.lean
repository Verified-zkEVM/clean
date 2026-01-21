import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget
import Mathlib.Data.Finsupp.Defs

variable {F : Type} [Field F] {α : Type} {n : ℕ}
variable {Message : TypeMap} [ProvableType Message]

/--
A named list of field elements, used for multiset add operations.
-/
structure NamedList (F : Type) where
  name : String
  values : List F
deriving DecidableEq, Repr

namespace NamedList
variable [Field F]

/-- Evaluate a NamedList of expressions to a NamedList of field elements -/
def eval (env : Environment F) (nl : NamedList (Expression F)) : NamedList F :=
  { name := nl.name, values := nl.values.map (Expression.eval env) }

end NamedList

structure Channel (F : Type) (Message : TypeMap) [ProvableType Message] where
  name : String

def NamedList.IsAdded (env : Environment F) (nl : NamedList (Expression F)) (mult : Expression F) : Prop :=
  let n := nl.values.length
  let interactions := env.channels nl.name n
  let element : Vector F n := ⟨ .mk (nl.values.map env), List.length_map .. ⟩
  (env mult, element) ∈ interactions

/--
An `InteractionDelta` represents a change to an interaction (multiset argument), as a list
of (NamedList, multiplicity) pairs. This representation is computable and supports efficient
addition via list concatenation. Two deltas are semantically equal if they have the same
total multiplicity for each key (checked via `toFinsupp` in proofs).

Note: Multiplicities are in `F` (the field) rather than `ℤ` because the `enabled` flag used
in conditional emission (e.g., `emitStateWhen enabled mult state`) is a field element.
Using `F` avoids ambiguity in converting `F → ℤ` and allows direct multiplication
`enabled * mult` without coercion issues.
-/
abbrev InteractionDelta (F : Type) := List (NamedList F × F)

namespace InteractionDelta
variable {F : Type}

instance : Zero (InteractionDelta F) := ⟨[]⟩

instance : Inhabited (InteractionDelta F) := ⟨0⟩

/-- Create a singleton interaction delta with one named list and its multiplicity -/
def single (nl : NamedList F) (mult : F) : InteractionDelta F :=
  [(nl, mult)]

/-- Addition is list concatenation - semantic equality handles combining multiplicities -/
instance : Add (InteractionDelta F) := ⟨List.append⟩

/-- Negation: negate all multiplicities -/
def neg [Neg F] (d : InteractionDelta F) : InteractionDelta F :=
  d.map (fun (nl, m) => (nl, -m))

instance [Neg F] : Neg (InteractionDelta F) := ⟨neg⟩

variable [Field F]

/-- Get the total multiplicity for a key by summing all entries -/
def getMultiplicity [DecidableEq F] (nl : NamedList F) (d : InteractionDelta F) : F :=
  d.foldl (fun acc (k, v) => if k = nl then acc + v else acc) 0

/-- Convert to Finsupp for proofs (noncomputable) -/
noncomputable def toFinsupp [DecidableEq F] (d : InteractionDelta F) : Finsupp (NamedList F) F :=
  d.foldl (fun acc (nl, m) => acc + Finsupp.single nl m) 0

omit [Field F] in
@[circuit_norm] theorem add_eq_append (d1 d2 : InteractionDelta F) : d1 + d2 = d1 ++ d2 := rfl

omit [Field F] in
@[circuit_norm] theorem zero_eq_nil : (0 : InteractionDelta F) = [] := rfl

omit [Field F] in
@[circuit_norm] theorem add_zero' (d : InteractionDelta F) : d + 0 = d := List.append_nil d

omit [Field F] in
@[circuit_norm] theorem zero_add' (d : InteractionDelta F) : 0 + d = d := List.nil_append d

omit [Field F] in
theorem add_assoc' (d1 d2 d3 : InteractionDelta F) : (d1 + d2) + d3 = d1 + (d2 + d3) :=
  List.append_assoc d1 d2 d3

/-- AddMonoid instance for InteractionDelta.
    Note: Addition is list concatenation, so commutativity only holds semantically
    (same result via toFinsupp), not definitionally. -/
instance instAddMonoid : AddMonoid (InteractionDelta F) where
  add := (· + ·)
  add_assoc := add_assoc'
  zero := 0
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmulRec

@[circuit_norm]
theorem single_zero (nl : NamedList F) : single nl 0 = [(nl, 0)] := rfl

-- Semantic equality: two deltas are equal if they have the same toFinsupp
theorem toFinsupp_add [DecidableEq F] (d1 d2 : InteractionDelta F) :
    (d1 + d2).toFinsupp = d1.toFinsupp + d2.toFinsupp := by
  simp only [toFinsupp, add_eq_append]
  have h : ∀ (init : Finsupp (NamedList F) F) (l : List (NamedList F × F)),
      List.foldl (fun acc x => acc + Finsupp.single x.1 x.2) init l =
      init + List.foldl (fun acc x => acc + Finsupp.single x.1 x.2) 0 l := by
    intro init l
    induction l generalizing init with
    | nil => simp
    | cons hd' tl' ih' =>
      simp only [List.foldl_cons]
      rw [ih' (init + Finsupp.single hd'.1 hd'.2), ih' (0 + Finsupp.single hd'.1 hd'.2)]
      simp only [zero_add]
      rw [add_assoc]
  induction d1 with
  | nil => simp [List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.cons_append, List.foldl_cons]
    rw [h (0 + Finsupp.single hd.1 hd.2) (tl ++ d2)]
    simp only [zero_add]
    rw [ih]
    rw [h (Finsupp.single hd.1 hd.2) tl]
    rw [add_assoc]

theorem toFinsupp_single [DecidableEq F] (nl : NamedList F) (m : F) :
    (single nl m).toFinsupp = Finsupp.single nl m := by
  simp only [single, toFinsupp, List.foldl_cons, List.foldl_nil, zero_add]

theorem toFinsupp_zero [DecidableEq F] : toFinsupp (0 : InteractionDelta F) = 0 := by
  simp only [zero_eq_nil, toFinsupp, List.foldl_nil]

theorem toFinsupp_zero_mult [DecidableEq F] (nl1 nl2 : NamedList F) :
    toFinsupp ([(nl1, 0), (nl2, 0)] : InteractionDelta F) = 0 := by
  simp only [toFinsupp, List.foldl_cons, List.foldl_nil, Finsupp.single_zero, add_zero]

/-- Helper lemma: equality of InteractionDeltas implies equality of their toFinsupp. -/
theorem toFinsupp_eq_of_eq [DecidableEq F] {a b : InteractionDelta F} (h : a = b) :
    a.toFinsupp = b.toFinsupp := by rw [h]

/-- Helper lemma: if collectAdds = 0, then toFinsupp of collectAdds = toFinsupp 0. -/
theorem toFinsupp_zero_of_eq_zero [DecidableEq F] {a : InteractionDelta F} (h : a = 0) :
    a.toFinsupp = (0 : InteractionDelta F).toFinsupp := by rw [h]

/-- Relates a foldl over List.finRange to a Finset.sum at the toFinsupp level.
    This is useful for proving localAdds_eq when localAdds is defined using foldl. -/
theorem toFinsupp_foldl_finRange [DecidableEq F] {n : ℕ} (f : Fin n → InteractionDelta F) :
    ((List.finRange n).foldl (fun acc i => acc + f i) 0).toFinsupp =
    ∑ i : Fin n, (f i).toFinsupp := by
  induction n with
  | zero =>
    simp only [List.finRange_zero, List.foldl_nil, Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  | succ n ih =>
    -- Use the _last variant: finRange (n+1) = map castSucc (finRange n) ++ [last n]
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil]
    -- Show that foldl.toFinsupp = sum for the first n elements
    have ih' : ((List.finRange n).foldl (fun acc i => acc + f (Fin.castSucc i)) 0).toFinsupp =
        ∑ i : Fin n, (f (Fin.castSucc i)).toFinsupp := by
      have := ih (f ∘ Fin.castSucc)
      simp only [Function.comp_def] at this
      exact this
    rw [toFinsupp_add, ih', Fin.sum_univ_castSucc]

end InteractionDelta
