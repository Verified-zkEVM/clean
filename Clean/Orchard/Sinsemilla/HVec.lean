import Clean.Circuit
import Clean.Utils.Vector

/-!
# Heterogeneous vectors of vectors as a `ProvableType`

`HVec ns F` is the Clean analogue of halo2's `Vec<Vec<AssignedCell>>` with
statically-known inner lengths: given a list of lengths `ns`, a value holds,
for each piece `i`, a `Vector F ns[i]`.

It is represented as one flat vector of length `ns.sum`, with `head`, `tail`,
`cons`, and `get` as views. This keeps the circuit encoding compact and avoids
making generic `ProvableType`/`ProvableStruct` evaluation unfold a large
recursive nested-pair type when `ns` is concrete.
-/

namespace Orchard.Sinsemilla

variable {F : Type}

/-- Heterogeneous vector of vectors with inner lengths `ns`, stored flat. -/
structure HVec (ns : List ℕ) (F : Type) where
  elems : Vector F ns.sum

namespace HVec

instance instProvableType (ns : List ℕ) : ProvableType (HVec ns) where
  size := ns.sum
  toElements x := x.elems
  fromElements v := { elems := v }
  fromElements_toElements _ := rfl
  toElements_fromElements _ := rfl

/-- The empty heterogeneous vector. -/
def nil : HVec [] F :=
  { elems := #v[] }

/-- Prepend a vector. -/
def cons {n : ℕ} {ns : List ℕ} (v : Vector F n) (rest : HVec ns F) :
    HVec (n :: ns) F :=
  { elems := v ++ rest.elems }

/-- The first inner vector. -/
def head {n : ℕ} {ns : List ℕ} (f : HVec (n :: ns) F) : Vector F n :=
  Vector.cast (by simp) (f.elems.take n)

/-- The remaining heterogeneous vector. -/
def tail {n : ℕ} {ns : List ℕ} (f : HVec (n :: ns) F) : HVec ns F :=
  { elems := Vector.cast (by simp) (f.elems.drop n) }

@[simp] theorem head_cons {n : ℕ} {ns : List ℕ} (v : Vector F n) (rest : HVec ns F) :
    head (cons v rest) = v := by
  simp only [head, cons]
  exact Vector.cast_take_append_of_eq_length

@[simp] theorem tail_cons {n : ℕ} {ns : List ℕ} (v : Vector F n) (rest : HVec ns F) :
    tail (cons v rest) = rest := by
  simp only [tail, cons]
  exact congrArg HVec.mk Vector.cast_drop_append_of_eq_length

@[simp] theorem cons_head_tail {n : ℕ} {ns : List ℕ} (f : HVec (n :: ns) F) :
    cons (head f) (tail f) = f := by
  cases f with
  | mk elems =>
      simp only [cons, head, tail]
      congr
      exact Vector.append_take_drop

theorem eq_nil (f : HVec [] F) : f = nil := by
  cases f with
  | mk elems =>
      cases elems using Vector.casesOn with
      | mk arr h =>
          cases arr using Array.casesOn with
          | mk xs =>
              simp only [List.size_toArray] at h
              cases xs with
              | nil => rfl
              | cons x xs => simp at h

/-- Function-style access: the running sums of piece `i`. -/
def get : (ns : List ℕ) → HVec ns F → (i : Fin ns.length) → Vector F ns[i]
  | [], _, i => i.elim0
  | _ :: _, f, ⟨0, _⟩ => head f
  | _ :: ns, f, ⟨i + 1, h⟩ => get ns (tail f) ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- `eval` commutes with `head`. -/
theorem eval_head [FiniteField F] (env : Environment F) {n : ℕ} {ns : List ℕ}
    (v : Var (HVec (n :: ns)) F) :
    eval env (head v) = head (eval env v) := by
  simp only [head]
  rw [CircuitType.eval_var_fields]
  rw [CircuitType.eval_expression]
  change (Vector.cast _ (v.elems.take n)).map (Expression.eval env) =
    Vector.cast _ ((v.elems.map (Expression.eval env)).take n)
  rw [Vector.map_take]
  rfl

/-- `eval` commutes with `tail`. -/
theorem eval_tail [FiniteField F] (env : Environment F) {n : ℕ} {ns : List ℕ}
    (v : Var (HVec (n :: ns)) F) :
    eval env (tail v) = tail (eval env v) := by
  rw [CircuitType.eval_expression (M := HVec ns)]
  rw [CircuitType.eval_expression (M := HVec (n :: ns))]
  simp +instances only [tail, ProvableType.eval, instProvableType]
  congr
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_cast, Vector.getElem_drop]

/-- `eval` commutes with function-style heterogeneous-vector access. -/
theorem eval_get [FiniteField F] (env : Environment F) :
    (ns : List ℕ) → (v : Var (HVec ns) F) → (i : Fin ns.length) →
      eval env (get ns v i) = get ns (eval env v) i
  | [], _, i => i.elim0
  | _ :: _, v, ⟨0, _⟩ => eval_head env v
  | _ :: ns, v, ⟨i + 1, h⟩ => by
      have htail := eval_tail env v
      simpa only [get, htail] using eval_get env ns (tail v) ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- `eval` commutes with indexing a function-style heterogeneous-vector access. -/
theorem eval_getElem [FiniteField F] (env : Environment F) (ns : List ℕ)
    (v : Var (HVec ns) F) (i : Fin ns.length) (j : ℕ) (hj : j < ns[i]) :
    eval env ((get ns v i)[j]'hj) = (get ns (eval env v) i)[j]'hj := by
  rw [ProvableType.eval_field]
  rw [ProvableType.getElem_eval_fields]
  rw [eval_get]

/-- `eval` distributes over `cons`. -/
theorem eval_cons [FiniteField F] (env : Environment F) {n : ℕ} {ns : List ℕ}
    (a : Var (fields n) F) (b : Var (HVec ns) F) :
    (eval env (HVec.cons a b : Var (HVec (n :: ns)) F) : HVec (n :: ns) F)
      = HVec.cons (eval env a) (eval env b) := by
  rw [CircuitType.eval_expression (M := HVec (n :: ns))]
  rw [CircuitType.eval_expression (M := HVec ns)]
  simp +instances only [ProvableType.eval, instProvableType, cons, CircuitType.eval_var_fields]
  exact congrArg HVec.mk (Vector.map_append ..)

end HVec

end Orchard.Sinsemilla
