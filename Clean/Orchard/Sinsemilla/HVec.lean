import Clean.Circuit
import Clean.Utils.Vector

/-!
# Heterogeneous vectors of vectors as a `ProvableType`

`HVec ns F` is the Clean analogue of halo2's `Vec<Vec<AssignedCell>>` with statically-known
inner lengths: given a list of lengths `ns`, a value holds, for each piece `i`, a
`Vector F (ns.get i)`.

It is encoded as **nested pairs** (`ProvablePair (fields n₀) (ProvablePair (fields n₁) …)`),
i.e. honest data, not a `Fin`-indexed dependent function. This keeps the `ProvableType`
instance free (composition of the existing `ProvablePair`/`unit` instances) and — crucially —
keeps its definitional equality *structural*, so downstream circuits that instantiate it at a
concrete length list (e.g. `MerkleCRH`) stay within the elaboration budget. A dependent-function
encoding type-checks but makes that defeq blow up `circuit_proof_start`.

Function-style access is still available through `HVec.get`.
-/

namespace Orchard.Sinsemilla

variable {F : Type}

/-- Heterogeneous vector of vectors with inner lengths `ns`, as nested pairs. -/
def HVec : List ℕ → TypeMap
  | [] => unit
  | n :: ns => ProvablePair (fields n) (HVec ns)

instance instProvableType : (ns : List ℕ) → ProvableType (HVec ns)
  | [] => inferInstanceAs (ProvableType unit)
  | n :: ns =>
    haveI := instProvableType ns
    inferInstanceAs (ProvableType (ProvablePair (fields n) (HVec ns)))

namespace HVec

/-- The empty heterogeneous vector. -/
@[reducible] def nil : HVec [] F := ()

/-- Prepend a vector. -/
@[reducible] def cons {n : ℕ} {ns : List ℕ} (v : Vector F n) (rest : HVec ns F) :
    HVec (n :: ns) F := (v, rest)

/-- The first inner vector. -/
@[reducible] def head {n : ℕ} {ns : List ℕ} (f : HVec (n :: ns) F) : Vector F n := f.1

/-- The remaining heterogeneous vector. -/
@[reducible] def tail {n : ℕ} {ns : List ℕ} (f : HVec (n :: ns) F) : HVec ns F := f.2

@[simp] theorem head_cons {n : ℕ} {ns : List ℕ} (v : Vector F n) (rest : HVec ns F) :
    head (cons v rest) = v := rfl

@[simp] theorem tail_cons {n : ℕ} {ns : List ℕ} (v : Vector F n) (rest : HVec ns F) :
    tail (cons v rest) = rest := rfl

@[simp] theorem cons_head_tail {n : ℕ} {ns : List ℕ} (f : HVec (n :: ns) F) :
    cons (head f) (tail f) = f := rfl

theorem eq_nil (f : HVec [] F) : f = nil := rfl

/-- Function-style access: the running sums of piece `i`. -/
def get : (ns : List ℕ) → HVec ns F → (i : Fin ns.length) → Vector F ns[i]
  | [], _, i => i.elim0
  | _ :: _, f, ⟨0, _⟩ => f.1
  | _ :: ns, f, ⟨i + 1, h⟩ => get ns f.2 ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- `eval` commutes with function-style heterogeneous-vector access. -/
theorem eval_get [Field F] (env : Environment F) :
    (ns : List ℕ) → (v : Var (HVec ns) F) → (i : Fin ns.length) →
      eval env (get ns v i) = get ns (eval env v) i
  | [], _, i => i.elim0
  | _ :: _, v, ⟨0, _⟩ => by
      cases v
      rw [eval_pair]
      simp only [get]
  | _ :: ns, v, ⟨i + 1, h⟩ => by
      cases v with
      | mk head tail =>
          rw [eval_pair]
          simp only [get]
          exact eval_get env ns tail ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- `eval` distributes over `cons` (it is just `ProvablePair`'s `eval_pair`). -/
theorem eval_cons [Field F] (env : Environment F) {n : ℕ} {ns : List ℕ}
    (a : Var (fields n) F) (b : Var (HVec ns) F) :
    (eval env (HVec.cons a b : Var (HVec (n :: ns)) F) : HVec (n :: ns) F)
      = HVec.cons (eval env a) (eval env b) :=
  eval_pair (α := fields n) (β := HVec ns) env a b

end HVec

end Orchard.Sinsemilla
