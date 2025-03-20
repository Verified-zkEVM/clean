import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

variable {α β : Type} {n : ℕ}

@[reducible, deprecated "use native Vector creation"]
def vec (l: List α) : Vector α l.length := ⟨ l.toArray, rfl ⟩

def fromList (l: List α) : Vector α l.length := ⟨ .mk l, rfl ⟩

namespace Vector
def len (_: Vector α n) : ℕ := n

@[simp]
def nil : Vector α 0 := #v[]

@[simp]
def cons (a: α) (v: Vector α n)  : Vector α (n + 1) :=
  ⟨ .mk (a :: v.toList), by simp ⟩

def get_eq {n} (v: Vector α n) (i: Fin n) : v.get i = v.toArray[i.val] := by
  simp only [get, List.get_eq_getElem, Fin.coe_cast]

/-- this is exactly what's needed to rewrite `v.get i` into a `List.getElem` if `n` is a concrete Nat -/
-- def get_eq_lt {n} [NeZero n] (v: Vector α n) (i : ℕ) (h: i < n := by norm_num) :
--   v.get ((Fin.instOfNatOfNeZeroNat (a:=i)).ofNat : Fin n) = v.val[i]'(by rw [v.prop]; exact h) := by
--   simp only [get_eq, OfNat.ofNat, Fin.val_ofNat', Nat.mod_eq_of_lt h]

@[simp]
theorem get_map {n} {f: α → β} {v: Vector α n} {i: Fin n} : get (map f v) i = f (get v i) := by
  simp only [get, map, Fin.coe_cast, Array.getElem_map, getElem_toArray]

@[simp]
theorem append_vec (v w: Array α) : v.toVector ++ w.toVector = ⟨ v ++ w, by simp ⟩ := rfl

-- map over monad
def mapMonad {M : Type → Type} {n} [Monad M] (v : Vector (M α) n) : M (Vector α n) :=
  match (v : Vector (M α) n) with
  | ⟨ .mk [], h ⟩ => pure ⟨ #[], h ⟩
  | ⟨ .mk (a :: as), (h : as.length + 1 = n) ⟩ => do
    let hd ← a
    let tl ← mapMonad ⟨ .mk as, rfl ⟩
    pure ⟨ .mk <| hd :: tl.toList, by simp only [Array.size_toArray, List.length_cons,
      Array.length_toList, size_toArray]; exact h⟩

/- induction principle for Vector.cons -/
def induct {motive : {n: ℕ} → Vector α n → Prop}
  (h0: motive nil)
  (h1: ∀ {n: ℕ} (a: α) {as: Vector α n}, motive as → motive (cons a as))
  {n: ℕ} (v: Vector α n) : motive v :=
  match v with
  | ⟨ .mk [], h ⟩ => by
    have : n = 0 := by rw [←h, List.length_eq_zero]
    subst this
    congr
  | ⟨ .mk (a::as), h ⟩ => by
    have : as.length + 1 = n := by rw [←h, Array.size_toArray, List.length_cons]
    subst this
    have ih := induct (n:=as.length) h0 h1 ⟨ .mk as, rfl ⟩
    let h' : motive ⟨ .mk (a :: as), rfl ⟩ := h1 a ih
    congr

/- induction principle for Vector.push -/
def induct_push {motive : {n: ℕ} → Vector α n → Prop}
  (h0: motive nil)
  (h1: ∀ {n: ℕ} {as: Vector α n} (a: α), motive as → motive (as.push a))
  {n: ℕ} (v: Vector α n) : motive v := by
  match v with
  | ⟨ .mk [], prop ⟩ =>
    have : n = 0 := by rw [←prop, List.length_eq_zero]
    subst this
    congr
  | ⟨ .mk (a::as), h ⟩ =>
    have : as.length + 1 = n := by rw [←h, Array.size_toArray, List.length_cons]
    subst this
    obtain ⟨ as', a', ih ⟩ := exists_push (xs := ⟨.mk (a :: as), rfl⟩)
    have ih' : motive as' := induct_push h0 h1 as'
    have h' := h1 a' ih'
    rwa [ih]

@[simp]
def init {n} (create: Fin n → α) : Vector α n :=
  match n with
  | 0 => nil
  | k + 1 =>
    (init (fun i : Fin k => create i)).push (create k)

def finRange (n : ℕ) : Vector (Fin n) n :=
  ⟨ .mk (List.finRange n), List.length_finRange n ⟩

def fill (n : ℕ) (a: α) : Vector α n :=
  match n with
  | 0 => nil
  | k + 1 => (fill k a).push a

instance [Inhabited α] {n: ℕ} : Inhabited (Vector α n) where
  default := fill n default
end Vector
